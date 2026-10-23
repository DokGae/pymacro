"""Quick controls: runtime copies, nested actions and compact window behavior."""
import copy
import json
import os
import threading
import unittest
from types import SimpleNamespace

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
from PyQt6 import QtCore, QtGui, QtWidgets, QtTest
from engine import Action, Condition, Macro, MacroEngine
from main import ActionEditDialog, MacroDialog, MacroWindow, ActionTreeWidget
from quick_toggle import QuickToggleWindow, ToggleSwitch, macro_actions
from test_execution_analysis import make_runner
from editor_view_state import collect_editor_view, restore_editor_view

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class Owner(QtWidgets.QWidget):
    def __init__(self, macros):
        super().__init__()
        self.macros = macros
        self._state = {}
        self.macro_table = QtWidgets.QTableWidget(len(macros), 1)

    def _macro_from_row(self, row):
        return self.macros[row]

    def _update_state(self, key, value):
        self._state[key] = value

    def _set_quick_toggle(self, row, key, enabled):
        for action, _ in macro_actions(self.macros[row]):
            if action.quick_toggle_id == key:
                action.enabled = enabled


class QuickToggleTests(unittest.TestCase):
    def test_serialization_and_old_profiles(self):
        action = Action(type='noop', quick_toggle_id='switch', quick_toggle_name='물약', enabled=False)
        self.assertEqual(Action.from_dict(action.to_dict()).quick_toggle_name, '물약')
        self.assertFalse(Action.from_dict(action.to_dict()).enabled)
        self.assertEqual(Action.from_dict({'type': 'noop'}).quick_toggle_id, '')

    def test_running_copy_observes_toggle_without_restart(self):
        action = Action(type='press', key='a', quick_toggle_id='switch')
        runner, engine = make_runner([copy.deepcopy(action)])
        engine._profile.macros = [Macro(trigger_key='a', actions=[action])]
        engine._lock = threading.RLock()
        engine.quick_action_enabled = lambda idx, act: MacroEngine.quick_action_enabled(engine, idx, act)
        MacroEngine.set_quick_toggle(engine, 0, 'switch', False)
        runner._run_actions(runner.macro.actions, {})
        engine._send_key.assert_not_called()
        MacroEngine.set_quick_toggle(engine, 0, 'switch', True)
        runner._run_actions(runner.macro.actions, {})
        self.assertTrue(engine._send_key.called)
        self.assertTrue(runner.macro.actions[0].enabled)

    def test_copied_macros_have_independent_runtime_states(self):
        engine = SimpleNamespace(_quick_toggle_states={(0, 'same'): False, (1, 'same'): True})
        action = Action(type='noop', quick_toggle_id='same')
        self.assertFalse(MacroEngine.quick_action_enabled(engine, 0, action))
        self.assertTrue(MacroEngine.quick_action_enabled(engine, 1, action))

    def test_nested_branches_and_stop_actions(self):
        parent = Action(type='if', enabled=False, actions=[Action(type='noop')],
                        elif_blocks=[(Condition(type='key', key='a'), [Action(type='noop')], '')],
                        else_actions=[Action(type='noop')])
        macro = Macro(trigger_key='a', actions=[parent], stop_actions=[Action(type='noop')])
        self.assertEqual([blocked for _, blocked in macro_actions(macro)], [False, True, True, True, False])

    def test_compact_window_sync_and_restore(self):
        action = Action(type='noop', name='자동 물약', quick_toggle_id='a')
        owner = Owner([Macro(trigger_key='a', name='숨겨진 매크로', actions=[action])])
        panel = QuickToggleWindow(owner)
        panel.show()
        APP.processEvents()
        switch = panel.findChild(ToggleSwitch)
        switch.click()
        self.assertFalse(action.enabled)
        panel.refresh()
        self.assertFalse(panel.findChildren(ToggleSwitch)[-1].isChecked())
        labels = [label.text() for label in panel.findChildren(QtWidgets.QLabel)]
        self.assertNotIn('숨겨진 매크로', labels)
        self.assertEqual(panel.windowModality(), QtCore.Qt.WindowModality.NonModal)
        panel.resize(320, 290)
        panel.close()
        self.assertFalse(owner._state['quick_toggle']['visible'])
        restored = QuickToggleWindow(owner)
        self.assertEqual(restored.size(), panel.size())
        restored.deleteLater()
        panel.deleteLater()
        owner.deleteLater()

    def test_editor_preserves_toggle_metadata(self):
        action = Action(type='noop', quick_toggle_id='one', quick_toggle_name='버프')
        editor = ActionEditDialog(action=action)
        result = editor.get_action()
        self.assertEqual(result.quick_toggle_id, 'one')
        self.assertEqual(result.quick_toggle_name, '버프')
        editor.quick_toggle_check.setChecked(False)
        self.assertEqual(editor.get_action().quick_toggle_id, '')
        editor.deleteLater()

    def test_copied_actions_get_separate_switches(self):
        action = Action(type='noop', quick_toggle_id='one')
        editor = MacroDialog(macro=Macro(trigger_key='a', actions=[action, copy.deepcopy(action)]))
        ids = [a.quick_toggle_id for a in editor.get_macro().actions]
        self.assertEqual(len(set(ids)), 2)
        editor.deleteLater()

    def test_external_switch_updates_profile_runtime_and_open_editor(self):
        action = Action(type='noop', quick_toggle_id='one')
        macro = Macro(trigger_key='a', actions=[action])
        tree = ActionTreeWidget()
        tree.load_actions([copy.deepcopy(action)])
        empty = ActionTreeWidget()
        calls = []
        owner = SimpleNamespace(
            _macro_from_row=lambda row: macro,
            profile=SimpleNamespace(macros=[copy.deepcopy(macro)]),
            engine=SimpleNamespace(set_quick_toggle=lambda *args: calls.append(args)),
            _shared_controller=SimpleNamespace(macro_editor_row=0, macro_editor=SimpleNamespace(
                main_action_tree=tree, parallel_action_tree=empty, stop_action_tree=empty)),
            _mark_dirty=lambda: calls.append('dirty'), _quick_toggle_window=None)
        MacroWindow._set_quick_toggle(owner, 0, 'one', False)
        self.assertFalse(action.enabled)
        self.assertFalse(owner.profile.macros[0].actions[0].enabled)
        self.assertFalse(tree.collect_actions()[0].enabled)
        self.assertEqual(calls, [(0, 'one', False), 'dirty'])
        tree.deleteLater()
        empty.deleteLater()

    def test_background_transparency_and_shutdown_visibility_restore(self):
        owner = Owner([Macro(trigger_key='a', actions=[Action(type='noop', quick_toggle_id='a')])])
        panel = QuickToggleWindow(owner)
        panel.show()
        APP.processEvents()
        self.assertTrue(panel.windowFlags() & QtCore.Qt.WindowType.FramelessWindowHint)
        panel.opacity_slider.setValue(65)
        QtTest.QTest.qWait(350)
        self.assertEqual(owner._state['quick_toggle']['background_opacity'], 35)
        self.assertLess(panel.grab().toImage().pixelColor(5, 100).alpha(), 100)
        self.assertEqual(panel.findChild(ToggleSwitch).grab().toImage().pixelColor(15, 15).alpha(), 255)
        panel.prepare_app_close()
        panel.close()
        self.assertTrue(owner._state['quick_toggle']['visible'])
        restored = QuickToggleWindow(owner)
        self.assertEqual(restored.opacity_slider.value(), 65)
        self.assertIs(restored.opacity_slider.parentWidget(), restored.header)
        restored.show()
        QtTest.QTest.keyClick(restored, QtCore.Qt.Key.Key_Escape)
        self.assertFalse(owner._state['quick_toggle']['visible'])
        self.assertFalse(restored.timer.isActive())
        restored.deleteLater()
        panel.deleteLater()
        owner.deleteLater()

    def test_toggle_is_independent_of_main_window_visibility(self):
        action = Action(type='noop', quick_toggle_id='a')
        owner = Owner([Macro(trigger_key='a', actions=[action])])
        panel = QuickToggleWindow(owner)
        panel.show()
        APP.processEvents()
        self.assertIsNone(panel.parentWidget())
        self.assertIsNone(panel.windowHandle().transientParent())
        panel.findChild(ToggleSwitch).click()
        APP.processEvents()
        self.assertFalse(action.enabled)
        self.assertFalse(owner.isVisible())
        owner.showMinimized()
        APP.processEvents()
        panel.findChild(ToggleSwitch).click()
        APP.processEvents()
        self.assertTrue(owner.isMinimized())
        owner.hide()
        self.assertTrue(panel.isVisible())
        panel.close()
        owner.close()
        panel.deleteLater()
        owner.deleteLater()

    def test_custom_header_drag_and_corner_resize(self):
        owner = Owner([])
        panel = QuickToggleWindow(owner)
        panel.show()
        APP.processEvents()

        def drag(widget, delta):
            local = QtCore.QPointF(5, 5)
            start = QtCore.QPointF(widget.mapToGlobal(QtCore.QPoint(5, 5)))
            for kind, point, buttons in (
                    (QtCore.QEvent.Type.MouseButtonPress, start, QtCore.Qt.MouseButton.LeftButton),
                    (QtCore.QEvent.Type.MouseMove, start + delta, QtCore.Qt.MouseButton.LeftButton),
                    (QtCore.QEvent.Type.MouseButtonRelease, start + delta, QtCore.Qt.MouseButton.NoButton)):
                event = QtGui.QMouseEvent(kind, local, point, QtCore.Qt.MouseButton.LeftButton,
                                          buttons, QtCore.Qt.KeyboardModifier.NoModifier)
                APP.sendEvent(widget, event)

        before = panel.pos()
        drag(panel.header, QtCore.QPointF(35, 20))
        self.assertEqual(panel.pos(), before + QtCore.QPoint(35, 20))
        before = panel.size()
        drag(panel.resize_grips[-1], QtCore.QPointF(40, 30))
        self.assertEqual(panel.size(), before + QtCore.QSize(40, 30))
        panel.close()
        panel.deleteLater()
        owner.deleteLater()

    def test_editor_presentation_roundtrips_through_json(self):
        macro = Macro(trigger_key='a', actions=[
            Action(type='if', name='outer', condition=Condition(type='key', key='a'),
                   actions=[Action(type='noop'), Action(type='noop', enabled=False)])]
                    + [Action(type='noop', name=str(i)) for i in range(65)])
        editor = MacroDialog(macro=macro)
        editor.resize(1050, 720)
        editor.show()
        tree = editor.main_action_tree
        APP.processEvents()
        tree.hide_disabled_button.setChecked(True)
        tree.topLevelItem(0).setExpanded(False)
        tree.setCurrentItem(tree.topLevelItem(30))
        tree.setColumnWidth(2, 390)
        tree.verticalScrollBar().setValue(220)
        editor.action_tabs.setCurrentIndex(1)
        state = json.loads(json.dumps(collect_editor_view(editor)))
        restored = MacroDialog(macro=macro)
        restored.show()
        APP.processEvents()
        restore_editor_view(restored, state)
        target = restored.main_action_tree
        self.assertTrue(target._hide_disabled)
        self.assertTrue(target.hide_disabled_button.isChecked())
        self.assertFalse(target.topLevelItem(0).isExpanded())
        self.assertEqual(target.currentItem().text(2), tree.currentItem().text(2))
        self.assertEqual(target.columnWidth(2), 390)
        self.assertEqual(restored.action_tabs.currentIndex(), 1)
        self.assertEqual(target.verticalScrollBar().value(), state['trees'][0]['scroll'])
        editor.close()
        restored.close()
        editor.deleteLater()
        restored.deleteLater()

    def test_locked_body_passes_clicks_but_buttons_remain_interactive(self):
        action = Action(type='noop', name='자동 물약', quick_toggle_id='a')
        owner = Owner([Macro(trigger_key='a', actions=[action])])
        panel = QuickToggleWindow(owner)
        panel.show()
        APP.processEvents()
        panel.lock_button.click()
        APP.processEvents()
        switch = panel.findChild(ToggleSwitch)
        controls = panel.control_region()
        point = switch.mapTo(panel, switch.rect().center())
        unlock = panel.lock_button.mapTo(panel, panel.lock_button.rect().center())
        title = panel.profile_title.mapTo(panel, panel.profile_title.rect().center())
        label = panel.body.findChild(QtWidgets.QLabel)
        label_point = label.mapTo(panel, label.rect().center())
        self.assertTrue(controls.contains(point))
        self.assertTrue(controls.contains(unlock))
        self.assertFalse(controls.contains(title))
        self.assertFalse(controls.contains(label_point))
        self.assertFalse(controls.contains(panel.opacity_slider.mapTo(panel, panel.opacity_slider.rect().center())))
        surface = panel.clickthrough_surface
        self.assertIsNotNone(surface)
        self.assertTrue(surface.windowFlags() & QtCore.Qt.WindowType.WindowTransparentForInput)
        self.assertTrue(surface.windowFlags() & QtCore.Qt.WindowType.WindowDoesNotAcceptFocus)
        self.assertTrue(surface.mask().contains(label_point))
        self.assertFalse(surface.mask().contains(point))
        self.assertEqual(panel.mask(), controls)
        self.assertFalse(panel.opacity_slider.isEnabled())
        self.assertTrue(all(grip.isHidden() for grip in panel.resize_grips))
        switch.click()
        self.assertFalse(action.enabled)
        panel.lock_button.click()
        self.assertFalse(panel.interaction_locked)
        self.assertTrue(panel.mask().isEmpty())
        self.assertFalse(surface.isVisible())
        self.assertTrue(panel.opacity_slider.isEnabled())
        panel.close()
        panel.deleteLater()
        owner.deleteLater()

    def test_lock_state_restores_and_surface_follows_window_lifecycle(self):
        owner = Owner([])
        owner._state['quick_toggle'] = {'locked': True, 'pinned': True}
        panel = QuickToggleWindow(owner)
        panel.show()
        APP.processEvents()
        self.assertTrue(panel.interaction_locked)
        self.assertTrue(panel.lock_button.isChecked())
        surface = panel.clickthrough_surface
        self.assertTrue(surface.isVisible())
        self.assertTrue(surface.windowFlags() & QtCore.Qt.WindowType.WindowStaysOnTopHint)
        panel.move(panel.pos() + QtCore.QPoint(20, 25))
        self.assertEqual(surface.geometry(), panel.geometry())
        panel.hide()
        self.assertFalse(surface.isVisible())
        panel.show()
        APP.processEvents()
        self.assertTrue(surface.isVisible())
        panel.close()
        self.assertTrue(owner._state['quick_toggle']['locked'])
        self.assertFalse(surface.isVisible())
        panel.deleteLater()
        owner.deleteLater()


if __name__ == '__main__':
    unittest.main()
