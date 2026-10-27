import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import unittest
import json
import tempfile
from types import SimpleNamespace
from unittest.mock import patch
from pathlib import Path
from PyQt6 import QtCore, QtWidgets, QtTest
from main import ActionEditDialog, ConditionDialog
from engine import Action, Condition, MacroCondition
APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

class EditorLayoutTests(unittest.TestCase):
    def test_preview_test_button_starts_stops_and_cleans_up(self):
        from unittest.mock import Mock
        stop = Mock()
        start = Mock(return_value=stop)
        dialog = ActionEditDialog(action=Action(type='if', condition=Condition(
            type='var', var_name='count', var_value_raw='1')), start_condition_debug=start)
        self.addCleanup(dialog.close)
        dialog.show()
        APP.processEvents()
        button = dialog.condition_test_btn
        self.assertTrue(button.isVisible())
        self.assertTrue(button.isEnabled())
        self.assertIs(button.parentWidget(), dialog.edit_cond_btn.parentWidget())
        button.click()
        self.assertEqual(button.text(), '중지')
        provider = start.call_args.args[0]
        self.assertEqual(provider()['condition'].var_name, 'count')
        dialog._condition.var_value_raw = '2'
        self.assertEqual(provider()['condition'].var_value_raw, '2')
        draft = ConditionDialog(cond=MacroCondition(condition=Condition(type='key', key='q')))
        self.addCleanup(draft.close)
        dialog._condition_preview_dialog = draft
        self.assertEqual(provider()['condition'].key, 'q')
        self.assertEqual(draft.debug_test_btn.text(), '테스트')
        dialog._condition_preview_dialog = None
        button.click()
        stop.assert_called_once()
        self.assertEqual(button.text(), '테스트')
        button.click()
        start.call_args.kwargs['on_stop']()
        self.assertEqual(button.text(), '테스트')
        button.click()
        dialog.reject()
        self.assertEqual(stop.call_count, 2)

    def test_variable_condition_choices_follow_macro_actions(self):
        from main import MacroDialog, ConditionNodeDialog
        from engine import Macro
        macro = MacroDialog(macro=Macro(name='test', trigger_key='a', actions=[
            Action(type='group', actions=[Action(type='set_var', var_name='몬스터탐색')])]),
            variable_provider=lambda category: ['등록변수'] if category == 'var' else [])
        self.addCleanup(macro.close)
        dialog = ConditionNodeDialog(cond=Condition(type='var', var_name='몬스터탐색'),
                                     variable_provider=macro._variable_provider)
        self.addCleanup(dialog.close)
        self.assertGreaterEqual(dialog.var_name_edit.findText('등록변수'), 0)
        self.assertIn('몬스터탐색', macro._variable_provider('var'))
        macro.main_action_tree.load_actions([Action(type='set_var', var_name='새변수')])
        dialog._refresh_var_name_combo()
        self.assertGreaterEqual(dialog.var_name_edit.findText('새변수'), 0)
        for op in ('ge', 'le', 'gt', 'lt'):
            dialog.var_op_combo.setCurrentIndex(dialog.var_op_combo.findData(op))
            self.assertFalse(dialog.var_value_edit.isHidden())
            dialog.var_value_edit.setText('10.5')
            condition = Condition.from_dict(dialog.get_condition().to_dict())
            self.assertEqual(condition.var_operator, op)
            self.assertEqual(condition.var_value_raw, '10.5')

    def test_variable_mode_and_name_changes_keep_value_clickable(self):
        dialog = ActionEditDialog(action=Action(type='set_var', var_name='변수1'))
        self.addCleanup(dialog.close)
        dialog.show()
        for mode in ('set', 'add', 'sub'):
            dialog.var_update_mode_combo.setCurrentIndex(
                dialog.var_update_mode_combo.findData(mode))
            dialog.var_name_edit.setEditText('몬스터탐색')
            for _ in range(4):
                APP.processEvents()
            self.assertTrue(dialog.var_help_label.isHidden())
            self.assertIn('몬스터탐색', dialog.var_value_edit.toolTip())
            field = dialog.var_value_edit
            point = field.mapToGlobal(field.rect().center())
            self.assertIs(APP.widgetAt(point), field)
            QtTest.QTest.mouseClick(APP.widgetAt(point), QtCore.Qt.MouseButton.LeftButton)
            self.assertTrue(field.hasFocus())
            field.selectAll()
            QtTest.QTest.keyClicks(field, '1')
            action = dialog.get_action()
            self.assertEqual(action.var_value_raw, '1')
            self.assertEqual(action.var_update_mode, mode)
            self.assertEqual(action.var_name, '몬스터탐색')

    def test_linked_group_edits_and_deletion_do_not_restore_shared_pixels(self):
        old = Condition(type='any', shared_ref='distance', conditions=[
            Condition(type='pixel', name='10M앞자리', region=(1, 2, 1, 1),
                      color=(255, 255, 255))])
        controller = SimpleNamespace(entries={'distance': {
            'name': '6m이상일때', 'condition': old.to_dict()}})
        controller.entries['distance']['condition']['shared_ref'] = None
        parent = ActionEditDialog(action=Action(type='if', condition=old))
        def edit(draft):
            draft.root_condition.conditions = [Condition(type='external',
                external_key='대상거리', external_operator='ge', external_value='7')]
            draft._refresh_condition_tree()
            self.assertIsNone(draft.root_condition.shared_ref)
            self.assertIn('대상거리 >= 7', parent.cond_label.text())
            self.assertNotIn('10M앞자리', parent.cond_label.text())
            draft.root_condition.conditions.clear()
            draft._refresh_condition_tree()
            self.assertNotIn('10M앞자리', parent.cond_label.text())
            self.assertIn('조건이 없습니다', parent.cond_label.text())
            draft.root_condition.conditions = [Condition(type='external',
                external_key='대상거리', external_operator='ge', external_value='7')]
            draft._refresh_condition_tree()
            return 1
        with patch('shared_ui.controller_for', return_value=controller), patch(
                'main._run_dialog_non_modal', side_effect=edit):
            parent._edit_condition()
            self.assertIsNone(parent.get_action().condition.shared_ref)
            self.assertIn('대상거리 >= 7', parent.cond_label.text())
        parent.close()

    def test_replacing_pixel_group_updates_parent_preview_immediately(self):
        dialog = ActionEditDialog(action=Action(type='if', condition=Condition(
            type='any', conditions=[Condition(type='pixel', name='10M앞자리',
                region=(1382, 466, 1, 1), color=(255, 255, 255))])))
        def edit(draft):
            draft.root_condition = Condition(type='any', conditions=[Condition(
                type='external', external_source='leesangjin-monitor',
                external_key='대상거리', external_operator='ge', external_value='7')])
            draft._refresh_condition_tree()
            self.assertIn('대상거리 >= 7', dialog.cond_label.text())
            self.assertNotIn('10M앞자리', dialog.cond_label.text())
            # Clicking edit again must keep the same draft instead of opening a stale copy.
            dialog._edit_condition()
            self.assertIs(dialog._condition_preview_dialog, draft)
            return 1
        with patch('main._run_dialog_non_modal', side_effect=edit) as run:
            dialog._edit_condition()
            self.assertEqual(run.call_count, 1)
        self.assertIn('대상거리 >= 7', dialog.cond_label.text())
        self.assertEqual(dialog.get_action().condition.conditions[0].external_value, '7')
        dialog.close()

    def test_condition_preview_tracks_shared_values_and_cancelled_draft(self):
        original = Condition(type='key', key='a')
        dialog = ActionEditDialog(action=Action(type='if', condition=original))
        controller = SimpleNamespace(entries={'distance': {
            'name': '6m이상일때', 'condition': Condition(type='external',
                external_source='leesangjin-monitor', external_key='대상거리',
                external_operator='ge', external_value='6').to_dict()}})
        from compact_action_layout import refresh_condition_summary
        with patch('shared_ui.controller_for', return_value=controller):
            def edit(draft):
                draft.root_condition = Condition(type='any', conditions=[
                    Condition(type='external', shared_ref='distance')])
                dialog._condition_preview_timer.timeout.emit()
                self.assertIn('>= 6', dialog.cond_label.text())
                controller.entries['distance']['condition']['external_value'] = '7'
                dialog._condition_preview_timer.timeout.emit()
                self.assertIn('>= 7', dialog.cond_label.text())
                self.assertNotIn('>= 6', dialog.cond_label.text())
                self.assertEqual(dialog._condition.to_dict(), original.to_dict())
                return 0
            with patch('main._run_dialog_non_modal', side_effect=edit):
                dialog._edit_condition()
            self.assertIn('키/마우스 a', dialog.cond_label.text())
            dialog._condition = Condition(type='external', shared_ref='distance')
            refresh_condition_summary(dialog)
            self.assertIn('>= 7', dialog.cond_label.text())
            controller.entries['distance']['condition']['external_value'] = '8'
            dialog._condition_preview_timer.timeout.emit()
            self.assertIn('>= 8', dialog.cond_label.text())
        dialog.close()

    def test_action_submodes_keep_fields_inside_rows(self):
        dialog = ActionEditDialog(action=Action(type='press', key='a'))
        dialog.show()
        dialog.resize(400, 420)
        for typ, attribute in [('process_control', 'process_control_action_combo'),
                ('sound_alert', 'sound_wait_mode_combo'), ('press', 'key_source_combo'),
                ('group', 'group_mode_combo'), ('set_var', 'var_update_mode_combo'),
                ('if', 'transition_confirm_combo')]:
            dialog.type_combo.setCurrentIndex(dialog.type_combo.findData(typ))
            if typ == 'if':
                dialog.transition_check.setChecked(True)
            combo = getattr(dialog, attribute)
            for index in range(combo.count()):
                combo.setCurrentIndex(index)
                for _ in range(4):
                    APP.processEvents()
                self.assertEqual(dialog.action_scroll.horizontalScrollBar().maximum(), 0,
                                 (typ, combo.currentData()))
                for wrapper, field, _ in dialog._compact_pairs:
                    if wrapper.isVisible() and field.isVisible():
                        self.assertLess(field.geometry().right(), wrapper.width(),
                                        (typ, combo.currentData()))
        dialog.close()

    def test_condition_summary_and_option_visibility(self):
        action = Action(type='if', condition=Condition(type='any', conditions=[
            Condition(type='key', key='a', name='실제 조건')]))
        dialog = ActionEditDialog(action=action)
        self.assertIn('실제 조건', dialog.cond_label.text())
        self.assertFalse(dialog.parallel_interval_spin.isEnabled())
        self.assertTrue(dialog.quick_toggle_name.isHidden())
        dialog.quick_toggle_check.setChecked(True)
        self.assertFalse(dialog.quick_toggle_name.isHidden())
        dialog.parallel_check.setChecked(True)
        self.assertTrue(dialog.parallel_interval_spin.isEnabled())
        self.assertTrue(dialog.parallel_hint.isHidden())
        self.assertIn('반복', dialog.parallel_check.toolTip())
        dialog.close()

    def test_enabled_fold_sections_restore_and_keep_values(self):
        dialog = ActionEditDialog(action=Action(type='press', key='a',
                                               key_delay_override_enabled=True))
        self.assertTrue(dialog.delay_section.toggle.isChecked())
        self.assertFalse(dialog.action_scroll.isAncestorOf(dialog.name_edit))
        before = dialog.get_action().to_dict()
        dialog.delay_section.setExpanded(False)
        self.assertEqual(dialog.get_action().to_dict(), before)
        dialog.delay_section.setExpanded(True)
        dialog.show()
        dialog.resize(400, 360)
        for _ in range(4):
            APP.processEvents()
        self.assertEqual(dialog.action_scroll.horizontalScrollBar().maximum(), 0)
        dialog.close()
        conditional = ActionEditDialog(action=Action(type='if', condition=Condition(type='key', key='a'),
                                                    transition_enabled=True))
        self.assertFalse(conditional.cond_label.isHidden())
        self.assertTrue(conditional.transition_section.toggle.isChecked())
        self.assertFalse(conditional.transition_section.body.isHidden())
        self.assertTrue(conditional.get_action().transition_enabled)
        conditional.close()

    def test_structure_arrows_keep_expand_controls_and_condition_data(self):
        root = Condition(type='all', conditions=[
            Condition(type='key', key='a', on_true=[Condition(type='key', key='b')]),
            Condition(type='key', key='c')])
        dialog = ConditionDialog(cond=MacroCondition(condition=root, actions=[]))
        dialog.show()
        tree = dialog.condition_tree
        tree.expandAll()
        for _ in range(4):
            APP.processEvents()
        group = tree.topLevelItem(0)
        leaf = group.child(0).child(0).child(0)
        tree.setCurrentItem(leaf)
        self.assertIn('소속', dialog.condition_selection.text())
        self.assertIn('참이면', dialog.condition_selection.text())
        self.assertFalse(tree.viewport().grab().isNull())
        rect = tree.visualRect(tree.indexFromItem(group))
        toggle = QtCore.QPoint(rect.left() - tree.indentation() // 2, rect.center().y())
        QtTest.QTest.mouseClick(tree.viewport(), QtCore.Qt.MouseButton.LeftButton, pos=toggle)
        self.assertFalse(group.isExpanded())
        QtTest.QTest.mouseClick(tree.viewport(), QtCore.Qt.MouseButton.LeftButton, pos=toggle)
        self.assertTrue(group.isExpanded())
        self.assertEqual(dialog.root_condition.to_dict(), root.to_dict())
        check = tree.visualRect(tree.indexFromItem(group, 3))
        for expected in (False, True):
            QtTest.QTest.mouseClick(tree.viewport(), QtCore.Qt.MouseButton.LeftButton, pos=check.center())
            self.assertEqual(dialog.root_condition.enabled, expected)
        # The checked indicator must remain visibly blue after a mouse toggle.
        rendered = tree.viewport().grab(check).toImage()
        self.assertTrue(any(rendered.pixelColor(x, y).name() == '#1673bf'
                            for x in range(rendered.width()) for y in range(rendered.height())))
        dialog.close()

    def test_condition_presentation_preserves_structure_and_checkbox(self):
        root = Condition(type='any', conditions=[
            Condition(type='all', name='묶음', conditions=[Condition(type='key', key='a')]),
            Condition(type='key', key='b', name='감지',
                      on_true=[Condition(type='key', key='c')],
                      on_false=[Condition(type='key', key='d')])])
        dialog = ConditionDialog(cond=MacroCondition(condition=root, actions=[]))
        tree = dialog.condition_tree
        self.assertEqual(dialog.root_condition.to_dict(), root.to_dict())
        self.assertEqual(tree.headerItem().text(3), '')
        self.assertEqual(tree.header().visualIndex(3), 0)
        self.assertEqual(tree.treePosition(), 0)
        self.assertTrue(tree.isColumnHidden(1))
        self.assertIn('OR', dialog.condition_logic.text())
        self.assertIn('모두 만족', tree.topLevelItem(0).text(0))
        branch = tree.topLevelItem(1)
        self.assertEqual(branch.child(0).text(0), '참이면 →')
        self.assertEqual(branch.child(1).text(0), '거짓이면 →')
        tree.setCurrentItem(branch.child(0).child(0))
        self.assertIn('참이면 →', dialog.condition_selection.text())
        branch.setCheckState(3, QtCore.Qt.CheckState.Unchecked)
        self.assertFalse(dialog.root_condition.conditions[1].enabled)
        self.assertEqual(branch.child(0).child(0).foreground(0).color().name(), '#9aa0a6')
        branch.setCheckState(3, QtCore.Qt.CheckState.Checked)
        self.assertEqual(dialog.root_condition.to_dict(), root.to_dict())
        for button in (dialog.copy_node_btn, dialog.paste_node_btn, dialog.delete_node_btn,
                       dialog.condition_up_btn, dialog.condition_down_btn,
                       dialog.debug_test_btn, dialog.viewer_btn):
            self.assertFalse(button.isHidden())
        self.assertEqual(dialog.debug_test_btn.text(), '테스트')
        self.assertEqual(dialog.viewer_btn.text(), '뷰어')
        dialog.close()

    def test_geometry_survives_cancel_save_and_restart(self):
        class StateOwner(QtWidgets.QWidget):
            def __init__(self, path):
                super().__init__()
                self.path = path
                self._state = json.loads(path.read_text()) if path.exists() else {}

            def _update_state(self, key, value):
                self._state[key] = value
                self.path.write_text(json.dumps(self._state))

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'state.json'
            owner = StateOwner(path)
            parent = QtWidgets.QWidget(owner)
            dialog = ActionEditDialog(parent, action=Action(type='press', key='a'))
            dialog.show()
            APP.processEvents()
            dialog.resize(610, 430)
            dialog.move(90, 85)
            for _ in range(4):
                APP.processEvents()
            expected = dialog.geometry()
            dialog.reject()
            self.assertIn('geometry', owner._state['action_editor'])
            owner.close()
            # A fresh owner reads disk, as it does after application restart.
            restarted = StateOwner(path)
            reopened = ActionEditDialog(restarted, action=Action(type='press', key='b'))
            reopened.show()
            for _ in range(4):
                APP.processEvents()
            self.assertEqual(reopened.geometry(), expected)
            reopened.resize(530, 410)
            APP.processEvents()
            expected = reopened.geometry()
            reopened.accept()
            again = ActionEditDialog(restarted)
            again.show()
            for _ in range(4):
                APP.processEvents()
            self.assertEqual(again.geometry(), expected)
            again.close()
            restarted.close()

    def test_single_page_preserves_values_and_sizes_short_fields(self):
        action = Action(type='press', key='ctrl+a', name='테스트', repeat=3)
        dialog = ActionEditDialog(action=action)
        dialog.show()
        for _ in range(4):
            APP.processEvents()
        self.assertEqual(dialog.get_action().to_dict(), action.to_dict())
        self.assertLessEqual(dialog.key_edit.width(), 120)
        self.assertLessEqual(dialog.key_source_combo.width(), 230)
        self.assertLessEqual(dialog.repeat_edit.width(), 80)
        def position(field):
            return field.mapTo(dialog.action_scroll.widget(), QtCore.QPoint())
        self.assertEqual(position(dialog.key_edit).y(), position(dialog.repeat_edit).y())
        self.assertTrue(dialog.action_main_key_edit.isHidden())
        self.assertFalse(dialog.once_check.isHidden())
        self.assertTrue(all(tab.isHidden() for tab in dialog.findChildren(QtWidgets.QTabWidget)))
        dialog.type_combo.setCurrentIndex(dialog.type_combo.findData('if'))
        self.assertFalse(dialog.edit_cond_btn.isHidden())
        self.assertFalse(dialog.transition_section.isHidden())
        self.assertTrue(dialog.key_edit.isHidden())
        dialog.close()

    def test_all_types_fit_compact_page_and_keep_category_headings(self):
        dialog = ActionEditDialog(action=Action(type='press', key='a'))
        dialog.show()
        dialog.resize(400, 360)
        headings = [dialog.type_combo.model().item(i) for i in range(dialog.type_combo.count())
                    if dialog.type_combo.itemData(i) is None]
        self.assertEqual(len(headings), 6)
        self.assertTrue(all(not item.isEnabled() and not item.isSelectable() for item in headings))
        for index in range(dialog.type_combo.count()):
            if dialog.type_combo.itemData(index) is None:
                continue
            dialog.type_combo.setCurrentIndex(index)
            for _ in range(4):
                APP.processEvents()
            self.assertEqual(dialog.action_scroll.horizontalScrollBar().maximum(), 0,
                             dialog.type_combo.currentData())
            for wrapper, field, _ in dialog._compact_pairs:
                if wrapper.isVisible() and field.isVisible():
                    self.assertGreaterEqual(field.geometry().left(), 0)
                    self.assertLessEqual(field.geometry().right(), wrapper.width(),
                                         (dialog.type_combo.currentData(), field.objectName()))
        dialog.close()

    def test_condition_move_preserves_branch_and_multiselection(self):
        root = Condition(type='all', conditions=[Condition(type='key', key=k) for k in 'abcd'])
        dialog = ConditionDialog(cond=MacroCondition(condition=root, actions=[]))
        parent = dialog.condition_tree.topLevelItem(0)
        parent.child(1).setSelected(True)
        parent.child(2).setSelected(True)
        dialog._move_condition_nodes(-1)
        self.assertEqual([c.key for c in dialog.root_condition.conditions], list('bcad'))
        dialog._move_condition_nodes(1)
        self.assertEqual([c.key for c in dialog.root_condition.conditions], list('abcd'))
        dialog.close()

if __name__ == '__main__':
    unittest.main()
