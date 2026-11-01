import copy
import json
import unittest

from PyQt6 import QtCore, QtGui, QtWidgets
from engine import Action, Macro
from quick_toggle import QuickToggleWindow, ToggleSwitch
from quick_toggle_groups import DragHandle, DropArea, linked_entries
from test_quick_toggle import APP, Owner


class GroupedToggleTests(unittest.TestCase):
    def setUp(self):
        self.a = Action(type='noop', name='암습', quick_toggle_id='a', quick_toggle_name='암습 사용')
        self.b = Action(type='noop', name='연속 암습', quick_toggle_id='b', quick_toggle_name=' 암습 사용 ', enabled=False)
        self.c = Action(type='noop', name='물약', quick_toggle_id='c', quick_toggle_name='물약')
        self.owner = Owner([Macro(trigger_key='a', actions=[self.a]), Macro(trigger_key='b', actions=[self.b, self.c])])
        self.owner.current_profile_path = 'D:/Ion/macro/test-profile.json'
        self.panel = QuickToggleWindow(self.owner)
        self.panel.show()
        APP.processEvents()

    def tearDown(self):
        self.panel.close()
        self.panel.deleteLater()
        self.owner.deleteLater()
        QtCore.QCoreApplication.sendPostedEvents(None, QtCore.QEvent.Type.DeferredDelete)
        APP.processEvents()

    def switches(self):
        APP.processEvents()
        return [s for s in self.panel.findChildren(ToggleSwitch) if s.isVisibleTo(self.panel)]

    def test_same_name_across_macros_is_one_mixed_switch(self):
        self.assertEqual(len(self.panel.linked), 2)
        switch = next(s for s in self.switches() if s.accessibleName() == '암습 사용')
        self.assertTrue(switch.mixed)
        switch.click()
        self.assertTrue(self.a.enabled and self.b.enabled)
        switch = next(s for s in self.switches() if s.accessibleName() == '암습 사용')
        switch.click()
        self.assertFalse(self.a.enabled or self.b.enabled)
        self.assertTrue(self.c.enabled)

    def test_unnamed_actions_with_same_display_name_stay_independent(self):
        self.a.quick_toggle_name = self.b.quick_toggle_name = ''
        self.b.name = self.a.name
        self.panel.refresh()
        self.assertEqual(len(self.panel.linked), 3)

    def test_group_master_updates_only_group_members(self):
        group = self.panel.add_group('전투')
        self.panel.move_toggle('name:암습 사용', group)
        APP.processEvents()
        button = next(b for b in self.panel.findChildren(QtWidgets.QToolButton, 'groupToggle')
                      if b.isVisibleTo(self.panel) and b.accessibleName() == '전투 모두 켜기')
        self.assertEqual(button.text(), '일부 ON')
        button.click()
        self.assertTrue(self.a.enabled and self.b.enabled)
        APP.processEvents()
        button = next(b for b in self.panel.findChildren(QtWidgets.QToolButton, 'groupToggle')
                      if b.isVisibleTo(self.panel) and b.accessibleName() == '전투 모두 끄기')
        self.assertEqual(button.text(), '전체 ON')
        button.click()
        self.assertFalse(self.a.enabled or self.b.enabled)
        self.assertTrue(self.c.enabled)

    def test_layout_persists_per_profile_without_changing_action_order(self):
        before = [copy.deepcopy(m.to_dict()) for m in self.owner.macros]
        first = self.panel.add_group('전투')
        second = self.panel.add_group('회복')
        self.panel.move_toggle('name:암습 사용', first)
        self.panel.move_toggle('name:물약', first, 'name:암습 사용')
        self.panel.move_group(second, first)
        self.panel.toggle_fold(first)
        self.panel.save_state()
        self.owner._state = json.loads(json.dumps(self.owner._state))
        other = QuickToggleWindow(self.owner)
        try:
            other.refresh()
            data = other.profile_layout()
            self.assertEqual([g['id'] for g in data['groups']], [second, first])
            self.assertTrue(data['groups'][1]['collapsed'])
            self.assertEqual(other.ordered_keys(), ['name:물약', 'name:암습 사용'])
            self.owner.current_profile_path = 'D:/Ion/macro/another-profile.json'
            other.refresh()
            self.assertEqual(other.profile_layout()['groups'], [])
            self.owner.current_profile_path = 'D:/Ion/macro/test-profile.json'
            other.refresh()
            self.assertEqual(other.profile_layout()['placements']['name:암습 사용'], first)
        finally:
            other.deleteLater()
        self.assertEqual(before, [m.to_dict() for m in self.owner.macros])

    def test_delete_group_keeps_toggles_and_enabled_states(self):
        group = self.panel.add_group('전투')
        self.panel.move_toggle('name:암습 사용', group)
        self.panel.remove_group(group)
        self.assertEqual(len(self.panel.linked), 2)
        self.assertNotIn('name:암습 사용', self.panel.profile_layout()['placements'])
        self.assertTrue(self.a.enabled)
        self.assertFalse(self.b.enabled)

    def test_lock_leaves_edit_mode_and_clips_all_scrolled_controls(self):
        self.panel.set_editing(True)
        self.assertTrue(self.panel.add_group_button.isVisible())
        self.panel.set_locked(True)
        self.assertFalse(self.panel.editing)
        self.assertFalse(self.panel.edit_button.isEnabled())
        self.assertFalse(self.panel.add_group_button.isVisible())
        self.panel.set_locked(False)
        self.assertTrue(self.panel.edit_button.isEnabled())

    def test_drag_drop_event_moves_toggle_to_group(self):
        group = self.panel.add_group('전투')
        self.panel.set_editing(True)
        APP.processEvents()
        source = next(h for h in self.panel.findChildren(DragHandle)
                      if h.isVisibleTo(self.panel) and h.key == 'name:물약')
        target = next(w for w in self.panel.findChildren(DropArea)
                      if w.isVisibleTo(self.panel) and w.group == group and w.key is None)
        # Qt's native QDrag supplies source(); the drop handler uses that identity
        # to reject cross-window drops rather than trusting external MIME data.
        class Event:
            def source(self): return source
            def mimeData(self):
                mime = QtCore.QMimeData()
                mime.setData('application/x-macro-quick-toggle', json.dumps(['toggle', 'name:물약']).encode())
                return mime
            def position(self): return QtCore.QPointF(2, 2)
            def acceptProposedAction(self): self.accepted = True
        event = Event()
        target.dropEvent(event)
        self.assertTrue(event.accepted)
        self.assertEqual(self.panel.profile_layout()['placements']['name:물약'], group)


if __name__ == '__main__':
    unittest.main()
