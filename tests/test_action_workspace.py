"""Headless Qt regression checks; no input driver, engine or user profile is run."""
import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import copy
import unittest
from PyQt6 import QtCore, QtGui, QtWidgets, QtTest
from engine import Action, Condition, Macro
from main import ActionTreeWidget, MacroDialog
from action_workspace import build_tree_panel, ROLE

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


def pump():
    for _ in range(5):
        APP.processEvents()


def fixture():
    return [Action(type='timer', timer_index=1, timer_value=0),
        Action(type='if', name='Outer', condition=Condition(type='key', key='a'), actions=[
            Action(type='press', name='A', key='a'),
            Action(type='if', name='Inner', condition=Condition(type='key', key='b'), actions=[
                Action(type='press', name='B', key='b'), Action(type='press', name='C', key='c')],
                elif_blocks=[(Condition(type='key', key='d'), [Action(type='press', key='d')], 'elif description')],
                has_else_branch=True, else_actions=[Action(type='press', name='Else', key='e')]),
            Action(type='sleep', sleep_ms=50)], has_else_branch=True,
            else_actions=[Action(type='press', key='f')]),
        Action(type='press', name='Last', key='z')]


class TreeTests(unittest.TestCase):
    def setUp(self):
        self.tree = ActionTreeWidget()
        self.panel = build_tree_panel(self.tree)
        self.panel.resize(1100, 700)
        self.tree.load_actions(fixture())
        self.panel.show()
        pump()

    def tearDown(self):
        self.panel.close()
        self.panel.deleteLater()
        pump()

    def outer(self):
        return self.tree.topLevelItem(1)

    def inner(self):
        return self.outer().child(1)

    def test_presentation_does_not_modify_actions(self):
        before = self.tree.collect_actions()
        self.tree.setCurrentItem(self.inner())
        self.tree.refresh_workspace()
        self.assertEqual(before, self.tree.collect_actions())
        self.assertEqual(sum(map(len, self.tree._ends.values())), 2)
        self.assertIn('#02 Inner', self.tree._find_else_header(self.inner()).text(2))
        self.assertEqual(self.tree.collect_actions()[1].actions[1].name, 'Inner')

    def test_move_many_preserves_order_and_branch(self):
        inner = self.inner()
        a, b = inner.child(0), inner.child(1)
        ok, _ = self.tree.transfer_items([b, a], inner, 'no')
        self.assertTrue(ok)
        action = self.tree.collect_actions()[1].actions[1]
        self.assertEqual([a.name for a in action.else_actions], ['Else', 'B', 'C'])
        self.assertFalse(action.actions)
        self.assertEqual(len(action.elif_blocks), 1)
        self.assertEqual(len(self.tree.selectedItems()), 2)

    def test_copy_if_includes_all_branches_and_no_aliases(self):
        outer = self.outer()
        inner = self.inner()
        ok, _ = self.tree.transfer_items([inner, inner.child(0)], outer, 'no', True)
        self.assertTrue(ok)
        actions = self.tree.collect_actions()
        original, clone = actions[1].actions[1], actions[1].else_actions[-1]
        self.assertEqual(original, clone)
        clone.actions[0].key = 'x'
        self.assertEqual(original.actions[0].key, 'b')

    def test_same_parent_forward_and_backward_moves(self):
        t = self.tree
        first, last = t.topLevelItem(0), t.topLevelItem(2)
        self.assertTrue(t.transfer_items([first], last, 'after')[0])
        self.assertEqual([a.type for a in t.collect_actions()], ['if','press','timer'])
        self.assertTrue(t.transfer_items([first], t.topLevelItem(0), 'before')[0])
        self.assertEqual([a.type for a in t.collect_actions()], ['timer','if','press'])

    def test_cycle_rejected_without_mutation(self):
        before = self.tree.collect_actions()
        for copying in (False, True):
            self.assertFalse(self.tree.transfer_items([self.outer()], self.inner(), 'yes', copying)[0])
            self.assertEqual(before, self.tree.collect_actions())

    def test_if_true_insert_precedes_elif_and_else(self):
        self.assertTrue(self.tree.transfer_items([self.tree.topLevelItem(2)], self.inner(), 'yes')[0])
        inner = self.tree.collect_actions()[1].actions[1]
        self.assertEqual(inner.actions[-1].name, 'Last')
        self.assertEqual(inner.elif_blocks[0][1][0].key, 'd')
        self.assertEqual(inner.else_actions[0].key, 'e')

    def test_focus_is_view_only_and_restores(self):
        before = self.tree.collect_actions()
        self.tree.setCurrentItem(self.inner())
        self.tree.toggle_focus()
        self.assertTrue(self.tree.topLevelItem(0).isHidden())
        self.assertTrue(self.outer().child(0).isHidden())
        self.assertFalse(self.inner().isHidden())
        self.assertTrue(self.tree.rootIndex().isValid())
        self.assertEqual(self.tree.collect_actions(), before)
        self.tree.toggle_focus()
        self.assertFalse(any(i.isHidden() for i in self.tree.items()))
        self.assertFalse(self.tree.rootIndex().isValid())
        self.assertEqual(self.tree.collect_actions(), before)

    def test_jump_else_and_location(self):
        self.tree.setCurrentItem(self.inner().child(0))
        self.tree.jump_else()
        self.assertEqual(self.tree.currentItem().data(0, ROLE), '__else__')
        self.assertIn('거짓', self.tree.path_text(self.tree.currentItem()))
        self.assertIn('Inner', self.tree.selection_label.text())

    def test_destination_bands_do_not_serialize(self):
        before = self.tree.collect_actions()
        self.tree.setCurrentItem(self.tree.topLevelItem(2))
        self.tree.begin_destination()
        bands = [b for bands in self.tree._bands.values() for b in bands]
        self.assertEqual(sum(b[0] == 'target' for b in bands), 0)
        self.assertEqual(before, self.tree.collect_actions())
        self.tree.cancel_destination()
        self.assertTrue(all(b[0] == 'end' for bands in self.tree._bands.values() for b in bands))

    def test_disabled_text_and_fixed_checkbox_indent(self):
        self.outer().setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        self.outer().setExpanded(True)
        self.tree.refresh_workspace()
        self.assertEqual(self.tree._disabled_text_brush(4).color().name(), '#c4c4c4')
        self.assertNotEqual(self.tree.itemDelegateForColumn(5).original.__class__.__name__, '_DepthCheckDelegate')

    def test_parallel_restrictions(self):
        self.tree.parallel_roots = True
        before = self.tree.collect_actions()
        self.assertFalse(self.tree.transfer_items([self.inner().child(0)], None, 'end')[0])
        self.assertEqual(before, self.tree.collect_actions())

    def test_disabled_scope_and_descendants_have_no_colored_pixels(self):
        tree = self.tree
        owner = self.outer()
        owner.setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        tree.setCurrentItem(self.inner().child(0))
        pump()
        image = tree.viewport().grab().toImage()
        for item in tree.items():
            if item is not owner and not tree._is_descendant(item, owner):
                continue
            self.assertIsNotNone(tree._disabled_depth(item))
            self.assertEqual(tree.html_row_color(item), '#ffffff')
            rect = tree.visualItemRect(item).intersected(image.rect())
            self.assertEqual(image.pixelColor(350, rect.top()+12).name(), '#ffffff')
            for y in range(rect.top()+1, rect.bottom()):
                for x in range(0, image.width(), 2):
                    color = image.pixelColor(x, y)
                    self.assertEqual(color.red(), color.green(), (item.text(1), x, y, color.name()))
                    self.assertEqual(color.green(), color.blue(), (item.text(1), x, y, color.name()))

    def test_html_colors_and_checkbox_survive_native_stylesheet(self):
        previous = APP.styleSheet()
        try:
            APP.setStyleSheet('QTreeView::item {background:white;} QTreeView::indicator:checked {background:white;color:white;}')
            self.tree.clearSelection()
            self.tree.setCurrentItem(None)
            pump()
            image = self.tree.viewport().grab().toImage()
            outer_rect = self.tree.visualItemRect(self.outer())
            inner_rect = self.tree.visualItemRect(self.inner())
            self.assertEqual(image.pixelColor(350, outer_rect.top()+12).name(), '#f0f5fc')
            self.assertEqual(image.pixelColor(350, inner_rect.top()+12).name(), '#f1f5ef')
            check = self.tree.check_rect(self.outer())
            self.assertEqual(image.pixelColor(check.left()+3,check.top()+3).name(), '#1673bf')
            grip = self.tree.grip_rect(self.outer().child(0))
            # Antialiased dots blend at fractional pixel boundaries but remain visible.
            dot = image.pixelColor(grip.left()+5,grip.top()+3)
            self.assertLess(dot.lightness(), 200)
            self.assertGreater(dot.blue(), dot.red())
        finally:
            APP.setStyleSheet(previous)

    def test_mouse_multiselect_and_last_child_selection(self):
        self.tree.clearSelection()
        for item, modifier in [(self.tree.topLevelItem(0), QtCore.Qt.KeyboardModifier.NoModifier),
                                (self.tree.topLevelItem(2), QtCore.Qt.KeyboardModifier.ControlModifier)]:
            rect = self.tree.visualItemRect(item)
            QtTest.QTest.mouseClick(self.tree.viewport(), QtCore.Qt.MouseButton.LeftButton, modifier,
                                   QtCore.QPoint(250, rect.top()+10))
        self.assertEqual(len(self.tree.selectedItems()), 2)
        before = self.tree.collect_actions()
        last = self.tree._find_else_header(self.inner()).child(0)
        rect = self.tree.visualItemRect(last)
        QtTest.QTest.mouseClick(self.tree.viewport(), QtCore.Qt.MouseButton.LeftButton,
                               pos=QtCore.QPoint(250, rect.top()+10))
        self.assertIs(self.tree.currentItem(), last)
        self.assertEqual(rect.height(), self.tree.row_height)
        self.assertEqual(before, self.tree.collect_actions())

    def test_local_target_copies_and_keeps_source(self):
        tree = self.tree
        tree.setCurrentItem(tree.topLevelItem(2))
        tree.begin_destination()
        pump()
        target = self.inner()
        tree.choose_destination(target)
        row = next(i for i, (_,where) in enumerate(tree._targets) if where=='no')
        tree.destination_list.setCurrentRow(row)
        self.assertEqual(tree.collect_actions()[-1].name,'Last')
        tree.apply_destination(True)
        result = tree.collect_actions()
        self.assertEqual(result[-1].name, 'Last')
        self.assertEqual(result[1].actions[1].else_actions[-1].name, 'Last')
        self.assertFalse(tree.destination_panel.isVisible())

    def test_prepared_move_requires_explicit_commit_and_cancel_keeps_data(self):
        tree = self.tree
        before = tree.collect_actions()
        source = tree.topLevelItem(2)
        tree.setCurrentItem(source)
        QtTest.QTest.keyClick(tree, QtCore.Qt.Key.Key_X, QtCore.Qt.KeyboardModifier.ControlModifier)
        self.assertEqual(tree._destination_items, [source])
        rect = tree.visualItemRect(self.inner())
        QtTest.QTest.mouseClick(tree.viewport(), QtCore.Qt.MouseButton.LeftButton,
                               pos=QtCore.QPoint(300, rect.top()+10))
        self.assertTrue(tree.target_card.isVisible())
        self.assertEqual(tree.collect_actions(), before)
        tree.cancel_destination()
        self.assertFalse(tree.target_card.isVisible())
        self.assertEqual(tree.collect_actions(), before)

    def test_selection_uses_teal_background_and_clear_edge(self):
        self.tree.setCurrentItem(self.outer().child(0))
        pump()
        image = self.tree.viewport().grab().toImage()
        rect = self.tree.visualItemRect(self.outer().child(0))
        self.assertEqual(image.pixelColor(350, rect.top()+12).name(), '#d5f0ec')
        self.assertEqual(image.pixelColor(2, rect.top()+12).name(), '#159a87')
        self.assertIn('하위 포함 총', self.tree.selection_label.text())

    def test_local_move_is_undoable(self):
        tree = self.tree
        source = tree.topLevelItem(2)
        tree.setCurrentItem(source)
        tree.begin_destination()
        tree.choose_destination(self.inner())
        row = next(i for i,(_,where) in enumerate(tree._targets) if where=='yes')
        tree.destination_list.setCurrentRow(row)
        tree.apply_destination()
        self.assertEqual(tree.collect_actions()[1].actions[1].actions[-1].name,'Last')
        self.assertEqual(len(tree.collect_actions()),2)

    def test_body_drag_cannot_start(self):
        self.tree._grip_pressed = False
        self.tree.startDrag(QtCore.Qt.DropAction.MoveAction)
        self.assertIsNone(self.tree._drop_feedback)

    def test_if_grip_selects_without_folding(self):
        tree = self.tree
        owner = self.inner()
        expanded = owner.isExpanded()
        self.assertFalse(tree.grip_rect(owner).intersects(tree.fold_rect(owner)))
        QtTest.QTest.mousePress(tree.viewport(), QtCore.Qt.MouseButton.LeftButton,
                               pos=tree.grip_rect(owner).center())
        self.assertTrue(tree._grip_pressed)
        self.assertIs(tree.currentItem(), owner)
        self.assertEqual(owner.isExpanded(), expanded)
        QtTest.QTest.mouseRelease(tree.viewport(), QtCore.Qt.MouseButton.LeftButton,
                                 pos=tree.grip_rect(owner).center())

    def test_whole_if_moves_inside_another_if_and_back_to_same_level(self):
        tree = self.tree
        tree.load_actions([Action(type='if', name='Target', condition=Condition(type='key', key='a')),
                           fixture()[1]])
        pump()
        target, source = tree.topLevelItem(0), tree.topLevelItem(1)
        original = copy.deepcopy(tree.collect_actions()[1])
        self.assertTrue(tree.transfer_items([source], target, 'yes')[0])
        self.assertEqual(tree.collect_actions()[0].actions[0], original)
        self.assertIs(source.parent(), target)
        self.assertTrue(tree.transfer_items([source], target, 'after')[0])
        self.assertIsNone(source.parent())
        self.assertEqual(tree.collect_actions()[1], original)
        self.assertFalse(tree.collect_actions()[0].actions)

    def test_drop_press_into_empty_collapsed_if(self):
        tree = self.tree
        tree.load_actions([Action(type='if', condition=Condition(type='key', key='a')),
                           Action(type='press', key='b')])
        owner, source = tree.topLevelItem(0), tree.topLevelItem(1)
        owner.setExpanded(False)
        pump()
        tree.setCurrentItem(source)

        class Drop:
            accepted = False
            def position(self):
                return QtCore.QPointF(tree.fold_rect(owner).center())
            def source(self):
                return tree
            def modifiers(self):
                return QtCore.Qt.KeyboardModifier.NoModifier
            def setDropAction(self, action):
                self.action = action
            def accept(self):
                self.accepted = True
            def ignore(self):
                self.accepted = False

        event = Drop()
        self.assertEqual(tree._drop_target(event), (owner, 'yes'))
        tree.dropEvent(event)
        self.assertTrue(event.accepted)
        self.assertEqual(tree.topLevelItemCount(), 1)
        self.assertIs(source.parent(), owner)
        self.assertTrue(owner.isExpanded())
        self.assertEqual(tree.collect_actions()[0].actions[0].key, 'b')

    def test_if_drop_center_enters_branch_and_edges_reorder(self):
        tree = self.tree
        owner = self.inner()
        rect = tree.visualItemRect(owner)

        class Hover:
            def position(self):
                return QtCore.QPointF(300, self.y)

        event = Hover()
        for offset, expected in [(1, 'before'), (12, 'yes'), (23, 'after')]:
            event.y = rect.top()+offset
            self.assertEqual(tree._drop_target(event), (owner, expected))

    def test_clicked_ifnot_parent_and_jump_button(self):
        tree = self.tree
        owner = self.inner()
        jump = tree.jump_rect(owner)
        QtTest.QTest.mouseClick(tree.viewport(), QtCore.Qt.MouseButton.LeftButton, pos=jump.center())
        branch = tree._find_else_header(owner)
        self.assertIs(tree.currentItem(), branch)
        rect = tree.visualItemRect(branch)
        QtTest.QTest.mouseClick(tree.viewport(), QtCore.Qt.MouseButton.LeftButton,
                               pos=QtCore.QPoint(250, rect.top()+10))
        self.assertIs(tree.currentItem(), owner)

    def test_collapse_footer_and_repeated_disabled_copy(self):
        self.inner().setExpanded(False)
        pump()
        self.assertEqual(sum(map(len, self.tree._ends.values())), 1)
        self.outer().child(0).setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        for _ in range(3):
            item = self.outer().child(0)
            self.tree.transfer_items([item], self.outer(), 'no', True)
        for item in self.tree.items():
            self.assertLessEqual(item.text(1).count('×'), 1)

    def test_no_move_over_branch_header(self):
        before = self.tree.collect_actions()
        marker = self.tree._find_else_header(self.inner())
        self.assertFalse(self.tree.transfer_items([self.tree.topLevelItem(2)], marker, 'after')[0])
        self.assertEqual(before, self.tree.collect_actions())

    def test_multi_selection_across_branch_headers_skips_markers(self):
        inner = self.inner()
        branch = self.tree._find_else_header(inner)
        action = inner.child(0)
        false_action = branch.child(0)
        ok, _ = self.tree.transfer_items([action, branch, false_action], self.outer(), 'no', True)
        self.assertTrue(ok)
        result = self.tree.collect_actions()[1]
        self.assertEqual([a.name for a in result.else_actions[-2:]], ['B','Else'])


class HistoryTests(unittest.TestCase):
    def setUp(self):
        self.dialog = MacroDialog(macro=Macro(trigger_key='z', actions=fixture()))
        self.dialog.resize(1200, 900)
        self.dialog.show()
        pump()
        self.tree = self.dialog.main_action_tree
        self.history = self.dialog.action_history

    def tearDown(self):
        self.dialog.close()
        self.dialog.deleteLater()
        pump()

    def test_move_copy_undo_redo_and_branching_history(self):
        before = self.tree.collect_actions()
        self.tree.transfer_items([self.tree.topLevelItem(2)], self.tree.topLevelItem(1), 'no', True)
        after = self.tree.collect_actions()
        self.assertNotEqual(before, after)
        self.history.undo()
        self.assertEqual(self.tree.collect_actions(), before)
        self.history.redo()
        self.assertEqual(self.tree.collect_actions(), after)
        self.history.undo()
        self.tree.topLevelItem(0).setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        pump()
        self.assertEqual(self.history.position, len(self.history.states)-1)
        self.assertFalse(self.history.redo_button.isEnabled())

    def test_delete_subtree_restores_elif_and_else(self):
        before = self.tree.collect_actions()
        self.tree.setCurrentItem(self.tree.topLevelItem(1))
        self.dialog._delete_action()
        pump()
        self.assertEqual(len(self.tree.collect_actions()), 2)
        self.history.undo()
        self.assertEqual(self.tree.collect_actions(), before)

    def test_add_edit_checkbox_stop_and_no_view_history(self):
        start = len(self.history.states)
        self.tree.collapse_all()
        self.tree.expandAll()
        self.tree.setCurrentItem(self.tree.topLevelItem(1))
        self.tree.toggle_focus()
        self.tree.toggle_focus()
        pump()
        self.assertEqual(start, len(self.history.states))
        item = self.tree._append_action_item(Action(type='press',key='q'))
        self.tree.renumber()
        pump()
        item.setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        pump()
        self.history.undo()
        self.assertTrue(self.tree.collect_actions()[-1].enabled)
        self.history.undo()
        self.assertEqual(len(self.tree.collect_actions()), 3)
        self.dialog.stop_group.setChecked(True)
        self.dialog.stop_action_tree._append_action_item(Action(type='up',key='q'))
        self.dialog.stop_action_tree.renumber()
        pump()
        self.history.undo()
        self.assertFalse(self.dialog.stop_group.isChecked())
        self.assertEqual(self.dialog.stop_action_tree.collect_actions(), [])

    def test_transfer_between_tabs_is_one_undo(self):
        before = self.tree.collect_actions()
        self.tree.setCurrentItem(self.tree.topLevelItem(1))
        self.dialog._transfer_selected_actions()
        pump()
        self.assertEqual(len(self.dialog.parallel_action_tree.collect_actions()), 1)
        self.history.undo()
        self.assertEqual(before, self.tree.collect_actions())
        self.assertFalse(self.dialog.parallel_action_tree.collect_actions())
        self.history.redo()
        self.assertEqual(len(self.dialog.parallel_action_tree.collect_actions()), 1)

    def test_action_properties_edit_undo(self):
        item = self.tree.topLevelItem(2)
        edited = copy.deepcopy(item.data(0, ROLE))
        edited.key = 'f8'
        edited.name = 'Edited'
        item.setData(0, ROLE, edited)
        item.setText(3, 'f8')
        pump()
        self.history.undo()
        self.assertEqual(self.tree.collect_actions()[-1].key, 'z')
        self.history.redo()
        self.assertEqual(self.tree.collect_actions()[-1].key, 'f8')

    def test_multi_clipboard_paste_selection_and_undo(self):
        before = self.tree.collect_actions()
        self.tree.clearSelection()
        self.tree.topLevelItem(0).setSelected(True)
        self.tree.topLevelItem(2).setSelected(True)
        self.dialog._copy_action()
        self.tree.setCurrentItem(self.tree.topLevelItem(1))
        self.dialog._paste_action()
        pump()
        self.assertEqual(len(self.tree.selectedItems()), 2)
        self.assertEqual(len(self.tree.collect_actions()), 5)
        self.history.undo()
        self.assertEqual(before, self.tree.collect_actions())

    def test_keyboard_undo_redo(self):
        self.dialog.activateWindow()
        self.tree.setFocus()
        pump()
        self.tree.topLevelItem(0).setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        pump()
        QtTest.QTest.keyClick(self.tree, QtCore.Qt.Key.Key_Z, QtCore.Qt.KeyboardModifier.ControlModifier)
        pump()
        self.assertTrue(self.tree.collect_actions()[0].enabled)
        QtTest.QTest.keyClick(self.tree, QtCore.Qt.Key.Key_Y, QtCore.Qt.KeyboardModifier.ControlModifier)
        pump()
        self.assertFalse(self.tree.collect_actions()[0].enabled)

    def test_parallel_names_not_affected_by_visible_ids(self):
        self.dialog.parallel_action_tree.load_actions([Action(type='if',name='병렬 IF 1',parallel_enabled=True,
                                                           condition=Condition(type='key',key='a'))])
        pump()
        self.assertEqual(self.dialog._parallel_task_name('병렬 IF'), '병렬 IF 2')

    def test_tab_layout_gives_actions_the_window_height(self):
        d = self.dialog
        self.assertEqual(d.action_tabs.count(), 5)
        self.assertEqual(d.action_tabs.currentIndex(), 0)
        self.assertFalse(d.trigger_table.isVisible())
        self.assertFalse(d.name_edit.isVisible())
        self.assertFalse(d.stop_action_tree.isVisible())
        self.assertGreater(self.tree.viewport().height(), d.height() * .55)
        d.action_tabs.setCurrentWidget(d.trigger_page)
        pump()
        self.assertTrue(d.trigger_table.isVisible())
        self.assertFalse(d.action_controls.isVisible())
        self.assertGreater(d.trigger_table.height(), d.height() * .5)
        d.action_tabs.setCurrentWidget(d.settings_page)
        pump()
        self.assertTrue(d.name_edit.isVisible())
        self.assertFalse(d.trigger_table.isVisible())

    def test_stop_tab_expands_and_keeps_action_target(self):
        d = self.dialog
        d.action_tabs.setCurrentWidget(d.stop_group)
        d.stop_group.setChecked(True)
        pump()
        self.assertTrue(d.stop_action_tree.isVisible())
        self.assertFalse(d.stop_collapse_btn.isVisible())
        self.assertFalse(d.action_controls.isVisible())
        self.assertGreater(d.stop_action_tree.height(), d.height() * .5)
        d._with_action_tree(d.stop_action_tree, lambda: None)
        self.assertIs(d.action_tree, d.stop_action_tree)
        d.action_tabs.setCurrentIndex(0)
        self.assertIs(d.action_tree, d.main_action_tree)

    def test_tab_switch_does_not_change_macro_or_history(self):
        d = self.dialog
        d.name_edit.setText('탭 테스트')
        d.desc_edit.setText('설명 유지')
        d.cycle_spin.setValue(7)
        before = d.get_macro().to_dict()
        history = len(self.history.states)
        for i in (3, 4, 2, 1, 0):
            d.action_tabs.setCurrentIndex(i)
            pump()
        self.assertEqual(d.get_macro().to_dict(), before)
        self.assertEqual(len(self.history.states), history)


if __name__ == '__main__':
    unittest.main()
