import os
import unittest
from unittest.mock import patch

os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")

from PyQt6 import QtCore, QtWidgets
from engine import Action, Condition, Macro
from main import ActionEditDialog, MacroDialog


def task(name="버프", interval=1.0, enabled=True):
    return Action(type="group", name=name, group_mode="all", parallel_enabled=True,
                  parallel_interval_sec=interval, enabled=enabled,
                  actions=[Action(type="press", key="f1"), Action(type="sleep", sleep_ms=50)])


class ParallelWorkspaceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.app = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

    def setUp(self):
        self.dialogs = []

    def tearDown(self):
        MacroDialog._action_clipboard = None
        self.app.processEvents()
        for dialog in self.dialogs:
            dialog.close()
            dialog.deleteLater()

    def editor(self, actions, **kwargs):
        dialog = MacroDialog(macro=Macro(trigger_key="f10", actions=actions, **kwargs))
        self.dialogs.append(dialog)
        return dialog

    def test_legacy_parallel_items_split_and_save_from_either_tab(self):
        dialog = self.editor([Action(type="press", key="a"), task(), Action(type="sleep", sleep_ms=100), task("힐", 2, False)])
        self.assertEqual(dialog.main_action_tree.topLevelItemCount(), 2)
        self.assertEqual(dialog.parallel_action_tree.topLevelItemCount(), 2)
        for tab in (0, 1):
            dialog.action_tabs.setCurrentIndex(tab)
            saved = dialog.get_macro()
            self.assertEqual([action.type for action in saved.actions[:2]], ["press", "sleep"])
            self.assertEqual([action.parallel_interval_sec for action in saved.actions[2:]], [1, 2])
            self.assertFalse(saved.actions[3].enabled)
        self.assertIn("활성 1개", dialog.parallel_summary.text())
        self.assertIn("(2)", dialog.action_tabs.tabText(1))
        reloaded = self.editor(Macro.from_dict(saved.to_dict()).actions)
        self.assertEqual(reloaded.parallel_action_tree.topLevelItemCount(), 2)

    def test_move_multiple_plain_actions_wraps_in_order_and_back(self):
        dialog = self.editor([Action(type="press", key="a"), Action(type="sleep", sleep_ms=150)])
        dialog.main_action_tree.selectAll()
        dialog._transfer_selected_actions()
        self.assertEqual(dialog.action_tabs.currentIndex(), 1)
        self.assertEqual(dialog.main_action_tree.topLevelItemCount(), 0)
        actions = dialog.parallel_action_tree.collect_actions()
        self.assertEqual(len(actions), 1)
        self.assertTrue(actions[0].parallel_enabled)
        self.assertEqual([action.type for action in actions[0].actions], ["press", "sleep"])
        dialog._transfer_selected_actions()
        self.assertEqual(dialog.action_tabs.currentIndex(), 0)
        self.assertEqual(dialog.parallel_action_tree.topLevelItemCount(), 0)
        self.assertFalse(dialog.get_macro().actions[0].parallel_enabled)
        self.assertEqual(len(dialog.get_macro().actions[0].actions), 2)

    def test_child_selection_changes_owning_task_interval(self):
        dialog = self.editor([task(), task("힐", 2)])
        dialog.action_tabs.setCurrentIndex(1)
        tree = dialog.parallel_action_tree
        tree.setCurrentItem(tree.topLevelItem(1).child(0))
        dialog.parallel_quick_interval.setValue(0.25)
        saved = dialog.get_macro()
        self.assertEqual([action.parallel_interval_sec for action in saved.actions], [1, 0.25])
        self.assertIn("0.25초마다", tree.topLevelItem(1).text(3))
        self.assertFalse(dialog.transfer_action_btn.isEnabled())
        tree.clearSelection()
        self.assertFalse(dialog.parallel_quick_interval.isEnabled())

    def test_required_editor_only_allows_group_and_if(self):
        dialog = ActionEditDialog(action=task(), parallel_required=True)
        self.dialogs.append(dialog)
        self.assertEqual({dialog.type_combo.itemData(i) for i in range(dialog.type_combo.count())}, {"group", "if"})
        self.assertTrue(dialog.parallel_check.isChecked())
        self.assertFalse(dialog.parallel_check.isEnabled())
        self.assertTrue(dialog.get_action().parallel_enabled)

    def test_zero_interval_quick_edit_and_dialog_roundtrip(self):
        dialog = self.editor([task()])
        dialog.action_tabs.setCurrentIndex(1)
        tree = dialog.parallel_action_tree
        tree.setCurrentItem(tree.topLevelItem(0))
        dialog.parallel_quick_interval.setValue(0)
        saved = Macro.from_dict(dialog.get_macro().to_dict())
        self.assertEqual(saved.actions[0].parallel_interval_sec, 0)
        self.assertIn("기본 속도", tree.topLevelItem(0).text(3))
        editor = ActionEditDialog(action=saved.actions[0], parallel_required=True)
        self.dialogs.append(editor)
        self.assertIn("0초", editor.parallel_interval_spin.text())
        self.assertEqual(editor.get_action().parallel_interval_sec, 0)

    def test_add_parallel_task_with_child_selected_stays_top_level(self):
        dialog = self.editor([task()])
        dialog.action_tabs.setCurrentIndex(1)
        tree = dialog.parallel_action_tree
        tree.setCurrentItem(tree.topLevelItem(0).child(0))
        with patch("main._run_dialog_non_modal", return_value=1):
            dialog._add_action(parallel_type="group")
        self.assertEqual(tree.topLevelItemCount(), 2)
        self.assertTrue(tree.collect_actions()[1].parallel_enabled)
        self.assertEqual(len(tree.collect_actions()[0].actions), 2)

    def test_edit_main_group_parallel_checkbox_moves_to_parallel_tab(self):
        dialog = self.editor([Action(type="group", name="감시")])
        dialog.main_action_tree.setCurrentItem(dialog.main_action_tree.topLevelItem(0))
        def accept(editor):
            editor.parallel_check.setChecked(True)
            return 1
        with patch("main._run_dialog_non_modal", side_effect=accept):
            dialog._edit_action()
        self.assertEqual(dialog.main_action_tree.topLevelItemCount(), 0)
        self.assertEqual(dialog.parallel_action_tree.topLevelItemCount(), 1)
        self.assertEqual(dialog.action_tabs.currentIndex(), 1)

    def test_paste_plain_actions_into_parallel_tab_wraps_them(self):
        dialog = self.editor([])
        dialog.action_tabs.setCurrentIndex(1)
        MacroDialog._action_clipboard = [Action(type="press", key="a"), Action(type="sleep", sleep_ms=50)]
        dialog._paste_action()
        result = dialog.get_macro().actions
        self.assertEqual(len(result), 1)
        self.assertTrue(result[0].parallel_enabled)
        self.assertEqual([action.type for action in result[0].actions], ["press", "sleep"])

    def test_paste_parallel_task_into_main_goes_to_parallel_tab(self):
        dialog = self.editor([])
        MacroDialog._action_clipboard = [task()]
        dialog._paste_action()
        self.assertEqual(dialog.main_action_tree.topLevelItemCount(), 0)
        self.assertEqual(dialog.parallel_action_tree.topLevelItemCount(), 1)

    def test_stop_tree_edit_context_restores_selected_tab(self):
        dialog = self.editor([Action(type="press", key="a"), task()], stop_actions=[Action(type="up", key="a")])
        dialog.action_tabs.setCurrentIndex(1)
        observed = []
        dialog._with_action_tree(dialog.stop_action_tree, lambda: observed.append(dialog.action_tree))
        self.assertEqual(observed, [dialog.stop_action_tree])
        self.assertIs(dialog.action_tree, dialog.parallel_action_tree)
        saved = dialog.get_macro()
        self.assertEqual(len(saved.actions), 2)
        self.assertEqual(saved.stop_actions[0].key, "a")

    def test_parallel_if_branches_and_disabled_state_survive(self):
        action = Action(type="if", name="체력", parallel_enabled=True, parallel_interval_sec=2,
                        condition=Condition(type="key", key="a"),
                        actions=[Action(type="press", key="f1")],
                        else_actions=[Action(type="press", key="f2")], has_else_branch=True)
        dialog = self.editor([action])
        item = dialog.parallel_action_tree.topLevelItem(0)
        item.setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        self.app.processEvents()
        result = dialog.get_macro().actions[0]
        self.assertTrue(result.parallel_enabled)
        self.assertFalse(result.enabled)
        self.assertEqual(result.actions[0].key, "f1")
        self.assertEqual(result.else_actions[0].key, "f2")
        self.assertIn("활성 0개", dialog.parallel_summary.text())

    def test_label_picker_only_offers_current_parallel_task_labels(self):
        first, second = task("첫 작업"), task("두 번째 작업")
        first.actions.append(Action(type="label", label="first_only"))
        second.actions.append(Action(type="label", label="second_only"))
        dialog = self.editor([Action(type="label", label="main_only"), first, second])
        dialog.action_tabs.setCurrentIndex(1)
        tree = dialog.parallel_action_tree
        tree.setCurrentItem(tree.topLevelItem(1).child(0))
        self.assertEqual(dialog._available_labels(), ["second_only"])
        dialog.action_tabs.setCurrentIndex(0)
        self.assertEqual(dialog._available_labels(), ["main_only"])


if __name__ == "__main__":
    unittest.main()
