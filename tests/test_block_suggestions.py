import copy
import unittest

from PyQt6 import QtCore, QtWidgets
from engine import Action, Condition, Macro, MacroProfile
from main import MacroDialog
from block_suggestions import discover, SuggestionDialog
from test_shared_blocks import APP, pump


class SuggestionTests(unittest.TestCase):
    def setUp(self):
        self.owner = QtWidgets.QWidget()
        self.owner.profile = MacroProfile()
        block = Action(type='if', name='침투', condition=Condition(type='key', key='a'),
                       actions=[Action(type='press', key='x'), Action(type='sleep', sleep_ms=17)])
        self.dialog = MacroDialog(self.owner, macro=Macro(trigger_key='z', actions=[
            copy.deepcopy(block), Action(type='press', key='b'), copy.deepcopy(block)]))
        self.blocks = self.dialog.block_workspace
        self.tree = self.dialog.main_action_tree
        pump()

    def tearDown(self):
        pump()
        self.owner.close()
        self.owner.deleteLater()
        QtCore.QCoreApplication.sendPostedEvents(None, QtCore.QEvent.Type.DeferredDelete)
        pump()

    def test_larger_bundle_suppresses_nested_duplicates(self):
        results = discover(self.blocks)
        self.assertEqual(len(results), 1)
        self.assertEqual(len(results[0]), 2)
        self.assertEqual(results[0][0].actions[0]['name'], '침투')

    def test_shared_apply_is_one_undo_and_preserves_sleep(self):
        original = [a.to_dict() for a in self.tree.collect_actions()]
        review = SuggestionDialog(self.blocks)
        review.apply(True)
        actions = self.tree.collect_actions()
        self.assertEqual(actions[0].block_ref, actions[2].block_ref)
        self.assertEqual(actions[0].type, 'shared_block')
        self.assertEqual(len(self.blocks.entries), 1)
        source = next(iter(self.blocks.entries.values()))['actions']
        self.assertEqual(source[0]['actions'][1]['sleep_ms'], 17)
        self.dialog.action_history.undo()
        self.assertEqual([a.to_dict() for a in self.tree.collect_actions()], original)
        self.assertFalse(self.blocks.entries)

    def test_group_apply_only_checked_location(self):
        review = SuggestionDialog(self.blocks)
        review.locations.item(1).setCheckState(QtCore.Qt.CheckState.Unchecked)
        review.apply(False)
        actions = self.tree.collect_actions()
        self.assertEqual(actions[0].type, 'group')
        self.assertEqual(actions[0].group_mode, 'all')
        self.assertEqual(actions[2].type, 'if')
        self.assertFalse(self.blocks.entries)

    def test_stale_review_does_not_mutate(self):
        review = SuggestionDialog(self.blocks)
        self.tree.topLevelItem(0).setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        review.apply(True)
        self.assertFalse(self.blocks.entries)
        self.assertIn('변경', review.status.text())
        review.close()

    def test_selection_without_duplicates_can_be_grouped(self):
        self.tree.setCurrentItem(self.tree.topLevelItem(1))
        review = self.blocks.suggest(tree=self.tree)
        self.assertEqual(len(review.occurrences), 1)
        review.apply(False)
        self.assertEqual(self.tree.collect_actions()[1].type, 'group')

    def test_overlapping_sequences_are_not_double_replaced(self):
        self.tree.load_actions([Action(type='press', key='x') for _ in range(5)])
        results = discover(self.blocks)
        self.assertEqual(len(results), 1)
        self.assertEqual(len(results[0]), 2)
        self.assertEqual(len(results[0][0].actions), 2)
        self.assertFalse(results[0][0].covered() & results[0][1].covered())

    def test_timer_difference_and_scope_sensitive_actions_are_excluded(self):
        actions = self.tree.collect_actions()
        actions[2].condition = Condition(type='all', conditions=[actions[2].condition,
            Condition(type='timer', timer_index=1, timer_value=1)])
        # The IFs differ, but their identical inner action lists remain valid candidates.
        self.tree.load_actions(actions)
        self.assertTrue(all(r[0].actions[0]['type'] != 'if' for r in discover(self.blocks)))
        priority = Action(type='group', group_mode='first_true', actions=[Action(type='press', key='a') for _ in range(4)])
        self.tree.load_actions([priority, Action(type='label', label='L'), Action(type='goto', goto_label='L')])
        self.assertFalse(discover(self.blocks))
        actions[0].confirm_fails = 2
        self.tree.load_actions([actions[0], copy.deepcopy(actions[0])])
        self.assertTrue(all(r[0].actions[0]['type'] != 'if' for r in discover(self.blocks)))


if __name__ == '__main__':
    unittest.main()
