import os
import unittest
from unittest.mock import patch

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
from PyQt6 import QtCore, QtWidgets
from engine import Action, Condition, Macro
from main import MacroDialog

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])
ROLE = QtCore.Qt.ItemDataRole.UserRole


class EditorLatencyTests(unittest.TestCase):
    def setUp(self):
        self.dialog = MacroDialog(macro=Macro(trigger_key='f1', actions=[
            Action(type='if', condition=Condition(type='key', key='a'),
                   actions=[Action(type='label', label='inner')],
                   has_else_branch=True, else_actions=[Action(type='label', label='other')])]))
        APP.processEvents()
        self.dialog.action_history.flush()

    def tearDown(self):
        self.dialog.close()
        self.dialog.deleteLater()
        APP.processEvents()

    def test_presentation_does_not_schedule_history_but_edits_do(self):
        history = self.dialog.action_history
        tree = self.dialog.main_action_tree
        history.timer.stop()
        tree.refresh_workspace()
        self.assertFalse(history.timer.isActive())
        item = tree.topLevelItem(0)
        item.setCheckState(5, QtCore.Qt.CheckState.Unchecked)
        self.assertTrue(history.timer.isActive())

    def test_labels_do_not_serialize_actions(self):
        tree = self.dialog.main_action_tree
        with patch.object(tree, 'collect_actions', side_effect=AssertionError('unnecessary copy')):
            self.assertEqual(self.dialog._available_labels(tree), ['inner', 'other'])

    def test_collected_actions_have_independent_conditions_and_children(self):
        tree = self.dialog.main_action_tree
        first = tree.collect_actions()
        second = tree.collect_actions()
        first[0].condition.key = 'b'
        first[0].actions[0].label = 'changed'
        first[0].else_actions.clear()
        self.assertEqual(second[0].condition.key, 'a')
        self.assertEqual(second[0].actions[0].label, 'inner')
        self.assertEqual(len(second[0].else_actions), 1)
        self.assertEqual(tree.collect_actions(), second)
