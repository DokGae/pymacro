import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import unittest
from PyQt6 import QtWidgets
from engine import Condition
from main import ConditionDialog, ConditionTreeWidget

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class ConditionDeletionTests(unittest.TestCase):
    def dialog(self):
        dialog = ConditionDialog()
        dialog.root_condition = Condition(type='any', conditions=[
            Condition(type='key', key='a'), Condition(type='key', key='b')])
        dialog._refresh_condition_tree()
        dialog.condition_tree.topLevelItem(0).setSelected(True)
        self.addCleanup(dialog.close)
        return dialog

    def test_confirmation_returns_immediately_and_cancel_preserves_conditions(self):
        dialog = self.dialog()
        dialog._delete_condition_node()
        pending = dialog._delete_confirmation
        self.assertTrue(pending.isVisible())
        self.assertFalse(pending.isModal())
        dialog._delete_condition_node()
        self.assertIs(dialog._delete_confirmation, pending)
        pending.reject()
        self.assertEqual(len(dialog.root_condition.conditions), 2)

    def test_confirm_uses_original_target_after_tree_rebuild(self):
        dialog = self.dialog()
        dialog._delete_condition_node()
        dialog._refresh_condition_tree()
        dialog.condition_tree.topLevelItem(1).setSelected(True)
        dialog._delete_confirmation.accept()
        self.assertEqual([c.key for c in dialog.root_condition.conditions], ['b'])

    def test_selected_ancestors_exclude_descendants_without_pairwise_scans(self):
        tree = ConditionTreeWidget()
        self.addCleanup(tree.close)
        parent = QtWidgets.QTreeWidgetItem(['parent'])
        child = QtWidgets.QTreeWidgetItem(parent, ['child'])
        leaf = QtWidgets.QTreeWidgetItem(child, ['leaf'])
        sibling = QtWidgets.QTreeWidgetItem(['sibling'])
        tree.addTopLevelItems([parent, sibling])
        tree._is_descendant = lambda *_: self.fail('pairwise scan')
        self.assertEqual(tree._top_level_selected([leaf, sibling, child, parent]), [parent, sibling])
