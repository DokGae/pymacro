import os
os.environ.setdefault('QT_QPA_PLATFORM','offscreen')
from types import SimpleNamespace
import unittest
from PyQt6 import QtWidgets
from engine import Condition
from main import ConditionDialog

APP=QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class SharedConditionValidationTests(unittest.TestCase):
    def dialog(self,root,entries):
        dialog=ConditionDialog()
        dialog._shared_controller=SimpleNamespace(entries=entries)
        dialog.root_condition=root
        self.addCleanup(dialog.close)
        return dialog

    def test_linked_or_and_timer_save_without_materializing_link(self):
        linked=Condition(type='any',shared_ref='distance',conditions=[])
        root=Condition(type='all',conditions=[linked,Condition(type='timer',timer_index=1,timer_value=1)])
        entries={'distance':{'name':'6m이상일때','condition':{'type':'any','conditions':[{'type':'key','key':'a'}]}}}
        dialog=self.dialog(root,entries)
        saved=dialog.get_condition().condition
        self.assertEqual(saved.conditions[0].shared_ref,'distance')
        self.assertEqual(saved.conditions[0].conditions,[])
        self.assertEqual(root.conditions[0].conditions,[])
        self.assertEqual(len(saved.conditions),2)
        # Saving must use the current shared definition rather than a stale snapshot.
        entries['distance']['condition']['conditions']=[]
        with self.assertRaisesRegex(ValueError,'하위 조건'):dialog.get_condition()

    def test_missing_link_has_specific_error(self):
        dialog=self.dialog(Condition(type='any',shared_ref='missing'),{})
        with self.assertRaisesRegex(ValueError,'연결된 공용 설정이 없습니다'):dialog.get_condition()

    def test_nested_links_and_cycles(self):
        entries={'a':{'condition':{'type':'any','conditions':[{'type':'any','shared_ref':'b'}]}},
                 'b':{'condition':{'type':'all','conditions':[{'type':'key','key':'b'}]}}}
        dialog=self.dialog(Condition(type='any',shared_ref='a'),entries)
        dialog.get_condition()
        entries['b']['condition']={'type':'any','shared_ref':'a'}
        with self.assertRaisesRegex(ValueError,'서로를 참조'):dialog.get_condition()

    def test_empty_local_branch_is_still_rejected(self):
        entries={'a':{'condition':{'type':'key','key':'a'}}}
        dialog=self.dialog(Condition(type='any',shared_ref='a',on_false=[Condition(type='all')]),entries)
        with self.assertRaisesRegex(ValueError,'하위 조건'):dialog.get_condition()

    def test_disabled_shared_link_preserves_disabled_state(self):
        entries={'a':{'condition':{'type':'any','conditions':[{'type':'key','key':'a'}]}}}
        dialog=self.dialog(Condition(type='any',shared_ref='a',enabled=False),entries)
        saved=dialog.get_condition().condition
        self.assertFalse(saved.enabled)
        self.assertEqual(saved.shared_ref,'a')
