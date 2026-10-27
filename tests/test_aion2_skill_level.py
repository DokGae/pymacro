import os
os.environ.setdefault('QT_QPA_PLATFORM','offscreen')
import unittest
from unittest.mock import Mock
from engine import Condition
from aion2_conditions import LEVEL_SKILLS,evaluate_aion2,condition_summary
from main import ConditionNodeDialog
from test_execution_analysis import APP


class SkillLevelTests(unittest.TestCase):
    def test_comparisons_and_fail_closed_values(self):
        cond=Condition(type='aion2',aion2_kind='skill_level',aion2_skill=11010000,aion2_level=10)
        client=Mock()
        for op,expected in [('ge',True),('gt',False),('le',True),('lt',False),('eq',True),('ne',False)]:
            cond.aion2_level_operator=op;client.lookup.return_value=(True,10,'연결됨')
            self.assertEqual(evaluate_aion2(client,cond)[0],expected)
        self.assertEqual(client.lookup.call_args.args[1],'내.스킬.절단의맹타')
        for available,value in [(False,None),(True,False),(True,True),(True,'10'),(True,10.5),(True,-1),(True,101)]:
            client.lookup.return_value=(available,value,'미확인')
            result,detail=evaluate_aion2(client,cond)
            self.assertFalse(result);self.assertTrue(detail['unavailable'])
        cond.aion2_level=0;cond.aion2_level_operator='eq';client.lookup.return_value=(True,0,'연결됨')
        self.assertTrue(evaluate_aion2(client,cond)[0])

    def test_stigma_mapping(self):
        row=next(r for r in LEVEL_SKILLS if r['key'].startswith('내.스티그마.'))
        client=Mock();client.lookup.return_value=(True,3,'연결됨')
        cond=Condition(type='aion2',aion2_kind='skill_level',aion2_skill=row['code'],aion2_level=3)
        self.assertTrue(evaluate_aion2(client,cond)[0]);self.assertEqual(client.lookup.call_args.args[1],row['key'])

    def test_editor_saved_level_and_mode_switch(self):
        cond=Condition(type='aion2',aion2_kind='skill_level',aion2_skill=11010000,aion2_level=12,aion2_level_operator='ge')
        dialog=ConditionNodeDialog(cond=Condition.from_dict(cond.to_dict()))
        try:
            self.assertEqual(dialog.aion2_skill.count(),len(LEVEL_SKILLS))
            self.assertEqual(dialog.get_condition().to_dict(),cond.to_dict())
            self.assertFalse(dialog.aion2_level_value.isHidden());self.assertTrue(dialog.aion2_wait.isHidden())
            self.assertTrue(dialog.aion2_role.isHidden())
            self.assertIn('12레벨',condition_summary(cond))
            dialog.aion2_kind.setCurrentIndex(dialog.aion2_kind.findData('cooldown'))
            self.assertTrue(dialog.aion2_level_value.isHidden())
            dialog.aion2_kind.setCurrentIndex(dialog.aion2_kind.findData('skill_level'))
            self.assertEqual(dialog.aion2_level_value.value(),12)
        finally:dialog.close()


if __name__=='__main__':unittest.main()
