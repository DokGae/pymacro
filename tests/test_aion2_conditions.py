import os
os.environ.setdefault('QT_QPA_PLATFORM','offscreen')
import unittest
from unittest.mock import Mock,patch
from aion2_conditions import CHARGE_SKILLS,ALL_SKILLS,evaluate_use_wait,evaluate_aion2
from engine import Condition,Action,MacroEngine
from main import ConditionNodeDialog,_condition_brief
from test_execution_analysis import APP,make_runner,main_macro


class Aion2Tests(unittest.TestCase):
    def test_cooldown_numeric_comparisons_roles_and_unknown(self):
        cond=Condition(type='aion2',aion2_kind='cooldown',aion2_skill=11010000)
        client=Mock();client.lookup.return_value=(True,0,'연결됨')
        self.assertTrue(evaluate_aion2(client,cond)[0])
        self.assertEqual(client.lookup.call_args.args[1],'내.스킬쿨.절단의맹타')
        cond.aion2_role='target';cond.aion2_cooldown_operator='le';cond.aion2_cooldown_seconds=3
        for value,expected in ((0,True),(3,True),(4,False)):
            client.lookup.return_value=(True,value,'연결됨')
            self.assertEqual(evaluate_aion2(client,cond)[0],expected)
        self.assertEqual(client.lookup.call_args.args[1],'대상.스킬쿨.절단의맹타')
        cond.aion2_cooldown_operator='cooling'
        client.lookup.return_value=(True,5,'연결됨');self.assertTrue(evaluate_aion2(client,cond)[0])
        for available,value in ((False,None),(True,False),(True,-1),(True,'0')):
            client.lookup.return_value=(available,value,'전송 꺼짐')
            self.assertTrue(evaluate_aion2(client,cond)[1]['unavailable'])

    def test_unequipped_own_skill_is_false_for_every_cooldown_comparison(self):
        cond=Condition(type='aion2',aion2_kind='cooldown',aion2_skill=17300000)
        client=Mock();client.lookup.return_value=(True,False,'연결됨')
        for op in ('ready','cooling','le','lt','ge','gt','eq','ne'):
            cond.aion2_cooldown_operator=op
            result,detail=evaluate_aion2(client,cond)
            self.assertFalse(result)
            self.assertFalse(detail['unavailable'])
            self.assertIn('미채용',detail['status'])

    def test_all_jobs_shock_release_numeric_cooldown_without_slot_requirement(self):
        skills=[row for row in ALL_SKILLS if '충격 해제' in row[1]]
        self.assertEqual(len(skills),9)
        client=Mock()
        for code,label,suffix in skills:
            cond=Condition(type='aion2',aion2_kind='cooldown',aion2_skill=code,aion2_cooldown_operator='cooling')
            client.lookup.return_value=(True,11,'연결됨')
            self.assertTrue(evaluate_aion2(client,cond)[0],label)
            self.assertEqual(client.lookup.call_args.args[1],'내.스킬쿨.'+suffix)
            cond.aion2_cooldown_operator='ready'
            self.assertFalse(evaluate_aion2(client,cond)[0])
            client.lookup.return_value=(True,0,'연결됨')
            self.assertTrue(evaluate_aion2(client,cond)[0])
            client.lookup.return_value=(False,None,'미수신')
            self.assertFalse(evaluate_aion2(client,cond)[0])

    def test_unequipped_skill_runs_false_branch_and_continues(self):
        cond=Condition(type='aion2',aion2_kind='cooldown',aion2_skill=17300000)
        actions=[Action(type='if',condition=cond,actions=[Action(type='press',key='x')],
                        else_actions=[Action(type='press',key='r')]),Action(type='press',key='y')]
        runner,engine=make_runner(actions)
        engine._evaluate_condition=MacroEngine._evaluate_condition.__get__(engine)
        engine._external_conditions_ready=MacroEngine._external_conditions_ready.__get__(engine)
        engine._external_result=MacroEngine._external_result.__get__(engine)
        client=Mock();client.lookup.return_value=(True,False,'연결됨')
        result=evaluate_aion2(client,cond)
        with patch('engine.state_hub.evaluate',return_value=result):runner._run_actions(actions,{})
        self.assertEqual([call.args[1] for call in engine._send_key.call_args_list],['r','y'])
        counts=main_macro(engine.execution_analysis.snapshot())['counts']
        self.assertEqual(counts[(0,)]['false'],1)
        self.assertEqual(counts[(0,)]['unavailable'],0)

    def test_cooldown_editor_catalog_switch_and_roundtrip(self):
        self.assertEqual(len(ALL_SKILLS),247)
        original=Condition(type='aion2',aion2_kind='cooldown',aion2_skill=11010000,aion2_role='target',aion2_cooldown_operator='le',aion2_cooldown_seconds=3)
        dialog=ConditionNodeDialog(cond=Condition.from_dict(original.to_dict()))
        try:
            self.assertEqual(dialog.aion2_skill.count(),247)
            self.assertEqual(dialog.get_condition().to_dict(),original.to_dict())
            self.assertIn('절단의 맹타',_condition_brief(original))
            dialog.aion2_kind.setCurrentIndex(dialog.aion2_kind.findData('use_wait'))
            self.assertEqual(dialog.aion2_skill.count(),len(CHARGE_SKILLS))
            dialog.aion2_kind.setCurrentIndex(dialog.aion2_kind.findData('cooldown'))
            self.assertEqual(dialog.aion2_skill.count(),247)
        finally:dialog.close()

    def test_baseline_wait_boundary_and_unknown(self):
        cond=Condition(type='aion2',aion2_skill=18120000,aion2_wait_seconds=1)
        client=Mock()
        for elapsed,expected in ((-1,True),(0,False),(.999,False),(1,True),(2,True)):
            client.lookup.return_value=(True,elapsed,'연결됨')
            result,detail=evaluate_use_wait(client,cond)
            self.assertEqual(result,expected);self.assertFalse(detail['unavailable'])
        for elapsed in (True,'1',None,float('nan'),-2):
            client.lookup.return_value=(True,elapsed,'연결됨')
            self.assertTrue(evaluate_use_wait(client,cond)[1]['unavailable'])
        client.lookup.return_value=(False,None,'연결 끊김')
        self.assertTrue(evaluate_use_wait(client,cond)[1]['unavailable'])

    def test_condition_roundtrip_and_editor_registered_charge_skills(self):
        for code,_,_ in CHARGE_SKILLS:
            original=Condition(type='aion2',aion2_skill=code,aion2_wait_seconds=1.25,external_port=47654,external_source='test')
            restored=Condition.from_dict(original.to_dict())
            dialog=ConditionNodeDialog(cond=restored)
            try:
                self.assertEqual(dialog._current_type(),'aion2')
                self.assertEqual(dialog.aion2_skill.count(),len(CHARGE_SKILLS))
                result=dialog.get_condition()
                self.assertEqual(result.to_dict(),original.to_dict())
                self.assertIn('1.25초',_condition_brief(result))
            finally:dialog.close()

    def test_assassin_ambush_trait_wait_condition(self):
        self.assertIn((13060000,'살성 · 기습','기습'),CHARGE_SKILLS)
        cond=Condition(type='aion2',aion2_skill=13060000,aion2_wait_seconds=1)
        client=Mock()
        for elapsed,expected in ((-1,True),(0,False),(.999,False),(1,True)):
            client.lookup.return_value=(True,elapsed,'연결됨')
            self.assertEqual(evaluate_use_wait(client,cond)[0],expected)
            self.assertEqual(client.lookup.call_args.args[1],'내.스킬사용경과.기습')

    def test_false_wait_runs_next_if_without_sleep_or_recovery_input(self):
        cond=Condition(type='aion2')
        actions=[Action(type='if',condition=cond,actions=[Action(type='press',key='x')]),
                 Action(type='if',condition=Condition(type='key',key='b'),actions=[Action(type='press',key='y')])]
        runner,engine=make_runner(actions)
        engine._evaluate_condition=MacroEngine._evaluate_condition.__get__(engine)
        engine._external_conditions_ready=MacroEngine._external_conditions_ready.__get__(engine)
        engine._external_result=MacroEngine._external_result.__get__(engine)
        engine._key_pressed=Mock(return_value=True)
        detail=dict(actual=.2,expected=1,unavailable=False,status='사용 후 대기 중')
        with patch('external_state.state_hub.evaluate',return_value=(False,detail)),patch.object(runner,'_sleep_with_condition_poll',wraps=runner._sleep_with_condition_poll) as sleep:
            runner._run_actions(actions,{})
        self.assertFalse(any(call.args and call.args[0]>=1000 for call in sleep.call_args_list))
        counts=main_macro(engine.execution_analysis.snapshot())['counts']
        self.assertEqual(counts[(0,)]['false'],1)
        self.assertEqual(counts[(1,)]['true'],1)
        self.assertEqual(counts[(0,0)]['inputs'],0)
        self.assertEqual(counts[(1,0)]['inputs'],1)
        self.assertIn('0.2',counts[(0,)]['condition_detail']['actual'])
        self.assertEqual(engine._send_key.call_count,1)
