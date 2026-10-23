"""Missing external inputs are false leaves, not a veto on the entire tree."""
import unittest
from unittest.mock import Mock,patch
from engine import Action,Condition,MacroEngine
from external_state import StateHub,external_result,external_conditions_ready
from test_condition_evidence import real_runner,inspect
from test_execution_analysis import make_runner,main_macro


def dispatch(cond):
    if cond.type=='aion2':return True,dict(actual=0,unavailable=False,status='사용 가능',aion2_kind='cooldown')
    if cond.external_key=='내.공격방향':
        return False,dict(actual=None,unavailable=True,status='공격 방향 미감지',key=cond.external_key,
                          connected=True,connection_status='연결됨',source='leesangjin-monitor',port=47653)
    return True,dict(actual=True,unavailable=False,status='연결됨',key=cond.external_key,
                     connected=True,connection_status='연결됨',source='leesangjin-monitor',port=47653)


class ExternalFalseTests(unittest.TestCase):
    def test_missing_value_is_false_for_every_operator_without_substituting_zero(self):
        hub=StateHub();client=Mock()
        client.snapshot.return_value=(None,'연결 끊김')
        client.lookup.return_value=(False,None,'항목 수신 대기')
        cond=Condition(type='external',external_key='내.공격방향',external_value='2')
        try:
            with patch.object(hub,'client',return_value=client):
                for op in ('true','false','eq','ne','lt','le','gt','ge'):
                    cond.external_operator=op
                    result,detail=hub.evaluate(cond)
                    self.assertFalse(result,op);self.assertTrue(detail['unavailable'])
                    self.assertIsNone(detail['actual'])
        finally:hub.close()

    def test_cached_missing_leaf_stays_false_and_ready_check_does_not_prefetch(self):
        cond=Condition(type='external');cache={}
        with patch('external_state.state_hub.evaluate',return_value=(False,dict(unavailable=True,status='미수신'))) as evaluate:
            self.assertTrue(external_conditions_ready(cond,cache));evaluate.assert_not_called()
            self.assertFalse(external_result(cond,cache)[0]);self.assertFalse(external_result(cond,cache)[0])
            evaluate.assert_called_once()

    def test_screenshot_and_or_tree_is_true_when_direction_missing_but_buff_true(self):
        cond=Condition(type='all',conditions=[Condition(type='aion2',aion2_kind='cooldown',aion2_skill=13070000),
            Condition(type='any',conditions=[
                Condition(type='external',external_key='내.공격방향',external_operator='ne',external_value='2'),
                Condition(type='external',external_key='나.암습효과')])])
        runner,engine=real_runner(cond)
        engine.debug_condition_tree=MacroEngine.debug_condition_tree.__get__(engine)
        with patch('external_state.state_hub.evaluate',side_effect=dispatch):
            evidence,counts=inspect(runner,engine)
            debug=engine.debug_condition_tree(cond,vars_ctx=runner._vars)
        self.assertEqual(evidence['state'],'true');self.assertEqual(counts['true'],1)
        self.assertEqual(counts['unavailable'],0)
        self.assertEqual(evidence['children'][1]['children'][0]['state'],'false')
        self.assertEqual(evidence['children'][1]['children'][1]['state'],'true')
        self.assertIs(debug['result'],True)
        self.assertIs(debug['children'][1]['children'][0]['result'],False)
        self.assertNotIn('unavailable',debug['detail'])
        from main import DebuggerDialog
        dialog=DebuggerDialog()
        try:
            dialog._render_condition_tree(debug,label='조건 디버그')
            self.assertIn('참',dialog.condition_state_label.text())
            root=dialog.condition_tree.topLevelItem(0)
            self.assertEqual(root.child(1).child(0).text(1),'거짓')
            self.assertIn('미수신',root.child(1).child(0).text(2))
        finally:dialog.close();dialog.deleteLater()

    def test_or_short_circuits_and_ignores_unknown_unselected_followup(self):
        cond=Condition(type='any',conditions=[Condition(type='key',key='a'),
            Condition(type='external',external_key='내.공격방향')])
        runner,engine=real_runner(cond);engine._key_pressed.return_value=True
        with patch('external_state.state_hub.evaluate',side_effect=AssertionError('Unvisited leaf must not be queried')):
            evidence,counts=inspect(runner,engine)
        self.assertEqual(evidence['state'],'true')
        self.assertEqual(evidence['children'][1]['state'],'not_evaluated')
        self.assertEqual(counts['true'],1)

    def test_unknown_if_and_elif_continue_to_else(self):
        unknown=Condition(type='external',external_key='내.공격방향',external_operator='ne',external_value='2')
        action=Action(type='if',condition=unknown,actions=[Action(type='press',key='x')],
            elif_blocks=[(Condition(type='aion2'),[Action(type='press',key='y')],'미수신 스킬')],
            has_else_branch=True,else_actions=[Action(type='press',key='z')])
        runner,engine=make_runner([action])
        engine._evaluate_condition=MacroEngine._evaluate_condition.__get__(engine)
        engine._external_result=MacroEngine._external_result.__get__(engine)
        with patch('external_state.state_hub.evaluate',return_value=(False,dict(unavailable=True,status='연결 끊김'))):
            runner._run_actions([action],{})
        self.assertEqual([call.args[1] for call in engine._send_key.call_args_list],['z'])
        counts=main_macro(engine.execution_analysis.snapshot())['counts']
        self.assertEqual(counts[(0,)]['false'],1)
        self.assertEqual(counts[(0,'elif0')]['false'],1)
        self.assertEqual(counts[(0,)]['unavailable'],0)

    def test_false_followup_can_run_after_unknown_external_base(self):
        cond=Condition(type='external',external_key='내.공격방향',on_false=[Condition(type='key',key='a')])
        runner,engine=real_runner(cond);engine._key_pressed.return_value=True
        with patch('external_state.state_hub.evaluate',return_value=(False,dict(unavailable=True,status='미수신'))):
            evidence,counts=inspect(runner,engine)
        self.assertIs(evidence['base_result'],False);self.assertIs(evidence['result'],True)
        self.assertEqual(evidence['state'],'true');self.assertEqual(counts['true'],1)


if __name__=='__main__':unittest.main()
