import json
import os
import socket
import threading
import time
import unittest
from unittest.mock import patch
os.environ.setdefault('QT_QPA_PLATFORM','offscreen')
from PyQt6 import QtWidgets
from engine import Action, Condition, Macro, MacroEngine, MacroRunner, MacroProfile
from external_state import StateClient, StateHub, parse_value, validate_message, state_hub
from main import ConditionNodeDialog, DebuggerDialog, _condition_brief
from test_parallel_actions import FakeEngine


def message(values=None, **extra):
    return dict(protocol='external-state-v1',source='other-program',session='session-1',sequence=1,
                values=values or {},**extra)


class ExternalEngine(FakeEngine):
    _evaluate_condition=MacroEngine._evaluate_condition
    _external_result=MacroEngine._external_result
    _external_conditions_ready=MacroEngine._external_conditions_ready
    debug_condition_tree=MacroEngine.debug_condition_tree


class ExternalStateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.app=QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

    def tearDown(self):state_hub.close()

    def test_condition_dialog_roundtrip_and_generic_values(self):
        cond=Condition(type='external',external_port=55555,external_source='other-program',
                       external_key='작업단계',external_operator='eq',external_value='완료')
        restored=Condition.from_dict(json.loads(json.dumps(cond.to_dict())))
        self.assertEqual(restored.to_dict(),cond.to_dict())
        dialog=ConditionNodeDialog(cond=restored);dialog.show();self.app.processEvents()
        try:
            self.assertFalse(dialog.isModal())
            self.assertTrue(dialog.external_value.isVisible())
            self.assertEqual(dialog.get_condition().to_dict(),cond.to_dict())
            self.assertIn('작업단계',_condition_brief(cond))
            dialog.external_op.setCurrentIndex(dialog.external_op.findData('false'))
            self.assertFalse(dialog.external_value.isVisible())
            dialog.type_combo.setCurrentIndex(dialog.type_combo.findData('pixel'))
            self.assertFalse(dialog.external_source.isVisible())
        finally:dialog.reject()

    def test_comparison_missing_source_and_false_defaults(self):
        client=StateClient(port=55555)
        data=message({'작업단계':'완료','체력':50,'내효과.123':True},false_prefixes=['내효과.'],unavailable_prefixes=['대상효과.'])
        with client._lock:client._data=validate_message(data);client._received_at=time.monotonic()
        hub=StateHub()
        with patch.object(hub,'client',return_value=client):
            for key,op,value,expected in [('작업단계','eq','완료',True),('체력','le','50',True),
                    ('내효과.123','true','',True),('내효과.456','false','',True),
                    ('없음','ne','다름',False),('대상효과.123','false','',False),('체력','true','',False)]:
                cond=Condition(type='external',external_source='other-program',external_key=key,
                               external_operator=op,external_value=value)
                self.assertEqual(hub.evaluate(cond)[0],expected,(key,op))
            cond.external_source='wrong-program'
            self.assertTrue(hub.evaluate(cond)[1]['unavailable'])
            client._received_at=time.monotonic()-4
            self.assertTrue(hub.evaluate(cond)[1]['unavailable'])
        self.assertTrue(parse_value('참'));self.assertEqual(parse_value('12.5'),12.5)
        data['unavailable_keys']=['내효과.123']
        client._received_at=time.monotonic()
        self.assertFalse(client.lookup('other-program','내효과.123')[0])
        self.assertFalse(client.lookup('other-program','内')[0])
        with self.assertRaises(ValueError):validate_message(message({'bad':None}))
        with self.assertRaises(ValueError):parse_value('NaN')

    def test_saved_profile_starts_shared_connection_before_macro_execution(self):
        hub=StateHub();cond=Condition(type='external',external_key='내효과.123')
        profile=MacroProfile(macros=[Macro(trigger_key='f10',actions=[
            Action(type='if',condition=cond,else_actions=[Action(type='if',condition=cond)])])])
        with patch.object(hub,'client') as connect:
            hub.connect_profile(profile)
            self.assertEqual(connect.call_count,2)
            connect.assert_called_with('127.0.0.1',47653)

    def test_disconnected_if_skips_both_branches_and_inverted_conditions(self):
        engine=ExternalEngine()
        cond=Condition(type='external',external_key='내효과.123',external_operator='false',
                       on_false=[Condition(type='external',external_key='else')])
        root=Condition(type='any',conditions=[cond])
        action=Action(type='if',condition=root,actions=[Action(type='noop',name='yes')],
                      else_actions=[Action(type='noop',name='no')])
        runner=MacroRunner(Macro(trigger_key='f10',actions=[action]),engine)
        with patch('external_state.state_hub.evaluate',return_value=(False,dict(unavailable=True))):
            self.assertFalse(engine._evaluate_condition(root))
            self.assertIsNone(engine.debug_condition_tree(root)['result'])
            runner._run_actions([action],{},root=True,path=['test'])
        names=[e.get('action_name') for _,e in engine.events if e.get('type')=='action_start']
        self.assertNotIn('yes',names);self.assertNotIn('no',names)

    def test_available_if_runs_expected_branch_with_one_cached_snapshot(self):
        engine=ExternalEngine();cond=Condition(type='external',external_key='内')
        action=Action(type='if',condition=cond,actions=[Action(type='noop',name='yes')],
                      else_actions=[Action(type='noop',name='no')])
        runner=MacroRunner(Macro(trigger_key='f10',actions=[action]),engine)
        with patch('external_state.state_hub.evaluate',return_value=(True,dict(unavailable=False))) as evaluate:
            runner._run_actions([action],{},root=True,path=['test'])
            self.assertEqual(evaluate.call_count,1)
        starts=[e for _,e in engine.events if e.get('type')=='action_start']
        self.assertTrue(any(e.get('action_name')=='yes' for e in starts))
        self.assertFalse(any(e.get('action_name')=='no' for e in starts))

    def test_debug_keeps_three_conditions_when_external_item_is_unavailable(self):
        engine=ExternalEngine();engine._pixel_patterns={}
        hp=Condition(type='external',external_key='내HP',external_operator='lt',external_value='90')
        buff=Condition(type='external',external_key='나.결계')
        pixel=Condition(type='pixel',region=(1,2,1,1),color=(66,51,22))
        root=Condition(type='any',conditions=[Condition(type='all',conditions=[hp,buff,pixel])])
        def evaluate(cond):
            missing=cond is buff
            return not missing,dict(source=cond.external_source,key=cond.external_key,port=47653,
                connected=True,connection_status='연결됨',status='아직 수신하지 않은 항목' if missing else '연결됨',
                actual=None if missing else 80,unavailable=missing)
        with patch('external_state.state_hub.evaluate',side_effect=evaluate) as external, \
                patch.object(engine,'_pixel_check',create=True,return_value={'result':True,'found':True}) as check:
            tree=engine.debug_condition_tree(root)
        self.assertEqual(external.call_count,2)
        check.assert_called_once()
        self.assertIsNone(tree['result'])
        children=tree['children'][0]['children']
        self.assertEqual(len(children),3)
        self.assertEqual([node['result'] for node in children],[True,None,True])
        dialog=DebuggerDialog()
        try:
            dialog._render_condition_tree(tree,label='테스트')
            item=dialog.condition_tree.topLevelItem(0).child(0)
            self.assertEqual(item.childCount(),3)
            self.assertIn('연결된 상태',item.child(1).text(2))
            self.assertIn('항목 대기',item.child(1).text(2))
            self.assertEqual(item.child(1).text(1),'판단 대기')
            self.assertEqual(item.child(1).foreground(2).color().name(),'#22863a')
        finally:dialog.close()

    def test_external_debug_disconnected_status_is_red(self):
        engine=ExternalEngine();cond=Condition(type='external',external_key='나.결계')
        with patch('external_state.state_hub.evaluate',return_value=(False,dict(unavailable=True,
                connected=False,connection_status='연결 대기',status='연결 대기',key=cond.external_key))):
            tree=engine.debug_condition_tree(cond)
        dialog=DebuggerDialog()
        try:
            item=dialog._build_condition_item(tree)
            self.assertIn('연결 실패 / 대기 중',item.text(2))
            self.assertEqual(item.foreground(2).color().name(),'#c62828')
        finally:dialog.close()

    def test_fragmented_unicode_snapshots_and_stale_stream(self):
        listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen();listener.settimeout(2)
        client=StateClient(port=listener.getsockname()[1],stale_seconds=.3,retry_seconds=.05)
        peers=[]
        try:
            client.start();peer,_=listener.accept();peers.append(peer)
            first=(json.dumps(message({'내용':'작업완료'}),ensure_ascii=False)+'\n').encode()
            peer.sendall(first[:12]);time.sleep(.03)
            self.assertIsNone(client.snapshot('other-program')[0])
            second=message({'내용':'새 상태'});second['sequence']=2
            peer.sendall(first[12:]+(json.dumps(second,ensure_ascii=False)+'\n').encode())
            deadline=time.monotonic()+2
            while time.monotonic()<deadline:
                data,_=client.snapshot('other-program')
                if data is not None and data['sequence']==2:break
                time.sleep(.01)
            self.assertEqual(client.lookup('other-program','내용')[1],'새 상태')
            deadline=time.monotonic()+2
            while client.snapshot('other-program')[0] is not None and time.monotonic()<deadline:time.sleep(.01)
            self.assertIsNone(client.snapshot('other-program')[0])
            peer.close();reconnected,_=listener.accept();peers.append(reconnected)
            restored=message({'내용':'재시작'});restored['session']='session-2'
            reconnected.sendall((json.dumps(restored,ensure_ascii=False)+'\n').encode())
            deadline=time.monotonic()+2
            while client.lookup('other-program','내용')[1]!='재시작' and time.monotonic()<deadline:time.sleep(.01)
            self.assertEqual(client.lookup('other-program','내용')[1],'재시작')
        finally:
            client.close()
            for peer in peers:peer.close()
            listener.close()
