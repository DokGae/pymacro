import copy
import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import unittest
from unittest.mock import Mock, patch
from PyQt6 import QtCore
from engine import Action
from main import ActionEditDialog
from aion2_actions import portable_key, resolve_skill_key
from test_execution_analysis import APP, make_runner, main_macro


def packet(key='Q', number=7):
    return dict(values={'게임연결':True}, aion2_quickslots=dict(
        version=1, enabled=True, available=True, reason='', slots=[dict(
            quick_use=number, slot_id=(0,1,2,3,4,5,6,7,20,21,22,23)[number-1],
            key=key, codes=[18120000,18140000])]))


class Aion2ActionTests(unittest.TestCase):
    def action(self, **kw):
        return Action(**dict(dict(type='press', key_source='aion2', aion2_skill=18120000), **kw))

    def test_legacy_direct_and_aion2_editor_roundtrip(self):
        self.assertEqual(Action.from_dict(dict(type='press', key='r')).key_source, 'direct')
        for action in (self.action(external_port=47654, external_source='test', repeat=3),
                       Action(type='press',key='r')):
            restored = Action.from_dict(action.to_dict())
            dialog = ActionEditDialog(action=restored)
            try:
                self.assertEqual(dialog.get_action().to_dict(), action.to_dict())
                self.assertEqual(dialog.aion2_key_skill.count(), 247)
                self.assertFalse(dialog.isModal())
                self.assertFalse(dialog.windowFlags() & QtCore.Qt.WindowType.WindowStaysOnTopHint)
            finally:dialog.close()
        for data in (dict(type='down',key_source='aion2'),
                     dict(type='press',key_source='aion2',aion2_skill=1)):
            with self.assertRaises(ValueError):Action.from_dict(data)

    def test_key_translation(self):
        for text, expected in (('1','1'),('Ctrl+Q','ctrl+q'),('Space','space'),
            ('Shift+Tab','shift+tab'),('PgUp','pageup'),('F12','f12'),
            ('Shift++','shift+='),('Num+1','numpad1'),('Ctrl+Num++','ctrl+numadd')):
            self.assertEqual(portable_key(text),expected)
        for text in ('',None,'Ctrl','A, B'):
            with self.assertRaises(ValueError):portable_key(text)

    def test_lowest_slot_chain_and_missing_information(self):
        client = Mock(); data = packet('E',8)
        data['aion2_quickslots']['slots'].append(packet('Ctrl+Q',7)['aion2_quickslots']['slots'][0])
        client.snapshot.return_value=(data,'연결됨')
        self.assertEqual(resolve_skill_key(client,self.action())[0],'ctrl+q')
        self.assertEqual(resolve_skill_key(client,self.action(aion2_skill=18140000))[0],'ctrl+q')
        failures=[]
        off=copy.deepcopy(data);off['aion2_quickslots']['enabled']=False;failures.append(off)
        unknown=copy.deepcopy(data);unknown['aion2_quickslots']['available']=False;failures.append(unknown)
        disconnected=copy.deepcopy(data);disconnected['values']['게임연결']=False;failures.append(disconnected)
        missing=copy.deepcopy(data);missing['aion2_quickslots']['slots']=[];failures.append(missing)
        no_key=packet('');failures.append(no_key)
        malformed=packet();malformed['aion2_quickslots']['slots'][0]['slot_id']=99;failures.append(malformed)
        for failure in failures:
            client.snapshot.return_value=(failure,'연결됨')
            self.assertIsNone(resolve_skill_key(client,self.action())[0])
        client.snapshot.return_value=(None,'수신 시간 초과')
        self.assertEqual(resolve_skill_key(client,self.action()),(None,'수신 시간 초과'))

    def test_repeat_uses_live_key_then_disconnect_skips_to_next_action(self):
        action=self.action(repeat=4)
        actions=[action,Action(type='press',key='r')]
        runner,engine=make_runner(actions)
        client=Mock();client.snapshot.side_effect=[(packet('Q'),'연결됨'),
            (packet('E',8),'연결됨'),(None,'연결 끊김')]
        with patch('external_state.state_hub.client',return_value=client):
            runner._run_actions(actions,{})
        self.assertEqual([call.args[1] for call in engine._send_key.call_args_list],['q','e','r'])
        counts=main_macro(engine.execution_analysis.snapshot())['counts']
        self.assertEqual(counts[(0,)]['inputs'],2)
        self.assertEqual(counts[(0,)]['unavailable'],1)
        self.assertEqual(counts[(1,)]['inputs'],1)

    def test_no_fallback_to_saved_key_when_unavailable(self):
        action=self.action(key='x')
        runner,engine=make_runner([action,Action(type='press',key='r')])
        client=Mock();client.snapshot.return_value=(None,'연결 끊김')
        with patch('external_state.state_hub.client',return_value=client):
            runner._run_actions(runner.macro.actions,{})
        self.assertEqual([call.args[1] for call in engine._send_key.call_args_list],['r'])
