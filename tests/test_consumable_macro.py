import copy
import unittest
from unittest.mock import Mock, patch
from aion2_actions import resolve_action_key
from aion2_consumables import resolve_item_key, evaluate_item_cooldown
from aion2_conditions import evaluate_aion2
from engine import Action, Condition
from main import ActionEditDialog, ConditionNodeDialog
from test_execution_analysis import APP, make_runner


def packet():
    return dict(values={'게임연결':True}, aion2_consumables=dict(version=1,group_version=1,enabled=True,available=True,
        slots=[dict(quick_use=1,slot_id=10,code=530116010,key='Ctrl+1'),
               dict(quick_use=2,slot_id=11,code=530116010,key='F2')],
        groups=[dict(code=530116010,present=True,observed=True,remaining=0)]))


class ConsumableMacroTests(unittest.TestCase):
    def test_action_and_condition_editor_roundtrip(self):
        original = Action(type='press',key_source='aion2_consumable',aion2_item=510116010)
        dialog = ActionEditDialog(action=Action.from_dict(original.to_dict()))
        try:
            self.assertEqual(dialog.key_source_combo.currentData(),'aion2_consumable')
            self.assertEqual(dialog.aion2_key_item.count(),6)
            self.assertEqual(dialog.get_action().to_dict(),original.to_dict())
        finally:dialog.close()
        original = Condition(type='aion2',aion2_kind='consumable_cooldown',aion2_item=511490001,
                             aion2_cooldown_operator='le',aion2_cooldown_seconds=3)
        dialog = ConditionNodeDialog(cond=Condition.from_dict(original.to_dict()))
        try:
            self.assertEqual(dialog.aion2_kind.currentData(),'consumable_cooldown')
            self.assertEqual(dialog.aion2_skill.count(),6)
            self.assertEqual(dialog.get_condition().to_dict(),original.to_dict())
            dialog.aion2_kind.setCurrentIndex(dialog.aion2_kind.findData('cooldown'))
            self.assertEqual(dialog.aion2_skill.count(),247)
        finally:dialog.close()

    def test_key_moves_duplicates_and_fail_closed(self):
        action = Action(type='press',key_source='aion2_consumable')
        client = Mock(); data = packet(); client.snapshot.return_value=(data,'연결됨')
        self.assertEqual(resolve_item_key(client,action)[0],'ctrl+1')
        data['aion2_consumables']['slots'][0]['key']=''
        self.assertEqual(resolve_item_key(client,action)[0],'f2')
        data['aion2_consumables']['slots'][1].update(quick_use=7,slot_id=16,key='Alt+7')
        self.assertEqual(resolve_item_key(client,action)[0],'alt+7')
        for field in ('enabled','available'):
            bad=copy.deepcopy(data);bad['aion2_consumables'][field]=False
            client.snapshot.return_value=(bad,'')
            self.assertIsNone(resolve_item_key(client,action)[0])
        client.snapshot.return_value=(None,'끊김')
        self.assertIsNone(resolve_item_key(client,action)[0])

    def test_cooldowns_missing_items_and_stale_connection(self):
        client=Mock();data=packet();client.snapshot.return_value=(data,'')
        cond=Condition(type='aion2',aion2_kind='consumable_cooldown')
        self.assertTrue(evaluate_aion2(client,cond)[0])
        data['aion2_consumables']['groups'][0]['remaining']=12
        self.assertFalse(evaluate_aion2(client,cond)[0])
        cond.aion2_cooldown_operator='cooling'
        self.assertTrue(evaluate_item_cooldown(client,cond)[0])
        for op in ('ready','cooling','le','lt','ge','gt','eq','ne'):
            cond.aion2_cooldown_operator=op
            data['aion2_consumables']['groups'][0]['present']=False
            self.assertFalse(evaluate_item_cooldown(client,cond)[0])
        data['aion2_consumables']['groups'][0]['observed']=False
        self.assertTrue(evaluate_item_cooldown(client,cond)[1]['unavailable'])
        client.snapshot.return_value=(None,'오래된 상태')
        self.assertFalse(evaluate_item_cooldown(client,cond)[0])

    def test_runner_rechecks_key_per_press_and_continues_on_disconnect(self):
        action=Action(type='press',key_source='aion2_consumable',repeat=3)
        actions=[action,Action(type='press',key='y')]
        runner,engine=make_runner(actions)
        with patch('aion2_actions.resolve_action_key',side_effect=[('ctrl+1',''),('f2',''),(None,'끊김')]):
            runner._run_actions(actions,{})
        self.assertEqual([c.args[1] for c in engine._send_key.call_args_list],['ctrl+1','f2','y'])
