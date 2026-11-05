import json
import unittest
from pathlib import Path
from engine import Action
from test_execution_analysis import make_runner


class PresetRestoreTests(unittest.TestCase):
    def scenario(self, initial, fail_first=False, target_set="일반", target_job="살성", flicker=False):
        data = json.loads(Path('setting/암극(살성).json').read_text(encoding='utf-8'))
        node = next(x for x in data['macros'][0]['actions'][8]['actions'] if x.get('name') == 'CC기걸린대상')
        change = Action.from_dict(node['actions'][0]['actions'][0])
        restore = [Action.from_dict(x) for x in node['else_actions']]
        runner, engine = make_runner([change] + restore)
        runner._vars.var['CC복귀프리셋'] = '0'
        state = {'preset': initial, 'fail': fail_first}
        def evaluate(cond, *args, **kwargs):
            if cond.type in ('all', 'any'):
                results = [evaluate(c) for c in cond.conditions]
                return all(results) if cond.type == 'all' else any(results)
            if cond.type == 'var':
                actual = runner._vars.var.get(cond.var_name, '0')
                return actual != cond.var_value_raw if cond.var_operator == 'ne' else actual == cond.var_value_raw
            if cond.external_key == '적.충격해제쿨':
                return True
            if cond.external_key in ('셋판정기준', '타겟직업'):
                actual = target_set if cond.external_key == '셋판정기준' else target_job
                return actual != cond.external_value if cond.external_operator == 'ne' else actual == cond.external_value
            actual = str(state['preset'])
            return actual != cond.external_value if cond.external_operator == 'ne' else actual == cond.external_value
        engine._evaluate_condition = evaluate
        def send(*args, **kwargs):
            key = args[1]
            if state['fail']:
                state['fail'] = False
                return True
            state['preset'] = {'f7': 2, 'f8': 3, 'f9': 4}[key]
            return True
        engine._send_key.side_effect = send
        runner._run_actions([change], {})
        original_set = target_set
        if flicker:
            target_set = '일반'
        runner._run_actions([change], {})
        target_set = original_set
        desired = 3 if target_set in ('회피셋', '막기셋') or target_job in ('치유성', '수호성') else 4
        if initial == desired:
            self.assertEqual(runner._vars.var['CC복귀프리셋'], '0')
        else:
            self.assertEqual(runner._vars.var['CC복귀프리셋'], str(initial))
            self.assertEqual(state['preset'], desired)
        runner._run_actions(restore, {})
        self.assertEqual(state['preset'], initial)
        self.assertEqual(runner._vars.var['CC복귀프리셋'], '0')
        count = engine._send_key.call_count
        runner._run_actions(restore, {})
        self.assertEqual(engine._send_key.call_count, count)
        if initial == desired:
            self.assertEqual(count, 0)

    def test_restore_2(self):
        self.scenario(2)

    def test_restore_3(self):
        self.scenario(3)

    def test_original_4_untouched(self):
        self.scenario(4)

    def test_retry_preserves_original(self):
        self.scenario(3, fail_first=True)

    def test_saved_number_survives_new_runner(self):
        from engine import MacroRunner
        data = json.loads(Path('setting/암극(살성).json').read_text(encoding='utf-8'))
        node = next(x for x in data['macros'][0]['actions'][8]['actions'] if x.get('name') == 'CC기걸린대상')
        change = Action.from_dict(node['actions'][0]['actions'][0])
        def find_save(action):
            if action.type == 'set_var' and action.var_value_raw == '2':
                return action
            for child in action.actions + action.else_actions:
                found = find_save(child)
                if found:
                    return found
        save = find_save(change)
        self.assertTrue(save.var_keep_between_runs)
        runner, engine = make_runner([save])
        runner._run_actions([save], {})
        restarted = MacroRunner(runner.macro, engine, 0)
        self.assertEqual(restarted._vars.var['CC복귀프리셋'], '2')
        other = MacroRunner(runner.macro, engine, 1)
        self.assertNotIn('CC복귀프리셋', other._vars.var)

    def test_special_targets_use_f8_and_restore(self):
        for target_set, job in [('회피셋', ''), ('막기셋', ''), ('일반', '치유성'), ('일반', '수호성')]:
            for initial in (2, 3, 4):
                with self.subTest(target_set=target_set, job=job, initial=initial):
                    self.scenario(initial, target_set=target_set, target_job=job)

    def test_evasion_does_not_flip_to_f9_on_changed_classification(self):
        self.scenario(2, target_set='회피셋', flicker=True)

    def test_unknown_keeps_initial_preset(self):
        for classification in ('미조회', '미확인', ''):
            data = json.loads(Path('setting/암극(살성).json').read_text(encoding='utf-8'))
            node = next(x for x in data['macros'][0]['actions'][8]['actions'] if x.get('name') == 'CC기걸린대상')
            guard = Action.from_dict(node['actions'][0]['actions'][0])
            runner, engine = make_runner([guard])
            runner._vars.var['CC복귀프리셋'] = '0'
            def evaluate(cond, *args, **kwargs):
                if cond.type == 'any':
                    return any(evaluate(c) for c in cond.conditions)
                if cond.type == 'var':
                    return runner._vars.var.get(cond.var_name, '0') == cond.var_value_raw
                return classification == cond.external_value
            engine._evaluate_condition = evaluate
            runner._run_actions([guard], {})
            engine._send_key.assert_not_called()

    def test_unknown_restores_pending_preset(self):
        data = json.loads(Path('setting/암극(살성).json').read_text(encoding='utf-8'))
        node = next(x for x in data['macros'][0]['actions'][8]['actions'] if x.get('name') == 'CC기걸린대상')
        guard = Action.from_dict(node['actions'][0]['actions'][0])
        runner, engine = make_runner([guard])
        runner._vars.var.update(CC복귀프리셋='2', CC임시프리셋='3')
        state = {'preset': '3'}
        def evaluate(cond, *args, **kwargs):
            if cond.type == 'any':
                return any(evaluate(c) for c in cond.conditions)
            if cond.type == 'var':
                return runner._vars.var.get(cond.var_name, '0') == cond.var_value_raw
            if cond.external_key == '셋판정기준':
                return False
            return state['preset'] != cond.external_value if cond.external_operator == 'ne' else state['preset'] == cond.external_value
        engine._evaluate_condition = evaluate
        def send(*args, **kwargs):
            self.assertEqual(args[1], 'f7')
            state['preset'] = '2'
            return True
        engine._send_key.side_effect = send
        runner._run_actions([guard], {})
        self.assertEqual(state['preset'], '2')
        self.assertEqual(runner._vars.var['CC복귀프리셋'], '0')
