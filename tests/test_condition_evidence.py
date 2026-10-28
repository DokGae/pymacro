"""Use the real evaluator with fake inputs; details never run a second inspection."""
import copy
import json
import os
import unittest
from unittest.mock import Mock, patch

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
from PyQt6 import QtWidgets
from engine import Action, Condition, MacroEngine
from execution_analysis_ui import ExecutionAnalysisDialog
from test_execution_analysis import APP, make_runner, main_macro


def real_runner(condition, *, variables=None, elif_blocks=None):
    runner, engine = make_runner([Action(type='if', name='판정 확인', condition=condition,
                                        elif_blocks=elif_blocks or [])])
    engine._evaluate_condition = MacroEngine._evaluate_condition.__get__(engine)
    engine._external_conditions_ready = MacroEngine._external_conditions_ready.__get__(engine)
    engine._external_result = MacroEngine._external_result.__get__(engine)
    engine._key_pressed = Mock(return_value=False)
    engine._get_timer_value = Mock(return_value=1.25)
    engine._pixel_patterns = {}
    engine._pixel_check = Mock(return_value=dict(result=False, found=False, match_count=0,
                                                sample_color=(12, 34, 56)))
    runner._vars.var.update(variables or {})
    return runner, engine


def inspect(runner, engine, path=(0,)):
    runner._run_actions(runner.macro.actions, {})
    counts = main_macro(engine.execution_analysis.snapshot())['counts'][path]
    return counts['condition_detail'], counts


class ConditionEvidenceTests(unittest.TestCase):
    def test_no_active_conditions_pass_without_inspecting_inputs(self):
        for mode in ('all', 'any'):
            for children in ([], [Condition(type='key', key='x', enabled=False)]):
                with self.subTest(mode=mode, children=len(children)):
                    condition = Condition(type=mode, conditions=children)
                    runner, engine = real_runner(condition)
                    engine.debug_condition_tree = MacroEngine.debug_condition_tree.__get__(engine)
                    self.assertTrue(engine._evaluate_condition(condition))
                    detail = MacroEngine.debug_condition_tree(engine, condition, vars_ctx=runner._vars)
                    self.assertTrue(detail['result'])
                    evidence, counts = inspect(runner, engine)
                    self.assertEqual(evidence['state'], 'true')
                    engine._key_pressed.assert_not_called()

    def test_disabled_root_passes_without_inspecting_inputs(self):
        condition = Condition(type='key', key='x', enabled=False)
        runner, engine = real_runner(condition)
        self.assertTrue(engine._evaluate_condition(condition))
        engine._key_pressed.assert_not_called()

    def test_numeric_variable_comparisons_match_debug_and_runtime(self):
        for op, outcomes in [('ge', (False, True, True)), ('le', (True, True, False)),
                             ('gt', (False, False, True)), ('lt', (True, False, False))]:
            for value, expected in zip(('9.5', '10', '10.5', 'hello', None),
                                       (*outcomes, False, False)):
                with self.subTest(op=op, value=value):
                    condition = Condition.from_dict(Condition(type='var', var_name='hp',
                        var_operator=op, var_value_raw='10').to_dict())
                    runner, engine = real_runner(condition, variables={'hp': value})
                    self.assertEqual(engine._evaluate_condition(condition, vars_ctx=runner._vars), expected)
                    detail = MacroEngine.debug_condition_tree(engine, condition, vars_ctx=runner._vars)
                    self.assertEqual(detail['result'], expected)

    def test_and_short_circuit_disabled_nodes_and_actual_values(self):
        condition = Condition(type='all', conditions=[
            Condition(type='key', key='x', enabled=False),
            Condition(type='var', name='체력', var_name='hp', var_value='50'),
            Condition(type='key', key='q')])
        runner, engine = real_runner(condition, variables={'hp': '72'})
        evidence, counts = inspect(runner, engine)
        self.assertEqual([node['state'] for node in evidence['children']], ['disabled', 'false', 'not_evaluated'])
        self.assertEqual(evidence['state'], 'false')
        self.assertEqual(counts['false'], 1)
        self.assertEqual(evidence['children'][1]['actual'], '72')
        self.assertIn('50', evidence['children'][1]['criterion'])
        self.assertIn('AND', evidence['children'][2]['reason'])
        engine._key_pressed.assert_not_called()

    def test_or_stops_after_first_true_without_testing_remaining_key(self):
        condition = Condition(type='any', conditions=[
            Condition(type='var', var_name='hp', var_value='50'),
            Condition(type='var', var_name='hp', var_value='72'),
            Condition(type='key', key='q')])
        runner, engine = real_runner(condition, variables={'hp': '72'})
        evidence, counts = inspect(runner, engine)
        self.assertEqual([node['state'] for node in evidence['children']], ['false', 'true', 'not_evaluated'])
        self.assertEqual(counts['true'], 1)
        self.assertIn('OR', evidence['children'][2]['reason'])
        engine._key_pressed.assert_not_called()

    def test_on_false_can_turn_base_false_into_final_true(self):
        condition = Condition(type='var', var_name='base', var_value='yes',
            on_true=[Condition(type='key', key='x')],
            on_false=[Condition(type='var', var_name='fallback', var_value='yes'),
                      Condition(type='key', key='y')])
        runner, engine = real_runner(condition, variables={'base': 'no', 'fallback': 'yes'})
        evidence, counts = inspect(runner, engine)
        self.assertIs(evidence['base_result'], False)
        self.assertIs(evidence['result'], True)
        self.assertEqual(evidence['on_true'][0]['state'], 'not_evaluated')
        self.assertEqual([n['state'] for n in evidence['on_false']], ['true', 'not_evaluated'])
        self.assertIn('후속 조건', evidence['reason'])
        self.assertEqual(counts['true'], 1)
        engine._key_pressed.assert_not_called()

    def test_on_true_can_turn_base_true_into_final_false_and_reads_key_once(self):
        condition = Condition(type='key', key='x', key_mode='press',
            on_true=[Condition(type='var', var_name='hp', var_value='50')],
            on_false=[Condition(type='key', key='y')])
        runner, engine = real_runner(condition, variables={'hp': '72'})
        engine._key_pressed.return_value = True
        evidence, counts = inspect(runner, engine)
        self.assertIs(evidence['base_result'], True)
        self.assertIs(evidence['result'], False)
        self.assertEqual(evidence['on_true'][0]['state'], 'false')
        self.assertEqual(evidence['on_false'][0]['state'], 'not_evaluated')
        self.assertEqual(counts['false'], 1)
        engine._key_pressed.assert_called_once_with('x')
        self.assertTrue(runner._cond_key_states['x'])

    def test_pixel_unavailable_is_not_presented_as_a_false_test(self):
        condition = Condition(type='all', conditions=[
            Condition(type='pixel', region=(0, 0, 2, 2), color=(255, 0, 0)),
            Condition(type='key', key='q')])
        runner, engine = real_runner(condition)
        engine._pixel_check.return_value = dict(result=False, unavailable=True, error='대상 창을 찾을 수 없습니다.')
        evidence, counts = inspect(runner, engine)
        self.assertEqual(evidence['state'], 'unavailable')
        self.assertEqual(evidence['children'][0]['state'], 'unavailable')
        self.assertIn('대상 창', evidence['children'][0]['reason'])
        self.assertEqual((counts['true'], counts['false'], counts['unavailable']), (0, 0, 1))
        engine._key_pressed.assert_not_called()

    def test_pixel_snapshot_excludes_images_and_large_coordinate_arrays(self):
        condition = Condition(type='pixel', region=(0, 0, 2, 2), color=(255, 0, 0), pixel_exists=False)
        runner, engine = real_runner(condition)
        engine._pixel_check.return_value = dict(result=True, match_count=0, sample_color=(12, 34, 56),
            image_png=b'x' * 10000, matched_coords=[(1, 2)] * 10000, pattern_points=[(1, 2)] * 10000)
        evidence, _ = inspect(runner, engine)
        serialized = json.dumps(evidence, ensure_ascii=False)
        self.assertEqual(evidence['state'], 'true')
        self.assertIn('일치 0개', evidence['criterion'])
        self.assertNotIn('image_png', serialized)
        self.assertNotIn('matched_coords', serialized)
        self.assertLess(len(serialized), 2000)
        engine._pixel_check.assert_called_once()

    def test_unavailable_followup_is_distinct_from_a_normal_false_result(self):
        runner, engine = real_runner(Condition(type='key', key='a', on_true=[
            Condition(type='pixel', region=(0, 0, 2, 2), color=(255, 0, 0))]))
        engine._key_pressed.return_value = True
        engine._pixel_check.return_value = dict(result=False, unavailable=True, error='대상 창 없음')
        evidence, counts = inspect(runner, engine)
        self.assertEqual(evidence['state'], 'unavailable')
        self.assertIs(evidence['base_result'], True)
        self.assertIs(evidence['result'], False)
        self.assertEqual((counts['false'], counts['unavailable']), (0, 1))

    def test_existing_false_followup_recovery_is_reported_without_changing_runtime_behavior(self):
        runner, engine = real_runner(Condition(type='pixel', region=(0, 0, 2, 2), color=(255, 0, 0),
                                              on_false=[Condition(type='key', key='a')]))
        engine._pixel_check.return_value = dict(result=False, unavailable=True, error='대상 창 없음')
        engine._key_pressed.return_value = True
        evidence, counts = inspect(runner, engine)
        self.assertEqual(evidence['state'], 'unavailable')
        self.assertIs(evidence['result'], True)
        self.assertIn('최종 참', evidence['reason'])
        self.assertEqual((counts['true'], counts['false'], counts['unavailable']), (1, 0, 1))

    def test_external_wait_is_false_and_does_not_skip_other_conditions(self):
        condition = Condition(type='all', conditions=[Condition(type='key', key='x'),
            Condition(type='external', external_key='회복가능')])
        runner, engine = real_runner(condition)
        engine._key_pressed.return_value=True
        with patch('external_state.state_hub.evaluate', return_value=(False,
                   dict(unavailable=True, key='회복가능', status='내용 이름 수신 대기'))) as evaluate:
            evidence, counts = inspect(runner, engine)
        evaluate.assert_called_once()
        self.assertEqual(evidence['state'], 'false')
        self.assertEqual(evidence['children'][0]['state'], 'true')
        self.assertEqual(evidence['children'][1]['state'], 'false')
        self.assertIn('수신 대기', evidence['children'][1]['reason'])
        self.assertEqual((counts['false'], counts['unavailable']), (1, 0))
        engine._key_pressed.assert_called_once_with('x')

    def test_elif_has_its_own_last_evaluation(self):
        runner, engine = real_runner(Condition(type='key', key='a'),
            elif_blocks=[(Condition(type='key', key='b'), [], '다른 조건')])
        engine._key_pressed.side_effect = lambda key: key == 'b'
        inspect(runner, engine)
        counts = main_macro(engine.execution_analysis.snapshot())['counts']
        self.assertEqual(counts[(0,)]['condition_detail']['state'], 'false')
        self.assertEqual(counts[(0, 'elif0')]['condition_detail']['state'], 'true')
        self.assertEqual(engine._key_pressed.call_count, 2)

    def test_disabled_root_is_not_counted_as_false(self):
        runner, engine = real_runner(Condition(type='key', key='q', enabled=False))
        evidence, counts = inspect(runner, engine)
        self.assertEqual(evidence['state'], 'disabled')
        self.assertEqual((counts['true'], counts['false']), (0, 0))
        engine._key_pressed.assert_not_called()

    def test_missing_if_condition_has_an_explicit_explanation(self):
        runner, engine = real_runner(None)
        evidence, counts = inspect(runner, engine)
        self.assertEqual(evidence['state'], 'error')
        self.assertIn('조건이 지정되지', evidence['reason'])
        self.assertEqual(counts['errors'], 1)

    def test_error_marks_the_failed_leaf_and_does_not_retry(self):
        runner, engine = real_runner(Condition(type='all', conditions=[
            Condition(type='pixel', region=(0, 0, 2, 2), color=(255, 0, 0))]))
        engine._pixel_check.side_effect = RuntimeError('검사 실패 원인')
        with self.assertRaisesRegex(RuntimeError, '검사 실패 원인'):
            inspect(runner, engine)
        counts = main_macro(engine.execution_analysis.snapshot())['counts'][(0,)]
        evidence = counts['condition_detail']
        self.assertEqual(evidence['state'], 'error')
        self.assertEqual(evidence['children'][0]['state'], 'error')
        self.assertIn('검사 실패 원인', evidence['children'][0]['reason'])
        self.assertEqual(counts['errors'], 1)
        engine._pixel_check.assert_called_once()

    def test_timer_and_schedule_keep_values_from_actual_evaluation(self):
        runner, engine = real_runner(Condition(type='timer', timer_index=1, timer_value=2,
                                                timer_operator='ge', timer_unit='sec'))
        evidence, _ = inspect(runner, engine)
        self.assertEqual(evidence['state'], 'false')
        self.assertIn('1.25', evidence['actual'])
        self.assertIn('2', evidence['criterion'])
        engine._get_timer_value.assert_called_once_with(1)
        runner, engine = real_runner(Condition(type='schedule', schedule_value_raw='12:00'))
        with patch('engine._evaluate_schedule_condition_result', return_value=(False, {'schedule':
                   dict(current_text='13:00', expected_text='12:00', operator_text='=')})) as evaluate:
            evidence, _ = inspect(runner, engine)
        evaluate.assert_called_once()
        self.assertEqual(evidence['actual'], '13:00')
        self.assertIn('12:00', evidence['criterion'])

    def test_shared_condition_uses_expanded_definition(self):
        runner, engine = real_runner(Condition(type='var', shared_ref='shared', name='공용 조건'))
        engine._profile.shared_settings = {'shared': {'name': '기준', 'condition':
            dict(type='var', var_name='hp', var_value='72')}}
        runner._vars.var['hp'] = '72'
        evidence, _ = inspect(runner, engine)
        self.assertEqual(evidence['state'], 'true')
        self.assertEqual(evidence['actual'], '72')
        self.assertIn('hp', evidence['criterion'])

    def test_unmeasured_evaluation_does_not_build_details_or_change_behavior(self):
        runner, engine = real_runner(Condition(type='all', conditions=[
            Condition(type='key', key='a'), Condition(type='key', key='b')]))
        engine.execution_analysis.clear()
        with patch('engine.condition_template', side_effect=AssertionError('Unexpected detail collection')):
            runner._run_actions(runner.macro.actions, {})
        self.assertIsNone(engine.execution_analysis.snapshot())
        engine._key_pressed.assert_called_once_with('a')

    def test_new_measurement_does_not_show_detail_captured_before_start(self):
        runner, engine = real_runner(Condition(type='key', key='a'))
        engine._key_pressed.side_effect = lambda key: (engine.execution_analysis.start(), False)[1]
        evidence, counts = inspect(runner, engine)
        self.assertIsNone(evidence)
        self.assertEqual(counts['false'], 1)

    def test_repeated_checks_overwrite_one_snapshot_and_stopping_freezes_it(self):
        runner, engine = real_runner(Condition(type='var', var_name='hp', var_value='50'), variables={'hp': '72'})
        for value in ('72', '50') * 50:
            runner._vars.var['hp'] = value
            inspect(runner, engine)
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(len(snapshot['macros']), 1)
        counts = main_macro(snapshot)['counts'][(0,)]
        self.assertEqual((counts['true'], counts['false']), (50, 50))
        self.assertEqual(counts['condition_detail']['actual'], '50')
        engine.execution_analysis.stop()
        frozen = copy.deepcopy(engine.execution_analysis.snapshot())
        runner._vars.var['hp'] = '15'
        runner._run_actions(runner.macro.actions, {})
        self.assertEqual(engine.execution_analysis.snapshot(), frozen)

    def test_ui_detail_is_collapsed_and_never_rechecks_live_values(self):
        runner, engine = real_runner(Condition(type='all', conditions=[
            Condition(type='var', name='체력 확인', var_name='hp', var_value='50'),
            Condition(type='key', key='a')]), variables={'hp': '72'})
        inspect(runner, engine)
        engine.execution_analysis.stop()
        runner._vars.var['hp'] = '50'
        engine._evaluate_condition = Mock(side_effect=AssertionError('UI must not evaluate conditions'))
        dialog = ExecutionAnalysisDialog(engine.execution_analysis)
        dialog.show()
        APP.processEvents()
        key = next(iter(engine.execution_analysis.snapshot()['macros']))
        dialog.tree.setCurrentItem(dialog._items[key, (0,)])
        self.assertTrue(dialog.condition_panel.isHidden())
        self.assertTrue(dialog.condition_button.isEnabled())
        dialog.condition_button.click()
        APP.processEvents()
        self.assertTrue(dialog.condition_panel.isVisible())
        root = dialog.condition_tree.topLevelItem(0)
        self.assertEqual(root.child(0).text(1), '거짓')
        self.assertIn('72', root.child(0).text(2))
        self.assertEqual(root.child(1).text(1), '미검사')
        dialog.refresh()
        engine._evaluate_condition.assert_not_called()
        dialog.start_button.click()
        self.assertEqual(dialog.condition_tree.topLevelItemCount(), 0)
        self.assertFalse(dialog.condition_button.isEnabled())
        dialog.close()
        self.assertIsNone(dialog._displayed_condition)
        dialog.deleteLater()


if __name__ == '__main__':
    unittest.main()
