"""Exercise the real runner with fake input, condition evaluation and no drivers."""
import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import threading
import copy
import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch

from PyQt6 import QtCore, QtWidgets, QtTest
from engine import Action, Condition, Macro, MacroRunner, MacroVariables, MacroEngine
from execution_analysis import ExecutionRecorder, action_catalog, row_explanation, selection_evidence
from execution_analysis_ui import ExecutionAnalysisDialog

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


def make_runner(actions, *, outcomes=None, stop_actions=None):
    values = iter(outcomes or [])
    engine = SimpleNamespace(
        execution_analysis=ExecutionRecorder(), _profile=SimpleNamespace(variables=MacroVariables()),
        tick=0.0001, _emit_event=Mock(), _emit_log=Mock(), _start_all_timers_from_zero=Mock(),
        _resolve_key_delays=lambda _: (0, 0), _resolve_mouse_delays=lambda _: (0, 0),
        _send_key=Mock(return_value=True), _send_mouse=Mock(return_value=True),
        _send_mouse_wheel=Mock(return_value=True),
        _evaluate_condition=lambda *args, **kwargs: next(values),
    )
    macro = Macro(name='테스트', trigger_key='mouse2', mode='hold', cycle_count=1,
                  actions=actions, stop_actions=stop_actions or [])
    engine.execution_analysis.start()
    runner = MacroRunner(macro, engine, 0)
    runner._current_cycle = 0
    runner._terminal_status = 'running'
    runner._begin_analysis()
    return runner, engine


def run_snapshot(runner, engine):
    runner._run()
    return engine.execution_analysis.snapshot()


def main_macro(snapshot):
    return next(iter(snapshot['macros'].values()))


class EngineAnalysisTests(unittest.TestCase):
    def test_nested_if_false_and_disabled_descendants(self):
        actions = [Action(type='if', condition=Condition(type='key', key='a'), actions=[
            Action(type='if', condition=Condition(type='key', key='b'), actions=[Action(type='press', key='x')])]),
            Action(type='if', enabled=False, condition=Condition(type='key', key='c'),
                   actions=[Action(type='press', key='y')])]
        runner, engine = make_runner(actions, outcomes=[True, False])
        snapshot = run_snapshot(runner, engine)
        macro = main_macro(snapshot)
        c = macro['counts']
        self.assertEqual((c[(0,)]['true'], c[(0, 0)]['false']), (1, 1))
        self.assertEqual(c[(0, 0, 0)]['reached'], 0)
        row = next(r for r in macro['rows'] if r['path'] == (0, 0, 0))
        self.assertIn('부모 조건 참 0회', row_explanation(row, macro))
        self.assertTrue(next(r for r in macro['rows'] if r['path'] == (1, 0))['disabled'])
        self.assertEqual(c[(1,)]['skipped'], 1)
        self.assertEqual(engine._send_key.call_count, 0)
        self.assertIsNone(snapshot['ended'])
        self.assertTrue(engine.execution_analysis.enabled)

    def test_true_count_survives_nested_goto_and_records_actual_source(self):
        actions = [Action(type='if', condition=Condition(type='key', key='a'), actions=[
            Action(type='press', key='x', repeat=3), Action(type='goto', goto_label='end')]),
            Action(type='press', key='unreached'), Action(type='label', label='end')]
        runner, engine = make_runner(actions, outcomes=[True])
        snapshot = run_snapshot(runner, engine)
        c = main_macro(snapshot)['counts']
        self.assertEqual(c[(0,)]['true'], 1)
        self.assertEqual(c[(0, 0)]['inputs'], 3)
        self.assertEqual(c[(0, 0)]['reached'], 1)
        self.assertEqual(c[(1,)]['reached'], 0)
        self.assertEqual(c[(0, 1)]['jumps'], 1)
        self.assertEqual(c[(0, 1)]['destination'], 'end')

    def test_partial_input_failure_counts_only_successes(self):
        runner, engine = make_runner([Action(type='press', key='x', repeat=5)])
        engine._send_key.side_effect = [True, True, False]
        c = main_macro(run_snapshot(runner, engine))['counts'][(0,)]
        self.assertEqual(c['inputs'], 2)
        self.assertEqual(c['errors'], 1)

    def test_elif_and_else_use_runner_offsets(self):
        action = Action(type='if', condition=Condition(type='key', key='a'),
                        actions=[Action(type='press', key='a')],
                        elif_blocks=[(Condition(type='key', key='b'), [Action(type='press', key='b')], 'B')],
                        has_else_branch=True, else_actions=[Action(type='press', key='c')])
        for outcomes, destination in [([False, True], (0, 1)), ([False, False], (0, 2))]:
            runner, engine = make_runner([action], outcomes=outcomes)
            macro = main_macro(run_snapshot(runner, engine))
            self.assertEqual(macro['counts'][destination]['inputs'], 1)
            self.assertEqual(macro['counts'][(0, 'elif0')]['reached'], 1)
            self.assertEqual(macro['counts'][(0, 'elif0')]['true'], int(outcomes[1]))
            if not outcomes[1]:
                self.assertEqual(macro['counts'][(0, 'else')]['reached'], 1)
                row = next(r for r in macro['rows'] if r['path'] == destination)
                self.assertNotIn('부모 조건 참 0회', row_explanation(row, macro))

    def test_external_readiness_does_not_skip_a_false_condition(self):
        runner, engine = make_runner([Action(type='if', condition=Condition(type='external'))],outcomes=[False])
        with patch('engine.external_conditions_ready', return_value=False):
            c = main_macro(run_snapshot(runner, engine))['counts'][(0,)]
        self.assertEqual((c['reached'], c['true'], c['false'], c['errors'], c['unavailable']), (1, 0, 1, 0, 0))

    def test_disabled_else_skips_only_false_branch_and_roundtrips(self):
        action = Action(type='if', condition=Condition(type='key', key='a'),
                        actions=[Action(type='press', key='a')], has_else_branch=True,
                        else_enabled=False, else_actions=[Action(type='press', key='b')])
        restored = Action.from_dict(action.to_dict())
        self.assertFalse(restored.else_enabled)
        self.assertTrue(Action.from_dict({'type': 'if'}).else_enabled)
        for outcome in (True, False):
            runner, engine = make_runner([restored], outcomes=[outcome])
            macro = main_macro(run_snapshot(runner, engine))
            self.assertEqual(macro['counts'][(0, 0)]['inputs'], int(outcome))
            self.assertEqual(macro['counts'][(0, 1)]['inputs'], 0)
            disabled = [row for row in macro['rows'] if row['path'] in ((0, 'else'), (0, 1))]
            self.assertTrue(all(row['disabled'] for row in disabled))
            self.assertEqual(macro['counts'][(0,)]['false'], int(not outcome))

    def test_invalid_goto_not_counted_as_success(self):
        runner, engine = make_runner([Action(type='goto', goto_label='missing')])
        snapshot = run_snapshot(runner, engine)
        c = main_macro(snapshot)['counts'][(0,)]
        self.assertEqual((c['jumps'], c['errors']), (0, 1))
        self.assertEqual(c['destination'], '')

    def test_return_is_not_counted_as_reaching_end_of_list(self):
        runner, engine = make_runner([Action(type='return'), Action(type='press', key='x')])
        snapshot = run_snapshot(runner, engine)
        self.assertEqual(main_macro(snapshot)['counts'][(0,)]['last'], 'return')
        self.assertEqual(main_macro(snapshot)['counts'][(1,)]['reached'], 0)

    def test_confirm_fails_counts_every_evaluation(self):
        runner, engine = make_runner([Action(type='if', condition=Condition(type='key', key='a'),
                                             confirm_fails=3)], outcomes=[False]*3)
        c = main_macro(run_snapshot(runner, engine))['counts'][(0,)]
        self.assertEqual((c['reached'], c['false']), (3, 3))

    def test_mouse_repeat_counts_successful_logical_inputs(self):
        runner, engine = make_runner([Action(type='mouse_click', mouse_button='mouse1', repeat=4)])
        c = main_macro(run_snapshot(runner, engine))['counts'][(0,)]
        self.assertEqual(c['inputs'], 4)
        self.assertEqual(engine._send_mouse.call_count, 4)

    def test_current_position_during_sleep_and_last_after_finish(self):
        runner, engine = make_runner([Action(type='sleep', sleep_ms=10)])
        def observe(*args, **kwargs):
            snap = engine.execution_analysis.snapshot()
            self.assertEqual(main_macro(snap)['counts'][(0,)]['last'], 'action_start')
        runner._sleep_with_condition_poll = observe
        snapshot = run_snapshot(runner, engine)
        self.assertEqual(main_macro(snapshot)['counts'][(0,)]['last'], 'sleep')

    def test_start_thread_records_run_and_retains_result_after_stop(self):
        runner, engine = make_runner([Action(type='press', key='x', repeat=3)])
        # Start through the same entry point used by the engine, not just the test helper.
        runner.start(reset_all_timers=False)
        runner._thread.join(timeout=2)
        self.assertFalse(runner.is_alive())
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(snapshot['state'], 'running')
        self.assertEqual(main_macro(snapshot)['counts'][(0,)]['inputs'], 3)
        self.assertIsNone(snapshot['ended'])

    def test_parallel_workers_share_session_and_keep_separate_lanes(self):
        runner, engine = make_runner([Action(type='group', parallel_enabled=True,
                                             actions=[Action(type='press', key='p')]),
                                      Action(type='sleep', sleep_ms=5)])
        snapshot = run_snapshot(runner, engine)
        self.assertEqual(len(snapshot['macros']), 1)
        self.assertGreater(main_macro(snapshot)['counts'][(0, 0)]['inputs'], 0)
        self.assertNotIn('trace', snapshot)
        self.assertNotIn('current', snapshot)

    def test_stop_actions_have_separate_catalog(self):
        runner, engine = make_runner([Action(type='noop')], stop_actions=[Action(type='press', key='s')])
        runner._run_actions(runner.macro.actions, {}, root=True)
        runner._run_stop_actions()
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(len(snapshot['macros']), 2)
        stop = next(m for m in snapshot['macros'].values() if '종료 액션' in m['name'])
        self.assertEqual(stop['counts'][(0,)]['inputs'], 1)


class RecorderTests(unittest.TestCase):
    def test_threaded_counts_are_exact_without_event_history(self):
        recorder = ExecutionRecorder()
        measurement = recorder.start()
        recorder.register(measurement, 'm', 'fast', action_catalog([Action(type='noop')]))
        def work():
            for _ in range(2500):
                recorder.record(measurement, 'm', (0,), 'action_start')
        workers = [threading.Thread(target=work) for _ in range(4)]
        for worker in workers:
            worker.start()
        for worker in workers:
            worker.join()
        snapshot = recorder.snapshot()
        self.assertEqual(snapshot['macros']['m']['counts'][(0,)]['reached'], 10000)
        self.assertNotIn('trace', snapshot)
        self.assertNotIn('jumps', snapshot)
        self.assertNotIn('current', snapshot)
        snapshot['macros']['m']['counts'][(0,)]['reached'] = 0
        self.assertEqual(recorder.snapshot()['macros']['m']['counts'][(0,)]['reached'], 10000)

    def test_repeated_macro_executions_share_one_fixed_size_measurement(self):
        runner, engine = make_runner([Action(type='press', key='q')])
        for _ in range(1000):
            repeated = MacroRunner(runner.macro, engine, 0)
            repeated._current_cycle = 0
            repeated._run()
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(len(snapshot['macros']), 1)
        self.assertEqual(len(main_macro(snapshot)['counts']), 1)
        self.assertEqual(main_macro(snapshot)['counts'][(0,)]['inputs'], 1000)
        self.assertEqual(len(engine.execution_analysis._definitions), 1)

    def test_stop_freezes_result_and_restart_rejects_old_measurement_events(self):
        recorder = ExecutionRecorder()
        first = recorder.start()
        catalog = action_catalog([Action(type='noop')])
        recorder.register(first, 'm', 'A', catalog)
        recorder.record(first, 'm', (0,), 'action_start')
        recorder.stop()
        before = recorder.snapshot()
        recorder.record(first, 'm', (0,), 'action_start')
        self.assertEqual(recorder.snapshot(), before)
        second = recorder.start()
        self.assertNotEqual(first, second)
        self.assertEqual(recorder.snapshot()['macros'], {})
        recorder.register(second, 'm', 'A', catalog)
        recorder.record(first, 'm', (0,), 'action_start')
        self.assertEqual(main_macro(recorder.snapshot())['counts'][(0,)]['reached'], 0)
        recorder.clear()
        self.assertIsNone(recorder.snapshot())
        self.assertFalse(recorder.enabled)

    def test_new_configuration_stops_instead_of_mixing_results(self):
        recorder = ExecutionRecorder()
        measurement = recorder.start()
        catalog = action_catalog([Action(type='noop')])
        recorder.register(measurement, 'old', 'A', catalog, slot=(0, False))
        recorder.record(measurement, 'old', (0,), 'action_start')
        self.assertFalse(recorder.register(measurement, 'changed', 'A', catalog, slot=(0, False)))
        self.assertFalse(recorder.enabled)
        self.assertIn('설정이 변경', recorder.snapshot()['reason'])
        self.assertEqual(list(recorder.snapshot()['macros']), ['old'])

    def test_same_action_paths_from_different_macros_are_separate(self):
        runner, engine = make_runner([Action(type='press', key='q')])
        other = MacroRunner(Macro(trigger_key='b', name='다른 매크로', actions=[Action(type='press', key='w')]), engine, 1)
        other._current_cycle = 0
        runner._run_actions(runner.macro.actions, {})
        other._run_actions(other.macro.actions, {})
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(len(snapshot['macros']), 2)
        self.assertEqual([m['counts'][(0,)]['inputs'] for m in snapshot['macros'].values()], [1, 1])

    def test_manual_once_and_repeat_use_the_same_action_definition(self):
        runner, engine = make_runner([Action(type='press', key='q')])
        runner._run_actions(runner.macro.actions, {})
        repeated_macro = copy.deepcopy(runner.macro)
        repeated_macro.cycle_count = None
        repeated = MacroRunner(repeated_macro, engine, 0)
        repeated._current_cycle = 0
        repeated._run_actions(repeated.macro.actions, {})
        snapshot = engine.execution_analysis.snapshot()
        self.assertTrue(engine.execution_analysis.enabled)
        self.assertEqual(len(snapshot['macros']), 1)
        self.assertEqual(main_macro(snapshot)['counts'][(0,)]['inputs'], 2)

    def test_start_shows_only_macros_actually_executed_during_measurement(self):
        runner, engine = make_runner([Action(type='press', key='q')])
        engine._lock = threading.RLock()
        engine._profile.macros = [runner.macro,
            Macro(trigger_key='b', name='미실행', actions=[Action(type='noop')]),
            Macro(trigger_key='c', enabled=False, actions=[Action(type='noop')])]
        MacroEngine.start_execution_analysis(engine)
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(snapshot['macros'], {})
        runner._run_actions(runner.macro.actions, {})
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(len(snapshot['macros']), 1)
        self.assertEqual(main_macro(snapshot)['counts'][(0,)]['inputs'], 1)
        self.assertEqual(main_macro(snapshot)['name'], '테스트')
        other = MacroRunner(engine._profile.macros[1], engine, 1)
        other._current_cycle = 0
        other._run_actions(other.macro.actions, {})
        self.assertEqual(len(engine.execution_analysis.snapshot()['macros']), 2)

    def test_live_quick_switch_stops_measurement_and_can_be_measured_again(self):
        runner, engine = make_runner([Action(type='press', key='q', quick_toggle_id='switch')])
        engine._lock = threading.RLock()
        engine._profile.macros = [copy.deepcopy(runner.macro)]
        engine.quick_action_enabled = lambda index, action: MacroEngine.quick_action_enabled(engine, index, action)
        MacroEngine.set_quick_toggle(engine, 0, 'switch', False)
        self.assertFalse(engine.execution_analysis.enabled)
        self.assertIn('설정이 변경', engine.execution_analysis.snapshot()['reason'])
        MacroEngine.start_execution_analysis(engine)
        runner._run_actions(runner.macro.actions, {})
        self.assertTrue(engine.execution_analysis.enabled)
        snapshot = engine.execution_analysis.snapshot()
        self.assertEqual(len(snapshot['macros']), 1)
        self.assertTrue(main_macro(snapshot)['rows'][0]['disabled'])
        self.assertEqual(main_macro(snapshot)['counts'][(0,)]['inputs'], 0)


class MeasurementGateTests(unittest.TestCase):
    def test_default_off_skips_catalog_and_signature_work(self):
        recorder = ExecutionRecorder()
        self.assertFalse(recorder.enabled)
        self.assertIsNone(recorder.begin())
        runner, engine = make_runner([Action(type='noop')])
        engine.execution_analysis = recorder
        with patch('engine.macro_signature', side_effect=AssertionError('Disabled analysis must not hash macros')):
            runner._begin_analysis()
            runner._run_actions(runner.macro.actions, {})
        self.assertIsNone(recorder.snapshot())

    def test_open_waits_for_start_stop_does_not_stop_macro_and_close_discards(self):
        runner, engine = make_runner([Action(type='press', key='a')])
        recorder = engine.execution_analysis
        recorder.clear()
        dialog = ExecutionAnalysisDialog(recorder)
        dialog.show()
        APP.processEvents()
        self.assertFalse(recorder.enabled)
        runner._run_actions(runner.macro.actions, {})
        self.assertIsNone(recorder.snapshot())
        dialog.start_button.click()
        runner._run_actions(runner.macro.actions, {})
        dialog.stop_button.click()
        before = recorder.snapshot()
        self.assertEqual(main_macro(before)['counts'][(0,)]['inputs'], 1)
        runner._run_actions(runner.macro.actions, {})
        self.assertEqual(engine._send_key.call_count, 3)
        self.assertEqual(recorder.snapshot(), before)
        dialog.start_button.click()
        self.assertEqual(recorder.snapshot()['macros'], {})
        runner._run_actions(runner.macro.actions, {})
        self.assertEqual(main_macro(recorder.snapshot())['counts'][(0,)]['inputs'], 1)
        dialog.close()
        self.assertIsNone(recorder.snapshot())
        self.assertIsNone(dialog._snapshot)
        self.assertFalse(dialog._items)
        dialog.show()
        APP.processEvents()
        self.assertFalse(recorder.enabled)
        QtTest.QTest.keyClick(dialog, QtCore.Qt.Key.Key_Escape)
        self.assertIsNone(recorder.snapshot())
        dialog.deleteLater()

    def test_parallel_worker_joins_current_measurement_after_restart(self):
        runner, engine = make_runner([Action(type='noop')])
        worker = MacroRunner(runner.macro, engine, 0)
        worker._parallel_owner = runner
        engine.execution_analysis.stop()
        engine.execution_analysis.start()
        worker._analysis_record('action_start', [0])
        runner._analysis_record('action_start', [0])
        self.assertEqual(worker._analysis_id, runner._analysis_id)
        self.assertEqual(main_macro(engine.execution_analysis.snapshot())['counts'][(0,)]['reached'], 2)

    def test_start_during_input_counts_only_events_in_measurement(self):
        runner, engine = make_runner([Action(type='press', key='q', repeat=3)])
        recorder = engine.execution_analysis
        recorder.clear()
        sends = []
        def send(*args, **kwargs):
            sends.append(1)
            if len(sends) == 2:
                recorder.start()
            return True
        engine._send_key.side_effect = send
        runner._run_actions(runner.macro.actions, {})
        macro = main_macro(recorder.snapshot())
        self.assertEqual((macro['counts'][(0,)]['reached'], macro['counts'][(0,)]['inputs']), (0, 2))
        explanation, _, _ = selection_evidence(macro['rows'][0], macro)
        self.assertIn('측정 시작 전부터 실행 중', explanation)


class AnalysisUiTests(unittest.TestCase):
    def test_numbers_match_editor_including_branches_and_parallel_tab(self):
        from main import ActionTreeWidget
        branch = Action(type='if', condition=Condition(type='key', key='a'),
            actions=[Action(type='noop'), Action(type='if', condition=Condition(type='key', key='b'),
                actions=[Action(type='noop')], has_else_branch=True, else_actions=[Action(type='noop')])],
            elif_blocks=[(Condition(type='key', key='c'), [Action(type='noop')], '다른 조건')],
            has_else_branch=True, else_actions=[Action(type='noop')])
        parallel = Action(type='group', parallel_enabled=True, actions=[copy.deepcopy(branch)])
        actions = [Action(type='noop'), parallel, branch, Action(type='noop', enabled=False)]
        catalog = action_catalog(actions)
        for is_parallel in (False, True):
            tree = ActionTreeWidget()
            tree.load_actions([copy.deepcopy(action) for action in actions if action.parallel_enabled == is_parallel])
            tree.refresh_workspace()
            expected = [item.text(0) for item in tree.items()]
            actual = [row['number'] for row in catalog if actions[row['path'][0]].parallel_enabled == is_parallel]
            self.assertEqual(actual, expected)
            editor_if_labels = [item.text(2) for item in tree.items() if tree.is_if(item)]
            analysis_if_labels = [row['label'] for row in catalog
                                  if row['kind'] == 'if' and actions[row['path'][0]].parallel_enabled == is_parallel]
            self.assertEqual(analysis_if_labels, editor_if_labels)
            self.assertEqual(analysis_if_labels, ['#01', '#02'])
            tree.deleteLater()
        runner, engine = make_runner([Action(type='noop')])
        runner._run_actions(runner.macro.actions, {})
        dialog = ExecutionAnalysisDialog(engine.execution_analysis)
        self.assertEqual(dialog.tree.headerItem().text(0), '순번')
        self.assertEqual(dialog.tree.treePosition(), 1)
        item = next(iter(dialog._items.values()))
        self.assertEqual(item.text(0), '1')
        for column in (0, 2, 3, 4, 5):
            self.assertEqual(item.textAlignment(column), QtCore.Qt.AlignmentFlag.AlignCenter)
            self.assertEqual(dialog.tree.headerItem().textAlignment(column), QtCore.Qt.AlignmentFlag.AlignCenter)
        dialog.close()
        dialog.deleteLater()

    def test_selection_explains_conditions_and_highlights_executed_actions(self):
        actions = [Action(type='if', name='물약 확인', condition=Condition(type='key', key='a'),
                          actions=[Action(type='press', key='q', repeat=3), Action(type='sleep', sleep_ms=1)]),
                   Action(type='if', name='조건 실패', condition=Condition(type='key', key='b'),
                          actions=[Action(type='press', key='w')])]
        runner, engine = make_runner(actions, outcomes=[True, False])
        run_snapshot(runner, engine)
        dialog = ExecutionAnalysisDialog(engine.execution_analysis)
        key = next(iter(engine.execution_analysis.snapshot()['macros']))
        dialog.tree.setCurrentItem(dialog._items[key, (0,)])
        self.assertIn('총 3회', dialog.detail.toPlainText())
        self.assertEqual(dialog._items[key, (0,)].text(4), '—')
        self.assertEqual(dialog._items[key, (0, 0)].text(4), '3')
        self.assertEqual(dialog._items[key, (0, 1)].background(0).color().name(), '#edf8f4')
        dialog.tree.setCurrentItem(dialog._items[key, (1, 0)])
        self.assertIn('부모 조건 참 0회', dialog.detail.toPlainText())
        dialog.close()
        dialog.deleteLater()

    def test_pin_keeps_measurement_and_refresh_keeps_selection_scroll_and_folds(self):
        actions = [Action(type='if', condition=Condition(type='key', key='a'), actions=[Action(type='noop')])]
        actions += [Action(type='noop', name=f'액션 {n}') for n in range(100)]
        runner, engine = make_runner(actions, outcomes=[False])
        run_snapshot(runner, engine)
        dialog = ExecutionAnalysisDialog(engine.execution_analysis)
        dialog.show()
        APP.processEvents()
        key = next(iter(engine.execution_analysis.snapshot()['macros']))
        current = dialog._items[key, (40,)]
        dialog.tree.setCurrentItem(current)
        dialog._items[key, (0,)].setExpanded(False)
        dialog.tree.verticalScrollBar().setValue(25)
        scroll = dialog.tree.verticalScrollBar().value()
        before = engine.execution_analysis.snapshot()
        dialog.pin_button.click()
        APP.processEvents()
        self.assertTrue(dialog.windowFlags() & QtCore.Qt.WindowType.WindowStaysOnTopHint)
        self.assertEqual(engine.execution_analysis.snapshot(), before)
        dialog.pin_button.click()
        APP.processEvents()
        self.assertFalse(dialog.windowFlags() & QtCore.Qt.WindowType.WindowStaysOnTopHint)
        dialog.refresh()
        self.assertIs(dialog.tree.currentItem(), current)
        self.assertFalse(dialog._items[key, (0,)].isExpanded())
        self.assertEqual(dialog.tree.verticalScrollBar().value(), scroll)
        self.assertFalse(dialog.isModal())
        self.assertEqual(dialog.timer.interval(), 500)
        dialog.close()
        dialog.deleteLater()

    def test_disabled_and_search_keep_parent_context(self):
        runner, engine = make_runner([
            Action(type='if', name='부모', condition=Condition(type='key', key='a'),
                   actions=[Action(type='press', key='q', name='회복')]),
            Action(type='noop', enabled=False, name='꺼진 항목')], outcomes=[True])
        run_snapshot(runner, engine)
        dialog = ExecutionAnalysisDialog(engine.execution_analysis)
        key = next(iter(engine.execution_analysis.snapshot()['macros']))
        self.assertTrue(dialog._items[key, (1,)].isHidden())
        dialog.hide_disabled.setChecked(False)
        self.assertFalse(dialog._items[key, (1,)].isHidden())
        dialog.search.setText('회복')
        self.assertFalse(dialog._items[key, (0,)].isHidden())
        self.assertFalse(dialog._items[key, (0, 0)].isHidden())
        self.assertTrue(dialog._items[key, (1,)].isHidden())
        dialog.close()
        dialog.deleteLater()


if __name__ == '__main__':
    unittest.main()


