"""Exercise IF edges through the real runner, evaluator, and action editor."""
import copy
import itertools
import unittest
from unittest.mock import Mock, patch

from PyQt6 import QtCore
from engine import Action, Condition, Macro, MacroEngine, MacroRunner, MacroProfile
from execution_analysis import action_catalog, row_explanation, selection_evidence
from execution_analysis_ui import ExecutionAnalysisDialog
from action_controls import macro_actions
from if_transition import target_choices, target_condition, bind_target, condition_identity
from main import ActionEditDialog, ActionTreeWidget, MacroDialog
from test_execution_analysis import APP, make_runner


def state(name):
    return Condition(type='var', var_name=name, var_value_raw='1')


def assign(name, value):
    return Action(type='set_var', var_name=name, var_value_raw=str(value))


class IfTransitionTests(unittest.TestCase):
    def setUp(self):
        self._existing_windows = {id(widget) for widget in APP.topLevelWidgets()}

    def tearDown(self):
        # Drain workspace callbacks while their trees are still alive, then
        # destroy parentless test windows before QApplication shuts down.
        for _ in range(3):
            APP.processEvents()
        for widget in APP.topLevelWidgets():
            if widget.parent() is None and id(widget) not in self._existing_windows:
                widget.close()
                widget.deleteLater()
        QtCore.QCoreApplication.sendPostedEvents(None, QtCore.QEvent.Type.DeferredDelete)
        APP.processEvents()

    def runner(self, actions, **values):
        runner, engine = make_runner(actions)
        engine._evaluate_condition = MacroEngine._evaluate_condition.__get__(engine)
        runner._vars.var.update({key: str(value) for key, value in values.items()})
        return runner, engine

    def edge(self, condition=None, target=None, actions=None, **kwargs):
        action = Action(type='if', condition=condition or state('ready'),
                      transition_enabled=True, transition_target=target or [],
                      transition_actions=actions if actions is not None else [Action(type='press', key='z')],
                      **kwargs)
        try:
            bind_target(action, {})
        except ValueError:
            pass
        return action

    def poll(self, runner):
        runner._transition_poll_at = 0
        return runner._poll_if_transitions({})

    def keys(self, engine):
        return [call.args[1] for call in engine._send_key.call_args_list]

    def test_initial_false_never_fires(self):
        action = self.edge()
        runner, engine = self.runner([action], ready=0)
        runner._run_actions([action], {})
        for _ in range(3):
            self.poll(runner)
        self.assertFalse(runner._if_transitions)
        self.assertEqual(self.keys(engine), [])

    def test_edge_fires_once_and_true_execution_rearms(self):
        action = self.edge()
        runner, engine = self.runner([action], ready=1)
        runner._exec_action(action, {}, [], [0])
        self.poll(runner)
        self.assertEqual(self.keys(engine), [])
        runner._vars.var['ready'] = '0'
        self.poll(runner)
        self.poll(runner)
        self.assertEqual(self.keys(engine), ['z'])
        runner._vars.var['ready'] = '1'
        runner._exec_action(action, {}, [], [0])
        runner._vars.var['ready'] = '0'
        self.poll(runner)
        self.assertEqual(self.keys(engine), ['z', 'z'])

    def test_selected_condition_ignores_other_false_and_skipped_parent(self):
        inner = self.edge(Condition(type='all', conditions=[state('target'), state('ready')]), [1])
        outer = Action(type='if', condition=state('parent'), actions=[inner])
        runner, engine = self.runner([outer], target=1, ready=1, parent=1)
        runner._exec_action(outer, {}, [], [0])
        runner._vars.var.update(target='0', parent='0')
        self.poll(runner)
        self.assertEqual(self.keys(engine), [])
        runner._vars.var['ready'] = '0'
        self.poll(runner)
        self.assertEqual(self.keys(engine), ['z'])

    def test_selected_or_child_must_first_be_seen_true(self):
        action = self.edge(Condition(type='any', conditions=[state('other'), state('ready')]), [1])
        runner, engine = self.runner([action], other=1, ready=0)
        runner._exec_action(action, {}, [], [0])
        self.poll(runner)
        self.assertEqual(self.keys(engine), [])
        runner._vars.var['ready'] = '1'
        self.poll(runner)
        runner._vars.var['ready'] = '0'
        self.poll(runner)
        self.assertEqual(self.keys(engine), ['z'])

    def test_real_flow_goto_keeps_watch_and_transition_goto_routes(self):
        action = self.edge()
        action.actions = [assign('ready', 0), Action(type='goto', goto_label='first')]
        action.transition_actions = [Action(type='press', key='z'), Action(type='goto', goto_label='end')]
        actions = [Action(type='label', label='first'), action, Action(type='press', key='bad'),
                   Action(type='label', label='end'), Action(type='press', key='y')]
        runner, engine = self.runner(actions, ready=1)
        with patch('engine.time.perf_counter', side_effect=itertools.count(0, 0.1)):
            runner._run_actions(actions, runner._label_index(actions), root=True)
        self.assertEqual(self.keys(engine), ['z', 'y'])

    def test_real_flow_transition_stops_before_next_input(self):
        action = self.edge(actions=[Action(type='macro_stop')])
        action.actions = [assign('ready', 0), Action(type='press', key='bad')]
        runner, engine = self.runner([action], ready=1)
        with patch('engine.time.perf_counter', side_effect=itertools.count(0, 0.1)):
            runner._run_actions([action], {})
        self.assertEqual(self.keys(engine), [])
        self.assertTrue(runner._stop_event.is_set())

    def test_new_trigger_and_restarted_runner_clear_watch(self):
        action = self.edge()
        runner, engine = self.runner([action], ready=1)
        runner._exec_action(action, {}, [], [0])
        second = MacroRunner(runner.macro, engine, 0)
        self.assertFalse(second._if_transitions)
        with patch('engine.threading.Thread'):
            runner.start()
        self.assertFalse(runner._if_transitions)

    def test_disabled_transition_and_disabled_if_do_not_fire(self):
        for disable_if in (False, True):
            action = self.edge()
            runner, engine = self.runner([action], ready=1)
            runner._exec_action(action, {}, [], [0])
            if disable_if:
                action.enabled = False
            else:
                action.transition_enabled = False
            runner._vars.var['ready'] = '0'
            self.poll(runner)
            self.assertEqual(self.keys(engine), [])

    def test_external_disconnect_is_not_a_false_edge(self):
        action = self.edge(Condition(type='external', external_key='ready'))
        runner, engine = self.runner([action])
        engine._external_conditions_ready = MacroEngine._external_conditions_ready.__get__(engine)
        engine._external_result = MacroEngine._external_result.__get__(engine)
        with patch('engine.state_hub.evaluate', return_value=(True, {})):
            runner._exec_action(action, {}, [], [0])
        with patch('engine.state_hub.evaluate', return_value=(False, {'unavailable': True})):
            self.poll(runner)
        self.assertEqual(self.keys(engine), [])
        with patch('engine.state_hub.evaluate', return_value=(False, {'unavailable': False})):
            self.poll(runner)
        self.assertEqual(self.keys(engine), ['z'])

    def test_shared_nested_target_and_removed_target(self):
        entries = {'skill': {'name': '스킬', 'condition': {'type': 'all', 'conditions': [state('ready').to_dict()]}}}
        cond = Condition(type='all', conditions=[Condition(type='all', shared_ref='skill')])
        self.assertEqual([path for path, _, _ in target_choices(cond, entries)], [(), (0,), (0, 0)])
        self.assertEqual(target_condition(cond, [0, 0], entries).var_name, 'ready')
        action = self.edge(cond, [0, 0])
        runner, engine = self.runner([action], ready=1)
        engine._profile.shared_settings = entries
        runner._exec_action(action, {}, [], [0])
        entries['skill']['condition']['conditions'] = []
        runner._vars.var['ready'] = '0'
        self.poll(runner)
        self.assertEqual(self.keys(engine), [])
        self.assertFalse(runner._if_transitions)

    def test_profile_editor_tree_and_analysis_roundtrip(self):
        action = self.edge(Condition(type='all', conditions=[state('target'), state('ready')]), [1],
                           actions=[Action(type='press', key='z')])
        action.actions = [Action(type='press', key='x')]
        action.has_else_branch = True
        action.else_actions = [Action(type='press', key='y')]
        original = action.to_dict()
        restored = Action.from_dict(original)
        self.assertEqual(restored.to_dict(), original)
        dialog = ActionEditDialog(action=restored)
        tree = ActionTreeWidget()
        try:
            self.assertEqual(dialog.transition_target_combo.currentData(), [1])
            self.assertEqual(dialog.get_action().to_dict(), original)
            tree.load_actions([restored])
            self.assertEqual(tree.collect_actions()[0].to_dict(), original)
            header = tree.topLevelItem(0).child(2)
            self.assertEqual(header.data(0, QtCore.Qt.ItemDataRole.UserRole), '__transition__')
            header.setCheckState(5, QtCore.Qt.CheckState.Unchecked)
            self.assertFalse(tree.collect_actions()[0].transition_enabled)
            self.assertEqual(len(tree.collect_actions()[0].transition_actions), 1)
            tree.topLevelItem(0).removeChild(header)
            self.assertFalse(tree.collect_actions()[0].transition_actions)
            rows = action_catalog([restored])
            self.assertEqual(next(row for row in rows if row['kind'] == 'transition')['path'], (0, 'transition'))
            self.assertEqual(rows[-1]['path'], (0, 2))
            measured = Action.from_dict(original)
            runner, engine = self.runner([measured], target=1, ready=1)
            runner._exec_action(measured, {}, [], [0])
            runner._vars.var['ready'] = '0'
            self.poll(runner)
            counts = next(iter(engine.execution_analysis.snapshot()['macros'].values()))['counts']
            self.assertEqual(counts[(0, 2)]['inputs'], 1)
            self.assertIn((0, 'transition'), counts)
            self.assertIn(measured.transition_actions[0], [child for child, _ in macro_actions(runner.macro)])
        finally:
            dialog.close()
            tree.close()

    def test_changed_target_requires_reselection(self):
        action = self.edge(Condition(type='all', conditions=[state('target'), state('ready')]), [1])
        dialog = ActionEditDialog(action=action)
        try:
            previous = copy.deepcopy(dialog._condition.conditions[1].to_dict())
            dialog._condition.conditions.pop()
            dialog._refresh_transition_targets([1], previous)
            with self.assertRaisesRegex(ValueError, '다시 선택'):
                dialog.get_action()
        finally:
            dialog.close()

    def test_disabled_if_can_be_saved_with_its_transition(self):
        action = self.edge(Condition(type='all', enabled=False, conditions=[state('ready')]), [0], enabled=False)
        dialog = ActionEditDialog(action=action)
        try:
            self.assertEqual(dialog.get_action().to_dict(), action.to_dict())
        finally:
            dialog.close()

    def test_adding_normal_branches_keeps_transition_last(self):
        action = self.edge()
        tree = ActionTreeWidget()
        try:
            tree.load_actions([action])
            item = tree.topLevelItem(0)
            tree._ensure_else_header(item, create_if_missing=True)
            tree._create_elif_header(item, state('other'))
            self.assertEqual(item.child(2).data(0, QtCore.Qt.ItemDataRole.UserRole), '__transition__')
        finally:
            tree.close()

    def test_parallel_actions_forbidden_inside_transition(self):
        action = self.edge(actions=[Action(type='group', parallel_enabled=True)])
        with self.assertRaisesRegex(ValueError, '최상위'):
            Action.validate_parallel_actions([action])

    def test_macro_call_inside_transition_can_monitor_its_own_if(self):
        child_if = self.edge(actions=[Action(type='press', key='child')])
        child_if.condition = state('child_ready')
        child_if.actions = [assign('child_ready', 0), Action(type='press', key='x')]
        nested = Macro(name='child', trigger_key='q', actions=[child_if], cycle_count=1)
        parent = self.edge(actions=[Action(type='macro_cycle', macro_target='child')])
        runner, engine = self.runner([parent], ready=1, child_ready=1)
        engine._resolve_macro_reference = Mock(return_value=(1, nested))
        engine._macro_display_name = Mock(return_value='child')
        engine._macro_identifier = Mock(return_value='child-id')
        runner._exec_action(parent, {}, [], [0])
        runner._vars.var['ready'] = '0'
        with patch('engine.time.perf_counter', side_effect=itertools.count(0, 0.1)):
            self.poll(runner)
        self.assertEqual(self.keys(engine), ['child', 'x'])
        self.assertIs(runner.macro, runner._root_macro)
        self.assertFalse(runner._if_transitions)

    def test_macro_editor_adds_child_to_transition_and_keeps_history(self):
        action = self.edge(actions=[])
        editor = MacroDialog(macro=Macro(trigger_key='z', actions=[action]))
        editor.show()
        for _ in range(3):
            APP.processEvents()
        try:
            tree = editor.main_action_tree
            item = tree.topLevelItem(0)
            tree.setCurrentItem(item.child(0))
            dialog = Mock()
            dialog.get_action.return_value = Action(type='macro_stop')
            with patch('main.ActionEditDialog', return_value=dialog), patch('main._run_dialog_non_modal', return_value=True):
                editor._add_action(as_child=True, tree=tree)
            saved = tree.collect_actions()[0]
            self.assertEqual(saved.transition_actions[0].type, 'macro_stop')
            self.assertFalse(saved.actions)
            editor.action_history.flush()
            editor.action_history.undo()
            self.assertFalse(tree.collect_actions()[0].transition_actions)
            editor.action_history.redo()
            self.assertEqual(tree.collect_actions()[0].transition_actions[0].type, 'macro_stop')
            # A full tree copy retains the independent transition action list.
            duplicate = copy.deepcopy(saved)
            duplicate.transition_actions[0].name = 'copy'
            self.assertIsNone(saved.transition_actions[0].name)
        finally:
            editor.close()
            editor.deleteLater()
            for _ in range(3):
                APP.processEvents()

    def test_every_group_mode_checks_before_the_next_input(self):
        for mode in ('all', 'first_true', 'first_true_continue', 'first_true_return', 'repeat_n', 'while'):
            with self.subTest(mode=mode):
                edge = self.edge(actions=[Action(type='macro_stop')])
                group = Action(type='group', group_mode=mode, group_repeat=2, actions=[
                    assign('ready', 0), Action(type='press', key='bad')])
                actions = [edge, group, Action(type='noop')]
                runner, engine = self.runner(actions, ready=1)
                with patch('engine.time.perf_counter', side_effect=itertools.count(0, 0.1)):
                    runner._run_actions(actions, {})
                self.assertEqual(self.keys(engine), [])
                self.assertTrue(runner._stop_event.is_set())

    def test_group_transition_goto_routes_without_running_remaining_children(self):
        edge = self.edge(actions=[Action(type='goto', goto_label='end')])
        actions = [edge, Action(type='group', group_mode='all', actions=[
            assign('ready', 0), Action(type='press', key='bad')]),
            Action(type='label', label='end'), Action(type='press', key='y')]
        runner, engine = self.runner(actions, ready=1)
        with patch('engine.time.perf_counter', side_effect=itertools.count(0, 0.1)):
            runner._run_actions(actions, runner._label_index(actions), root=True)
        self.assertEqual(self.keys(engine), ['y'])

    def poll_at(self, runner, seconds):
        with patch('engine.time.perf_counter', return_value=seconds):
            return self.poll(runner)

    def test_count_confirmation_requires_consecutive_false_samples(self):
        action = self.edge(transition_confirm_mode='count', transition_confirm_count=3)
        runner, engine = self.runner([action], ready=1)
        runner._exec_action(action, {}, [], [0])
        runner._vars.var['ready'] = '0'
        self.poll_at(runner, 0)
        self.poll_at(runner, .02)
        self.assertEqual(self.keys(engine), [])
        runner._vars.var['ready'] = '1'
        self.poll_at(runner, .04)
        runner._vars.var['ready'] = '0'
        for instant in (.06, .08):
            self.poll_at(runner, instant)
        self.assertEqual(self.keys(engine), [])
        self.poll_at(runner, .10)
        self.poll_at(runner, .12)
        self.assertEqual(self.keys(engine), ['z'])

    def test_duration_confirmation_uses_elapsed_time_and_resets_on_true(self):
        action = self.edge(transition_confirm_mode='duration', transition_confirm_ms=50)
        runner, engine = self.runner([action], ready=1)
        runner._exec_action(action, {}, [], [0])
        runner._vars.var['ready'] = '0'
        self.poll_at(runner, 0)
        self.poll_at(runner, .049)
        self.assertEqual(self.keys(engine), [])
        runner._vars.var['ready'] = '1'
        self.poll_at(runner, .050)
        runner._vars.var['ready'] = '0'
        self.poll_at(runner, .060)
        self.poll_at(runner, .109)
        self.assertEqual(self.keys(engine), [])
        self.poll_at(runner, .110)
        self.assertEqual(self.keys(engine), ['z'])

    def test_unavailable_sample_breaks_count_and_duration_confirmation(self):
        for mode in ('count', 'duration'):
            with self.subTest(mode=mode):
                action = self.edge(transition_confirm_mode=mode, transition_confirm_count=2, transition_confirm_ms=50)
                runner, engine = self.runner([action], ready=1)
                runner._exec_action(action, {}, [], [0])
                with patch.object(runner, '_transition_value', side_effect=[False, None, False, False]):
                    self.poll_at(runner, 0)
                    self.poll_at(runner, .1)
                    self.poll_at(runner, .2)
                    self.assertEqual(self.keys(engine), [])
                    self.poll_at(runner, .251)
                self.assertEqual(self.keys(engine), ['z'])

    def test_confirmation_controls_and_validation_roundtrip(self):
        for mode in ('immediate', 'count', 'duration'):
            action = self.edge(transition_confirm_mode=mode, transition_confirm_count=4, transition_confirm_ms=125)
            dialog = ActionEditDialog(action=Action.from_dict(action.to_dict()))
            try:
                self.assertEqual(dialog.get_action().to_dict(), action.to_dict())
                self.assertEqual(dialog.transition_count_spin.isHidden(), mode != 'count')
                self.assertEqual(dialog.transition_ms_spin.isHidden(), mode != 'duration')
            finally:
                dialog.close()
        for field, value in (('transition_confirm_mode', 'bad'), ('transition_confirm_count', 0),
                             ('transition_confirm_ms', -1), ('transition_confirm_ms', True)):
            data = self.edge().to_dict()
            data[field] = value
            with self.assertRaises(ValueError):
                Action.from_dict(data)

    def test_local_reorder_preserves_selected_criterion_and_updates_editor_path(self):
        action = self.edge(Condition(type='all', conditions=[state('ready'), state('distance')]), [0])
        original_key = action.transition_target_key
        action.condition.conditions.reverse()
        dialog = ActionEditDialog(action=action)
        try:
            self.assertEqual(dialog.transition_target_combo.currentData(), [1])
            saved = dialog.get_action()
            self.assertEqual(saved.transition_target_key, original_key)
            self.assertEqual(saved.transition_target, [1])
        finally:
            dialog.close()
        runner, engine = self.runner([action], ready=1, distance=1)
        runner._exec_action(action, {}, [], [0])
        runner._vars.var['distance'] = '0'
        self.poll(runner)
        self.assertEqual(self.keys(engine), [])
        runner._vars.var['ready'] = '0'
        self.poll(runner)
        self.assertEqual(self.keys(engine), ['z'])

    def test_shared_reorder_and_replacement_do_not_retarget(self):
        entries = {'skill': {'name': '공용', 'condition': {'type': 'all', 'conditions': [state('ready').to_dict(), state('distance').to_dict()]}}}
        action = self.edge(Condition(type='all', shared_ref='skill'), [0])
        bind_target(action, entries)
        entries['skill']['condition']['conditions'].reverse()
        selected = target_condition(action.condition, action.transition_target, entries, identity=action.transition_target_key)
        self.assertEqual(selected.var_name, 'ready')
        entries['skill']['condition']['conditions'][1] = state('replacement').to_dict()
        with self.assertRaisesRegex(ValueError, '다시 선택'):
            target_condition(action.condition, action.transition_target, entries, identity=action.transition_target_key)

    def test_legacy_profile_binds_target_before_shared_edit(self):
        entries = {'skill': {'name': '공용', 'condition': {'type': 'all', 'conditions': [state('ready').to_dict(), state('distance').to_dict()]}}}
        action = self.edge(Condition(type='all', shared_ref='skill'), [0])
        data = dict(macros=[Macro(trigger_key='q', actions=[action]).to_dict()], shared_settings=entries)
        profile = MacroProfile.from_dict(data)
        saved = profile.macros[0].actions[0]
        self.assertTrue(saved.transition_target_key)
        profile.shared_settings['skill']['condition']['conditions'].reverse()
        self.assertEqual(target_condition(saved.condition, saved.transition_target, profile.shared_settings,
            identity=saved.transition_target_key).var_name, 'ready')

    def test_renames_preserve_identity_and_duplicate_criteria_require_reselection(self):
        leaf = state('ready')
        identity = condition_identity(leaf)
        leaf.name = '이름 변경'
        self.assertEqual(condition_identity(leaf), identity)
        action = self.edge(Condition(type='all', conditions=[leaf, copy.deepcopy(leaf)]), [0])
        with self.assertRaisesRegex(ValueError, '여러 개'):
            bind_target(action, {})

    def test_analysis_displays_target_and_live_transition_states(self):
        action = self.edge(Condition(type='all', conditions=[state('ready')]), [0],
                           transition_confirm_mode='count', transition_confirm_count=2)
        runner, engine = self.runner([action], ready=1)
        def measurement():
            macro = next(iter(engine.execution_analysis.snapshot()['macros'].values()))
            row = next(row for row in macro['rows'] if row['kind'] == 'transition')
            return macro, row, macro['counts'][row['path']]
        macro, row, counts = measurement()
        self.assertIn('감지 대기', row_explanation(row, macro))
        runner._exec_action(action, {}, [], [0])
        self.assertEqual(measurement()[2]['transition_state'], 'watching')
        runner._vars.var['ready'] = '0'
        self.poll(runner)
        macro, row, counts = measurement()
        self.assertEqual(counts['transition_state'], 'confirming')
        self.assertIn('1/2', row_explanation(row, macro))
        self.poll(runner)
        macro, row, counts = measurement()
        self.assertEqual(counts['transition_state'], 'completed')
        text, _, _ = selection_evidence(row, macro)
        self.assertIn('ready', text)
        self.assertIn('실행 완료', text)
        dialog = ExecutionAnalysisDialog(engine.execution_analysis)
        try:
            key = next(iter(engine.execution_analysis.snapshot()['macros']))
            self.assertIn('실행 완료', dialog._items[key, row['path']].text(5))
        finally:
            dialog.close()
            dialog.deleteLater()
            APP.processEvents()

    def test_missing_target_reports_state_without_repeating_error_logs(self):
        action = self.edge(Condition(type='all', conditions=[state('ready')]), [0])
        action.condition.conditions[0] = state('replacement')
        runner, engine = self.runner([action], replacement=1)
        for _ in range(4):
            runner._exec_action(action, {}, [], [0])
        self.assertFalse(runner._if_transitions)
        self.assertEqual(engine._emit_log.call_count, 1)
        macro = next(iter(engine.execution_analysis.snapshot()['macros'].values()))
        self.assertEqual(macro['counts'][(0, 'transition')]['transition_state'], 'target_error')

    def test_analysis_started_mid_watch_receives_current_state(self):
        action = self.edge()
        runner, engine = self.runner([action], ready=1)
        engine.execution_analysis.stop()
        runner._exec_action(action, {}, [], [0])
        engine.execution_analysis.start()
        self.poll(runner)
        macro = next(iter(engine.execution_analysis.snapshot()['macros'].values()))
        self.assertEqual(macro['counts'][(0, 'transition')]['transition_state'], 'watching')
