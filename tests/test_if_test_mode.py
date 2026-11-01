"""IF tests exercise the real runner with fake input and headless Qt."""
import copy
import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch

from PyQt6 import QtWidgets
from engine import Action, Condition, Macro, MacroEngine, MacroProfile
from main import ActionEditDialog, MacroDialog
from if_test_runtime import IfTestState, locate, run_from_path
from if_test_ui import EditorTests, tree_paths
from test_execution_analysis import APP, make_runner, main_macro


def branch(key='x', **kwargs):
    return Action(type='if', condition=Condition(type='key', key='q'),
                  actions=[Action(type='press', key=key)], **kwargs)


class IfTestModeTests(unittest.TestCase):
    def runner(self, actions, outcomes=()):
        runner, engine = make_runner(actions, outcomes=outcomes)
        engine.if_test_state = IfTestState()
        return runner, engine

    def keys(self, engine):
        return [call.args[1] for call in engine._send_key.call_args_list]

    def test_once_only_consumed_when_if_reached_and_then_real_false(self):
        action = branch()
        runner, engine = self.runner([action], [False])
        state = engine.if_test_state
        state.set(0, False, (0,), action, 'once')
        self.assertEqual(state.mode(0, False, (0,)), 'once')
        runner._exec_action(action, {}, [], [0])
        runner._exec_action(action, {}, [], [0])
        self.assertEqual(self.keys(engine), ['x'])
        self.assertEqual(state.mode(0, False, (0,)), 'actual')
        counts = main_macro(engine.execution_analysis.snapshot())['counts'][(0,)]
        self.assertEqual((counts['true'], counts['false']), (1, 1))

    def test_always_does_not_evaluate_condition_or_force_nested_if(self):
        nested = branch('n')
        action = branch()
        action.actions.append(nested)
        runner, engine = self.runner([action], [False, False])
        engine.if_test_state.set(0, False, (0,), action, 'always')
        for _ in range(2):
            runner._exec_action(action, {}, [], [0])
        self.assertEqual(self.keys(engine), ['x', 'x'])
        self.assertEqual(engine.if_test_state.mode(0, False, (0,)), 'always')
        detail = main_macro(engine.execution_analysis.snapshot())['counts'][(0,)]['condition_detail']
        self.assertIn('강제 참', detail['reason'])

    def test_disabled_action_does_not_consume_once(self):
        action = branch(enabled=False)
        runner, engine = self.runner([action])
        engine.if_test_state.set(0, False, (0,), action, 'once')
        runner._exec_action(action, {}, [], [0])
        self.assertEqual(engine.if_test_state.mode(0, False, (0,)), 'once')
        self.assertEqual(self.keys(engine), [])

    def test_definition_and_macro_and_stop_scope_do_not_leak(self):
        action = branch()
        state = IfTestState()
        before = action.to_dict()
        state.set(0, False, (0,), action, 'always')
        self.assertEqual(before, action.to_dict())
        self.assertEqual(state.mode(1, False, (0,), action), 'actual')
        self.assertEqual(state.mode(0, True, (0,), action), 'actual')
        changed = copy.deepcopy(action)
        changed.condition.key = 'z'
        self.assertEqual(state.mode(0, False, (0,), changed), 'actual')

    def test_finish_clears_override_and_keeps_execution_history(self):
        action = branch()
        runner, engine = self.runner([action])
        engine.if_test_state.set(0, False, (0,), action, 'always')
        runner._run()
        self.assertEqual(self.keys(engine), ['x'])
        self.assertEqual(engine.if_test_state.mode(0, False, (0,)), 'actual')
        self.assertIn('실행 종료', engine.if_test_state.history(0)[-1])

    def test_start_nested_else_skips_ancestors_and_continues_cycle(self):
        target = branch()
        outer = branch('wrong', else_actions=[Action(type='press', key='before'), target,
                                              Action(type='press', key='after')])
        actions = [Action(type='press', key='prefix'), outer, Action(type='press', key='end')]
        runner, engine = self.runner(actions)
        engine.if_test_state.set(0, False, (1, 2), target, 'once')
        runner._test_start_path = (1, 2)
        runner._run()
        self.assertEqual(self.keys(engine), ['x', 'after', 'end'])

    def test_start_nested_goto_preserves_root_label_destinations(self):
        target = branch()
        target.actions = [Action(type='goto', goto_label='end')]
        outer = branch()
        outer.actions = [target, Action(type='press', key='wrong')]
        actions = [outer, Action(type='press', key='wrong'), Action(type='label', label='end'),
                   Action(type='press', key='end')]
        runner, engine = self.runner(actions, [True])
        runner._test_start_path = (0, 0)
        runner._run()
        self.assertEqual(self.keys(engine), ['end'])

    def test_entry_preserves_first_true_group_rule(self):
        target = branch()
        group = Action(type='group', group_mode='first_true', actions=[
            branch('before'), target, branch('wrong')])
        runner, engine = self.runner([group, Action(type='press', key='end')])
        engine.if_test_state.set(0, False, (0, 1), target, 'once')
        runner._test_start_path = (0, 1)
        runner._run()
        self.assertEqual(self.keys(engine), ['x', 'end'])

    def test_entry_only_skips_prefix_on_first_group_iteration(self):
        target = branch()
        group = Action(type='group', group_mode='repeat_n', group_repeat=2, actions=[
            Action(type='press', key='prefix'), target, Action(type='press', key='after')])
        runner, engine = self.runner([group], [False])
        engine.if_test_state.set(0, False, (0, 1), target, 'once')
        runner._test_start_path = (0, 1)
        runner._run()
        self.assertEqual(self.keys(engine), ['x', 'after', 'prefix', 'after'])

    def test_entry_preserves_break_from_while_group(self):
        target = branch()
        target.actions.append(Action(type='break'))
        group = Action(type='group', group_mode='while', actions=[target])
        runner, engine = self.runner([group, Action(type='press', key='end')])
        engine.if_test_state.set(0, False, (0, 0), target, 'once')
        runner._test_start_path = (0, 0)
        runner._run()
        self.assertEqual(self.keys(engine), ['x', 'end'])

    def test_always_keeps_whole_if_transition_true(self):
        action = branch(transition_enabled=True, transition_actions=[Action(type='press', key='bad')])
        runner, engine = self.runner([action])
        engine.if_test_state.set(0, False, (0,), action, 'always')
        runner._exec_action(action, {}, [], [0])
        runner._transition_poll_at = 0
        runner._poll_if_transitions({})
        self.assertEqual(self.keys(engine), ['x'])

    def test_profile_apply_keeps_matching_test_and_drops_changed_target(self):
        action = branch()
        state = IfTestState()
        state.set(0, False, (0,), action, 'once')
        profile = MacroProfile(macros=[Macro(trigger_key='f8', actions=[copy.deepcopy(action)])])
        state.reconcile(profile)
        self.assertEqual(state.mode(0, False, (0,)), 'once')
        profile.macros[0].actions[0].condition.key = 'changed'
        state.reconcile(profile)
        self.assertEqual(state.mode(0, False, (0,)), 'actual')

    def test_manual_entry_builds_one_cycle_runner_without_changing_profile(self):
        action = branch()
        _, engine = self.runner([action])
        macro = Macro(trigger_key='f8', cycle_count=0, actions=[action])
        engine._profile.macros = [copy.deepcopy(macro)]
        engine.running = engine.active = True
        engine.paused = False
        engine._macro_runners = {}
        engine._apply_macro_interaction = Mock()
        engine._manual_scope_bypass_indices = set()
        engine._once_latched_indices = set()
        engine._toggle_states = {}
        engine._emit_state = Mock()
        with patch('engine.MacroRunner.start') as start:
            ok, status = MacroEngine.run_macro_from_if_manual(engine, 0, macro, (0,), test_mode='once')
        self.assertTrue(ok, status)
        start.assert_called_once()
        runner = engine._macro_runners[0]
        self.assertEqual(runner._test_start_path, (0,))
        self.assertEqual(runner.macro.cycle_count, 1)
        self.assertEqual(engine._profile.macros[0].cycle_count, 0)
        self.assertEqual(engine.if_test_state.mode(0, False, (0,), runner.macro.actions[0]), 'once')
        self.assertIn(0, engine._once_latched_indices)

    def test_manual_entry_rejects_active_runner_without_replacing_override(self):
        action = branch()
        _, engine = self.runner([action])
        engine.running = engine.active = True
        engine.paused = False
        engine._profile.macros = [Macro(trigger_key='f8', actions=[action])]
        engine._macro_runners = {0: SimpleNamespace(is_alive=lambda: True)}
        engine.if_test_state.set(0, False, (0,), action, 'always')
        result = MacroEngine.run_macro_from_if_manual(engine, 0, engine._profile.macros[0], (0,), test_mode='once')
        self.assertEqual(result, (False, 'already_running'))
        self.assertEqual(engine.if_test_state.mode(0, False, (0,)), 'always')


class IfTestGuiTests(unittest.TestCase):
    def setUp(self):
        self.editor = MacroDialog(macro=Macro(trigger_key='f8', actions=[branch(name='암영보')]))
        self.editor._block_macro_row = 0
        self.engine = SimpleNamespace(if_test_state=IfTestState(), _macro_runners={},
                                      run_macro_from_if_manual=Mock(return_value=(True, 'started')))
        self.session = EditorTests(self.editor, self.engine)
        self.item = self.editor.main_action_tree.topLevelItem(0)
        self.dialog = ActionEditDialog(self.editor, action=self.editor.main_action_tree._action_from_item(self.item))
        self.session.bind(self.dialog, self.item, self.editor.main_action_tree)

    def tearDown(self):
        self.dialog.reject()
        self.editor.close()
        APP.processEvents()
        self.editor.deleteLater()

    def test_mode_badge_and_auto_reset_do_not_change_saved_definition(self):
        before = self.editor.get_macro().to_dict()
        self.dialog.if_test_combo.setCurrentIndex(1)
        self.assertEqual(self.engine.if_test_state.mode(0, False, (0,)), 'once')
        self.assertIn('1회 강제 참', self.item.text(3))
        self.assertEqual(before, self.editor.get_macro().to_dict())
        self.engine.if_test_state.mode(0, False, (0,), consume=True)
        self.session.refresh()
        self.assertEqual(self.dialog.if_test_combo.currentData(), 'actual')
        self.assertNotIn('강제 참', self.item.text(3))

    def test_start_uses_current_draft_and_correct_path(self):
        self.dialog.name_edit.setText('draft')
        self.dialog.if_test_combo.setCurrentIndex(2)
        self.dialog.if_test_start.click()
        args = self.engine.run_macro_from_if_manual.call_args.args
        self.assertEqual(args[0], 0)
        self.assertEqual(args[1].actions[0].name, 'draft')
        self.assertEqual(args[2], (0,))
        self.assertEqual(self.editor.get_macro().actions[0].name, '암영보')

    def test_failure_message_survives_refresh(self):
        self.engine.run_macro_from_if_manual.return_value = (False, 'engine_not_running')
        self.dialog.if_test_start.click()
        self.session.refresh()
        self.assertIn('엔진을 시작', self.dialog.if_test_status.text())

    def test_stop_clears_pending_override(self):
        self.dialog.if_test_combo.setCurrentIndex(2)
        self.dialog.if_test_stop.click()
        self.assertEqual(self.dialog.if_test_combo.currentData(), 'actual')

    def test_tree_paths_match_elif_else_and_transition_offsets(self):
        action = branch(elif_blocks=[(Condition(type='key', key='e'), [branch('e')], '')],
                        else_actions=[branch('s')], transition_actions=[branch('t')], transition_enabled=True)
        self.editor.main_action_tree.load_actions([action])
        macro = self.editor.get_macro()
        for path, item in tree_paths(self.editor.main_action_tree):
            actions, index, _ = locate(macro.actions, path)
            self.assertEqual(actions[index].type, item.data(0, 256).type)
            self.assertEqual(actions[index].key, item.data(0, 256).key)


if __name__ == '__main__':
    unittest.main()
