"""Parallel execution tests; fake input backend never sends real keys."""
import os
import threading
import time
import unittest
from types import SimpleNamespace

os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")

from engine import Action, Condition, Macro, MacroRunner, MacroVariables


class FakeEngine:
    tick = 0.005

    def __init__(self):
        self._profile = SimpleNamespace(variables=MacroVariables())
        self.events = []
        self.inputs = []
        self.logs = []
        self.condition = False
        self.condition_checks = 0

    def _emit_event(self, event):
        self.events.append((time.monotonic(), event))

    def _emit_log(self, message):
        self.logs.append(message)

    def _send_key(self, kind, key, **kwargs):
        self.inputs.append((kind, key))
        return True

    def _resolve_key_delays(self, action):
        return 0, 0

    def _evaluate_condition(self, condition, **kwargs):
        self.condition_checks += 1
        return self.condition


def background(actions, interval=0.03, **kwargs):
    return Action(type="group", group_mode="all", actions=actions,
                  parallel_enabled=True, parallel_interval_sec=interval, **kwargs)


class ParallelTests(unittest.TestCase):
    def setUp(self):
        self.engine = FakeEngine()
        self.runners = []

    def tearDown(self):
        for runner in self.runners:
            runner.stop(run_stop_actions=False)
            self.assertFalse(runner.is_alive())

    def start(self, actions, **kwargs):
        runner = MacroRunner(Macro(trigger_key="f10", actions=actions, **kwargs), self.engine)
        self.runners.append(runner)
        runner.start(reset_all_timers=False)
        return runner

    def wait_for(self, predicate, timeout=1.5):
        deadline = time.monotonic() + timeout
        while not predicate() and time.monotonic() < deadline:
            time.sleep(0.005)
        self.assertTrue(predicate(), self.engine.logs)

    def starts(self, name):
        return [(stamp, event) for stamp, event in self.engine.events
                if event.get("type") == "action_start" and event.get("action_name") == name]

    def test_serialization_and_legacy_defaults(self):
        action = background([Action(type="sleep", sleep_ms=20)], interval=0.25)
        loaded = Action.from_dict(action.to_dict())
        self.assertTrue(loaded.parallel_enabled)
        self.assertEqual(loaded.parallel_interval_sec, 0.25)
        self.assertFalse(Action.from_dict({"type": "group"}).parallel_enabled)
        for value in (0, -1, float("nan"), float("inf"), "oops"):
            with self.assertRaises(ValueError):
                Action.parse_parallel_interval(value)

    def test_invalid_positions_and_flags(self):
        for actions in ([Action(type="group", actions=[background([])])],
                        [Action(type="press", key="a", parallel_enabled=True)],
                        [background([], once_per_macro=True)]):
            with self.assertRaises(ValueError):
                Action.validate_parallel_actions(actions)
        with self.assertRaises(ValueError):
            Action.validate_parallel_actions([background([])], allow_parallel=False)

    def test_runs_during_main_sleep_without_duplicate_workers(self):
        runner = self.start([Action(type="sleep", sleep_ms=180),
                             background([Action(type="noop", name="poll")])])
        self.wait_for(lambda: len(self.starts("poll")) >= 4)
        self.assertEqual(runner.current_cycle(), 0)
        self.assertEqual(len(runner._parallel_snapshot()), 1)
        self.assertTrue(all(event["parallel"] for _, event in self.starts("poll")))
        self.wait_for(lambda: runner.current_cycle() >= 1)
        self.assertEqual(len(runner._parallel_snapshot()), 1)

    def test_overruns_do_not_overlap_or_catch_up(self):
        runner = self.start([background([Action(type="sleep", sleep_ms=75)], name="slow"),
                             Action(type="sleep", sleep_ms=1000)])
        self.wait_for(lambda: len(self.starts("slow")) >= 3)
        runner.stop()
        times = [stamp for stamp, _ in self.starts("slow")]
        self.assertTrue(all(b - a >= 0.075 for a, b in zip(times, times[1:])))

    def test_if_reevaluates_true_and_false_branches(self):
        condition = Action(type="if", parallel_enabled=True, parallel_interval_sec=0.025,
                           condition=Condition(type="key", key="a"),
                           actions=[Action(type="noop", name="yes")],
                           else_actions=[Action(type="noop", name="no")])
        self.start([condition, Action(type="sleep", sleep_ms=1000)])
        self.wait_for(lambda: len(self.starts("no")) >= 2)
        self.engine.condition = True
        self.wait_for(lambda: len(self.starts("yes")) >= 2)

    def test_stop_interrupts_sleep_and_releases_parallel_holds(self):
        runner = self.start([background([Action(type="down", key="a"),
                                         Action(type="sleep", sleep_ms=10000)]),
                             Action(type="sleep", sleep_ms=10000)],
                            stop_actions=[Action(type="press", key="b")])
        self.wait_for(lambda: ("down", "a") in self.engine.inputs)
        self.assertIn("a", runner.snapshot_held_inputs()[0])
        before = time.monotonic()
        runner.stop()
        self.assertLess(time.monotonic() - before, 0.5)
        self.assertIn(("up", "a"), self.engine.inputs)
        self.assertEqual(self.engine.inputs.count(("press", "b")), 1)
        count = len(self.engine.events)
        time.sleep(0.06)
        self.assertEqual(len(self.engine.events), count)

    def test_suspension_preserves_parallel_hold_policy(self):
        runner = self.start([background([Action(type="down", key="a", hold_keep_on_pause=True),
                                         Action(type="sleep", sleep_ms=10000)]),
                             Action(type="sleep", sleep_ms=10000)],
                            stop_actions=[Action(type="press", key="b")])
        self.wait_for(lambda: ("down", "a") in self.engine.inputs)
        self.assertTrue(runner.snapshot_held_inputs_with_policy()[0]["a"])
        runner.stop(release_inputs=False, run_stop_actions=False)
        self.assertNotIn(("up", "a"), self.engine.inputs)
        self.assertNotIn(("press", "b"), self.engine.inputs)
        self.assertIn("a", runner.snapshot_held_inputs()[0])

    def test_natural_completion_stops_background(self):
        runner = self.start([background([Action(type="noop", name="poll")]),
                             Action(type="sleep", sleep_ms=90)], cycle_count=1)
        self.wait_for(lambda: not runner.is_alive())
        self.assertGreaterEqual(len(self.starts("poll")), 2)
        self.assertEqual(runner.terminal_status(), "finished")
        self.assertEqual(runner._parallel_snapshot(), [])

    def test_parallel_return_only_finishes_that_worker(self):
        runner = self.start([background([Action(type="noop", name="once"), Action(type="return")]),
                             background([Action(type="noop", name="poll")]),
                             Action(type="sleep", sleep_ms=1000)])
        self.wait_for(lambda: len(self.starts("poll")) >= 3)
        self.assertEqual(len(self.starts("once")), 1)
        self.assertTrue(runner.is_alive())

    def test_macro_stop_from_background_stops_owner(self):
        runner = self.start([background([Action(type="sleep", sleep_ms=40), Action(type="macro_stop")]),
                             Action(type="sleep", sleep_ms=10000)],
                            stop_actions=[Action(type="press", key="b")])
        self.wait_for(lambda: not runner.is_alive())
        self.assertEqual(runner.terminal_status(), "macro_stop")
        self.assertEqual(self.engine.inputs.count(("press", "b")), 1)

    def test_disabled_background_is_not_started(self):
        runner = self.start([background([Action(type="noop", name="off")], enabled=False),
                             Action(type="sleep", sleep_ms=60)], cycle_count=1)
        self.wait_for(lambda: not runner.is_alive())
        self.assertEqual(self.starts("off"), [])

    def test_workers_share_variables_with_main(self):
        runner = self.start([background([Action(type="set_var", var_name="count", var_value="1", var_update_mode="add")]),
                             Action(type="sleep", sleep_ms=1000)])
        self.wait_for(lambda: int(runner._vars.var.get("count", "0")) >= 3)
        self.assertIs(runner._vars, runner._parallel_snapshot()[0]._vars)

    def test_nested_macro_parallel_workers_are_scoped_to_call(self):
        target = Macro(trigger_key="f11", name="target", actions=[
            background([Action(type="noop", name="nested_poll")]),
            Action(type="sleep", sleep_ms=100),
        ])
        self.engine._resolve_macro_reference = lambda *args, **kwargs: (1, target)
        self.engine._macro_display_name = lambda *args: "target"
        self.engine._macro_identifier = lambda *args: "target"
        runner = self.start([Action(type="macro_cycle", macro_target="target"),
                             Action(type="sleep", name="after", sleep_ms=1000)])
        self.wait_for(lambda: len(self.starts("after")) == 1)
        count = len(self.starts("nested_poll"))
        self.assertGreaterEqual(count, 2)
        self.assertEqual(runner._parallel_snapshot(), [])
        time.sleep(0.06)
        self.assertEqual(len(self.starts("nested_poll")), count)

    def test_background_local_goto_does_not_touch_main_labels(self):
        runner = self.start([background([
            Action(type="goto", goto_label="end"),
            Action(type="noop", name="skip"), Action(type="label", label="end"),
            Action(type="noop", name="local_end"),
        ]), Action(type="sleep", sleep_ms=1000)])
        self.wait_for(lambda: len(self.starts("local_end")) >= 2)
        self.assertEqual(self.starts("skip"), [])
        self.assertEqual(runner.current_cycle(), 0)

    def test_stop_during_nested_call_runs_stop_actions_once_in_order(self):
        target = Macro(trigger_key="f11", name="target", actions=[
            background([Action(type="noop", name="nested_poll")]),
            Action(type="sleep", sleep_ms=10000),
        ], stop_actions=[Action(type="press", key="b")])
        self.engine._resolve_macro_reference = lambda *args, **kwargs: (1, target)
        self.engine._macro_display_name = lambda *args: "target"
        self.engine._macro_identifier = lambda *args: "target"
        runner = self.start([Action(type="macro_cycle", macro_target="target")],
                            stop_actions=[Action(type="press", key="c")])
        self.wait_for(lambda: len(self.starts("nested_poll")) >= 2)
        runner.stop()
        self.assertEqual(self.engine.inputs, [("press", "b"), ("press", "c")])


class ParallelUiTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from PyQt6.QtWidgets import QApplication
        cls.app = QApplication.instance() or QApplication([])

    def test_editor_roundtrip_and_tree_badge(self):
        from main import ActionEditDialog, ActionTreeWidget
        dialog = ActionEditDialog(action=background([], interval=0.25, name="buff"))
        try:
            self.assertTrue(dialog.parallel_check.isChecked())
            self.assertTrue(dialog.parallel_interval_spin.isEnabled())
            self.assertFalse(dialog.once_check.isEnabled())
            result = dialog.get_action()
            tree = ActionTreeWidget()
            tree.load_actions([result])
            self.assertIn("병렬 · 0.25초마다", tree.topLevelItem(0).text(3))
            self.assertEqual(tree.collect_actions()[0].parallel_interval_sec, 0.25)
            dialog.parallel_check.setChecked(False)
            self.assertFalse(dialog.parallel_interval_spin.isEnabled())
            self.assertTrue(dialog.once_check.isEnabled())
            tree.deleteLater()
        finally:
            dialog.deleteLater()

    def test_nested_editor_disables_parallel(self):
        from main import ActionEditDialog
        dialog = ActionEditDialog(action=Action(type="group"), parallel_allowed=False)
        try:
            self.assertFalse(dialog.parallel_check.isEnabled())
            self.assertIn("최상위", dialog.parallel_hint.text())
        finally:
            dialog.deleteLater()


if __name__ == "__main__":
    unittest.main()
