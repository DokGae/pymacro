"""Cycle regression tests; no real keyboard input is sent."""
import threading
import unittest

from engine import Action, Macro, MacroRunner
from test_parallel_actions import FakeEngine


class MacroCycleTests(unittest.TestCase):
    def test_toggle_repeats_without_goto_until_stopped(self):
        for limit in (None, 0):
            with self.subTest(cycle_count=limit):
                engine = FakeEngine()
                repeated = threading.Event()
                timer_calls = []
                engine._set_timer = lambda *args: timer_calls.append(args)
                send_key = engine._send_key

                def record_input(*args, **kwargs):
                    result = send_key(*args, **kwargs)
                    if len(engine.inputs) >= 4:
                        repeated.set()
                    return result

                engine._send_key = record_input
                runner = MacroRunner(Macro(
                    trigger_key="ctrl+\\", mode="toggle", cycle_count=limit,
                    actions=[
                        Action(type="timer", timer_index=1, timer_value=10,
                               once_per_macro=True),
                        Action(type="label", label="first"),
                        Action(type="press", key="]"),
                        Action(type="return", enabled=False),
                    ],
                ), engine)
                try:
                    runner.start(reset_all_timers=False)
                    self.assertTrue(repeated.wait(2), engine.logs)
                    self.assertTrue(runner.is_alive())
                    self.assertGreaterEqual(runner.current_cycle(), 3)
                    self.assertEqual(timer_calls, [(1, 10.0)])
                finally:
                    runner.stop(run_stop_actions=False)
                self.assertFalse(runner.is_alive())
                self.assertEqual(runner.terminal_status(), "stopped")

    def test_finite_cycle_limit_and_explicit_return(self):
        for limit, tail, expected in (
            (1, [], 1),
            (3, [], 3),
            (None, [Action(type="return")], 1),
            (None, [Action(type="macro_stop")], 1),
        ):
            with self.subTest(limit=limit, tail=tail):
                engine = FakeEngine()
                runner = MacroRunner(Macro(
                    trigger_key="ctrl+\\", mode="toggle", cycle_count=limit,
                    actions=[Action(type="label", label="first"),
                             Action(type="press", key="]"), *tail],
                ), engine)
                try:
                    runner.start(reset_all_timers=False)
                    runner._thread.join(timeout=2)
                    self.assertFalse(runner.is_alive(), engine.logs)
                    self.assertEqual(engine.inputs, [("press", "]")] * expected)
                finally:
                    runner.stop(run_stop_actions=False)


if __name__ == "__main__":
    unittest.main()
