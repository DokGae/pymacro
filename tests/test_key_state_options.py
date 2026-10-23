import unittest
from unittest.mock import patch

from engine import Action
from main import ActionEditDialog
from test_execution_analysis import make_runner


class KeyStateOptionTests(unittest.TestCase):
    def run_actions(self, actions, pressed=()):
        runner, engine = make_runner(actions)
        with patch('engine.get_keystate', side_effect=lambda key, **_: key in pressed):
            runner._run_actions(actions, {})
        return runner, engine

    def test_duplicate_down_and_up_are_skipped(self):
        actions = [Action(type='down', key='a', skip_if_pressed=True, repeat=3),
                   Action(type='up', key='a', release_only_pressed=True, repeat=3)]
        runner, engine = self.run_actions(actions)
        self.assertEqual([(c.args[0], c.args[1]) for c in engine._send_key.call_args_list],
                         [('down', 'a'), ('up', 'a')])
        self.assertFalse(runner._held_keys)

    def test_held_modifier_is_preserved_by_press(self):
        _, engine = self.run_actions(
            [Action(type='press', key='ctrl+a', skip_if_pressed=True)], pressed={'ctrl'})
        engine._send_key.assert_called_once_with('press', 'a', hold_ms=0)

    def test_up_sends_only_pressed_component(self):
        _, engine = self.run_actions(
            [Action(type='up', key='ctrl+a', release_only_pressed=True)], pressed={'a'})
        engine._send_key.assert_called_once_with('up', 'a', hold_ms=0)

    def test_default_preserves_repeated_input(self):
        _, engine = self.run_actions([Action(type='down', key='a', repeat=3)], pressed={'a'})
        self.assertEqual(engine._send_key.call_count, 3)

    def test_options_survive_profile_and_editor(self):
        for typ, option in [('down', 'skip_if_pressed'), ('press', 'skip_if_pressed'),
                            ('up', 'release_only_pressed')]:
            action = Action(type=typ, key='a', **{option: True})
            restored = Action.from_dict(action.to_dict())
            dialog = ActionEditDialog(action=restored)
            try:
                self.assertTrue(getattr(dialog.get_action(), option))
            finally:
                dialog.close()
