import copy
import os
import threading
import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
from engine import Action, Macro, MacroEngine, MacroProfile
from main import MacroWindow


class MacroAutoApplyTests(unittest.TestCase):
    def test_confirm_updates_runtime_and_cancel_does_not(self):
        old = Macro(name='old', trigger_key='a', actions=[Action(type='press', key='a')])
        new = Macro(name='new', trigger_key='a', actions=[Action(type='press', key='b')])
        dialog = Mock()
        dialog.get_macro.return_value = new
        dialog.block_workspace.entries = {}
        owner = Mock()
        owner._loading_profile = False
        owner.profile.shared_blocks = {}
        owner._get_selected_row.return_value = 0
        owner._macro_from_row.return_value = old
        owner._run_macro_dialog.return_value = 1
        with patch('main.MacroDialog', return_value=dialog):
            MacroWindow._edit_macro(owner)
        owner._set_macro_row.assert_called_once_with(0, new)
        owner._sync_runtime_profile_from_macro_table.assert_called_once_with(preserve_running=True)
        owner._sync_runtime_profile_from_macro_table.reset_mock()
        owner._run_macro_dialog.return_value = 0
        with patch('main.MacroDialog', return_value=dialog):
            MacroWindow._edit_macro(owner)
        owner._sync_runtime_profile_from_macro_table.assert_not_called()

    def test_update_keeps_running_snapshot_and_installs_next_trigger_definition(self):
        old = Macro(trigger_key='a', actions=[Action(type='press', key='a')])
        profile = MacroProfile(macros=[copy.deepcopy(old)])
        runner = SimpleNamespace(macro=copy.deepcopy(old), stop=Mock())
        engine = Mock()
        engine._lock = threading.RLock()
        engine._profile = copy.deepcopy(profile)
        engine._macro_runners = {0: runner}
        engine.execution_analysis.enabled = False
        profile.macros[0].actions[0].key = 'b'
        with patch('engine.state_hub.connect_profile'):
            MacroEngine.update_profile(engine, profile, preserve_running=True)
        engine._stop_all_macros.assert_not_called()
        engine._reset_timers.assert_not_called()
        self.assertEqual(runner.macro.actions[0].key, 'a')
        self.assertEqual(engine._profile.macros[0].actions[0].key, 'b')
        with patch('engine.state_hub.connect_profile'):
            MacroEngine.update_profile(engine, profile)
        engine._stop_all_macros.assert_called_once()


if __name__ == '__main__':
    unittest.main()
