import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch
from PyQt6 import QtWidgets
from engine import KeySwallower, KeyState, Macro, MacroTrigger, MacroEngine, to_scan_code
from main import MacroDialog

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

class TriggerModifierTests(unittest.TestCase):
    def test_profile_and_editor_preserve_per_trigger_exclusions(self):
        macro = Macro(trigger_key='`', name='test', triggers=[
            MacroTrigger(key='`', mode='once', excluded_modifiers=['ctrl']),
            MacroTrigger(key='f2', mode='hold', excluded_modifiers=['alt', 'shift'])])
        restored = Macro.from_dict(macro.to_dict())
        dialog = MacroDialog(macro=restored)
        self.addCleanup(dialog.close)
        self.assertTrue(dialog.trigger_excluded_checks['ctrl'].isChecked())
        self.assertEqual(dialog.get_macro().triggers[0].excluded_modifiers, ['ctrl'])
        dialog.trigger_excluded_checks['shift'].setChecked(True)
        dialog._add_or_update_trigger(require_selection=True)
        self.assertEqual(dialog._collect_triggers()[0].excluded_modifiers, ['ctrl', 'shift'])
        dialog.trigger_table.selectRow(1)
        dialog._on_trigger_selection_changed()
        self.assertTrue(dialog.trigger_excluded_checks['alt'].isChecked())
        self.assertFalse(dialog.trigger_excluded_checks['ctrl'].isChecked())

    def test_ctrl_combo_is_forwarded_but_bare_key_is_swallowed(self):
        inter = Mock()
        swallower = KeySwallower(inter)
        swallower.set_triggers([{'key': '`', 'excluded_modifiers': ['ctrl']}])
        swallower.set_enabled(True)
        events = []
        for key, state in [('ctrl', KeyState.Down), ('`', KeyState.Down), ('`', KeyState.Up),
                           ('ctrl', KeyState.Up), ('`', KeyState.Down), ('`', KeyState.Up)]:
            events.append(SimpleNamespace(is_keyboard=True, is_mouse=False,
                stroke=SimpleNamespace(code=to_scan_code(key), state=state), send=Mock()))
        pending = iter(events)
        def receive(_):
            event = next(pending, None)
            if event is None:
                swallower._stop.set()
            return event
        inter.wait_receive.side_effect = receive
        with patch('engine.get_keystate', return_value=False):
            swallower._run()
        self.assertEqual([event.send.call_count for event in events], [1, 1, 1, 1, 0, 0])

    def test_ctrl_held_before_filter_starts_and_right_shift(self):
        swallower = KeySwallower(Mock())
        swallower.set_triggers([{'key': '`', 'excluded_modifiers': ['ctrl', 'shift']}])
        required, forbidden = swallower._key_modifiers[to_scan_code('`')][0]
        with patch('engine.get_keystate', side_effect=lambda key, **_: key == 'ctrl'):
            self.assertFalse(swallower._matches_modifier_rule(required, forbidden))
        swallower._pressed_keys.add(to_scan_code('rshift'))
        with patch('engine.get_keystate', return_value=False):
            self.assertFalse(swallower._matches_modifier_rule(required, forbidden))

    def test_ctrl_combo_cannot_start_trigger(self):
        fake = SimpleNamespace(_hotkey_states={}, _key_state_detail=lambda key: (key in {'ctrl', '`'}, {}))
        fake._trigger_state = lambda key, **kw: MacroEngine._trigger_state(fake, key, **kw)
        self.assertFalse(MacroEngine._edge(fake, '`', disallow_extra_modifiers=True))
        fake._key_state_detail = lambda key: (key == '`', {})
        self.assertTrue(MacroEngine._edge(fake, '`', disallow_extra_modifiers=True))

    def test_default_and_required_modifiers_remain_compatible(self):
        swallower = KeySwallower(Mock())
        swallower.set_triggers(['`', 'ctrl+f2'])
        self.assertEqual(MacroTrigger.from_any('`').excluded_modifiers, [])
        self.assertEqual(MacroTrigger.from_any(MacroTrigger('ctrl+f2', excluded_modifiers=['ctrl', 'alt'])).excluded_modifiers, ['alt'])
        with patch('engine.get_keystate', return_value=False):
            bare = swallower._key_modifiers[to_scan_code('`')][0]
            combo = swallower._key_modifiers[to_scan_code('f2')][0]
            self.assertTrue(swallower._matches_modifier_rule(*bare))
            self.assertFalse(swallower._matches_modifier_rule(*combo))
            swallower._pressed_keys.add(to_scan_code('ctrl'))
            self.assertTrue(swallower._matches_modifier_rule(*combo))

if __name__ == '__main__':
    unittest.main()
