import json
import tempfile
import unittest
from pathlib import Path

from engine import MacroProfile, KeyDelayConfig
from input_device_settings import FIELDS, InputDeviceSettings, portable_profile


class LocalInputTests(unittest.TestCase):
    def test_migrate_once_then_other_macro_cannot_replace_devices(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            old = MacroProfile(keyboard_device_id=3, keyboard_hardware_id='this-keyboard',
                               mouse_device_id=12, mouse_hardware_id='this-mouse', input_mode='hardware',
                               keyboard_test_key='f8', key_delay=KeyDelayConfig(press_delay_ms=25))
            legacy = base / 'macro.json'
            legacy.write_text(json.dumps(old.to_dict()), encoding='utf-8')
            local = InputDeviceSettings(base / 'input_devices' / 'settings.json')
            profile = MacroProfile()
            local.initialize(profile, legacy)
            self.assertEqual(profile.keyboard_device_id, 3)
            self.assertEqual(profile.mouse_device_id, 12)
            self.assertEqual(profile.key_delay.press_delay_ms, 25)
            foreign = MacroProfile(keyboard_device_id=8, mouse_device_id=19)
            legacy.write_text(json.dumps(foreign.to_dict()), encoding='utf-8')
            restored = InputDeviceSettings(local.path)
            restored.initialize(foreign, legacy)
            self.assertEqual(foreign.keyboard_device_id, 3)
            self.assertEqual(foreign.mouse_hardware_id, 'this-mouse')
            self.assertEqual(foreign.keyboard_test_key, 'f8')

    def test_save_settings_and_portable_export(self):
        with tempfile.TemporaryDirectory() as folder:
            local = InputDeviceSettings(Path(folder) / 'settings.json')
            profile = MacroProfile(input_mode='software', keyboard_device_id=4, mouse_device_id=13)
            local.save(profile)
            portable = portable_profile(profile)
            self.assertTrue(set(FIELDS).isdisjoint(portable))
            self.assertEqual(profile.keyboard_device_id, 4)
            new_profile = MacroProfile.from_dict(portable)
            local.initialize(new_profile)
            self.assertEqual(new_profile.input_mode, 'software')
            self.assertEqual(new_profile.keyboard_device_id, 4)
            self.assertEqual(new_profile.mouse_device_id, 13)
            self.assertEqual(set(json.loads(local.path.read_text(encoding='utf-8'))), set(FIELDS))
