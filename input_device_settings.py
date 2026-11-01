"""PC-local keyboard settings, separate from portable macro definitions."""
import copy
import json
import os
import sys
import tempfile
from pathlib import Path

FIELDS = ('input_mode', 'keyboard_device_id', 'keyboard_hardware_id',
          'mouse_device_id', 'mouse_hardware_id', 'key_delay', 'mouse_delay', 'keyboard_test_key')


def portable_profile(profile):
    data = profile.to_dict()
    for field in FIELDS:
        data.pop(field, None)
    return data


class InputDeviceSettings:
    def __init__(self, path=None):
        base = Path(sys.executable).resolve().parent if getattr(sys, 'frozen', False) else Path(__file__).resolve().parent
        self.path = Path(path) if path is not None else base / 'setting' / 'input_devices' / 'settings.json'
        self.data = None

    def initialize(self, profile, legacy_path=None):
        if self.path.exists():
            data = json.loads(self.path.read_text(encoding='utf-8'))
            if not isinstance(data, dict):
                raise ValueError('입력장치 설정 파일 형식이 올바르지 않습니다.')
            self.data = data
        else:
            if legacy_path and Path(legacy_path).is_file():
                from engine import MacroProfile
                legacy = json.loads(Path(legacy_path).read_text(encoding='utf-8'))
                if isinstance(legacy, dict):
                    source = MacroProfile.from_dict(legacy)
                    self.save(source)
            if self.data is None:
                self.save(profile)
        self.apply(profile)

    def apply(self, profile):
        from engine import MacroProfile
        normalized = MacroProfile.from_dict(copy.deepcopy(self.data or {}))
        for field in FIELDS:
            setattr(profile, field, copy.deepcopy(getattr(normalized, field)))
        return profile

    def save(self, profile):
        values = profile.to_dict()
        data = {field: values[field] for field in FIELDS}
        self.path.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=self.path.parent,
                                             suffix='.tmp', delete=False) as stream:
                temporary = Path(stream.name)
                json.dump(data, stream, ensure_ascii=False, indent=2)
                stream.write('\n')
            os.replace(temporary, self.path)
            self.data = data
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()
