import os
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")
from main import MacroWindow


class StateHarness:
    _load_state = MacroWindow._load_state
    _write_state = MacroWindow._write_state
    _append_log = MacroWindow._append_log


class AppStateTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.window = StateHarness()
        self.window._state_path = Path(self.directory.name) / "local" / "global_state.json"
        self.window._legacy_state_path = Path(self.directory.name) / "global_state.json"

    def test_empty_state_before_log_widget_uses_legacy(self):
        self.window._state_path.parent.mkdir()
        self.window._state_path.write_text("", encoding="utf-8")
        self.window._legacy_state_path.write_text('{"log_enabled": true}', encoding="utf-8")
        self.assertEqual(self.window._load_state(), {"log_enabled": True})
        self.assertEqual(len(self.window._pending_logs), 1)

    def test_invalid_state_without_fallback_uses_defaults(self):
        self.window._state_path.parent.mkdir()
        self.window._state_path.write_text("broken", encoding="utf-8")
        self.assertEqual(self.window._load_state(), {})

    def test_state_write_roundtrip(self):
        state = {"profile": "한글", "log_enabled": False}
        self.window._write_state(state)
        self.assertEqual(self.window._load_state(), state)
        self.assertEqual(list(self.window._state_path.parent.glob("*.tmp")), [])

    def test_failed_replace_preserves_existing_state(self):
        self.window._write_state({"previous": True})
        with patch.object(Path, "replace", side_effect=PermissionError("locked")):
            self.window._write_state({"new": True})
        self.assertEqual(json.loads(self.window._state_path.read_text(encoding="utf-8")), {"previous": True})
        self.assertEqual(list(self.window._state_path.parent.glob("*.tmp")), [])
        self.assertEqual(len(self.window._pending_logs), 1)


if __name__ == "__main__":
    unittest.main()
