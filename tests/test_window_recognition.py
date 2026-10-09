import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch, Mock

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import numpy as np
from PyQt6 import QtCore, QtGui, QtWidgets
from PIL import Image
from engine import Condition, MacroEngine
from capture import ScreenCaptureManager
from main import ConditionNodeDialog, ImageViewerDialog, ScreenshotDialog, WindowPickerDialog, DebuggerDialog
from lib import windows

TARGET = {'process_name': 'game.exe', 'process_path': 'C:\\game.exe', 'class_name': 'Game', 'title': 'Game', 'client_size': [800, 600]}

class WindowRecognitionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.app = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

    def engine(self):
        engine = MacroEngine.__new__(MacroEngine)
        engine._debug_image_override = None
        return engine

    def test_condition_roundtrip_and_legacy(self):
        cond = Condition(type='pixel', region=(10, 20, 1, 1), color=(1, 2, 3), window_target=TARGET)
        self.assertEqual(Condition.from_dict(cond.to_dict()).window_target, TARGET)
        self.assertIsNone(Condition.from_dict({'type': 'pixel'}).window_target)

    def test_capture_tracks_movement_and_cache(self):
        engine = self.engine()
        frame = np.full((1, 1, 3), [1, 2, 3], dtype=np.uint8)
        with patch('engine.target_client_region', side_effect=[(110, 220, 1, 1), (310, 420, 1, 1)]), patch('engine.capture_region_np', return_value=frame) as grab:
            cache = {}
            for _ in range(2):
                result = engine._pixel_check((10, 20, 1, 1), (1, 2, 3), 0, window_target=TARGET, pixel_cache=cache)
                self.assertTrue(result['result'])
                self.assertEqual(result['coord'], (10, 20))
            self.assertEqual([call.args[0] for call in grab.call_args_list], [(110, 220, 1, 1), (310, 420, 1, 1)])

    def test_unavailable_never_means_absent(self):
        with patch('engine.target_client_region', side_effect=RuntimeError('최소화')), patch('engine.capture_region_np') as grab:
            result = self.engine()._pixel_check((0, 0, 1, 1), (0, 0, 0), 0, expect_exists=False, window_target=TARGET)
            self.assertFalse(result['result'])
            self.assertTrue(result['unavailable'])
            grab.assert_not_called()

    def test_offline_debug_uses_client_pixels(self):
        engine = self.engine()
        engine._debug_image_override = np.zeros((2, 2, 3), dtype=np.uint8)
        with patch('engine.target_client_region') as resolve:
            self.assertTrue(engine._pixel_check((0, 0, 1, 1), (0, 0, 0), 0, window_target=TARGET)['result'])
            resolve.assert_not_called()

    def test_viewer_f1_range_binding_and_screen_reset(self):
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / '1.png'
            Image.new('RGB', (4, 4)).save(path)
            ScreenCaptureManager._write_metadata(path, {'window_target': TARGET})
            node = ConditionNodeDialog(cond=Condition(type='pixel', region=(0, 0, 1, 1), color=(0, 0, 0)))
            node.show()
            viewer = ImageViewerDialog(start_dir=Path(root))
            viewer._select_index(0)
            viewer._last_sample = {'pos': (1, 2), 'hex': '000000'}
            # F2 alone must also select the screenshot's source window.
            viewer.keyPressEvent(QtGui.QKeyEvent(
                QtCore.QEvent.Type.KeyPress, QtCore.Qt.Key.Key_F2,
                QtCore.Qt.KeyboardModifier.NoModifier,
            ))
            self.assertEqual(node.get_condition().window_target, TARGET)
            self.assertIn('창 내부', node.capture_target_btn.text())
            node.set_capture_target(None)
            viewer.keyPressEvent(QtGui.QKeyEvent(
                QtCore.QEvent.Type.KeyPress, QtCore.Qt.Key.Key_F1,
                QtCore.Qt.KeyboardModifier.NoModifier,
            ))
            self.assertEqual(node.get_condition().window_target, TARGET)
            self.assertEqual(node.get_condition().region, (1, 2, 1, 1))
            viewer._on_region_selected((0, 0, 3, 3))
            self.assertEqual(node.get_condition().region, (0, 0, 3, 3))
            viewer._copy_color()
            self.assertEqual(node.color_edit.text(), '000000')
            viewer._capture_metadata = {'screen_origin': [-100, 0]}
            viewer.keyPressEvent(QtGui.QKeyEvent(
                QtCore.QEvent.Type.KeyPress, QtCore.Qt.Key.Key_F2,
                QtCore.Qt.KeyboardModifier.NoModifier,
            ))
            self.assertIsNone(node.get_condition().window_target)
            self.assertEqual(node.capture_target_btn.text(), '전체 화면')
            viewer._on_region_selected((0, 0, 3, 3))
            self.assertIsNone(node.get_condition().window_target)
            self.assertEqual(node.get_condition().region, (-100, 0, 3, 3))
            viewer.close()
            node.close()

    def test_manager_captures_client_and_persists_source(self):
        with tempfile.TemporaryDirectory() as root:
            manager = ScreenCaptureManager(output_dir=root, image_format='png')
            manager.window_target = {k: v for k, v in TARGET.items() if k != 'client_size'}
            sct = Mock()
            sct.grab.return_value = Mock(rgb=bytes(12), size=(2, 2))
            with patch('capture.mss.mss') as factory, patch('capture.target_client_region', return_value=(100, 200, 2, 2)):
                factory.return_value.__enter__.return_value = sct
                path = manager.capture_once()
            sct.grab.assert_called_once_with({'left': 100, 'top': 200, 'width': 2, 'height': 2})
            import json
            metadata = json.loads(path.with_suffix('.png.json').read_text(encoding='utf-8'))
            self.assertEqual(metadata['window_target']['client_size'], [2, 2])
            self.assertTrue(path.exists())

    def test_selector_rejects_ambiguous_and_minimized_windows(self):
        info = dict(TARGET, hwnd=123)
        with patch.object(windows, 'list_windows', return_value=[info, info]):
            with self.assertRaisesRegex(RuntimeError, '여러'):
                windows.target_client_region(TARGET)

    def test_native_client_origin_resize_and_bounds(self):
        api = Mock()
        def rect(hwnd, out):
            out._obj.right, out._obj.bottom = 800, 600
            return True
        def origin(hwnd, out):
            out._obj.x, out._obj.y = 100, 200
            return True
        api.GetClientRect.side_effect = rect
        api.ClientToScreen.side_effect = origin
        api.GetSystemMetrics.side_effect = lambda metric: {76: 0, 77: 0, 78: 1920, 79: 1080}[metric]
        info = dict(TARGET, hwnd=123)
        with patch.object(windows, 'user32', api), patch.object(windows, 'list_windows', return_value=[info]), patch.object(windows, 'IsIconic', return_value=False):
            self.assertEqual(windows.target_client_region(TARGET, (10, 20, 30, 40)), (110, 220, 30, 40))
            with self.assertRaisesRegex(RuntimeError, '크기가'):
                windows.target_client_region(dict(TARGET, client_size=[1024, 768]))
            with self.assertRaisesRegex(RuntimeError, '내부'):
                windows.target_client_region(TARGET, (790, 0, 20, 10))
            with self.assertRaisesRegex(RuntimeError, '프로그램'):
                windows.target_client_region({})
        with patch.object(windows, 'list_windows', return_value=[info]), patch.object(windows, 'IsIconic', return_value=True):
            with self.assertRaisesRegex(RuntimeError, '최소화'):
                windows.target_client_region(TARGET)

    def test_screenshot_dialog_remembers_target(self):
        manager = ScreenCaptureManager()
        manager.window_target = TARGET
        dialog = ScreenshotDialog(manager)
        self.assertIn('game.exe', dialog.target_btn.text())
        self.assertEqual(dialog._collect_state()['window_target'], TARGET)
        dialog.close()

    def test_picker_external_click_accepts_without_list_lookup(self):
        info = dict(TARGET, hwnd=123, pid=42)
        with patch('main.list_windows', return_value=[]), patch('main.get_keystate', return_value=False):
            dialog = WindowPickerDialog()
            dialog.show()
        with patch('main.get_keystate', return_value=True), patch('main.window_under_cursor', return_value=info):
            dialog._poll_window_click()
        self.assertEqual(dialog.result(), QtWidgets.QDialog.DialogCode.Accepted)
        self.assertEqual(dialog.selected_window(), info)
        self.assertFalse(dialog._click_timer.isActive())

    def test_debug_tree_displays_capture_target_column(self):
        dialog = DebuggerDialog()
        self.assertEqual(dialog.condition_tree.headerItem().text(3), '인식 대상')
        for target, expected in ((None, '전체 화면'), (TARGET, '창 내부 · game.exe')):
            cond = Condition(type='pixel', region=(0, 0, 1, 1), color=(0, 0, 0), window_target=target)
            item = dialog._build_condition_item({'cond': cond, 'type': 'pixel', 'result': False, 'detail': {}})
            self.assertEqual(item.text(3), expected)
            if target:
                self.assertIn(TARGET['title'], item.toolTip(3))
        item = dialog._build_condition_item({'type': 'pixel', 'result': False, 'detail': {'pixel': {'window_target': TARGET}}})
        self.assertEqual(item.text(3), '창 내부 · game.exe')
        item = dialog._build_condition_item({'cond': Condition(type='timer'), 'type': 'timer', 'result': False, 'detail': {}})
        self.assertEqual(item.text(3), '')
        dialog.close()

    def test_picker_ignores_own_window_and_already_held_click(self):
        with patch('main.list_windows', return_value=[]), patch('main.get_keystate', return_value=True):
            dialog = WindowPickerDialog()
            dialog.show()
            with patch('main.window_under_cursor') as under:
                dialog._poll_window_click()
                under.assert_not_called()
        with patch('main.get_keystate', return_value=False):
            dialog._poll_window_click()
        with patch('main.get_keystate', return_value=True), patch('main.window_under_cursor', return_value=None):
            dialog._poll_window_click()
        self.assertIsNone(dialog.selected_window())
        self.assertTrue(dialog.isVisible())
        dialog.reject()
        self.assertFalse(dialog._click_timer.isActive())

if __name__ == '__main__':
    unittest.main()
