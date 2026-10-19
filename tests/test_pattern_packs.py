import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import numpy as np
from PyQt6 import QtCore, QtGui, QtWidgets
from engine import MacroEngine, Condition
from lib.pattern_packs import PackReference, load_packs, save_packs, resolve_pattern, pattern_label
from main import ImageViewerDialog, ConditionNodeDialog, PixelTestDialog
from pack_manager import PackManager


class PackTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.app = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'packs.json'
        patcher = patch('lib.pattern_packs.PACK_FILE', self.path)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.data = {'a': {'name': '숫자팩', 'items': {
            'one': {'name': '1', 'points': [{'dx': 10, 'dy': 20, 'color': [255, 0, 0]}]},
            'two': {'name': '2', 'points': [{'dx': 20, 'dy': 30, 'color': [0, 255, 0]}]},
        }}}
        save_packs(self.data)

    def check(self, frame, exists=True):
        engine = MacroEngine.__new__(MacroEngine)
        engine._debug_image_override = frame
        return engine._pixel_check((0, 0, 3, 3), None, 0, pattern=PackReference('pack:a'), expect_exists=exists)

    def test_any_member_and_none_semantics(self):
        frame = np.zeros((3, 3, 3), dtype=np.uint8)
        self.assertTrue(self.check(frame, False)['result'])
        self.assertFalse(self.check(frame)['result'])
        frame[1, 2] = [0, 255, 0]
        self.assertTrue(self.check(frame)['result'])
        self.assertEqual(self.check(frame)['matched_item'], '2')
        self.assertFalse(self.check(frame, False)['result'])

    def test_missing_and_empty_not_absent(self):
        for data in ({}, {'a': {'name': 'empty', 'items': {}}}):
            save_packs(data)
            result = self.check(np.zeros((3, 3, 3), dtype=np.uint8), False)
            self.assertFalse(result['result'])
            self.assertTrue(result['error'])

    def test_individual_item_does_not_match_other_members(self):
        engine = MacroEngine.__new__(MacroEngine)
        frame = np.zeros((3, 3, 3), dtype=np.uint8)
        frame[1, 1] = [0, 255, 0]
        engine._debug_image_override = frame
        for reference, expected in [('pack:a', True), ('pack:a/one', False), ('pack:a/two', True)]:
            result = engine._pixel_check((0, 0, 3, 3), None, 0, pattern=resolve_pattern({}, reference))
            self.assertEqual(result['result'], expected)
        self.assertEqual(pattern_label('pack:a/one'), '숫자팩 / 1')
        for reference in ('pack:a/deleted', 'old-pattern'):
            result = engine._pixel_check((0, 0, 3, 3), None, 0, expect_exists=False, pattern=resolve_pattern({}, reference))
            self.assertFalse(result['result'])
            self.assertTrue(result['error'])

    def test_old_condition_requires_reselection(self):
        dialog = ConditionNodeDialog(cond=Condition(type='pixel', region=(0, 0, 3, 3), pixel_pattern='old-pattern'))
        try:
            self.assertEqual(dialog.pattern_combo.currentData(), 'old-pattern')
            self.assertTrue(dialog.color_wrap.isHidden())
            with self.assertRaisesRegex(ValueError, '다시 선택'):
                dialog.get_condition()
            self.assertEqual(dialog.pattern_combo.findData('pack:a/one') >= 0, True)
            self.assertFalse(any(button.text() == '패턴 관리' for button in dialog.findChildren(QtWidgets.QPushButton)))
        finally:
            dialog.deleteLater()

    def test_relative_spacing_requires_all_points(self):
        self.data['a']['items'] = {'shape': {'name': 'shape', 'points': [
            {'dx': 10, 'dy': 20, 'color': [255, 0, 0]},
            {'dx': 11, 'dy': 20, 'color': [0, 255, 0]},
        ]}}
        save_packs(self.data)
        frame = np.zeros((3, 3, 3), dtype=np.uint8)
        frame[1, 0] = [255, 0, 0]
        frame[1, 2] = [0, 255, 0]
        self.assertFalse(self.check(frame)['result'])
        frame[1, 1] = [0, 255, 0]
        self.assertTrue(self.check(frame)['result'])

    def test_pack_uses_one_capture(self):
        engine = MacroEngine.__new__(MacroEngine)
        engine._debug_image_override = None
        with patch('engine.capture_region_np', return_value=np.zeros((3, 3, 3), dtype=np.uint8)) as capture:
            result = engine._pixel_check((0, 0, 3, 3), None, 0, pattern=PackReference('pack:a'), expect_exists=False)
            self.assertTrue(result['result'])
            self.assertEqual(capture.call_count, 1)

    def test_condition_reference_roundtrip(self):
        condition = Condition(type='pixel', pixel_pattern='pack:a', pixel_exists=False, region=(0, 0, 3, 3))
        self.assertEqual(Condition.from_dict(condition.to_dict()).pixel_pattern, 'pack:a')

    def test_selection_alone_controls_condition_and_color(self):
        dialog = ConditionNodeDialog(
            cond=Condition(type='pixel', region=(0, 0, 3, 3), color=(12, 34, 56)),
            pattern_provider=lambda: ['single'],
        )
        try:
            original = dialog.color_edit.text()
            for reference in ('pack:a/one', 'pack:a'):
                dialog.pattern_combo.setCurrentIndex(dialog.pattern_combo.findData(reference))
                self.assertTrue(dialog.color_wrap.isHidden())
                self.assertFalse(dialog.color_edit.isEnabled())
                self.assertEqual(dialog.get_condition().pixel_pattern, reference)
                self.assertIsNone(dialog.get_condition().color)
            dialog.pattern_combo.setCurrentIndex(0)
            self.assertFalse(dialog.color_wrap.isHidden())
            self.assertTrue(dialog.color_edit.isEnabled())
            self.assertEqual(dialog.color_edit.text(), original)
            self.assertIsNone(dialog.get_condition().pixel_pattern)
            self.assertEqual(dialog.get_condition().color, (12, 34, 56))
        finally:
            dialog.deleteLater()

    def test_pixel_test_selection_hides_color(self):
        dialog = PixelTestDialog(pattern_provider=lambda: ['single'])
        try:
            dialog.pattern_combo.setCurrentIndex(dialog.pattern_combo.findData('pack:a'))
            self.assertTrue(dialog.color_wrap.isHidden())
            self.assertEqual(dialog._parse_inputs()[2], 'pack:a')
            dialog.pattern_combo.setCurrentIndex(0)
            self.assertFalse(dialog.color_wrap.isHidden())
            self.assertIsNone(dialog._parse_inputs()[2])
        finally:
            dialog.deleteLater()

    def test_reset_preserves_item_and_can_be_undone(self):
        owner = QtWidgets.QWidget()
        dialog = PackManager(owner)
        self.addCleanup(dialog.deleteLater)
        self.addCleanup(owner.deleteLater)
        dialog.item()['source'] = 'old-image'
        dialog.item()['thumbnail'] = 'old-preview'
        before = dict(dialog.item())
        key = dialog.items.currentItem().data(QtCore.Qt.ItemDataRole.UserRole)
        dialog.reset_item()
        self.assertEqual(dialog.item(), {'name': '1', 'points': []})
        self.assertEqual(dialog.items.count(), 2)
        self.assertEqual(load_packs()['a']['items'][key], dialog.item())
        dialog.undo()
        self.assertEqual(dialog.item(), before)

    def test_pack_window_independent_of_main_minimize(self):
        owner = QtWidgets.QWidget()
        dialog = PackManager(owner)
        try:
            owner.show()
            dialog.show()
            owner.showMinimized()
            self.app.processEvents()
            self.assertIsNone(dialog.parentWidget())
            self.assertIsNone(dialog.windowHandle().transientParent())
            self.assertTrue(dialog.isVisible())
            self.assertFalse(dialog.isMinimized())
            self.assertTrue(dialog.windowFlags() & QtCore.Qt.WindowType.WindowStaysOnTopHint)
        finally:
            dialog.close()
            owner.close()
            dialog.deleteLater()
            owner.deleteLater()

    def test_f1_switch_undo_and_deleted_source(self):
        image_path = Path(self.temp.name) / 'source.png'
        image = QtGui.QImage(30, 30, QtGui.QImage.Format.Format_RGB32)
        image.fill(QtGui.QColor(12, 34, 56))
        image.save(str(image_path))
        owner = QtWidgets.QWidget()
        viewer = ImageViewerDialog(start_dir=Path(self.temp.name))
        owner._image_viewer_dialog = viewer
        viewer.canvas.set_image(image_path)
        dialog = PackManager(owner)
        dialog.show()
        dialog.attach_viewer()
        dialog.insert_items(['new', 'next'])
        dialog.items.setCurrentRow(2)
        viewer._last_sample = {'pos': (5, 6), 'hex': '0c2238'}
        with patch.object(viewer, '_copy_coords') as copy_coords:
            event = QtGui.QKeyEvent(QtCore.QEvent.Type.KeyPress, QtCore.Qt.Key.Key_F1, QtCore.Qt.KeyboardModifier.NoModifier)
            self.app.sendEvent(viewer, event)
            copy_coords.assert_not_called()
        self.assertEqual(viewer.canvas._overlays, [(5, 6, 1, 1)])
        self.assertEqual(dialog.item()['points'][0]['color'], [12, 34, 56])
        dialog.items.setCurrentRow(3)
        self.assertEqual(viewer.canvas._overlays, [])
        dialog.items.setCurrentRow(2)
        self.assertEqual(viewer.canvas._overlays, [(5, 6, 1, 1)])
        dialog.capture_point()
        self.assertEqual(dialog.item()['points'], [])
        dialog.undo()
        self.assertEqual(len(dialog.item()['points']), 1)
        image_path.unlink()
        saved = load_packs()
        saved_item = next(v for v in saved['a']['items'].values() if v['name'] == 'new')
        self.assertTrue(saved_item['thumbnail'])
        self.assertEqual(saved_item['points'][0]['color'], [12, 34, 56])
        dialog.close()
        self.assertEqual(viewer.canvas._overlays, [])
        reopened = PackManager(owner)
        reopened.items.setCurrentRow(2)
        self.assertFalse(reopened.preview.pixmap().isNull())
        self.assertEqual(len(reopened.item()['points']), 1)
        reopened.close()
        reopened.deleteLater()
        viewer.close()
        owner.close()
        dialog.deleteLater()
        viewer.deleteLater()
        owner.deleteLater()


if __name__ == '__main__':
    unittest.main()
