import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import unittest
from PyQt6 import QtCore, QtGui, QtWidgets
from main import MacroDialog

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

class TriggerMouseCaptureTests(unittest.TestCase):
    def setUp(self):
        self.dialog = MacroDialog()
        self.addCleanup(self.dialog.close)
        self.dialog.show()
        self.dialog.action_tabs.setCurrentWidget(self.dialog.trigger_page)
        APP.processEvents()

    def press(self, edit, button, modifiers=QtCore.Qt.KeyboardModifier.NoModifier):
        event = QtGui.QMouseEvent(QtCore.QEvent.Type.MouseButtonPress,
            QtCore.QPointF(20, 10), QtCore.QPointF(20, 10), button, button, modifiers)
        APP.sendEvent(edit, event)

    def test_focus_click_preserves_existing_trigger(self):
        edit = self.dialog.trigger_edit
        edit.setText('f2')
        self.dialog.name_edit.setFocus()
        APP.processEvents()
        self.press(edit, QtCore.Qt.MouseButton.LeftButton)
        self.assertTrue(edit.hasFocus())
        self.assertEqual(edit.text(), 'f2')

    def test_all_supported_mouse_buttons_and_save(self):
        edit = self.dialog.trigger_edit
        edit.setFocus()
        APP.processEvents()
        for button, key in [(QtCore.Qt.MouseButton.LeftButton, 'mouse1'),
                            (QtCore.Qt.MouseButton.RightButton, 'mouse2'),
                            (QtCore.Qt.MouseButton.MiddleButton, 'mouse3'),
                            (QtCore.Qt.MouseButton.BackButton, 'mouse4'),
                            (QtCore.Qt.MouseButton.ForwardButton, 'mouse5')]:
            with self.subTest(key=key):
                self.press(edit, button)
                self.assertEqual(edit.text(), key)
                self.assertEqual(self.dialog.trigger_main_edit.text(), key)
        self.dialog._add_or_update_trigger()
        self.assertIn('mouse5', [t.key for t in self.dialog._collect_triggers()])

    def test_mouse_combo_syncs_builder(self):
        edit = self.dialog.trigger_edit
        edit.setFocus()
        APP.processEvents()
        self.press(edit, QtCore.Qt.MouseButton.BackButton,
                   QtCore.Qt.KeyboardModifier.ControlModifier)
        self.assertEqual(edit.text(), 'ctrl+mouse4')
        self.assertTrue(self.dialog.trigger_mod_ctrl.isChecked())
        self.assertEqual(self.dialog.trigger_main_edit.text(), 'mouse4')
        main = self.dialog.trigger_main_edit
        main.setFocus()
        APP.processEvents()
        self.press(main, QtCore.Qt.MouseButton.ForwardButton)
        self.assertEqual(edit.text(), 'ctrl+mouse5')

if __name__ == '__main__':
    unittest.main()
