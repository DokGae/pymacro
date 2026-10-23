import os
import unittest

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
from PyQt6 import QtCore, QtGui, QtWidgets
from lib.keyboard import vk_from_key
from main import MacroKeyLineEdit, _vk_to_macro_key

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class NumpadCaptureTests(unittest.TestCase):
    def test_digits_capture_and_resolve_separately(self):
        for digit in range(10):
            with self.subTest(digit=digit):
                self.assertEqual(_vk_to_macro_key(96 + digit), f'num{digit}')
                self.assertEqual(vk_from_key(f'NUM{digit}'), 96 + digit)
                self.assertEqual(vk_from_key(str(digit)), 48 + digit)
                edit = MacroKeyLineEdit()
                try:
                    for modifiers, expected in [
                        (QtCore.Qt.KeyboardModifier.KeypadModifier, f'NUM{digit}'),
                        (QtCore.Qt.KeyboardModifier.NoModifier, str(digit)),
                    ]:
                        edit.clear()
                        event = QtGui.QKeyEvent(QtCore.QEvent.Type.KeyPress,
                            48 + digit, modifiers, str(digit))
                        APP.sendEvent(edit, event)
                        self.assertEqual(edit.text(), expected)
                finally:
                    edit.close()

    def test_native_numpad_with_modifier(self):
        edit = MacroKeyLineEdit()
        try:
            event = QtGui.QKeyEvent(QtCore.QEvent.Type.KeyPress,
                QtCore.Qt.Key.Key_1,
                QtCore.Qt.KeyboardModifier.ControlModifier |
                QtCore.Qt.KeyboardModifier.KeypadModifier,
                79, 97, 0, '1')
            APP.sendEvent(edit, event)
            self.assertEqual(edit.text(), 'ctrl+NUM1')
        finally:
            edit.close()
