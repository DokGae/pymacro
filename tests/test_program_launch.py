import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import unittest
from unittest.mock import patch, Mock
from PyQt6 import QtWidgets
from engine import Action
from main import ActionEditDialog
from lib.program_launch import launch_program

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class ProgramLaunchTests(unittest.TestCase):
    def test_windows_exe_arguments_preserve_quotes_and_backslashes(self):
        with patch('lib.program_launch.subprocess.Popen') as launch:
            launch_program(r'C:\My App\app.exe', r'--path "C:\My Data\file.txt"', r'C:\My App')
        self.assertEqual(launch.call_args.args[0], r'"C:\My App\app.exe" --path "C:\My Data\file.txt"')
        self.assertEqual(launch.call_args.kwargs['cwd'], r'C:\My App')

    def test_batch_uses_command_interpreter(self):
        for suffix in ('.cmd', '.bat', '.CMD'):
            with patch('lib.program_launch.subprocess.Popen') as launch:
                launch_program('C:\\My Scripts\\start' + suffix, '"argument one"')
            command = launch.call_args.args[0]
            self.assertIn('cmd.exe', command)
            self.assertIn('/d /s /c ""C:\\My Scripts\\start' + suffix + '" "argument one""', command)

    def test_admin_uses_runas_and_handles_cancel(self):
        with patch('lib.program_launch.ctypes.windll.shell32.ShellExecuteW', Mock(return_value=42)) as execute:
            result = launch_program(r'C:\app.exe', '--flag', r'C:\work', elevated=True)
            execute.assert_called_once_with(None, 'runas', r'C:\app.exe', '--flag', r'C:\work', 1)
            self.assertIsNone(result.pid)
        with patch('lib.program_launch.ctypes.windll.shell32.ShellExecuteW', Mock(return_value=5)):
            with self.assertRaises(OSError):
                launch_program(r'C:\app.exe', elevated=True)

    def test_editor_and_profile_roundtrip(self):
        action = Action(type='process_control', process_control_action='launch',
                        process_path=r'C:\start.cmd', process_run_as_admin=True)
        action = Action.from_dict(action.to_dict())
        dialog = ActionEditDialog(action=action)
        try:
            self.assertTrue(dialog.process_admin_check.isChecked())
            self.assertFalse(dialog.process_admin_check.isHidden())
            self.assertTrue(dialog.get_action().process_run_as_admin)
            dialog.process_control_action_combo.setCurrentIndex(dialog.process_control_action_combo.findData('terminate'))
            self.assertTrue(dialog.process_admin_check.isHidden())
            dialog.process_control_action_combo.setCurrentIndex(dialog.process_control_action_combo.findData('restart'))
            self.assertFalse(dialog.process_admin_check.isHidden())
        finally:
            dialog.close()
        self.assertFalse(Action.from_dict({'type': 'process_control'}).process_run_as_admin)
