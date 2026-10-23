"""Remember user visibility, independently of parent hide and application shutdown."""
import copy
import os
import unittest
from types import SimpleNamespace
from unittest.mock import patch

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
from PyQt6 import QtWidgets
from shared_ui import SharedController

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class Owner(QtWidgets.QMainWindow):
    def __init__(self, state=None):
        super().__init__()
        self._state = copy.deepcopy(state or {})
        self.profile = SimpleNamespace(shared_settings={})
        self.macro_table = QtWidgets.QTableWidget()
        self.setCentralWidget(self.macro_table)

    def _update_state(self, key, value):
        self._state[key] = value


class SharedPanelStateTests(unittest.TestCase):
    def setUp(self):
        self.refresh_patch = patch.object(SharedController, 'refresh')
        self.refresh_patch.start()
        self.addCleanup(self.refresh_patch.stop)
        self.owners = []

    def owner(self, state=None):
        owner = Owner(state)
        self.owners.append(owner)
        owner.controller = SharedController(owner)
        owner.controller.timer.stop()
        owner.show()
        APP.processEvents()
        return owner

    def tearDown(self):
        for owner in self.owners:
            owner.controller.prepare_app_close()
            owner.close()
            owner.deleteLater()
        APP.processEvents()

    def test_hidden_panel_stays_hidden_after_reopening(self):
        owner = self.owner()
        owner.controller.dock.hide()
        APP.processEvents()
        self.assertFalse(owner._state['shared_settings_dock']['visible'])
        owner.controller.prepare_app_close()
        owner.close()
        restored = self.owner(owner._state)
        self.assertTrue(restored.controller.dock.isHidden())
        self.assertFalse(restored.controller.dock.isVisible())

    def test_visible_panel_restores_and_shutdown_does_not_overwrite_preference(self):
        owner = self.owner({'shared_settings_dock': {'visible': False}})
        self.assertTrue(owner.controller.dock.isHidden())
        owner.controller.show()
        APP.processEvents()
        self.assertTrue(owner._state['shared_settings_dock']['visible'])
        owner.controller.prepare_app_close()
        owner.controller.dock.hide()
        owner.close()
        self.assertTrue(owner._state['shared_settings_dock']['visible'])
        restored = self.owner(owner._state)
        self.assertTrue(restored.controller.dock.isVisible())

    def test_parent_hide_or_minimize_does_not_mean_user_closed_the_panel(self):
        owner = self.owner()
        owner.hide()
        APP.processEvents()
        self.assertTrue(owner._state['shared_settings_dock']['visible'])
        owner.showMinimized()
        APP.processEvents()
        self.assertTrue(owner._state['shared_settings_dock']['visible'])
        owner.showNormal()
        APP.processEvents()
        self.assertTrue(owner.controller.dock.isVisible())


if __name__ == '__main__':
    unittest.main()
