import copy
import unittest
from types import SimpleNamespace
from PyQt6 import QtWidgets
from engine import Condition
from shared_ui import copy_portable_conditions, paste_portable_conditions

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class SharedClipboardTests(unittest.TestCase):
    def owner(self, entries):
        owner = QtWidgets.QWidget()
        controller = SimpleNamespace(entries=entries, owner=owner)
        owner._variable_items = {}
        controller.snapshot = lambda: copy.deepcopy(entries)
        controller.commit = lambda before, description: None
        owner._shared_controller = controller
        return owner

    def test_cross_profile_collision_preserves_original(self):
        node = Condition(type='pixel', region=(0, 0, 1, 1), color=(255, 0, 0)).to_dict()
        source = self.owner({'same': {'name': '물약', 'condition': node}})
        target = self.owner({'same': {'name': '기존', 'condition': dict(node, tolerance=99)}})
        linked = dict(node, shared_ref='same')
        copy_portable_conditions(source, [linked])
        result = paste_portable_conditions(target)
        self.assertNotEqual(result[0]['shared_ref'], 'same')
        self.assertEqual(target._shared_controller.entries['same']['name'], '기존')
        self.assertEqual(target._shared_controller.entries[result[0]['shared_ref']]['name'], '물약')
        source.close()
        target.close()

    def test_common_value_copy(self):
        source = self.owner({})
        source._variable_items = {'color': [{'name': 'red', 'value': 'ff0000'}]}
        target = self.owner({})
        copy_portable_conditions(source, [], [{'color': '${red}'}])
        paste_portable_conditions(target)
        self.assertEqual(target._variable_items['color'], source._variable_items['color'])
        source.close()
        target.close()
