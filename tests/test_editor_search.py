import os
os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
import unittest
from PyQt6 import QtWidgets
from engine import Action, Condition, Macro
from main import MacroDialog

APP = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class SearchTests(unittest.TestCase):
    def setUp(self):
        self.dialog = MacroDialog(macro=Macro(trigger_key='a', actions=[
            Action(type='if', name='분기', condition=Condition(type='key', key='a'),
                   transition_enabled=True, transition_actions=[Action(type='macro_stop')]),
            Action(type='group', enabled=False, actions=[Action(type='macro_stop')]),
            Action(type='press', key='b', description='설명검색검증')],
            stop_actions=[Action(type='sleep', description='종료검색검증', sleep_ms=10)]))
        self.dialog.show()
        for _ in range(5): APP.processEvents()
        self.search = self.dialog.editor_search
        self.tree = self.dialog.main_action_tree

    def tearDown(self):
        self.dialog.close()
        self.dialog.deleteLater()
        APP.processEvents()

    def query(self, text):
        self.search.edit.setText(text)
        self.search.apply()
        for _ in range(5): APP.processEvents()

    def test_transition_and_disabled_search_preserve_actions_and_view(self):
        before = self.tree.collect_actions()
        self.tree.collapse_all()
        view = self.tree.view_state()
        self.query('매크로 중지')
        self.assertEqual(len(self.search.results()), 2)
        self.assertTrue(self.tree.topLevelItem(0).isExpanded())
        self.assertTrue(self.tree.topLevelItem(2).isHidden())
        self.search.enabled.setChecked(True)
        self.assertEqual(len(self.search.results()), 1)
        self.assertFalse(self.tree.dragEnabled())
        self.query('')
        self.assertEqual(self.tree.collect_actions(), before)
        self.assertEqual(self.tree.view_state()['expanded'], view['expanded'])
        self.assertFalse(self.tree.topLevelItem(2).isHidden())
        self.assertTrue(self.tree.dragEnabled())

    def test_description_and_stop_tab_navigation(self):
        self.query('설명검색검증')
        self.assertEqual(len(self.search.results()), 1)
        self.query('종료검색검증')
        self.assertEqual(len(self.search.results()), 1)
        self.search.navigate(1)
        self.assertEqual(self.dialog.action_tabs.currentWidget(), self.dialog.stop_group)
        self.query('없는검색결과')
        self.assertEqual(len(self.search.results()), 0)


if __name__ == '__main__':
    unittest.main()
