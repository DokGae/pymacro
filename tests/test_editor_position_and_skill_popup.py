import os
os.environ.setdefault('QT_QPA_PLATFORM','offscreen')
import unittest
from PyQt6 import QtCore,QtWidgets
from main import ConditionNodeDialog,ActionEditDialog
from engine import Condition,Action
from skill_combo import SkillComboBox

APP=QtWidgets.QApplication.instance() or QtWidgets.QApplication([])


class Owner(QtWidgets.QWidget):
    def __init__(self):super().__init__();self._state={}
    def _update_state(self,key,value):self._state[key]=value


class PresentationTests(unittest.TestCase):
    def test_condition_and_action_remember_independent_positions(self):
        owner=Owner()
        for cls,kwargs,key,point in (
            (ConditionNodeDialog,{'cond':Condition(type='aion2')},'condition_node_editor',QtCore.QPoint(42,53)),
            (ActionEditDialog,{'action':Action(type='press',key='a')},'action_editor',QtCore.QPoint(82,93))):
            first=cls(owner,**kwargs);first.show();APP.processEvents();first.move(point);APP.processEvents();first.reject()
            self.assertEqual(owner._state[key]['position'],[point.x(),point.y()])
            second=cls(owner,**kwargs);second.show();APP.processEvents()
            self.assertEqual(second.pos(),point)
            second.reject()
        owner.close()

    def test_skill_popup_extends_below_and_stays_on_screen(self):
        window=QtWidgets.QWidget();layout=QtWidgets.QVBoxLayout(window);combo=SkillComboBox();layout.addWidget(combo)
        for i in range(100):combo.addItem(f'스킬 {i}',i)
        window.move(20,20);window.show();APP.processEvents();combo.showPopup();APP.processEvents()
        popup=combo.view().window();bounds=combo.screen().availableGeometry()
        origin=combo.mapToGlobal(QtCore.QPoint(0,combo.height()))
        self.assertGreaterEqual(popup.y(),origin.y())
        self.assertGreater(popup.height(),300)
        self.assertLessEqual(popup.geometry().bottom(),bounds.bottom())
        combo.hidePopup();window.close()


if __name__=='__main__':unittest.main()
