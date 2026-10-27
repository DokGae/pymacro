"""Long skill lists that open below the field within the current screen."""
from PyQt6 import QtCore, QtWidgets


class SkillComboBox(QtWidgets.QComboBox):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMaxVisibleItems(24)
        self.setStyleSheet('QComboBox {combobox-popup: 0;}')
        self.view().setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAsNeeded)

    def showPopup(self):
        super().showPopup()
        popup=self.view().window()
        if popup is self.window():return
        origin=self.mapToGlobal(QtCore.QPoint(0,self.height()))
        screen=QtWidgets.QApplication.screenAt(origin) or self.screen()
        bounds=screen.availableGeometry()
        row_height=max(24,self.view().sizeHintForRow(0))
        desired=min(24,max(1,self.count()))*row_height+8
        below=max(0,bounds.bottom()-origin.y()+1)
        above=max(0,self.mapToGlobal(QtCore.QPoint()).y()-bounds.top())
        height=min(desired,below if below>=row_height*4 else max(below,above))
        top=origin.y() if below>=row_height*4 else self.mapToGlobal(QtCore.QPoint()).y()-height
        width=min(bounds.width(),max(self.width(),popup.width()))
        left=max(bounds.left(),min(origin.x(),bounds.right()-width+1))
        popup.setGeometry(left,max(bounds.top(),top),width,max(row_height,height))
