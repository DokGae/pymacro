"""Shared visual rules for action and condition editors."""
from PyQt6 import QtCore, QtGui, QtWidgets


def fold_icon(expanded):
    pixmap = QtGui.QPixmap(10, 10)
    pixmap.fill(QtCore.Qt.GlobalColor.transparent)
    painter = QtGui.QPainter(pixmap)
    painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
    painter.setPen(QtGui.QPen(QtGui.QColor('#74808C'), 1.3))
    points = [(2, 3), (5, 6), (8, 3)] if expanded else [(3, 2), (6, 5), (3, 8)]
    painter.drawPolyline(QtGui.QPolygon([QtCore.QPoint(*point) for point in points]))
    painter.end()
    return QtGui.QIcon(pixmap)


class ConditionCheckDelegate(QtWidgets.QStyledItemDelegate):
    """The same 14px blue check indicator used by the macro action tree."""
    @staticmethod
    def check_rect(rect):
        return QtCore.QRect(rect.center().x() - 7, rect.center().y() - 7, 14, 14)

    def paint(self, painter, option, index):
        selected = bool(option.state & QtWidgets.QStyle.StateFlag.State_Selected)
        background = index.data(QtCore.Qt.ItemDataRole.BackgroundRole)
        painter.fillRect(option.rect, QtGui.QColor('#E6F1EE') if selected else
                         background if isinstance(background, QtGui.QBrush) else QtGui.QColor('#FFFFFF'))
        if index.data(QtCore.Qt.ItemDataRole.CheckStateRole) is None:
            return
        checked = index.data(QtCore.Qt.ItemDataRole.CheckStateRole) in (QtCore.Qt.CheckState.Checked, QtCore.Qt.CheckState.Checked.value)
        check = self.check_rect(option.rect)
        painter.save()
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
        painter.setPen(QtGui.QPen(QtGui.QColor('#1673bf' if checked else '#8391a2'), 1))
        painter.setBrush(QtGui.QColor('#1673bf' if checked else '#ffffff'))
        painter.drawRoundedRect(QtCore.QRectF(check).adjusted(.5, .5, -.5, -.5), 3, 3)
        if checked:
            pen = QtGui.QPen(QtGui.QColor('#ffffff'), 1.8)
            pen.setCapStyle(QtCore.Qt.PenCapStyle.RoundCap)
            pen.setJoinStyle(QtCore.Qt.PenJoinStyle.RoundJoin)
            painter.setPen(pen)
            painter.drawPolyline(QtGui.QPolygonF([QtCore.QPointF(check.x()+3, check.y()+7),
                QtCore.QPointF(check.x()+6, check.y()+10), QtCore.QPointF(check.x()+11, check.y()+4)]))
        painter.restore()

    def editorEvent(self, event, model, option, index):
        if not index.flags() & QtCore.Qt.ItemFlag.ItemIsUserCheckable:
            return False
        if event.type() == QtCore.QEvent.Type.MouseButtonRelease:
            toggle = event.button() == QtCore.Qt.MouseButton.LeftButton and self.check_rect(option.rect).contains(event.pos())
        elif event.type() == QtCore.QEvent.Type.KeyPress:
            toggle = event.key() == QtCore.Qt.Key.Key_Space
        else:
            return False
        if toggle:
            checked = index.data(QtCore.Qt.ItemDataRole.CheckStateRole) in (QtCore.Qt.CheckState.Checked, QtCore.Qt.CheckState.Checked.value)
            return model.setData(index, QtCore.Qt.CheckState.Unchecked.value if checked else QtCore.Qt.CheckState.Checked.value,
                                 QtCore.Qt.ItemDataRole.CheckStateRole)
        return False
COLORS = dict(background='#F4F6F8', surface='#FFFFFF', text='#293541', muted='#74808C',
              border='#DCE2E7', selection='#E6F1EE', accent='#477D70', button='#EAF3F0')


def apply_editor_theme(dialog):
    dialog.setProperty('editorSurface', True)
    dialog.setStyleSheet('''
        QDialog[editorSurface="true"] { background: #F4F6F8; color: #293541; }
        QDialog[editorSurface="true"] QLabel, QDialog[editorSurface="true"] QCheckBox {
            color: #293541;
        }
        QDialog[editorSurface="true"] QScrollArea,
        QDialog[editorSurface="true"] QWidget#editorPage { background: #F4F6F8; border: 0; }
        QDialog[editorSurface="true"] QLineEdit,
        QDialog[editorSurface="true"] QComboBox {
            background: white; color: #293541; border: 1px solid #DCE2E7;
            border-radius: 4px; min-height: 22px; padding: 1px 5px;
        }
        QDialog[editorSurface="true"] QLineEdit:focus,
        QDialog[editorSurface="true"] QComboBox:focus { border-color: #477D70; }
        QDialog[editorSurface="true"] QAbstractSpinBox { min-height: 26px; }
        QDialog[editorSurface="true"] QAbstractSpinBox QLineEdit {
            min-height: 0px; border: 0px; padding: 0px; background: transparent;
        }
        QFrame#actionConditionSummary { background: white; border: 1px solid #DCE2E7; border-radius: 5px; }
        QDialog[editorSurface="true"] QPushButton,
        QDialog[editorSurface="true"] QToolButton[editorCommand="true"] {
            background: #FFFFFF; color: #293541; border: 1px solid #DCE2E7;
            border-radius: 4px; min-height: 22px; padding: 2px 8px;
        }
        QDialog[editorSurface="true"] QPushButton:hover,
        QDialog[editorSurface="true"] QToolButton[editorCommand="true"]:hover { background: #EEF2F4; }
        QDialog[editorSurface="true"] QPushButton:pressed { background: #E2E8EC; }
        QDialog[editorSurface="true"] QPushButton:focus,
        QDialog[editorSurface="true"] QToolButton[editorCommand="true"]:focus { border-color: #477D70; }
        QDialog[editorSurface="true"] QToolButton::menu-indicator {
            width: 7px; height: 7px; subcontrol-origin: padding;
            subcontrol-position: right center; right: 4px;
        }
        QDialog[editorSurface="true"] QLineEdit QToolButton {
            min-height: 0px; min-width: 0px; padding: 0px; border: 0px; background: transparent;
        }
        QDialog[editorSurface="true"] QPushButton[editorPrimary="true"] {
            background: #EAF3F0; color: #477D70; border-color: #BED3CA; font-weight: 600;
        }
        QDialog[editorSurface="true"] QPushButton[editorPrimary="true"]:hover { background: #DFECE7; }
        QDialog[editorSurface="true"] QPushButton[editorDanger="true"]:hover {
            background: #FAECEC; border-color: #E6C5C5; color: #9A4C4C;
        }
        QDialog[editorSurface="true"] QPushButton:disabled { color: #98A1AA; background: #F4F6F8; }
        QDialog[editorSurface="true"] QGroupBox[editorCard="true"] {
            background: #FFFFFF; border: 1px solid #DCE2E7; border-radius: 6px;
            margin-top: 9px; padding: 6px; font-weight: 600;
        }
        QDialog[editorSurface="true"] QGroupBox[editorCard="true"]::title {
            subcontrol-origin: margin; left: 10px; padding: 0 5px;
        }
        QDialog[editorSurface="true"] QToolButton#foldSection {
            background: transparent; border: 0; text-align: left; color: #526778;
        }
        QGroupBox#conditionCanvas { border: 0; margin: 0; padding: 0; }
        QDialog[editorSurface="true"] QTreeWidget {
            background: white; color: #293541; border: 1px solid #DCE2E7; border-radius: 5px;
            selection-background-color: #E6F1EE; selection-color: #293541;
        }
        QDialog[editorSurface="true"] QTreeWidget::item { padding: 5px 2px; }
        QDialog[editorSurface="true"] QTreeWidget::item:selected,
        QDialog[editorSurface="true"] QTreeWidget::item:selected:!active {
            background: #E6F1EE; color: #293541;
        }
        QDialog[editorSurface="true"] QHeaderView::section {
            background: #F4F6F8; color: #74808C; padding: 5px 4px;
            border: 0; border-bottom: 1px solid #DCE2E7;
        }
        QLabel#conditionLogic { padding: 6px 8px; background: #EEF2F4; border-radius: 4px; }
        QLabel#conditionSelection { padding: 4px 2px; color: #74808C; }
    ''')
