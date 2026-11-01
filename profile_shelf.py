"""Wrapped file chips matching the dark-control HTML shelves."""
from pathlib import Path
from PyQt6 import QtCore, QtGui, QtWidgets


class FileChipDelegate(QtWidgets.QStyledItemDelegate):
    def title(self, index):
        path = index.data(QtCore.Qt.ItemDataRole.UserRole)
        return ('☆ ' if self.parent().favorite else '') + (Path(path).stem if path else index.data() or '')

    def sizeHint(self, option, index):
        width = QtGui.QFontMetrics(option.font).horizontalAdvance(self.title(index)) + 26
        return QtCore.QSize(min(220, max(70, width)), 36)

    def paint(self, painter, option, index):
        selected = bool(option.state & QtWidgets.QStyle.StateFlag.State_Selected)
        current = index.data(QtCore.Qt.ItemDataRole.BackgroundRole) is not None
        hover = bool(option.state & QtWidgets.QStyle.StateFlag.State_MouseOver)
        active = selected or current
        rect = option.rect.adjusted(0, 0, -1, -1)
        painter.save()
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
        painter.setBrush(QtGui.QColor('#203d36' if active else '#2b3947' if hover else '#222d39'))
        painter.setPen(QtGui.QColor('#37b997' if active else '#222d39'))
        painter.drawRoundedRect(QtCore.QRectF(rect).adjusted(.5, .5, -.5, -.5), 6, 6)
        painter.setFont(option.font)
        painter.setPen(QtGui.QColor('#77dbbc' if active else '#edf1f7'))
        text_rect = rect.adjusted(12, 0, -12, 0)
        text = painter.fontMetrics().elidedText(self.title(index), QtCore.Qt.TextElideMode.ElideMiddle, text_rect.width())
        painter.drawText(text_rect, QtCore.Qt.AlignmentFlag.AlignVCenter | QtCore.Qt.AlignmentFlag.AlignLeft, text)
        if option.state & QtWidgets.QStyle.StateFlag.State_HasFocus:
            painter.setBrush(QtCore.Qt.BrushStyle.NoBrush)
            painter.setPen(QtGui.QPen(QtGui.QColor('#9ce9d2'), 1, QtCore.Qt.PenStyle.DotLine))
            painter.drawRoundedRect(QtCore.QRectF(rect).adjusted(3, 3, -3, -3), 4, 4)
        painter.restore()


class FileChipList(QtWidgets.QListWidget):
    def __init__(self, favorite=False):
        super().__init__()
        self.favorite = favorite
        self.setViewMode(QtWidgets.QListView.ViewMode.IconMode)
        self.setFlow(QtWidgets.QListView.Flow.LeftToRight)
        self.setWrapping(True)
        self.setResizeMode(QtWidgets.QListView.ResizeMode.Adjust)
        self.setMovement(QtWidgets.QListView.Movement.Static)
        self.setSpacing(4)
        self.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        self.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.setMouseTracking(True)
        self.setMinimumHeight(48)
        self.setMaximumHeight(100)
        self.setItemDelegate(FileChipDelegate(self))
        self.setStyleSheet('QListWidget{background:transparent;color:#edf1f7;border:0;outline:0;}')
        if favorite:
            self.setDragEnabled(True)
            self.setAcceptDrops(True)
            self.setDropIndicatorShown(True)
            self.setDragDropMode(QtWidgets.QAbstractItemView.DragDropMode.InternalMove)
            self.setDefaultDropAction(QtCore.Qt.DropAction.MoveAction)
        self.model().rowsInserted.connect(self.schedule_fit)
        self.model().rowsRemoved.connect(self.schedule_fit)
        self.model().modelReset.connect(self.schedule_fit)
        self._fit_pending = False

    def schedule_fit(self, *_):
        if not self._fit_pending:
            self._fit_pending = True
            QtCore.QTimer.singleShot(0, self.fit_height)

    def fit_height(self):
        self._fit_pending = False
        self.doItemsLayout()
        bottom = max((self.visualItemRect(self.item(i)).bottom() for i in range(self.count())), default=39)
        height = min(100, max(48, bottom + 7))
        if self.minimumHeight() != height or self.maximumHeight() != height:
            self.setFixedHeight(height)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.schedule_fit()


def build_profile_shelves(window):
    strip = QtWidgets.QWidget()
    strip.setObjectName('profileShelves')
    layout = QtWidgets.QHBoxLayout(strip)
    layout.setContentsMargins(0, 0, 0, 0)
    layout.setSpacing(16)
    for favorite in (True, False):
        card = QtWidgets.QFrame()
        card.setObjectName('fileShelf')
        card.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Maximum)
        card.setStyleSheet('QFrame#fileShelf{background:#1b222c;border:1px solid #303a49;border-radius:10px;}')
        column = QtWidgets.QVBoxLayout(card)
        column.setContentsMargins(17, 14, 17, 12)
        column.setSpacing(9)
        head = QtWidgets.QHBoxLayout()
        label = QtWidgets.QLabel('즐겨찾기' if favorite else '최근 불러온 파일')
        label.setStyleSheet('color:#edf1f7;font-size:12px;font-weight:600;')
        setattr(window, 'fav_label' if favorite else 'recent_label', label)
        head.addWidget(label, 1)
        specs = [('fav_load_btn', '불러오기'), ('fav_remove_btn', '즐겨찾기 해제')] if favorite else [
            ('recent_load_btn', '불러오기'), ('recent_to_fav_btn', '즐겨찾기 추가'),
            ('recent_clear_btn', '비우기')]
        for attr, title in specs:
            button = QtWidgets.QPushButton(title)
            button.setStyleSheet('QPushButton{background:#1b222c;color:#dce7f3;border:1px solid #303a49;border-radius:6px;padding:5px 9px;font-size:10px;}QPushButton:hover{background:#2b3947;}QPushButton:disabled{color:#718195;}')
            setattr(window, attr, button)
            head.addWidget(button)
        column.addLayout(head)
        view = FileChipList(favorite)
        setattr(window, 'favorite_list' if favorite else 'recent_list', view)
        column.addWidget(view)
        layout.addWidget(card, 1)
    window.recent_list.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.ActionsContextMenu)
    clear = QtGui.QAction('최근 기록 비우기', window.recent_list)
    clear.triggered.connect(window.recent_clear_btn.click)
    window.recent_list.addAction(clear)
    return strip
