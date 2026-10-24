"""Presentation for the action editor; saved action data stays in the dialog."""
from PyQt6 import QtCore, QtWidgets


class ActionEditorGeometry(QtCore.QObject):
    """Keep geometry in the application's existing local state file."""
    KEY = 'action_editor'

    def __init__(self, dialog, key='action_editor'):
        super().__init__(dialog)
        self.KEY = key
        self.dialog = dialog
        self.owner = dialog.parentWidget()
        while self.owner is not None:
            if isinstance(getattr(self.owner, '_state', None), dict) and callable(
                    getattr(self.owner, '_update_state', None)):
                break
            self.owner = self.owner.parentWidget()
        self.shown = False
        self.last_saved = None
        self.timer = QtCore.QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.setInterval(300)
        self.timer.timeout.connect(self.save)
        if self.owner is not None:
            state = self.owner._state.get(self.KEY, {})
            geometry = state.get('geometry') if isinstance(state, dict) else None
            if isinstance(geometry, str):
                try:
                    dialog.restoreGeometry(QtCore.QByteArray(bytes.fromhex(geometry)))
                except ValueError:
                    pass
        dialog.installEventFilter(self)
        dialog.finished.connect(self.save)

    def eventFilter(self, watched, event):
        kind = event.type()
        if kind == QtCore.QEvent.Type.Show:
            self.shown = True
        elif kind in (QtCore.QEvent.Type.Move, QtCore.QEvent.Type.Resize,
                      QtCore.QEvent.Type.WindowStateChange):
            if self.shown and self.dialog.isVisible():
                self.timer.start()
        elif kind == QtCore.QEvent.Type.Hide:
            self.save()
        return False

    def save(self, *_):
        self.timer.stop()
        if self.owner is None or not self.shown or self.dialog.isMinimized():
            return
        geometry = bytes(self.dialog.saveGeometry()).hex()
        if geometry != self.last_saved:
            state = dict(self.owner._state.get(self.KEY, {}))
            state['geometry'] = geometry
            self.owner._update_state(self.KEY, state)
            self.last_saved = geometry


def group_action_types(combo):
    """Use disabled headings while preserving action IDs and keyboard navigation."""
    groups = [
        ('키보드', ('press', 'down', 'up', 'touch_keyboard_open', 'touch_keyboard_close')),
        ('마우스', ('mouse_click', 'mouse_down', 'mouse_up', 'mouse_move', 'mouse_wheel')),
        ('조건·반복·흐름 제어', ('if', 'elif', 'group', 'sleep', 'label', 'goto',
                              'continue', 'break', 'return', 'macro_cycle', 'macro_stop', 'noop')),
        ('변수·타이머·픽셀', ('set_var', 'timer', 'pixel_get')),
        ('알림', ('sound_alert', 'telegram_message')),
        ('프로그램·시스템', ('process_control', 'computer_shutdown')),
    ]
    current = combo.currentData()
    entries = {combo.itemData(i): combo.itemText(i) for i in range(combo.count())}
    blocker = QtCore.QSignalBlocker(combo)
    combo.clear()
    for title, values in groups:
        present = [value for value in values if value in entries]
        if not present:
            continue
        combo.addItem(title)
        heading = combo.model().item(combo.count() - 1)
        heading.setFlags(QtCore.Qt.ItemFlag.NoItemFlags)
        font = heading.font()
        font.setBold(True)
        heading.setFont(font)
        heading.setData(QtCore.QSize(0, 28), QtCore.Qt.ItemDataRole.SizeHintRole)
        for value in present:
            combo.addItem('    ' + entries[value], value)
    combo.setCurrentIndex(combo.findData(current))
    combo.setMaxVisibleItems(18)
    del blocker


class FoldSection(QtWidgets.QWidget):
    def __init__(self, title):
        super().__init__()
        self.toggle = QtWidgets.QToolButton()
        self.toggle.setObjectName('foldSection')
        self.toggle.setProperty('editorCommand', True)
        self.toggle.setIconSize(QtCore.QSize(10, 10))
        self.toggle.setText(title)
        self.toggle.setCheckable(True)
        self.toggle.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.toggle.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Fixed)
        self.body = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(2)
        layout.addWidget(self.toggle)
        layout.addWidget(self.body)
        self.toggle.toggled.connect(self.setExpanded)
        self.setExpanded(False)

    def setExpanded(self, expanded):
        self.toggle.setChecked(expanded)
        from editor_theme import fold_icon
        self.toggle.setIcon(fold_icon(expanded))
        self.body.setVisible(expanded)

    def title(self):
        return self.toggle.text()



def arrange_action_editor(dialog):
    from compact_action_layout import arrange_compact_action
    arrange_compact_action(dialog)


def refresh_action_cards(dialog):
    from compact_action_layout import refresh_compact_action
    refresh_compact_action(dialog)


from condition_editor_ui import arrange_condition_editor
