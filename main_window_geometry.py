"""Remember the main window's normal geometry and maximized state locally."""
from PyQt6 import QtCore, QtWidgets


class MainWindowGeometry(QtCore.QObject):
    KEY = 'main_window'

    def __init__(self, window):
        super().__init__(window)
        self.window = window
        self.shown = False
        self.timer = QtCore.QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.setInterval(350)
        self.timer.timeout.connect(self.save)
        saved = window._state.get(self.KEY, {})
        if isinstance(saved, dict):
            geometry = saved.get('geometry')
            if isinstance(geometry, str):
                try:
                    window.restoreGeometry(QtCore.QByteArray(bytes.fromhex(geometry)))
                except ValueError:
                    pass
            # Never reopen minimized, even when the app was closed that way.
            state = window.windowState() & ~QtCore.Qt.WindowState.WindowMinimized
            if saved.get('maximized'):
                state |= QtCore.Qt.WindowState.WindowMaximized
            window.setWindowState(state)
        window.installEventFilter(self)

    def eventFilter(self, watched, event):
        kind = event.type()
        if kind == QtCore.QEvent.Type.Show and not self.shown:
            self.shown = True
            self.keep_on_screen()
        elif self.shown and kind in (QtCore.QEvent.Type.Move, QtCore.QEvent.Type.Resize,
                                     QtCore.QEvent.Type.WindowStateChange):
            self.timer.start()
        elif self.shown and kind in (QtCore.QEvent.Type.Close, QtCore.QEvent.Type.Hide):
            self.timer.stop()
            self.save()
        return False

    def keep_on_screen(self):
        window = self.window
        if window.isMaximized():
            return
        rect = window.frameGeometry()
        screens = QtWidgets.QApplication.screens()
        if any(screen.availableGeometry().contains(rect) for screen in screens):
            return
        screen = QtWidgets.QApplication.screenAt(rect.center()) or window.screen()
        available = screen.availableGeometry()
        window.resize(min(window.width(), available.width()), min(window.height(), available.height()))
        rect = window.frameGeometry()
        window.move(max(available.left(), min(rect.left(), available.right() - rect.width() + 1)),
                    max(available.top(), min(rect.top(), available.bottom() - rect.height() + 1)))

    def save(self):
        if not self.shown:
            return
        window = self.window
        previous = window._state.get(self.KEY, {})
        maximized = (previous.get('maximized', False) if window.isMinimized()
                     else window.isMaximized())
        value = {'geometry': bytes(window.saveGeometry().toHex()).decode(),
                 'maximized': bool(maximized)}
        if previous != value:
            window._update_state(self.KEY, value)
