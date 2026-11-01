"""Compact action controls and traversal shared by the UI and runtime."""
from pathlib import Path
from PyQt6 import QtCore, QtGui, QtWidgets
from action_controls import macro_actions
from quick_toggle_groups import GroupedToggleMixin


class ProfileTitle(QtWidgets.QLabel):
    def paintEvent(self, event):
        p = QtGui.QPainter(self)
        p.setFont(self.font())
        p.setPen(QtGui.QColor('#f3f6fc'))
        text = self.fontMetrics().elidedText(self.text(), QtCore.Qt.TextElideMode.ElideRight, self.width())
        p.drawText(self.rect(), QtCore.Qt.AlignmentFlag.AlignLeft | QtCore.Qt.AlignmentFlag.AlignVCenter, text)


class ClickThroughSurface(QtWidgets.QWidget):
    """Visible body on an input-transparent native window, separate from controls."""
    def __init__(self, panel):
        super().__init__(panel, QtCore.Qt.WindowType.Tool | QtCore.Qt.WindowType.FramelessWindowHint
                         | QtCore.Qt.WindowType.WindowTransparentForInput
                         | QtCore.Qt.WindowType.WindowDoesNotAcceptFocus)
        self.panel = panel
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_ShowWithoutActivating)

    def paintEvent(self, event):
        image = QtGui.QImage(self.panel.size(), QtGui.QImage.Format.Format_ARGB32_Premultiplied)
        image.fill(QtCore.Qt.GlobalColor.transparent)
        self.panel.render(image, QtCore.QPoint(), QtGui.QRegion(),
                          QtWidgets.QWidget.RenderFlag.DrawWindowBackground
                          | QtWidgets.QWidget.RenderFlag.DrawChildren
                          | QtWidgets.QWidget.RenderFlag.IgnoreMask)
        p = QtGui.QPainter(self)
        p.setCompositionMode(QtGui.QPainter.CompositionMode.CompositionMode_Source)
        p.drawImage(0, 0, image)


class HeaderButton(QtWidgets.QAbstractButton):
    def __init__(self, kind, name, parent=None):
        super().__init__(parent)
        self.kind = kind
        self.setFixedSize(24, 24)
        self.setToolTip(name)
        self.setAccessibleName(name)
        self.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)

    def paintEvent(self, event):
        p = QtGui.QPainter(self)
        p.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
        if self.underMouse() or self.isChecked() or self.hasFocus():
            p.setPen(QtCore.Qt.PenStyle.NoPen)
            p.setBrush(QtGui.QColor('#283244'))
            p.drawRoundedRect(QtCore.QRectF(0, 0, 24, 24), 6, 6)
        color = {'close': '#fb7185', 'minimize': '#fbbf24', 'settings': '#60a5fa'}.get(self.kind, '#a9b8cb')
        if self.isChecked():
            color = '#62dec0'
        p.setPen(QtGui.QPen(QtGui.QColor(color), 1.5, QtCore.Qt.PenStyle.SolidLine,
                           QtCore.Qt.PenCapStyle.RoundCap, QtCore.Qt.PenJoinStyle.RoundJoin))
        if self.kind == 'close':
            p.drawLine(8, 8, 16, 16)
            p.drawLine(16, 8, 8, 16)
        elif self.kind == 'minimize':
            p.drawLine(7, 12, 17, 12)
        elif self.kind == 'settings':
            for y, x in ((7, 10), (12, 15), (17, 9)):
                p.drawLine(6, y, 18, y)
                p.setBrush(QtGui.QColor('#191e26'))
                p.drawEllipse(QtCore.QPointF(x, y), 2, 2)
        elif self.kind == 'lock':
            shackle = QtGui.QPainterPath()
            shackle.moveTo(8, 11)
            shackle.lineTo(8, 8)
            shackle.cubicTo(8, 3, 16, 3, 16, 8)
            shackle.lineTo(16, 11 if self.isChecked() else 7)
            p.setBrush(QtCore.Qt.BrushStyle.NoBrush)
            p.drawPath(shackle)
            p.setBrush(QtGui.QColor(color))
            p.setPen(QtCore.Qt.PenStyle.NoPen)
            p.drawRoundedRect(QtCore.QRectF(6, 10, 12, 10), 2, 2)
            p.setPen(QtGui.QPen(QtGui.QColor('#10141c'), 1.5, QtCore.Qt.PenStyle.SolidLine,
                               QtCore.Qt.PenCapStyle.RoundCap))
            p.drawLine(12, 14, 12, 17)
        else:
            p.drawLine(9, 6, 15, 6)
            p.drawLine(10, 6, 10, 11)
            p.drawLine(14, 6, 14, 11)
            p.drawLine(10, 11, 7, 14)
            p.drawLine(14, 11, 17, 14)
            p.drawLine(7, 14, 17, 14)
            p.drawLine(12, 14, 12, 19)


class DragHeader(QtWidgets.QWidget):
    def __init__(self, parent):
        super().__init__(parent)
        self.offset = None
        self.setCursor(QtCore.Qt.CursorShape.SizeAllCursor)

    def mousePressEvent(self, event):
        if self.window().interaction_locked:
            return
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            self.offset = event.globalPosition().toPoint() - self.window().pos()
            event.accept()

    def mouseMoveEvent(self, event):
        if self.window().interaction_locked:
            return
        if self.offset is not None and event.buttons() & QtCore.Qt.MouseButton.LeftButton:
            self.window().move(event.globalPosition().toPoint() - self.offset)
            event.accept()

    def mouseReleaseEvent(self, event):
        self.offset = None
        self.window().schedule_save()


class ResizeGrip(QtWidgets.QWidget):
    def __init__(self, parent, left, top):
        super().__init__(parent)
        self.left, self.top, self.drag = left, top, None
        self.setFixedSize(12, 12)
        self.setCursor(QtCore.Qt.CursorShape.SizeFDiagCursor if left == top
                       else QtCore.Qt.CursorShape.SizeBDiagCursor)
        self.setToolTip('드래그하여 크기 조절')

    def mousePressEvent(self, event):
        if self.window().interaction_locked:
            return
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            self.drag = (event.globalPosition().toPoint(), self.window().geometry())
            event.accept()

    def mouseMoveEvent(self, event):
        if self.window().interaction_locked:
            return
        if self.drag is None or not event.buttons() & QtCore.Qt.MouseButton.LeftButton:
            return
        start, original = self.drag
        delta = event.globalPosition().toPoint() - start
        window = self.window()
        rect = QtCore.QRect(original)
        if self.left:
            rect.setLeft(min(original.right() - window.minimumWidth() + 1, original.left() + delta.x()))
        else:
            rect.setRight(max(original.left() + window.minimumWidth() - 1, original.right() + delta.x()))
        if self.top:
            rect.setTop(min(original.bottom() - window.minimumHeight() + 1, original.top() + delta.y()))
        else:
            rect.setBottom(max(original.top() + window.minimumHeight() - 1, original.bottom() + delta.y()))
        window.setGeometry(rect)
        event.accept()

    def mouseReleaseEvent(self, event):
        self.drag = None
        self.window().schedule_save()

    def paintEvent(self, event):
        if not self.left and not self.top:
            p = QtGui.QPainter(self)
            p.setPen(QtGui.QColor('#526074'))
            p.drawLine(3, 8, 8, 3)
            p.drawLine(7, 8, 8, 7)


class ToggleSwitch(QtWidgets.QAbstractButton):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setCheckable(True)
        self.setFixedSize(38, 24)
        self.mixed = False
        self.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(QtCore.Qt.FocusPolicy.StrongFocus)

    def paintEvent(self, event):
        p = QtGui.QPainter(self)
        p.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
        on = self.isChecked()
        mixed = self.mixed
        p.setPen(QtCore.Qt.PenStyle.NoPen)
        p.setBrush(QtGui.QColor('#665838' if mixed else '#65dfbd' if on else '#475263'))
        p.drawRoundedRect(QtCore.QRectF(1, 2, 36, 20), 10, 10)
        p.setBrush(QtGui.QColor('#f0d49e' if mixed else '#153a30' if on else '#a9b4c4'))
        if mixed:
            p.drawRoundedRect(QtCore.QRectF(13, 10, 12, 3), 1.5, 1.5)
        else:
            p.drawEllipse(QtCore.QRectF(21 if on else 5, 6, 12, 12))
        if self.hasFocus():
            p.setBrush(QtCore.Qt.BrushStyle.NoBrush)
            p.setPen(QtGui.QPen(QtGui.QColor('#b7f5e5'), 1))
            p.drawRoundedRect(QtCore.QRectF(1, 2, 36, 20), 10, 10)


class QuickToggleWindow(GroupedToggleMixin, QtWidgets.QDialog):
    def __init__(self, owner):
        # A native owned window brings its owner forward when activated on Windows.
        # Keep the controller reference without creating a Qt/native parent link.
        super().__init__(None)
        self.owner = owner
        self.setWindowFlags(QtCore.Qt.WindowType.Window | QtCore.Qt.WindowType.FramelessWindowHint)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground)
        self.background_opacity = 100
        self.interaction_locked = False
        self.clickthrough_surface = None
        self._ready = False
        self._app_closing = False
        font = QtGui.QFont('Malgun Gothic', 10)
        font.setHintingPreference(QtGui.QFont.HintingPreference.PreferFullHinting)
        self.setFont(font)
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.setWindowTitle('빠른 토글')
        self.resize(370, 560)
        self.setMinimumSize(250, 155)
        self.setStyleSheet('''
            QDialog {background:transparent; color:#edf1f7;}
            QLabel {color:#edf1f7; background:transparent; border:0;}
            QToolButton {color:#d0dbe8; font-size:12px; font-weight:600; background:transparent; border:0;
                border-radius:8px; padding:6px;}
            QToolButton:hover {background:#2a323e; color:#edf1f7;}
            QToolButton:checked {color:#a0f3d9; background:#253b38;}
            QScrollArea, QWidget#toggleBody {background:transparent; border:0;}
            QFrame#toggleRow {background:transparent; border:0;}
            QSlider::groove:horizontal {height:3px; background:#344154; border-radius:1px;}
            QSlider::sub-page:horizontal {background:#62dec0; border-radius:1px;}
            QSlider::handle:horizontal {width:11px; margin:-4px 0; background:#edf1f7; border-radius:5px;}
            QScrollBar:vertical {background:transparent; width:5px;}
            QScrollBar::handle:vertical {background:#424d5c; border-radius:2px; min-height:24px;}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {height:0;}
        ''')
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(12, 8, 12, 14)
        layout.setSpacing(10)
        self.header = DragHeader(self)
        header = QtWidgets.QHBoxLayout(self.header)
        header.setContentsMargins(2, 0, 0, 0)
        header.setSpacing(3)
        title = self.profile_title = ProfileTitle()
        title.setAttribute(QtCore.Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        title.setStyleSheet('font-size:14px; font-weight:700; color:#f3f6fc;')
        title.setMinimumWidth(0)
        title.setSizePolicy(QtWidgets.QSizePolicy.Policy.Ignored, QtWidgets.QSizePolicy.Policy.Preferred)
        header.addWidget(title, 1)
        self.opacity_slider = QtWidgets.QSlider(QtCore.Qt.Orientation.Horizontal)
        self.opacity_slider.setRange(0, 100)
        self.opacity_slider.setFixedSize(58, 24)
        self.opacity_slider.setAccessibleName('배경 투명도')
        self.opacity_slider.valueChanged.connect(self._change_opacity)
        header.addWidget(self.opacity_slider)
        self.pin = HeaderButton('pin', '항상 위에 표시')
        self.pin.setCheckable(True)
        self.pin.setToolTip('항상 위에 표시')
        self.pin.toggled.connect(self._pin)
        header.addWidget(self.pin)
        self.minimize_button = HeaderButton('minimize', '최소화')
        self.minimize_button.clicked.connect(self.showMinimized)
        header.addWidget(self.minimize_button)
        self.close_button = HeaderButton('close', '닫기')
        self.close_button.clicked.connect(self.close)
        header.addWidget(self.close_button)
        layout.addWidget(self.header)
        self.init_groups(layout)
        scroll = self.scroll = QtWidgets.QScrollArea()
        scroll.viewport().setAutoFillBackground(False)
        scroll.setWidgetResizable(True)
        self.body = QtWidgets.QWidget()
        self.body.setObjectName('toggleBody')
        self.rows = QtWidgets.QVBoxLayout(self.body)
        self.rows.setContentsMargins(0, 0, 0, 0)
        self.rows.setSpacing(8)
        self.rows.setAlignment(QtCore.Qt.AlignmentFlag.AlignTop)
        scroll.setWidget(self.body)
        scroll.verticalScrollBar().valueChanged.connect(self.update)
        layout.addWidget(scroll)
        footer = QtWidgets.QHBoxLayout()
        footer.setContentsMargins(0, 0, 0, 0)
        self.status_label = QtWidgets.QLabel()
        self.status_label.setStyleSheet("font-size:11px; font-weight:600; color:#bcd6c9;")
        footer.addWidget(self.status_label)
        footer.addStretch()
        self.lock_button = HeaderButton('lock', '잠금')
        self.lock_button.setObjectName('lockButton')
        self.lock_button.setCheckable(True)
        self.lock_button.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.lock_button.setToolTip('잠그면 버튼 외 영역의 클릭이 뒤의 게임으로 통과합니다')
        self.lock_button.toggled.connect(self.set_locked)
        footer.addWidget(self.lock_button)
        layout.addLayout(footer)
        self.resize_grips = [ResizeGrip(self, left, top) for left, top in
                             ((True, True), (False, True), (True, False), (False, False))]
        self.save_timer = QtCore.QTimer(self)
        self.save_timer.setSingleShot(True)
        self.save_timer.setInterval(300)
        self.save_timer.timeout.connect(self.save_state)
        self.signature = None
        self.timer = QtCore.QTimer(self)
        self.timer.setInterval(200)
        self.timer.timeout.connect(self.refresh)
        state = owner._state.get('quick_toggle', {})
        geometry = state.get('geometry')
        if geometry:
            self.restoreGeometry(QtCore.QByteArray.fromHex(geometry.encode()))
        self.pin.setChecked(bool(state.get('pinned', False)))
        self.opacity_slider.setValue(max(0, min(100, 100 - int(state.get('background_opacity', 100)))))
        self._change_opacity(self.opacity_slider.value())
        self.lock_button.setChecked(bool(state.get('locked', False)))
        self._ready = True

    def set_locked(self, locked):
        self.interaction_locked = locked
        self.edit_button.setEnabled(not locked)
        if locked and self.editing:
            self.set_editing(False)
        self.lock_button.setAccessibleName('잠금 해제' if locked else '잠금')
        self.lock_button.setToolTip('잠금 해제 · 클릭 통과 끄기' if locked
                                    else '잠금 · 버튼 외 영역의 클릭을 게임으로 통과')
        self.lock_button.update()
        self.header.offset = None
        self.header.setCursor(QtCore.Qt.CursorShape.ArrowCursor if locked else QtCore.Qt.CursorShape.SizeAllCursor)
        self.opacity_slider.setEnabled(not locked)
        for grip in self.resize_grips:
            grip.drag = None
            grip.setVisible(not locked)
        self.layout().activate()
        self.sync_clickthrough()
        self.schedule_save()

    def control_region(self):
        region = QtGui.QRegion()
        viewport = self.scroll.viewport()
        viewport_rect = QtCore.QRect(viewport.mapTo(self, QtCore.QPoint()), viewport.size())
        for button in self.findChildren(QtWidgets.QAbstractButton):
            if not button.isVisibleTo(self) or not button.isEnabled():
                continue
            rect = QtCore.QRect(button.mapTo(self, QtCore.QPoint()), button.size())
            if self.body.isAncestorOf(button):
                rect = rect.intersected(viewport_rect)
            region |= QtGui.QRegion(rect)
        return region

    def sync_clickthrough(self):
        if not self.interaction_locked:
            self.clearMask()
            if self.clickthrough_surface:
                self.clickthrough_surface.hide()
            self.update()
            return
        self.layout().activate()
        controls = self.control_region()
        if self.mask() != controls:
            self.setMask(controls)
        if not self.isVisible() or self.isMinimized():
            if self.clickthrough_surface:
                self.clickthrough_surface.hide()
            return
        if self.clickthrough_surface is None:
            self.clickthrough_surface = ClickThroughSurface(self)
        surface = self.clickthrough_surface
        pinned = bool(self.windowFlags() & QtCore.Qt.WindowType.WindowStaysOnTopHint)
        if bool(surface.windowFlags() & QtCore.Qt.WindowType.WindowStaysOnTopHint) != pinned:
            surface.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, pinned)
        surface.setGeometry(self.geometry())
        surface.setMask(QtGui.QRegion(self.rect()).subtracted(controls))
        surface.show()
        surface.update()

    def _pin(self, checked):
        visible = self.isVisible()
        self.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, checked)
        if visible:
            self.show()
        self.sync_clickthrough()
        self.schedule_save()

    def _change_opacity(self, value):
        self.background_opacity = 100 - value
        self.opacity_slider.setToolTip(f'배경 투명도 {value}% · 이름과 스위치는 선명하게 유지')
        self.update()
        self.sync_clickthrough()
        self.schedule_save()

    def schedule_save(self):
        if self._ready:
            self.save_timer.start()

    def paintEvent(self, event):
        p = QtGui.QPainter(self)
        p.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
        p.setCompositionMode(QtGui.QPainter.CompositionMode.CompositionMode_Source)
        p.fillRect(self.rect(), QtCore.Qt.GlobalColor.transparent)
        alpha = max(1, round(self.background_opacity * 255 / 100))

        def rounded(rect, fill, border, radius):
            color, line = QtGui.QColor(fill), QtGui.QColor(border)
            color.setAlpha(alpha)
            line.setAlpha(alpha)
            p.setBrush(color)
            p.setPen(QtGui.QPen(line, 1))
            p.drawRoundedRect(QtCore.QRectF(rect).adjusted(.5, .5, -.5, -.5), radius, radius)

        rounded(self.rect(), '#191e26', '#323b45', 12)
        if hasattr(self, 'scroll'):
            viewport = self.scroll.viewport()
            p.setClipRect(QtCore.QRect(viewport.mapTo(self, QtCore.QPoint()), viewport.size()))
            for card in self.body.findChildren(QtWidgets.QFrame, 'toggleRow'):
                if card.isVisible():
                    rounded(QtCore.QRect(card.mapTo(self, QtCore.QPoint()), card.size()),
                            '#27382f' if card.property('toggleState') == 'on' else '#202731',
                            '#45695c' if card.property('toggleState') == 'on' else '#202731', 8)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        for grip in getattr(self, 'resize_grips', []):
            grip.move(0 if grip.left else self.width() - grip.width(),
                      0 if grip.top else self.height() - grip.height())
            grip.raise_()
        self.schedule_save()
        if hasattr(self, 'lock_button'):
            self.sync_clickthrough()

    def moveEvent(self, event):
        super().moveEvent(event)
        if hasattr(self, 'lock_button'):
            self.sync_clickthrough()

    def entries(self):
        result = []
        for row in range(self.owner.macro_table.rowCount()):
            macro = self.owner._macro_from_row(row)
            if macro:
                for action, blocked in macro_actions(macro):
                    if action.quick_toggle_id:
                        result.append((row, action, blocked, macro.name))
        return result

    def refresh(self):
        self.refresh_groups()

    def showEvent(self, event):
        self.refresh()
        self.timer.start()
        super().showEvent(event)
        self.sync_clickthrough()

    def hideEvent(self, event):
        if self.clickthrough_surface:
            self.clickthrough_surface.hide()
        super().hideEvent(event)

    def save_state(self, visible=None):
        self.owner._update_state('quick_toggle', {
            'profiles': self.layouts,
            'geometry': bytes(self.saveGeometry().toHex()).decode(),
            'pinned': self.pin.isChecked(),
            'background_opacity': self.background_opacity,
            'locked': self.interaction_locked,
            'visible': self.isVisible() if visible is None else visible,
        })

    def closeEvent(self, event):
        self.timer.stop()
        self.save_timer.stop()
        if not self._app_closing:
            self.save_state(False)
        super().closeEvent(event)

    def prepare_app_close(self):
        self._app_closing = True
        self.save_timer.stop()
        self.timer.stop()
        self.save_state()

    def keyPressEvent(self, event):
        if event.key() == QtCore.Qt.Key.Key_Escape:
            self.close()
            return
        super().keyPressEvent(event)
