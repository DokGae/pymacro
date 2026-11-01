"""Dark control presentation for the main window only."""
from PyQt6 import QtCore, QtGui, QtWidgets

THEME = dict(is_dark=True, panel_bg='#1b222c', panel_alt_bg='#222d39', panel_border='#303a49',
             badge_bg='#202c32', button_bg='#222d39', button_border='#3b4a5c',
             button_text='#edf1f7', text='#edf1f7')


def build_status(window):
    frame = QtWidgets.QFrame()
    frame.setObjectName('statusStrip')
    row = QtWidgets.QHBoxLayout(frame)
    row.setContentsMargins(20, 16, 20, 16)
    row.setSpacing(18)
    column = QtWidgets.QVBoxLayout()
    caption = QtWidgets.QLabel('ENGINE STATUS')
    caption.setStyleSheet('color:#93a3b6;font-size:10px;letter-spacing:1px;')
    column.addWidget(caption)
    window.running_label = QtWidgets.QLabel('정지')
    window.running_label.setMinimumWidth(98)
    column.addWidget(window.running_label)
    row.addLayout(column)
    window._status_badge_style = 'border:0;background:transparent;padding:3px 0;font-size:12px;'
    for attr, title in [('active_label', '활성 상태'), ('paused_label', '시스템'),
                        ('admin_label', '실행 권한'), ('hardware_label', '입력 방식')]:
        column = QtWidgets.QVBoxLayout()
        label = QtWidgets.QLabel(title)
        label.setStyleSheet('color:#93a3b6;font-size:10px;')
        column.addWidget(label)
        value = QtWidgets.QLabel('확인 중')
        value.setStyleSheet(window._status_badge_style)
        setattr(window, attr, value)
        column.addWidget(value)
        row.addLayout(column)
    window.capture_label = QtWidgets.QLabel()
    window.capture_label.hide()
    row.addWidget(window.capture_label)
    row.addStretch()
    window.log_toggle_btn = QtWidgets.QToolButton()
    window.log_toggle_btn.setText('로그 기록')
    window.log_toggle_btn.setCheckable(True)
    window.log_toggle_btn.setChecked(window._log_enabled)
    window.log_toggle_btn.toggled.connect(window._toggle_log_enabled)
    row.addWidget(window.log_toggle_btn)
    window.active_toggle_btn = QtWidgets.QPushButton()
    window.active_toggle_btn.setCheckable(True)
    window.active_toggle_btn.setFixedSize(132, 40)
    window.active_toggle_btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
    window.active_toggle_btn.setToolTip('매크로 트리거 감지를 켜거나 끕니다.')
    row.addWidget(window.active_toggle_btn)
    window.apply_btn = QtWidgets.QPushButton('적용', frame)
    window.apply_btn.hide()
    window._apply_btn_default_style = ''
    window._apply_btn_working_style = 'background:#203d36;color:#77dbbc;'
    window._apply_flash_timer = QtCore.QTimer(window)
    window._apply_flash_timer.setSingleShot(True)
    window._apply_flash_timer.timeout.connect(lambda: window.apply_btn.setStyleSheet(''))
    window._set_engine_active_toggle(False)
    return frame


def apply_main_design(window):
    central = window.centralWidget()
    central.setObjectName('darkMain')
    central.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)
    central.layout().setContentsMargins(22, 16, 22, 12)
    central.layout().setSpacing(16)
    heading = QtWidgets.QHBoxLayout()
    window.main_profile_title = QtWidgets.QLabel('새 프로필')
    window.main_profile_title.setStyleSheet('font-size:22px;font-weight:700;color:#edf1f7;padding:2px 0;')
    window.profile_path_label = QtWidgets.QLabel('')
    window.profile_path_label.setStyleSheet('font-size:11px;color:#93a3b6;')
    window.profile_path_label.setMinimumWidth(0)
    window.profile_path_label.setSizePolicy(QtWidgets.QSizePolicy.Policy.Ignored, QtWidgets.QSizePolicy.Policy.Preferred)
    heading.addWidget(window.main_profile_title)
    heading.addWidget(window.profile_path_label, 1)
    for text, callback in [('빠른 토글', window._open_quick_toggle), ('입력장치 설정', window._open_keyboard_settings)]:
        button = QtWidgets.QPushButton(text)
        button.clicked.connect(callback)
        heading.addWidget(button)
    central.layout().insertLayout(0, heading)
    central.layout().setStretch(0, 0)
    central.layout().setStretch(1, 0)
    central.layout().setStretch(2, 1)
    # Scoped selectors keep other editor windows' established presentation.
    central.setStyleSheet('''
        QWidget#darkMain {background:#12171e;color:#edf1f7; font-size:12px;}
        #darkMain QLabel {color:#edf1f7;background:transparent;}
        #darkMain QFrame#statusStrip {background:qlineargradient(x1:0,y1:0,x2:1,y2:0,stop:0 #1c302b,stop:0.65 #1b222c);border:1px solid #345247;border-radius:10px;}
        #darkMain QFrame#profileStrip {background:#1b222c;border:1px solid #303a49;border-radius:10px;}
        #darkMain QGroupBox {color:#edf1f7;background:#1b222c;border:1px solid #303a49;border-radius:10px;margin-top:12px;padding:14px 10px 10px;}
        #darkMain QGroupBox::title {subcontrol-origin:margin;left:17px;padding:0 7px;color:#c4d2e2;}
        #darkMain QPushButton,#darkMain QToolButton {color:#dce7f3;background:#222d39;border:1px solid #3b4a5c;border-radius:6px;padding:6px 10px;}
        #darkMain QPushButton:hover,#darkMain QToolButton:hover {background:#2e3f4e;border-color:#658577;}
        #darkMain QPushButton:disabled,#darkMain QToolButton:disabled {color:#718195;background:#202833;border-color:#303a49;}
        #darkMain QToolButton:checked {background:#203d36;color:#77dbbc;}
        #darkMain QTableWidget {background:#1b222c;alternate-background-color:#202935;color:#edf1f7;border:0;gridline-color:#303a49;selection-background-color:#203d36;selection-color:#edf1f7;outline:0;}
        #darkMain QTableWidget::item {padding:7px;border:0;border-bottom:1px solid #303a49;}
        #darkMain QTableWidget::item:selected {background:#203d36;color:#edf1f7;}
        #darkMain QHeaderView::section {background:#202935;color:#aebed0;border:0;border-bottom:1px solid #3b4a5c;padding:11px 9px;font-weight:500;}
        #darkMain QTableCornerButton::section {background:#202935;border:0;}
        #darkMain QListWidget {background:#1b222c;color:#dce7f3;border:0;outline:0;}
        #darkMain QPlainTextEdit,#darkMain QTextEdit {background:#161e28;color:#bfcecf;border:1px solid #303a49;border-radius:6px;}
        #darkMain QScrollBar:vertical {background:#18212b;width:9px;}
        #darkMain QScrollBar::handle:vertical {background:#3d5062;border-radius:4px;min-height:24px;}
        #darkMain QScrollBar::add-line:vertical,#darkMain QScrollBar::sub-line:vertical {height:0;}
        #darkMain QSplitter::handle {background:#12171e;height:8px;}
    ''')
    window.menuBar().setStyleSheet('''
        QMenuBar {background:#12171e;color:#afbdce;padding:7px 16px;font-size:12px;font-weight:400;}
        QMenuBar::item,QMenuBar::item:selected,QMenuBar::item:pressed {
            font-size:12px;font-weight:400;padding:6px 12px;margin:0 3px;
            border:1px solid transparent;border-radius:5px;background:transparent;
        }
        QMenuBar::item:selected {background:#253b35;color:#a1eed5;}
        QMenuBar::item:pressed {background:#203d36;color:#a1eed5;}
        QMenu {background:#1b222c;color:#edf1f7;border:1px solid #3b4a5c;font-size:12px;font-weight:400;}
        QMenu::item,QMenu::item:selected {padding:7px 24px;border:0;font-size:12px;font-weight:400;}
        QMenu::item:selected {background:#203d36;}
    ''')
    window.statusBar().setStyleSheet('QStatusBar{background:#12171e;color:#93a3b6;border:0;}')
    table = window.macro_table
    table.setShowGrid(False)
    table.verticalHeader().setDefaultSectionSize(43)
    table.horizontalHeader().setDefaultAlignment(QtCore.Qt.AlignmentFlag.AlignLeft | QtCore.Qt.AlignmentFlag.AlignVCenter)
    table.setFont(QtGui.QFont('Malgun Gothic', 10))
    window.add_macro_btn.setStyleSheet('background:#37b997;color:#102e26;border:1px solid #37b997;font-weight:600;')
