"""Searchable list of built-in, custom and observed unknown effect codes."""
from functools import lru_cache
from PyQt6.QtCore import Qt, QSize, QRect, QEvent, QAbstractTableModel, QSortFilterProxyModel, pyqtSignal
from PyQt6.QtGui import QColor, QIcon, QPixmap,QPalette
from packetcore.icons import effect_icon
from effect_drafts import DraftCatalog
from PyQt6.QtWidgets import (QDialog, QVBoxLayout, QHBoxLayout, QLabel, QLineEdit,
    QPushButton, QComboBox, QTableView, QHeaderView, QMessageBox, QCheckBox, QColorDialog, QSpinBox,
    QStyledItemDelegate,QStyle,QStyleOptionViewItem,QWidget)


class EffectColorDialog(QColorDialog):
    def __init__(self,color,parent=None):
        super().__init__(color,parent)
        self.setWindowTitle('효과 색상 선택')
        self.setOption(QColorDialog.ColorDialogOption.DontUseNativeDialog,True)
        self.clear_color=False
        self.html_edit=self.findChild(QLineEdit,'qt_colorname_lineedit')
        if self.html_edit is not None:
            self.html_edit.disconnect()
            self.html_edit.setValidator(None)
            self.html_edit.textEdited.connect(self.html_edited)
        self.currentColorChanged.connect(self.color_changed)

    def html_edited(self,text):
        self.clear_color=not text.strip()
        if text.strip():
            color=QColor(text.strip())
            if color.isValid():self.setCurrentColor(color)

    def color_changed(self,color):
        self.clear_color=False
        if self.html_edit is not None:self.html_edit.setText(color.name())

    @classmethod
    def choose(cls,color,parent):
        dialog=cls(color,parent)
        if dialog.exec()!=QDialog.DialogCode.Accepted:return None
        if dialog.clear_color or (dialog.html_edit is not None and not dialog.html_edit.text().strip()):return ''
        return dialog.currentColor().name().upper()


class CenteredCellDelegate(QStyledItemDelegate):
    def createEditor(self,parent,option,index):
        if index.column()==11:
            editor=QSpinBox(parent);editor.setRange(0,9999);return editor
        if index.column()==12:
            editor=QComboBox(parent);editor.addItem('이미지','image');editor.addItem('색상','color');return editor
        return super().createEditor(parent,option,index)

    def setEditorData(self,editor,index):
        if index.column()==11:
            editor.setValue(int(index.data() or 0) if index.data()!='없음' else 0);return
        if index.column()==12:
            editor.setCurrentIndex(1 if index.data()=='색상' else 0);return
        super().setEditorData(editor,index)

    def setModelData(self,editor,model,index):
        if index.column()==11:model.setData(index,editor.value());return
        if index.column()==12:model.setData(index,editor.currentData());return
        super().setModelData(editor,model,index)
    def check_rect(self,option):
        style=option.widget.style()
        width=style.pixelMetric(QStyle.PixelMetric.PM_IndicatorWidth,None,option.widget)
        height=style.pixelMetric(QStyle.PixelMetric.PM_IndicatorHeight,None,option.widget)
        return QRect(option.rect.center().x()-width//2,option.rect.center().y()-height//2,width,height)

    def paint(self,painter,option,index):
        item=QStyleOptionViewItem(option);self.initStyleOption(item,index)
        if index.data(Qt.ItemDataRole.BackgroundRole) is not None:item.state &= ~QStyle.StateFlag.State_Selected
        check=index.data(Qt.ItemDataRole.CheckStateRole)
        if check is None:
            if not item.icon.isNull():
                icon=item.icon;text=item.text
                item.features &= ~(QStyleOptionViewItem.ViewItemFeature.HasDecoration|QStyleOptionViewItem.ViewItemFeature.HasDisplay)
                item.icon=QIcon();item.text=''
                item.widget.style().drawControl(QStyle.ControlElement.CE_ItemViewItem,item,painter,item.widget)
                size=min(item.decorationSize.width(),item.rect.height()-4)
                text=item.fontMetrics.elidedText(text,Qt.TextElideMode.ElideRight,max(0,item.rect.width()-size-10))
                width=size+(4+item.fontMetrics.horizontalAdvance(text) if text else 0)
                left=item.rect.x()+(item.rect.width()-width)//2
                icon.paint(painter,QRect(left,item.rect.y()+(item.rect.height()-size)//2,size,size))
                painter.save();painter.setFont(item.font)
                role=QPalette.ColorRole.HighlightedText if item.state & QStyle.StateFlag.State_Selected else QPalette.ColorRole.Text
                painter.setPen(item.palette.color(role))
                painter.drawText(QRect(left+size+4,item.rect.y(),max(0,width-size-4),item.rect.height()),Qt.AlignmentFlag.AlignCenter,text)
                painter.restore();return
            super().paint(painter,item,index);return
        item.features &= ~QStyleOptionViewItem.ViewItemFeature.HasCheckIndicator
        item.widget.style().drawControl(QStyle.ControlElement.CE_ItemViewItem,item,painter,item.widget)
        item.rect=self.check_rect(item)
        item.state &= ~(QStyle.StateFlag.State_On|QStyle.StateFlag.State_Off|QStyle.StateFlag.State_NoChange)
        item.state |= QStyle.StateFlag.State_On if check==Qt.CheckState.Checked else QStyle.StateFlag.State_Off
        item.widget.style().drawPrimitive(QStyle.PrimitiveElement.PE_IndicatorItemViewItemCheck,item,painter,item.widget)

    def editorEvent(self,event,model,option,index):
        if not index.flags() & Qt.ItemFlag.ItemIsEnabled:return False
        check=index.data(Qt.ItemDataRole.CheckStateRole)
        if check is None:return super().editorEvent(event,model,option,index)
        if event.type()==QEvent.Type.MouseButtonRelease:
            if event.button()!=Qt.MouseButton.LeftButton or not self.check_rect(option).contains(event.position().toPoint()):return False
        elif event.type()==QEvent.Type.KeyPress:
            if event.key() not in (Qt.Key.Key_Space,Qt.Key.Key_Select):return False
        else:return False
        return model.setData(index,Qt.CheckState.Unchecked if check==Qt.CheckState.Checked else Qt.CheckState.Checked,Qt.ItemDataRole.CheckStateRole)


@lru_cache(maxsize=1200)
def effect_thumbnail(path):
    return QIcon(path)


class EffectModel(QAbstractTableModel):
    headers = ['★', '효과 코드', '표시 이름', '기본 이름', '등록 상태', '종류', '표시', '나', '대상', '색상', '시간', '순위', '방식', '음성', '통신']
    previewChanged = pyqtSignal()
    invalid = pyqtSignal(str)

    def __init__(self, catalog, observed, parent=None):
        super().__init__(parent); self.catalog = catalog; self.observed = set(observed)
        self.rows = []; self.refresh()

    def refresh(self):
        self.beginResetModel()
        codes = set(self.catalog.entries) | set(self.catalog.overrides) | set(self.catalog.preview) | set(map(str,self.observed))
        self.rows = []
        for code in sorted(codes, key=lambda code: (1,code) if code.startswith('attack:') else (0,int(code))):
            original = self.catalog.entries.get(str(code), {})
            custom = str(code) in self.catalog.overrides
            status = '사용자 지정' if custom else ('기본 등록' if original else '미등록')
            kind = {'BUFF': '버프', 'DEBUFF': '디버프', 'PASSIVE': '패시브', 'ATTACK': '공격 판정'}.get(original.get('Type'), '미분류')
            self.rows.append([code, self.catalog.name(code), original.get('Name', ''), status, kind])
        self.endResetModel()

    def rowCount(self, parent=None): return len(self.rows) if parent is None or not parent.isValid() else 0
    def columnCount(self, parent=None): return len(self.headers)

    def data(self, index, role=Qt.ItemDataRole.DisplayRole):
        if not index.isValid(): return None
        if role==Qt.ItemDataRole.TextAlignmentRole:return Qt.AlignmentFlag.AlignCenter
        code=str(self.rows[index.row()][0])
        if role==Qt.ItemDataRole.EditRole and index.column()==2:return self.catalog.name(code)
        preview = self.catalog.preview.get(code, {})
        if index.column()==9 and preview.get('color'):
            color=QColor(preview['color'])
            if role==Qt.ItemDataRole.BackgroundRole:return color
            if role==Qt.ItemDataRole.ForegroundRole:
                luminance=0.2126*color.redF()+0.7152*color.greenF()+0.0722*color.blueF()
                return QColor('#000000' if luminance>0.55 else '#FFFFFF')
        if role==Qt.ItemDataRole.BackgroundRole and isinstance(self.catalog,DraftCatalog) and index.column() in self.catalog.dirty_columns(code):return QColor('#FFF1A8')
        preview = self.catalog.preview.get(str(self.rows[index.row()][0]), {})
        if index.column() == 2 and role == Qt.ItemDataRole.DecorationRole:
            icon=effect_icon(self.rows[index.row()][0])
            return effect_thumbnail(icon) if icon else None
        if index.column()==14:
            if role==Qt.ItemDataRole.CheckStateRole:return Qt.CheckState.Checked if preview.get('tcp_enabled',False) else Qt.CheckState.Unchecked
            if role==Qt.ItemDataRole.ToolTipRole:return '통신 전송 켜기 / 끄기 · 전체 변경 저장을 눌러 적용하세요.'
            return None
        if index.column()==13:
            if role==Qt.ItemDataRole.DisplayRole:return '켜짐' if preview.get('speech_enabled') else '꺼짐'
            if role==Qt.ItemDataRole.ToolTipRole:return '음성 알림 탭에서 문구·대상·시점을 설정하세요.'
            return None
        if index.column() == 12:
            if role == Qt.ItemDataRole.DisplayRole: return '색상' if preview.get('display_mode','image') == 'color' else '이미지'
            if role == Qt.ItemDataRole.ToolTipRole: return '더블 클릭하여 변경한 뒤 전체 변경 저장을 누르세요. 이미지가 없으면 색상으로 표시합니다.'
            return None
        if index.column() == 0:
            if role == Qt.ItemDataRole.DisplayRole: return '★' if preview.get('favorite',False) else '☆'
            if role == Qt.ItemDataRole.ForegroundRole: return QColor('#B8860B' if preview.get('favorite',False) else '#87917F')
            if role == Qt.ItemDataRole.TextAlignmentRole: return Qt.AlignmentFlag.AlignCenter
            if role == Qt.ItemDataRole.ToolTipRole: return '클릭하여 즐겨찾기 등록 / 해제'
            return None
        column = index.column()-1
        if column in (5,6,7,9):
            if role == Qt.ItemDataRole.CheckStateRole:
                field = {5:'enabled',6:'own',7:'target',9:'remaining_time'}[column]
                return Qt.CheckState.Checked if preview.get(field,field in ('own','target')) else Qt.CheckState.Unchecked
            return None
        if column == 10:
            if role == Qt.ItemDataRole.DisplayRole: return preview.get('priority',0) or '없음'
            return None
        if column == 8:
            if role == Qt.ItemDataRole.DisplayRole: return preview.get('color') or '—'
            return None
        if index.isValid() and role in (Qt.ItemDataRole.DisplayRole, Qt.ItemDataRole.ToolTipRole):
            return str(self.rows[index.row()][column])

    def flags(self, index):
        flags = super().flags(index)
        if index.isValid() and index.column() in (7,8):
            code=str(self.rows[index.row()][0])
            if not self.catalog.preview.get(code,{}).get('enabled',False):
                return flags & ~Qt.ItemFlag.ItemIsEnabled
        if index.isValid() and index.column()==14:flags |= Qt.ItemFlag.ItemIsUserCheckable
        if index.isValid() and index.column()-1 in (5,6,7,9): flags |= Qt.ItemFlag.ItemIsUserCheckable
        if index.isValid() and index.column() in (2,11,12):flags |= Qt.ItemFlag.ItemIsEditable
        return flags

    def setData(self, index, value, role=Qt.ItemDataRole.EditRole):
        if not index.isValid():return False
        if index.column() in (7,8) and not self.flags(index) & Qt.ItemFlag.ItemIsEnabled:return False
        if index.column()==14 and role==Qt.ItemDataRole.CheckStateRole:
            code=self.rows[index.row()][0];preview=self.catalog.preview.get(str(code),{})
            try:
                self.catalog.save_effect(code,self.catalog.overrides.get(str(code),''),preview.get('color',''),preview.get('enabled',False),
                    tcp=dict(tcp_enabled=value in (Qt.CheckState.Checked,Qt.CheckState.Checked.value)))
            except (ValueError,OSError) as exc:self.invalid.emit(str(exc));return False
            self.dataChanged.emit(index,index,[role]);self.previewChanged.emit();return True
        if role==Qt.ItemDataRole.EditRole and index.column() in (2,11,12):
            code=self.rows[index.row()][0];preview=self.catalog.preview.get(str(code),{})
            try:
                if index.column()==2:self.catalog.save_name(code,str(value))
                else:self.catalog.set_preview(code,preview.get('color',''),preview.get('enabled',False),**({'priority':int(value)} if index.column()==11 else {'display_mode':str(value)}))
            except (ValueError,OSError) as exc:self.invalid.emit(str(exc));return False
            self.refresh();self.previewChanged.emit();return True
        if index.column()-1 not in (5,6,7,9) or role != Qt.ItemDataRole.CheckStateRole:return False
        column = index.column()-1
        code = self.rows[index.row()][0]; preview = self.catalog.preview.get(str(code), {})
        try:
            flags = dict(enabled=preview.get('enabled',False),own=preview.get('own',True),target=preview.get('target',True),remaining_time=preview.get('remaining_time',False))
            flags[{5:'enabled',6:'own',7:'target',9:'remaining_time'}[column]] = value in (Qt.CheckState.Checked, Qt.CheckState.Checked.value)
            self.catalog.set_preview(code, preview.get('color',''), **flags)
        except (ValueError,OSError) as exc:
            self.invalid.emit(str(exc)); return False
        self.dataChanged.emit(self.index(index.row(),6),self.index(index.row(),10),[role]); self.previewChanged.emit(); return True

    def headerData(self, section, orientation, role=Qt.ItemDataRole.DisplayRole):
        if orientation==Qt.Orientation.Horizontal and role==Qt.ItemDataRole.TextAlignmentRole:return Qt.AlignmentFlag.AlignCenter
        if orientation==Qt.Orientation.Horizontal and role==Qt.ItemDataRole.ToolTipRole:
            return {6:'작은 모니터에 표시',7:'내 캐릭터 효과 표시',8:'현재 공격 대상 효과 표시',10:'남은시간 표시',11:'표시 우선순위',12:'이미지 / 색상 표시 방식'}.get(section,self.headers[section])
        if orientation == Qt.Orientation.Horizontal and role == Qt.ItemDataRole.DisplayRole:
            return self.headers[section]


class EffectFilter(QSortFilterProxyModel):
    status = '전체'

    def lessThan(self, left, right):
        model = self.sourceModel()
        def sort_key(index):
            code = str(model.rows[index.row()][0])
            preview = model.catalog.preview.get(code, {})
            code_key = (1, code) if code.startswith('attack:') else (0, int(code))
            column = index.column()
            flags = {0:'favorite',6:'enabled',7:'own',8:'target',10:'remaining_time',13:'speech_enabled',14:'tcp_enabled'}
            if column == 1:return code_key
            if column in flags:
                value = bool(preview.get(flags[column], column in (7,8)))
            elif column == 11:value = preview.get('priority',0)
            else:value = str(index.data(Qt.ItemDataRole.DisplayRole) or '').casefold()
            return (value, code_key)
        return sort_key(left) < sort_key(right)

    def filterAcceptsRow(self, row, parent):
        model = self.sourceModel()
        code = str(model.rows[row][0])
        matches = (self.status == '전체' or model.rows[row][3] == self.status
            or (self.status == '작은 모니터 표시' and model.catalog.preview.get(code,{}).get('enabled'))
            or (self.status == '즐겨찾기' and model.catalog.preview.get(code,{}).get('favorite',False))
            or (self.status == '통신 전송' and model.catalog.preview.get(code,{}).get('tcp_enabled',False))
            or (self.status == '공격 판정' and model.rows[row][4] == '공격 판정'))
        return matches and super().filterAcceptsRow(row, parent)


class EffectManager(QDialog):
    changed = pyqtSignal()
    speechPreview = pyqtSignal(str)
    monitorPreview = pyqtSignal(object)
    tcpPreview = pyqtSignal(object)

    def __init__(self, catalog, observed=(), parent=None):
        super().__init__(parent);self.drafts={};self._loading=True;self.form_snapshot=None
        self.catalog=self.draft_for(catalog)
        self.setWindowTitle('효과 코드 관리'); self.resize(950, 650)
        layout = QVBoxLayout(self)
        layout.addWidget(QLabel('등록된 효과 코드를 선택해 이름을 수정하거나, 새 코드와 이름을 입력해 저장하세요.'))
        search_bar = QHBoxLayout(); layout.addLayout(search_bar)
        self.search = QLineEdit(); self.search.setPlaceholderText('코드 또는 이름 검색')
        search_bar.addWidget(self.search)
        self.category = QComboBox(); self.category.addItems(['전체', '즐겨찾기', '통신 전송', '사용자 지정', '기본 등록', '미등록', '작은 모니터 표시', '공격 판정'])
        search_bar.addWidget(self.category)
        self.model = EffectModel(self.catalog, observed, self)
        self.model.previewChanged.connect(self.preview_toggled)
        self.model.invalid.connect(lambda message: self.note.set_status(message,'error'))
        self.proxy = EffectFilter(self); self.proxy.setSourceModel(self.model)
        self.proxy.setFilterKeyColumn(-1); self.proxy.setFilterCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        self.table = QTableView(); self.table.setModel(self.proxy)
        self.table.setSortingEnabled(True)
        self.table.sortByColumn(1,Qt.SortOrder.AscendingOrder)
        self.table.setItemDelegate(CenteredCellDelegate(self.table))
        self.table.setIconSize(QSize(20,20))
        self.table.setEditTriggers(QTableView.EditTrigger.DoubleClicked | QTableView.EditTrigger.EditKeyPressed)
        self.table.setSelectionBehavior(QTableView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QTableView.SelectionMode.SingleSelection)
        header=self.table.horizontalHeader();header.setDefaultAlignment(Qt.AlignmentFlag.AlignCenter)
        header.setMinimumSectionSize(28);header.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        for column in (2,3):header.setSectionResizeMode(column,QHeaderView.ResizeMode.Stretch)
        for column,width in ((0,32),(1,76),(4,80),(5,62),(6,38),(7,32),(8,38),(9,82),(10,38),(11,48),(12,54),(13,48),(14,48)):
            header.setSectionResizeMode(column,QHeaderView.ResizeMode.Fixed);self.table.setColumnWidth(column,width)
        self.table.clicked.connect(self.cell_clicked)
        self.table.verticalHeader().hide(); layout.addWidget(self.table)
        self.table.selectionModel().currentRowChanged.connect(self.select_row)
        self.search.textChanged.connect(self.search_changed); self.category.currentTextChanged.connect(self.category_changed)
        form = QHBoxLayout(); layout.addLayout(form)
        form.addWidget(QLabel('효과 코드'))
        self.code = QLineEdit(); self.code.setPlaceholderText('예: 10014'); self.code.setMaximumWidth(170); form.addWidget(self.code)
        form.addWidget(QLabel('표시 이름'))
        self.name = QLineEdit(); self.name.setMaxLength(120); form.addWidget(self.name)
        self.restore_button = QPushButton('초기화'); self.restore_button.setToolTip('표시 이름을 기본 이름으로 되돌립니다.')
        self.restore_button.clicked.connect(self.restore); form.addWidget(self.restore_button)
        display = QHBoxLayout(); layout.addLayout(display)
        display.addWidget(QLabel('표시 방식'))
        self.display_mode = QComboBox(); self.display_mode.addItem('효과 이미지 (기본)','image'); self.display_mode.addItem('색상 네모','color')
        display.addWidget(self.display_mode)
        self.icon_preview = QLabel(); self.icon_preview.setFixedSize(28,28); display.addWidget(self.icon_preview)
        self.icon_note = QLabel(); display.addWidget(self.icon_note,1)
        self.display_mode.currentIndexChanged.connect(self.update_effect_icon)
        self.code.textChanged.connect(self.update_effect_icon)
        appearance = QHBoxLayout(); layout.addLayout(appearance)
        self.preview_check = QCheckBox('작은 모니터에 표시'); appearance.addWidget(self.preview_check)
        self.own_check = QCheckBox('나'); self.own_check.setChecked(True); appearance.addWidget(self.own_check)
        self.target_check = QCheckBox('대상'); self.target_check.setChecked(True); appearance.addWidget(self.target_check)
        self.own_check.setEnabled(False);self.target_check.setEnabled(False)
        self.preview_check.toggled.connect(self.own_check.setEnabled)
        self.preview_check.toggled.connect(self.target_check.setEnabled)
        self.color = QLineEdit(); self.color.setPlaceholderText('색상 HEX · FE2B2B'); self.color.setMaxLength(7)
        self.color.setMaximumWidth(180); appearance.addWidget(self.color)
        self.swatch = QLabel(); self.swatch.setFixedSize(24,24); appearance.addWidget(self.swatch)
        self.color.textChanged.connect(self.update_swatch)
        self.pick_color = QPushButton('색상 선택'); self.pick_color.clicked.connect(self.choose_color); appearance.addWidget(self.pick_color)
        self.clear_color = QPushButton('색상 해제'); self.clear_color.clicked.connect(self.reset_color); appearance.addWidget(self.clear_color)
        appearance.addStretch()
        color_note = QLabel('같은 색상 지정 가능 · 나/대상 각각에서 같은 색상은 가장 최근 효과 하나로 덮어 표시합니다.')
        color_note.setStyleSheet('font-size:11px;color:#687181;')
        color_note.setWordWrap(True)
        layout.addWidget(color_note)
        self.color.setToolTip(color_note.text())
        self.pick_color.setToolTip(color_note.text())
        timing = QHBoxLayout(); layout.addLayout(timing)
        self.remaining_check = QCheckBox('남은시간 표시'); timing.addWidget(self.remaining_check)
        self.remaining_check.setToolTip('남은 시간이 5초 이하일 때 네모 중앙에 5~1을 표시합니다.')
        timing.addWidget(QLabel('우선순위'))
        self.priority = QSpinBox(); self.priority.setRange(0,9999); self.priority.setSpecialValueText('없음')
        timing.addWidget(self.priority); timing.addWidget(QLabel('1부터 앞쪽 표시 · 같은 순위는 효과 코드순')); timing.addStretch()
        voice = QHBoxLayout(); layout.addLayout(voice)
        self.speech_check=QCheckBox('음성 알림'); voice.addWidget(self.speech_check)
        self.speech_scope=QComboBox();self.speech_scope.addItem('나만','own');self.speech_scope.addItem('대상만','target');self.speech_scope.addItem('둘 다','both');self.speech_scope.setCurrentIndex(2)
        self.speech_scope.setToolTip('음성 알림 대상 · 미리보기 표시 설정과 별도로 적용됩니다.');voice.addWidget(self.speech_scope)
        self.speech_event=QComboBox(); self.speech_event.addItem('종료 전 / 종료','ending'); self.speech_event.addItem('적용될 때','start'); voice.addWidget(self.speech_event)
        self.speech_seconds=QSpinBox(); self.speech_seconds.setRange(0,300); self.speech_seconds.setValue(3); self.speech_seconds.setSuffix(' 초 전'); self.speech_seconds.setSpecialValueText('종료될 때'); voice.addWidget(self.speech_seconds)
        self.speech_event.currentIndexChanged.connect(lambda: self.speech_seconds.setEnabled(self.speech_event.currentData()=='ending'))
        self.speech_time=QCheckBox('남은 시간도 읽기'); voice.addWidget(self.speech_time); voice.addStretch()
        phrase=QHBoxLayout(); layout.addLayout(phrase); phrase.addWidget(QLabel('읽을 문구'))
        self.speech_text=QLineEdit(); self.speech_text.setMaxLength(240); self.speech_text.setPlaceholderText('비우면 효과 이름을 읽습니다. 예: 낙인 다시 넣으세요'); phrase.addWidget(self.speech_text,1)
        test=QPushButton('미리 듣기'); test.clicked.connect(self.preview_speech); phrase.addWidget(test)
        tcp_row=QHBoxLayout();layout.addLayout(tcp_row)
        self.tcp_check=QCheckBox('통신으로 전송');self.tcp_check.setChecked(False);tcp_row.addWidget(self.tcp_check)
        self.tcp_scope=QComboBox();self.tcp_scope.addItem('나만','own');self.tcp_scope.addItem('대상만','target');self.tcp_scope.addItem('둘 다','both');self.tcp_scope.setCurrentIndex(2);tcp_row.addWidget(self.tcp_scope)
        self.tcp_mode=QComboBox();self.tcp_mode.addItem('나 / 대상 각각 설정',True);self.tcp_mode.addItem('공통 내용 사용',False);tcp_row.addWidget(self.tcp_mode)
        self.tcp_test_toggle=QPushButton('전송 테스트');self.tcp_test_toggle.setCheckable(True);tcp_row.addWidget(self.tcp_test_toggle)
        tcp_row.addStretch()
        tcp_values=QHBoxLayout();layout.addLayout(tcp_values);self.tcp_common_row=tcp_values
        tcp_values.addWidget(QLabel('내용 이름'))
        self.tcp_name=QLineEdit();self.tcp_name.setMaxLength(120);self.tcp_name.setPlaceholderText('예: 수호의축복 · 비우면 효과 코드');tcp_values.addWidget(self.tcp_name,2)
        tcp_values.addWidget(QLabel('켜짐 값'));self.tcp_on=QLineEdit('true');self.tcp_on.setMaxLength(120);tcp_values.addWidget(self.tcp_on)
        tcp_values.addWidget(QLabel('꺼짐 값'));self.tcp_off=QLineEdit('false');self.tcp_off.setMaxLength(120);tcp_values.addWidget(self.tcp_off)
        tcp_roles=QVBoxLayout();layout.addLayout(tcp_roles);self.tcp_role_controls={};self.tcp_role_rows={}
        for role,title,prefix in (('own','나','내효과.'),('target','대상','대상효과.')):
            row=QHBoxLayout();tcp_roles.addLayout(row);self.tcp_role_rows[role]=row
            row.addWidget(QLabel(title));row.addWidget(QLabel('내용 이름'))
            name=QLineEdit();name.setMaxLength(120);name.setPlaceholderText('예: '+title+'.수호의축복 · 비우면 '+prefix+'효과코드');row.addWidget(name,2)
            row.addWidget(QLabel('켜짐 값'));on=QLineEdit('true');on.setMaxLength(120);row.addWidget(on)
            row.addWidget(QLabel('꺼짐 값'));off=QLineEdit('false');off.setMaxLength(120);row.addWidget(off)
            self.tcp_role_controls[role]=(name,on,off)
        tcp_help=QHBoxLayout();layout.addLayout(tcp_help)
        tcp_tip=QLabel('내용 이름은 나와 대상을 서로 다르게 입력하세요. 켜짐 / 꺼짐 값에는 참·거짓, 숫자 또는 문구를 입력할 수 있습니다.')
        tcp_tip.setWordWrap(True);tcp_help.addWidget(tcp_tip)
        self.tcp_test_panel=QWidget();test_row=QHBoxLayout(self.tcp_test_panel);test_row.setContentsMargins(0,0,0,0)
        self.tcp_test_target=QComboBox();test_row.addWidget(self.tcp_test_target)
        self.tcp_test_state=QComboBox();self.tcp_test_state.addItem('켜짐 값',True);self.tcp_test_state.addItem('꺼짐 값',False);test_row.addWidget(self.tcp_test_state)
        send=QPushButton('5초 전송');send.clicked.connect(lambda:self.preview_tcp(self.tcp_test_state.currentData(),self.tcp_test_target.currentData()));test_row.addWidget(send)
        stop=QPushButton('중지');stop.clicked.connect(lambda:self.tcpPreview.emit(None));test_row.addWidget(stop)
        note=QLabel('실제 통신으로 보내며, 5초 후 감지 상태로 돌아갑니다.');note.setWordWrap(True);test_row.addWidget(note,1)
        tcp_test=QHBoxLayout();layout.addLayout(tcp_test);tcp_test.addWidget(self.tcp_test_panel)
        self.tcp_test_toggle.toggled.connect(self.sync_tcp_fields)
        actions = QHBoxLayout(); layout.addLayout(actions)
        self.new_button = QPushButton('새 코드 등록'); self.new_button.clicked.connect(self.new_entry); actions.addWidget(self.new_button)
        self.save_button = QPushButton('전체 변경 저장'); self.save_button.clicked.connect(self.save); actions.addWidget(self.save_button)
        self.discard_button=QPushButton('변경 취소');self.discard_button.clicked.connect(self.discard_changes);actions.addWidget(self.discard_button)
        self.preview_button=QPushButton('미리 표시');self.preview_button.clicked.connect(self.show_monitor_preview);actions.addWidget(self.preview_button)
        self.preview_stop_button=QPushButton('미리 표시 해제');self.preview_stop_button.clicked.connect(lambda:self.monitorPreview.emit(None));actions.addWidget(self.preview_stop_button)
        close = QPushButton('닫기'); close.clicked.connect(self.accept); actions.addWidget(close)
        from status_label import StatusLabel
        self.note = StatusLabel(''); self.note.setWordWrap(True); layout.addWidget(self.note)
        self.count = QLabel(); layout.addWidget(self.count); self.update_count()
        if catalog.load_error: self.note.setText('설정 읽기 실패: ' + catalog.load_error)
        self.setting_rows={'display':(display,appearance,timing),'speech':(voice,phrase),'tcp':(tcp_row,tcp_values,tcp_roles,tcp_help,tcp_test)}
        self._settings_section=None
        self.sync_tcp_fields()
        self.update_swatch()
        self.update_effect_icon()
        self._loading=False;self.form_snapshot=self.form_values()
        for control in (self.preview_check,self.own_check,self.target_check,self.remaining_check,self.speech_check,self.speech_time):control.toggled.connect(self.stage_form)
        for control in (self.priority,self.speech_seconds):control.valueChanged.connect(self.stage_form)
        for control in (self.display_mode,self.speech_event,self.speech_scope):control.currentIndexChanged.connect(self.stage_form)
        for control in (self.name,self.color,self.speech_text):control.textEdited.connect(self.stage_form)
        self.tcp_check.toggled.connect(self.stage_form);self.tcp_scope.currentIndexChanged.connect(self.sync_tcp_fields);self.tcp_scope.currentIndexChanged.connect(self.stage_form)
        self.tcp_mode.currentIndexChanged.connect(self.sync_tcp_fields);self.tcp_mode.currentIndexChanged.connect(self.stage_form)
        for control in (self.tcp_name,self.tcp_on,self.tcp_off):control.textEdited.connect(self.stage_form)
        for controls in self.tcp_role_controls.values():
            for control in controls:control.textEdited.connect(self.stage_form)

    @staticmethod
    def set_layout_visible(row,visible):
        for i in range(row.count()):
            item=row.itemAt(i)
            if item.widget() is not None:item.widget().setVisible(visible)
            elif item.layout() is not None:EffectManager.set_layout_visible(item.layout(),visible)

    def select_settings_section(self,section):
        self._settings_section=section
        for name,rows in self.setting_rows.items():
            for row in rows:self.set_layout_visible(row,name==section)
        self.sync_tcp_fields()

    def update_effect_icon(self):
        icon=effect_icon(self.code.text().strip())
        if icon:
            self.icon_preview.setPixmap(QPixmap(icon).scaled(28,28,Qt.AspectRatioMode.KeepAspectRatio,Qt.TransformationMode.SmoothTransformation))
        else: self.icon_preview.clear()
        if self.display_mode.currentData() == 'color':
            self.icon_note.setText('지정한 색상 네모로 표시합니다.')
        elif icon: self.icon_note.setText('효과 이미지로 표시합니다. 색상은 지정하지 않아도 됩니다.')
        else: self.icon_note.setText('연결된 이미지 없음 · 지정한 색상으로 표시합니다. 색상이 없으면 회색으로 표시합니다.')

    def toggle_favorite(self,index):
        if index.column()!=0: return
        source=self.proxy.mapToSource(index)
        code=str(self.model.rows[source.row()][0])
        try:
            self.catalog.set_favorite(code,not self.catalog.preview.get(code,{}).get('favorite',False))
        except (ValueError,OSError) as exc:
            self.note.set_status(str(exc),'error'); return
        self.model.dataChanged.emit(source,source)
        self.proxy.invalidateFilter();self.update_count()

    def update_swatch(self):
        try: color = self.catalog.parse_color(self.color.text())
        except ValueError: color = ''
        self.swatch.setStyleSheet(f'background:{color or "#252B36"};border:1px solid #687181;border-radius:4px;')

    def choose_color(self):
        try: current = self.catalog.parse_color(self.color.text())
        except ValueError: current = ''
        color = EffectColorDialog.choose(QColor(current or '#FE2B2B'),self)
        if color == '':self.reset_color()
        elif color is not None:
            self.color.setText(color);self.stage_form()

    def reset_color(self):
        self.color.clear()
        if self.display_mode.currentData() == 'color': self.display_mode.setCurrentIndex(0)
        if hasattr(self,'form_snapshot'):self.stage_form()

    def preview_toggled(self):
        self.proxy.invalidateFilter();self.update_count()
        current = self.table.currentIndex()
        if current.isValid(): self.select_row(current,current)

    def update_count(self):
        pending=sum(len(d.dirty_codes()) for d in self.drafts.values())
        self.count.setText(f'저장 전 변경 {pending}개 · 전체 {len(self.model.rows):,}개 · 검색 결과 {self.proxy.rowCount():,}개 · 사용자 지정 {len(self.catalog.overrides):,}개')

    def search_changed(self, text):
        self.proxy.setFilterFixedString(text); self.update_count()

    def category_changed(self, status):
        self.proxy.status = status; self.proxy.invalidateFilter(); self.update_count()

    def select_row(self, current, previous):
        if not current.isValid():return
        if self._loading:return
        selected_code=self.model.rows[self.proxy.mapToSource(current).row()][0]
        if not self.stage_form():return
        self._loading=True
        row = next(row for row in self.model.rows if row[0]==selected_code)
        self.code.setText(str(row[0]))
        self.name.setText(row[1] if row[3] != '미등록' else '')
        preview = self.catalog.preview.get(str(row[0]),{})
        self.color.setText(preview.get('color','')); self.preview_check.setChecked(preview.get('enabled',False))
        self.own_check.setChecked(preview.get('own',True)); self.target_check.setChecked(preview.get('target',True))
        self.remaining_check.setChecked(preview.get('remaining_time',False)); self.priority.setValue(preview.get('priority',0))
        self.display_mode.setCurrentIndex(self.display_mode.findData(preview.get('display_mode','image')))
        self.load_speech(preview)
        self.load_tcp(preview)
        self.update_effect_icon()
        self.note.setText(f'{row[3]} · 기본 이름: {row[2] or "없음"}')
        self.form_snapshot=self.form_values();self._loading=False

    def new_entry(self):
        self.stage_form();self._loading=True
        self.table.clearSelection(); self.table.setCurrentIndex(self.proxy.index(-1, -1))
        self.code.clear(); self.name.clear(); self.code.setFocus()
        self.reset_color()
        self.preview_check.setChecked(False); self.display_mode.setCurrentIndex(0)
        self.remaining_check.setChecked(False); self.priority.setValue(0)
        self.load_speech({})
        self.load_tcp({})
        self.own_check.setChecked(True); self.target_check.setChecked(True)
        self.note.setText('새 코드와 표시 이름을 입력하세요. 변경 사항은 전체 변경 저장으로 한 번에 저장합니다.')
        self.form_snapshot=self.form_values();self._loading=False

    def tcp_settings(self):
        result=dict(tcp_enabled=self.tcp_check.isChecked(),tcp_scope=self.tcp_scope.currentData(),
                    tcp_separate=self.tcp_mode.currentData(),tcp_name=self.tcp_name.text().strip(),
                    tcp_on=self.tcp_on.text().strip(),tcp_off=self.tcp_off.text().strip())
        for role,controls in self.tcp_role_controls.items():
            for field,control in zip(('name','on','off'),controls):result['tcp_'+role+'_'+field]=control.text().strip()
        return result

    def sync_tcp_fields(self,*_):
        separate=self.tcp_mode.currentData()
        visible=getattr(self,'_settings_section',None) in (None,'tcp')
        self.set_layout_visible(self.tcp_common_row,visible and not separate)
        scope=self.tcp_scope.currentData()
        for role,row in self.tcp_role_rows.items():
            self.set_layout_visible(row,visible and separate and scope in ('both',role))
        previous=self.tcp_test_target.currentData()
        self.tcp_test_target.clear()
        if separate:
            if scope=='both':self.tcp_test_target.addItem('나 + 대상',None)
            for role,title in (('own','나'),('target','대상')):
                if scope in ('both',role):self.tcp_test_target.addItem(title,role)
        else:self.tcp_test_target.addItem('공통 내용',None)
        self.tcp_test_target.setCurrentIndex(max(0,self.tcp_test_target.findData(previous)))
        self.tcp_test_panel.setVisible(visible and self.tcp_test_toggle.isChecked())

    def preview_tcp(self,on,role=None):
        try:
            config=self.tcp_settings();self.catalog.validate_tcp(config)
            code=self.code.text().strip()
            if not code.isdecimal():raise ValueError('숫자 효과 코드를 입력하세요.')
            channels=self.catalog.tcp_channels(str(int(code)),config)
            values={}
            for roles,name,on_value,off_value in channels:
                if role is not None and role not in roles:continue
                if name in ('게임연결','내캐릭터','대상이름','대상감지'):raise ValueError('기본 상태 이름은 미리 전송 이름으로 사용할 수 없습니다.')
                if name in values:raise ValueError('나와 대상의 내용 이름을 서로 다르게 입력하세요.')
                values[name]=self.catalog.tcp_value(on_value if on else off_value)
            self.note.setText('미리 전송 시작 · 5초 후 실제 감지 상태로 돌아갑니다.')
            self.tcpPreview.emit(values)
        except ValueError as exc:self.note.setText('미리 전송 실패: '+str(exc))

    def load_tcp(self,config):
        self.tcp_check.setChecked(config.get('tcp_enabled',False))
        self.tcp_scope.setCurrentIndex(self.tcp_scope.findData(config.get('tcp_scope','both')))
        legacy=any(key in config for key in ('tcp_name','tcp_on','tcp_off'))
        self.tcp_mode.setCurrentIndex(self.tcp_mode.findData(config.get('tcp_separate',not legacy)))
        self.tcp_name.setText(config.get('tcp_name',''));self.tcp_on.setText(config.get('tcp_on','true'));self.tcp_off.setText(config.get('tcp_off','false'))
        for role,controls in self.tcp_role_controls.items():
            for field,default,control in zip(('name','on','off'),('','true','false'),controls):control.setText(config.get('tcp_'+role+'_'+field,default))
        self.sync_tcp_fields()

    def speech_settings(self):
        return dict(speech_scope=self.speech_scope.currentData(),speech_enabled=self.speech_check.isChecked(),speech_event=self.speech_event.currentData(),
                    speech_seconds=self.speech_seconds.value(),speech_text=self.speech_text.text().strip(),
                    speech_include_time=self.speech_time.isChecked())

    def load_speech(self,config):
        self.speech_check.setChecked(config.get('speech_enabled',False))
        scope=config.get('speech_scope','both' if config.get('own',True) and config.get('target',True) else ('own' if config.get('own',True) else 'target'))
        self.speech_scope.setCurrentIndex(self.speech_scope.findData(scope))
        self.speech_event.setCurrentIndex(self.speech_event.findData(config.get('speech_event','ending')))
        self.speech_seconds.setValue(config.get('speech_seconds',3))
        self.speech_text.setText(config.get('speech_text',''))
        self.speech_time.setChecked(config.get('speech_include_time',False))

    def preview_speech(self):
        text=self.speech_text.text().strip() or self.name.text().strip() or '음성 안내 테스트'
        if self.speech_time.isChecked() and self.speech_event.currentData()=='ending' and self.speech_seconds.value():
            text+=f', {self.speech_seconds.value()}초'
        self.speechPreview.emit(text)

    def draft_for(self,catalog):
        key=str(catalog.overrides_path)
        if key not in self.drafts:self.drafts[key]=DraftCatalog(catalog)
        return self.drafts[key]

    def bind_catalog(self,catalog):
        self.stage_form();self._loading=True
        self.catalog=self.draft_for(catalog);self.model.catalog=self.catalog
        self.model.refresh();self.new_entry();self.update_count()

    def form_values(self):
        return (self.code.text().strip(),self.name.text(),self.color.text(),self.preview_check.isChecked(),
                self.own_check.isChecked(),self.target_check.isChecked(),self.remaining_check.isChecked(),
                self.priority.value(),self.display_mode.currentData(),tuple(self.speech_settings().items()),tuple(self.tcp_settings().items()))

    def stage_form(self,*args):
        if self._loading:return True
        values=self.form_values()
        if values==self.form_snapshot or not values[0]:return True
        if not values[2].strip() and values[8]=='color':
            self._loading=True
            self.display_mode.setCurrentIndex(0)
            self._loading=False
            values=self.form_values()
        try:
            code=self.catalog.parse_code(values[0]);name=values[1].strip()
            # Keep a built-in name inherited unless the user actually renamed it.
            if name==self.catalog.entries.get(str(code),{}).get('Name') and str(code) not in self.catalog.overrides:name=''
            self.catalog.save_effect(code,name,*values[2:9],speech=dict(values[9]),tcp=dict(values[10]))
            self.form_snapshot=values
            current=self.table.currentIndex();self.model.refresh()
            if current.isValid():
                row=next((i for i,r in enumerate(self.model.rows) if str(r[0])==str(code)),None)
                if row is not None:
                    self._loading=True;self.table.setCurrentIndex(self.proxy.mapFromSource(self.model.index(row,1)));self._loading=False
            self.update_count();self.note.setText('변경을 임시로 반영했습니다. 전체 변경 저장을 누르면 적용됩니다.')
            return True
        except (ValueError,OSError) as exc:
            self.note.set_status(str(exc),'error');return False

    def show_monitor_preview(self):
        if not self.code.text().strip():
            self.note.set_status('미리 표시할 효과를 먼저 선택하세요.','error');return
        if not self.stage_form():return
        code=str(self.catalog.parse_code(self.code.text()))
        config=self.catalog.preview.get(code,{})
        if not config.get('own',True) and not config.get('target',True):
            self.note.set_status('미리 표시할 위치를 나 또는 대상에서 선택하세요.','error');return
        self.monitorPreview.emit(dict(code=code,name=self.catalog.name(code),config=dict(config)))
        self.note.setText('선택한 효과를 모니터에 고정 표시합니다. 캡처 후 미리 표시 해제를 누르세요.')

    def has_pending_changes(self):
        self.stage_form()
        return any(d.dirty_codes() for d in self.drafts.values()) or self.form_values()!=self.form_snapshot

    def save(self):
        return self.save_all()

    def save_all(self):
        if not self.stage_form():return False
        try:
            count=sum(len(d.dirty_codes()) for d in self.drafts.values())
            for draft in self.drafts.values():
                self.catalog.validate_settings(dict(version=1,names=draft.overrides,preview=draft.preview))
            for draft in self.drafts.values():draft.commit()
            self.model.refresh();self.update_count();self.changed.emit()
            self.note.setText(f'변경한 효과 {count}개를 모두 저장했습니다.')
            return True
        except (ValueError,OSError) as exc:
            self.note.set_status('저장 실패: '+str(exc),'error')
            QMessageBox.warning(self,'저장 실패',str(exc));return False

    def discard_changes(self):
        self._loading=True
        for draft in self.drafts.values():draft.discard()
        self.form_snapshot=None;self.model.refresh();self.new_entry();self.update_count()
        self.note.setText('저장 전 변경을 모두 취소했습니다.')

    def cell_clicked(self,index):
        if index.column()==9:
            code=self.model.rows[self.proxy.mapToSource(index).row()][0]
            prior=self.catalog.preview.get(str(code),{})
            color=EffectColorDialog.choose(QColor(prior.get('color') or '#FE2B2B'),self)
            if color is not None:
                try:self.catalog.set_preview(code,color,prior.get('enabled',False),display_mode='image' if not color else prior.get('display_mode','image'))
                except (ValueError,OSError) as exc:self.note.set_status(str(exc),'error');return
                self._loading=True
                self.model.refresh();self.update_count()
                self.color.setText(color)
                if not color:self.display_mode.setCurrentIndex(0)
                row=next((i for i,r in enumerate(self.model.rows) if str(r[0])==str(code)),None)
                if row is not None:self.table.setCurrentIndex(self.proxy.mapFromSource(self.model.index(row,9)))
                self.form_snapshot=self.form_values();self._loading=False
        else:self.toggle_favorite(index)

    def restore(self):
        try:
            code=self.catalog.parse_code(self.code.text());self.catalog.remove_name(code)
            self._loading=True;self.name.setText(self.catalog.name(code));self.form_snapshot=self.form_values();self._loading=False
            self.model.refresh();self.update_count()
            self.note.setText('표시 이름을 기본 이름으로 초기화했습니다. 전체 변경 저장을 눌러 적용하세요.')
        except (ValueError,OSError) as exc:
            self.note.set_status('표시 이름 초기화 실패: '+str(exc),'error')
            QMessageBox.warning(self,'표시 이름 초기화 실패',str(exc))
