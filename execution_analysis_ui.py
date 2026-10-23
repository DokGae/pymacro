"""One measurement with explicit start/stop and a stable action table."""
from __future__ import annotations

import time
from PyQt6 import QtCore, QtGui, QtWidgets
from execution_analysis import row_explanation, selection_evidence
from condition_evidence import STATES

ROLE = QtCore.Qt.ItemDataRole.UserRole
INPUT_KINDS = {'press', 'down', 'up', 'mouse_click', 'mouse_down', 'mouse_up', 'mouse_wheel'}


def status_text(value):
    return {'action_start': '실행 시작', 'ok': '완료', 'branch_true': '조건 참 처리 완료',
            'branch_else': '조건 거짓 처리 완료', 'branch_elif': '다음 조건 분기 완료',
            'disabled': '비활성', 'skip_once': '첫 사이클 실행 제한으로 건너뜀',
            'external_unavailable': '외부값 수신 대기', 'error': '오류', 'sound_failed': '소리 재생 실패',
            'stopped': '중단', 'input': '입력 전송 성공', 'branch_enter': '분기 진입',
            'sleep': '대기 완료', 'label': '라벨 도달', 'goto': '라벨 이동',
            'return': '실행 반환', 'noop': '완료', 'continue': '다음 반복',
            'break': '반복 종료'}.get(value, value)


class ExecutionAnalysisDialog(QtWidgets.QDialog):
    def __init__(self, recorder, parent=None, *, start_measurement=None):
        super().__init__(parent)
        self.recorder = recorder
        self.start_measurement = start_measurement or recorder.start
        self._snapshot = None
        self._generation = None
        self._items, self._rows, self._roots = {}, {}, {}
        self._changing_flags = False
        self._displayed_condition = None
        self.setFont(QtGui.QFont('Malgun Gothic', 9))
        self.setWindowTitle('실행 분석')
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, False)
        self.resize(1050, 740)
        self.setStyleSheet('''
            QDialog {background:#f5f7fa; color:#24364e;}
            QLabel {color:#52647b;}
            QTreeWidget {background:white; border:1px solid #dbe3ed; border-radius:8px; outline:0;}
            QTreeWidget::item {padding:6px 3px; border:0;}
            QTreeWidget::item:selected {background:#d5f0ec; color:#164e47;}
            QHeaderView::section {background:#edf2f7; color:#51647a; padding:8px;
                border:0; border-bottom:1px solid #dbe3ed;}
            QPushButton {background:white; color:#42566f; padding:6px 14px;
                border:1px solid #cfd9e5; border-radius:6px;}
            QPushButton:hover {background:#edf3f9;}
            QPushButton:checked {background:#d5f0ec; color:#164e47; border-color:#9ccfc5;}
            QPushButton:disabled {color:#a3afbd; background:#f0f3f7; border-color:#e0e6ee;}
            QPushButton#startButton {background:#168575; color:white; border-color:#168575;}
            QPushButton#startButton:hover {background:#107363;}
            QToolButton#conditionDetailButton {background:transparent; color:#42566f;
                border:0; border-radius:5px; padding:5px 7px;}
            QToolButton#conditionDetailButton:hover {background:#e5edf6;}
            QToolButton#conditionDetailButton:checked {color:#168575;}
            QToolButton#conditionDetailButton:disabled {color:#9ca7b6;}
            QLineEdit {background:white; padding:7px 10px; border:1px solid #dbe3ed; border-radius:6px;}
            QPlainTextEdit {background:#edf3f9; color:#34526b; border:0; border-radius:8px; padding:10px;}
        ''')
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(16, 14, 16, 14)
        layout.setSpacing(10)
        toolbar = QtWidgets.QHBoxLayout()
        self.summary = QtWidgets.QLabel()
        self.summary.setTextFormat(QtCore.Qt.TextFormat.PlainText)
        self.summary.setWordWrap(True)
        toolbar.addWidget(self.summary, 1)
        self.start_button = QtWidgets.QPushButton('시작')
        self.start_button.setObjectName('startButton')
        self.start_button.setToolTip('이전 결과를 초기화하고 새로 측정합니다')
        self.start_button.clicked.connect(self._start)
        self.stop_button = QtWidgets.QPushButton('멈춤')
        self.stop_button.setToolTip('측정만 멈춥니다. 매크로 실행은 계속됩니다')
        self.stop_button.clicked.connect(self._stop)
        self.pin_button = QtWidgets.QPushButton('항상 위')
        self.pin_button.setCheckable(True)
        self.pin_button.toggled.connect(self._pin)
        for button in (self.start_button, self.stop_button, self.pin_button):
            button.setAutoDefault(False)
            toolbar.addWidget(button)
        layout.addLayout(toolbar)
        searchbar = QtWidgets.QHBoxLayout()
        self.search = QtWidgets.QLineEdit()
        self.search.setPlaceholderText('액션 이름 또는 키 검색')
        self.search.textChanged.connect(self._filter_rows)
        searchbar.addWidget(self.search, 1)
        self.hide_disabled = QtWidgets.QCheckBox('비활성 숨기기')
        self.hide_disabled.setChecked(True)
        self.hide_disabled.toggled.connect(self._filter_rows)
        searchbar.addWidget(self.hide_disabled)
        self.expand_all_button = QtWidgets.QPushButton('전체 펼치기')
        self.expand_all_button.setAutoDefault(False)
        self.expand_all_button.clicked.connect(lambda: self.tree.expandAll())
        searchbar.addWidget(self.expand_all_button)
        self.collapse_all_button = QtWidgets.QPushButton('전체 접기')
        self.collapse_all_button.setAutoDefault(False)
        self.collapse_all_button.clicked.connect(lambda: self.tree.collapseAll())
        searchbar.addWidget(self.collapse_all_button)
        layout.addLayout(searchbar)
        splitter = self.splitter = QtWidgets.QSplitter(QtCore.Qt.Orientation.Vertical)
        self.tree = QtWidgets.QTreeWidget()
        self.tree.setColumnCount(6)
        self.tree.setHeaderLabels(['순번', '액션', '도달', '조건 참 / 거짓', '입력', '상태'])
        self.tree.setTreePosition(1)
        self.tree.setUniformRowHeights(True)
        self.tree.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        for column, width in enumerate((58, 310, 80, 140, 80)):
            self.tree.setColumnWidth(column, width)
        for column in (0, 2, 3, 4, 5):
            self.tree.headerItem().setTextAlignment(column, QtCore.Qt.AlignmentFlag.AlignCenter)
        self.tree.header().setStretchLastSection(True)
        self.tree.currentItemChanged.connect(self._selection_changed)
        splitter.addWidget(self.tree)
        detail_panel = QtWidgets.QWidget()
        detail_layout = QtWidgets.QVBoxLayout(detail_panel)
        detail_layout.setContentsMargins(0, 0, 0, 0)
        detail_layout.setSpacing(6)
        self.detail = QtWidgets.QPlainTextEdit()
        self.detail.setReadOnly(True)
        self.detail.setMinimumHeight(110)
        detail_layout.addWidget(self.detail)
        self.condition_button = QtWidgets.QToolButton()
        self.condition_button.setObjectName('conditionDetailButton')
        self.condition_button.setText('조건 상세보기')
        self.condition_button.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.condition_button.setArrowType(QtCore.Qt.ArrowType.RightArrow)
        self.condition_button.setCheckable(True)
        self.condition_button.setEnabled(False)
        self.condition_button.toggled.connect(self._toggle_condition_detail)
        detail_layout.addWidget(self.condition_button, 0, QtCore.Qt.AlignmentFlag.AlignLeft)
        self.condition_panel = QtWidgets.QWidget()
        condition_layout = QtWidgets.QVBoxLayout(self.condition_panel)
        condition_layout.setContentsMargins(0, 0, 0, 0)
        self.condition_summary = QtWidgets.QLabel()
        self.condition_summary.setTextFormat(QtCore.Qt.TextFormat.PlainText)
        self.condition_summary.setWordWrap(True)
        condition_layout.addWidget(self.condition_summary)
        self.condition_tree = QtWidgets.QTreeWidget()
        self.condition_tree.setHeaderLabels(['조건', '결과', '검사 당시 값 / 기준', '설명'])
        self.condition_tree.setColumnWidth(0, 220)
        self.condition_tree.setColumnWidth(1, 75)
        self.condition_tree.setColumnWidth(2, 310)
        self.condition_tree.setMinimumHeight(150)
        self.condition_tree.headerItem().setTextAlignment(1, QtCore.Qt.AlignmentFlag.AlignCenter)
        condition_layout.addWidget(self.condition_tree)
        detail_layout.addWidget(self.condition_panel)
        self.condition_panel.hide()
        splitter.addWidget(detail_panel)
        splitter.setSizes([470, 140])
        layout.addWidget(splitter, 1)
        note = QtWidgets.QLabel('시작하면 이전 결과가 초기화됩니다. 창을 닫으면 측정과 결과를 지웁니다. '
                               '입력 횟수는 게임 내 발동 횟수와 다를 수 있습니다.')
        note.setWordWrap(True)
        note.setStyleSheet('font-size:11px; color:#8190a2;')
        layout.addWidget(note)
        self.timer = QtCore.QTimer(self)
        self.timer.setInterval(500)
        self.timer.timeout.connect(self.refresh)
        self.refresh()

    def _start(self):
        self.start_measurement()
        self.timer.start()
        self.refresh()

    def _stop(self):
        self.recorder.stop()
        self.timer.stop()
        self.refresh()

    def _pin(self, checked):
        visible = self.isVisible()
        self._changing_flags = True
        try:
            self.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, checked)
            if visible:
                self.show()
        finally:
            self._changing_flags = False

    def _clear_view(self):
        blocker = QtCore.QSignalBlocker(self.tree)
        self._items.clear()
        self._rows.clear()
        self._roots.clear()
        self._snapshot = None
        self._generation = None
        self._displayed_condition = None
        self.tree.clear()
        del blocker
        self.detail.setPlainText('시작을 누르고 매크로를 실행한 뒤, 확인할 IF나 액션을 선택하세요.')
        self.condition_tree.clear()
        self.condition_summary.clear()
        self.condition_button.setEnabled(False)
        self.condition_panel.hide()

    def refresh(self, *_):
        snapshot = self.recorder.snapshot()
        self.stop_button.setEnabled(self.recorder.enabled)
        if snapshot is None:
            self._clear_view()
            self.summary.setText('측정 대기 · 시작을 누르세요')
            return
        if snapshot['id'] != self._generation:
            self._clear_view()
            self._generation = snapshot['id']
        self._snapshot = snapshot
        seconds = max(0, int((snapshot['ended'] or time.monotonic()) - snapshot['started']))
        duration = f'{seconds // 60:02d}:{seconds % 60:02d}'
        if self.recorder.enabled:
            self.summary.setText(f'● 측정 중 · {duration}')
        else:
            self.summary.setText(f"측정 멈춤 · {duration}" +
                                 (f" · {snapshot['reason']}" if snapshot['reason'] != '측정 멈춤' else ''))
            self.timer.stop()
        # Add only new definitions; ordinary refreshes preserve selection, folds and scroll.
        blocker = QtCore.QSignalBlocker(self.tree)
        for key, macro in snapshot['macros'].items():
            if key not in self._roots:
                root = QtWidgets.QTreeWidgetItem(self.tree, ['', macro['name']])
                for column in (0, 2, 3, 4, 5):
                    root.setTextAlignment(column, QtCore.Qt.AlignmentFlag.AlignCenter)
                root.setExpanded(True)
                self._roots[key] = root
                for row in macro['rows']:
                    location = (key, row['path'])
                    parent = self._items.get((key, row['parent']), root)
                    item = QtWidgets.QTreeWidgetItem(parent,
                        [row['number'], row['label'] + (' (병렬)' if row['parallel'] else '')])
                    item.setData(0, ROLE, location)
                    item.setExpanded(True)
                    for col in (0, 2, 3, 4, 5):
                        item.setTextAlignment(col, QtCore.Qt.AlignmentFlag.AlignCenter)
                    self._items[location] = item
                    self._rows[location] = row
            by_path = {row['path']: row for row in macro['rows']}
            for row in macro['rows']:
                item = self._items[key, row['path']]
                counts = macro['counts'][row['path']]
                values = [f"{counts['reached']:,}",
                          f"{counts['true']:,} / {counts['false']:,}" if row['kind'] in ('if', 'elif') else '—',
                          f"{counts['inputs']:,}" if row['kind'] in INPUT_KINDS else '—',
                          row_explanation(row, macro, by_path)]
                if row['disabled']:
                    values[:3] = ['—', '—', '—']
                for col, value in enumerate(values, 2):
                    item.setText(col, value)
                item.setToolTip(5, '마지막 상태: ' + (status_text(counts['last']) or '아직 실행 기록 없음'))
        del blocker
        self._filter_rows()
        self._selection_changed()

    def _filter_rows(self, *_):
        if self._snapshot is None:
            return
        query = self.search.text().strip().lower()
        for location, item in self._items.items():
            row = self._rows[location]
            matches = not (self.hide_disabled.isChecked() and row['disabled'])
            matches = matches and (not query or query in row['label'].lower())
            item.setHidden(not matches)
        for item in self._items.values():
            if not item.isHidden():
                parent = item.parent()
                while parent:
                    parent.setHidden(False)
                    if query:
                        parent.setExpanded(True)
                    parent = parent.parent()
        for root in self._roots.values():
            root.setHidden(all(root.child(i).isHidden() for i in range(root.childCount())))

    def _selection_changed(self, *_):
        current = self.tree.currentItem()
        selected = current.data(0, ROLE) if current else None
        related, outputs = set(), set()
        if selected in self._rows and self._snapshot is not None:
            macro = self._snapshot['macros'][selected[0]]
            row = self._rows[selected]
            counts = macro['counts'][selected[1]]
            explanation, related, outputs = selection_evidence(row, macro)
            names = []
            node = current
            while node is not None:
                names.append(node.text(1))
                node = node.parent()
            text = ' → '.join(reversed(names)) + '\n\n' + explanation
            if counts['last']:
                text += '\n마지막 상태: ' + status_text(counts['last'])
            if counts['skipped']:
                text += f"\n실행 제한 또는 비활성으로 건너뜀 {counts['skipped']:,}회."
            if self.detail.toPlainText() != text:
                self.detail.setPlainText(text)
        elif self._snapshot is not None:
            self.detail.setPlainText('확인할 IF나 액션을 선택하면 실행 결과를 설명합니다.')
        self._update_condition_detail(selected)
        for location, item in self._items.items():
            row = self._rows[location]
            active = bool(selected and selected[0] == location[0] and location[1] in related)
            color = '#acb5c2' if row['disabled'] else '#245e54' if active else '#24364e'
            background = '#edf8f4' if active and not row['disabled'] else '#ffffff'
            for column in range(self.tree.columnCount()):
                item.setForeground(column, QtGui.QBrush(QtGui.QColor(color)))
                item.setBackground(column, QtGui.QBrush(QtGui.QColor(background)))

    def _toggle_condition_detail(self, checked):
        self.condition_button.setArrowType(QtCore.Qt.ArrowType.DownArrow if checked else QtCore.Qt.ArrowType.RightArrow)
        self._selection_changed()
        total = max(1, sum(self.splitter.sizes()))
        height = min(total, 330 if checked else 160)
        self.splitter.setSizes([max(120, total - height), height])

    def _update_condition_detail(self, selected):
        eligible = bool(selected in self._rows and self._rows[selected]['kind'] in ('if', 'elif'))
        self.condition_button.setEnabled(eligible)
        visible = eligible and self.condition_button.isChecked()
        self.condition_panel.setVisible(visible)
        if not visible:
            return
        counts = self._snapshot['macros'][selected[0]]['counts'][selected[1]]
        evidence = counts.get('condition_detail')
        signature = (selected, evidence)
        if signature == self._displayed_condition:
            return
        same_selection = self._displayed_condition is not None and self._displayed_condition[0] == selected
        self._displayed_condition = signature
        scroll = self.condition_tree.verticalScrollBar().value()
        old_states = {}
        def remember(item):
            old_states[item.data(0, ROLE)] = item.isExpanded()
            for i in range(item.childCount()):
                remember(item.child(i))
        if same_selection:
            for i in range(self.condition_tree.topLevelItemCount()):
                remember(self.condition_tree.topLevelItem(i))
        self.condition_tree.clear()
        if not evidence:
            self.condition_summary.setText('이 조건의 실제 검사 상세가 아직 없습니다. 측정을 시작한 뒤 해당 조건이 검사되면 표시됩니다.')
            return
        state = STATES.get(evidence['state'], evidence['state'])
        transition = ''
        if type(evidence['base_result']) is bool and type(evidence['result']) is bool and evidence['base_result'] != evidence['result']:
            transition = f" · 본 조건 {'참' if evidence['base_result'] else '거짓'} → 후속 조건 반영 후 {'참' if evidence['result'] else '거짓'}"
        elif evidence['state'] == 'unavailable' and type(evidence['result']) is bool:
            transition = f" · 실행 시 {'참' if evidence['result'] else '거짓'}으로 처리"
        self.condition_summary.setText(f'마지막 실제 검사: {state}{transition} · 검사 당시 값입니다. 다시 검사하지 않습니다.')
        colors = {'true': '#168575', 'false': '#bb4545', 'unavailable': '#a16f16',
                  'error': '#bb4545', 'disabled': '#9ca7b6', 'not_evaluated': '#8190a2'}
        def append(node, parent, path):
            actual = node['actual']
            criterion = node['criterion']
            item = QtWidgets.QTreeWidgetItem(parent,
                [node['name'], STATES.get(node['state'], node['state']),
                 f'{actual} / {criterion}' if criterion else actual, node['reason']])
            item.setData(0, ROLE, path)
            item.setTextAlignment(1, QtCore.Qt.AlignmentFlag.AlignCenter)
            base_text = '참' if node['base_result'] is True else '거짓' if node['base_result'] is False else '판정 없음'
            result_text = '참' if node['result'] is True else '거짓' if node['result'] is False else '판정 없음'
            item.setToolTip(1, f'본 조건: {base_text} / 후속 조건 반영 결과: {result_text}')
            item.setForeground(1, QtGui.QBrush(QtGui.QColor(colors.get(node['state'], '#52647b'))))
            item.setExpanded(old_states.get(path, True))
            for column in (0, 2, 3):
                item.setToolTip(column, item.text(column))
            for index, child in enumerate(node['children']):
                append(child, item, path + ('children', index))
            for field, title in (('on_true', '참일 때 후속 조건 · 하나 이상 충족'),
                                 ('on_false', '거짓일 때 후속 조건 · 하나 이상 충족')):
                if node[field]:
                    group = QtWidgets.QTreeWidgetItem(item, [title])
                    group_path = path + (field,)
                    group.setData(0, ROLE, group_path)
                    group.setExpanded(old_states.get(group_path, True))
                    for index, child in enumerate(node[field]):
                        append(child, group, group_path + (index,))
        append(evidence, self.condition_tree, ())
        self.condition_tree.verticalScrollBar().setValue(scroll)

    def showEvent(self, event):
        super().showEvent(event)
        if self.recorder.enabled:
            self.timer.start()
        self.refresh()

    def _discard(self):
        self.timer.stop()
        self.recorder.clear()
        self.refresh()

    def closeEvent(self, event):
        self._discard()
        super().closeEvent(event)

    def hideEvent(self, event):
        if not self._changing_flags and not self.isMinimized() and not event.spontaneous():
            self._discard()
        super().hideEvent(event)

    def reject(self):
        self._discard()
        super().reject()
