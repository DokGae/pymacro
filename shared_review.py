"""Review direct settings before linking selected occurrences."""
import copy
import json

from PyQt6 import QtCore, QtWidgets
from lib.shared_settings import at_path, walk_conditions, register, expand_condition, REF

ROLE = QtCore.Qt.ItemDataRole.UserRole


def candidates(macros, entries, matching_key, partial=False):
    groups = {}
    existing = {}
    for ref, entry in entries.items():
        try:
            existing.setdefault(matching_key(expand_condition(entry['condition'], entries)), ref)
        except ValueError:
            continue
    for index, macro in enumerate(macros):
        for path, labels, condition in walk_conditions(macro):
            if condition.get('shared_ref'):
                continue
            location = {'macro': index, 'path': path, 'label': ' → '.join(labels) or str(path)}
            try:
                key = matching_key(condition)
            except ValueError:
                continue
            group = groups.setdefault(('condition', key), {'kind': 'condition', 'data': condition, 'uses': [], 'existing': existing.get(key)})
            group['uses'].append(location)
            if partial and condition.get('type') == 'pixel':
                for field in ('region', 'color'):
                    value = condition.get(field)
                    if value is None or (isinstance(value, str) and REF.search(value)):
                        continue
                    if field == 'color' and condition.get('pixel_pattern'):
                        continue
                    value = json.loads(key).get(field, value)
                    signature = json.dumps(value, sort_keys=True)
                    group = groups.setdefault((field, signature), {'kind': field, 'data': value, 'uses': [], 'existing': None})
                    group['uses'].append(location)
    return [g for g in groups.values() if len(g['uses']) > 1 or g['existing']]


class ReviewDialog(QtWidgets.QDialog):
    def __init__(self, controller):
        super().__init__(controller.owner)
        self.controller = controller
        self.setWindowTitle('공용화 검토')
        self.setModal(False)
        self.resize(960, 680)
        layout = QtWidgets.QVBoxLayout(self)
        bar = QtWidgets.QHBoxLayout()
        self.scope = QtWidgets.QComboBox()
        self.scope.addItem('프로필 전체', -1)
        for index, macro in enumerate(controller.preview_macros()):
            self.scope.addItem(macro.get('name') or f'이름 없는 매크로 {index + 1}', index)
        current = controller.macro_editor_row if controller.macro_editor is not None else controller.owner.macro_table.currentRow()
        self.scope.setCurrentIndex(max(0, self.scope.findData(current)))
        self.partial = QtWidgets.QCheckBox('일부 설정도 찾기 (영역·색상)')
        refresh = QtWidgets.QPushButton('다시 검토')
        for widget in (self.scope, self.partial, refresh):
            bar.addWidget(widget)
        layout.addLayout(bar)
        self.summary = QtWidgets.QLabel()
        layout.addWidget(self.summary)
        self.table = QtWidgets.QTableWidget(0, 3)
        self.table.setHorizontalHeaderLabels(['공용화 후보', '위치 수', '설정'])
        self.table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        self.table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.horizontalHeader().setSectionResizeMode(QtWidgets.QHeaderView.ResizeMode.Stretch)
        layout.addWidget(self.table)
        layout.addWidget(QtWidgets.QLabel('연결할 위치를 체크하세요. 더블클릭하면 해당 매크로의 조건을 엽니다.'))
        self.locations = QtWidgets.QListWidget()
        layout.addWidget(self.locations)
        self.name = QtWidgets.QLineEdit()
        self.name.setPlaceholderText('새 공용 이름')
        layout.addWidget(self.name)
        self.apply_button = QtWidgets.QPushButton('선택한 위치 연결')
        layout.addWidget(self.apply_button)
        self.table.itemSelectionChanged.connect(self.select_group)
        self.locations.itemDoubleClicked.connect(self.open_location)
        self.locations.itemChanged.connect(self.update_button)
        self.apply_button.clicked.connect(self.apply_group)
        self.scope.currentIndexChanged.connect(self.scan)
        self.partial.toggled.connect(self.scan)
        refresh.clicked.connect(self.scan)
        self.scan()

    def scan(self):
        c = self.controller
        self.baseline = c.snapshot()
        self.macros = c.preview_macros()
        current = self.scope.currentData()
        self.scope.blockSignals(True)
        self.scope.clear()
        self.scope.addItem('프로필 전체', -1)
        for index, macro in enumerate(self.macros):
            self.scope.addItem(macro.get('name') or f'이름 없는 매크로 {index + 1}', index)
        self.scope.setCurrentIndex(max(0, self.scope.findData(current)))
        self.scope.blockSignals(False)
        current = self.scope.currentData()
        self.groups = candidates(self.macros, c.entries, c.matching_key, self.partial.isChecked())
        if current != -1:
            for group in self.groups:
                group['uses'] = [u for u in group['uses'] if u['macro'] == current]
            self.groups = [g for g in self.groups if len(g['uses']) > 1 or (g['uses'] and g['existing'])]
        self.table.setRowCount(0)
        for group in self.groups:
            row = self.table.rowCount()
            self.table.insertRow(row)
            title = ('기존 공용에 연결: ' + c.entries[group['existing']]['name']) if group['existing'] else {
                'condition': '동일 조건 · 공용 감지/묶음', 'region': '반복 영역 · 영역만 공용화', 'color': '반복 색상 · 색상만 공용화'}[group['kind']]
            from shared_ui import brief
            detail = brief(group['data']) if group['kind'] == 'condition' else str(group['data'])
            for col, text in enumerate((title, str(len(group['uses'])), detail)):
                self.table.setItem(row, col, QtWidgets.QTableWidgetItem(text))
        self.summary.setText(f'공용화 후보 {len(self.groups)}개 · 이미 연결된 조건 제외 · 후보별 연결 후 다시 검토합니다.')
        self.select_group()
        if self.groups:
            self.table.selectRow(0)

    def select_group(self):
        self.locations.clear()
        row = self.table.currentRow()
        if not 0 <= row < len(self.groups):
            self.apply_button.setEnabled(False)
            return
        group = self.groups[row]
        for use in group['uses']:
            item = QtWidgets.QListWidgetItem(f"#{use['macro'] + 1} {use['label']}  [{'/'.join(map(str, use['path']))}]")
            item.setData(ROLE, use)
            item.setCheckState(QtCore.Qt.CheckState.Checked)
            self.locations.addItem(item)
        ref = group['existing']
        self.name.setText(self.controller.entries[ref]['name'] if ref else (group['data'].get('name', '') if isinstance(group['data'], dict) else ''))
        self.name.setEnabled(not ref)
        self.update_button()

    def update_button(self):
        count = sum(self.locations.item(i).checkState() == QtCore.Qt.CheckState.Checked for i in range(self.locations.count()))
        self.apply_button.setEnabled(count > 0)
        self.apply_button.setText(f'{count}곳 연결 · 변경 적용 전까지 취소 가능')

    def open_location(self, item):
        c = self.controller
        use = item.data(ROLE)
        if c.preview_macros() != self.macros:
            c.error('매크로가 변경되었습니다. 다시 검토하세요.')
            return
        if c.macro_editor is not None:
            if c.macro_editor_row != use['macro']:
                c.error('현재 매크로 편집을 완료한 뒤 다른 매크로를 여세요.')
                return
            from shared_ui import navigate_usage
            navigate_usage(c.macro_editor, use['path'], self.macros[use['macro']])
        else:
            c.owner.macro_table.selectRow(use['macro'])
            c.owner._edit_macro(usage_path=use['path'])

    def apply_group(self):
        c = self.controller
        if c.macro_editor is not None:
            c.error('열려 있는 매크로 편집을 완료한 뒤 다시 검토하고 연결하세요.')
            return
        if c.snapshot() != self.baseline:
            c.error('검토 이후 설정이 변경되었습니다. 다시 검토하세요.')
            return
        row = self.table.currentRow()
        if not 0 <= row < len(self.groups):
            return
        group = self.groups[row]
        name = self.name.text().strip()
        if not name:
            c.error('공용 이름을 입력하세요.')
            return
        kind = group['kind']
        if kind != 'condition' and (any(ch.isspace() or ch in '/{}@$' for ch in name) or any(v['name'] == name for v in c.owner._variable_items[kind])):
            c.error('사용할 수 없거나 중복된 이름입니다.')
            return
        uses = [self.locations.item(i).data(ROLE) for i in range(self.locations.count()) if self.locations.item(i).checkState() == QtCore.Qt.CheckState.Checked]
        if not uses:
            return
        before = c.snapshot()
        macros = copy.deepcopy(self.macros)
        if kind == 'condition':
            reference = group['existing'] or register(c.entries, name, group['data'])
            for use in uses:
                at_path(macros[use['macro']], use['path'])['shared_ref'] = reference
        else:
            value = group['data']
            if isinstance(value, (list, tuple)):
                value = ','.join(map(str, value)) if kind == 'region' else ''.join(f'{v:02x}' for v in value)
            c.owner._ensure_variable(kind, name, str(value))
            for use in uses:
                at_path(macros[use['macro']], use['path'])[kind] = '${' + name + '}'
        try:
            c.restore_macros(macros)
        except Exception as exc:
            c.owner.profile.shared_settings, original_macros, c.owner._variable_items = before
            c.restore_macros(original_macros)
            c.error(str(exc))
            return
        c.commit(before, f'{name} · {len(uses)}곳 공용 연결')
        self.scan()
