"""Common-settings workspace, inline condition links, and viewer picking."""
import copy
import json
import weakref
from PyQt6 import QtCore, QtGui, QtWidgets
from lib.shared_settings import (
    at_path, condition_usages, definition, dependencies, duplicate_groups,
    expand_condition, fingerprint, register, variable_usages, walk_conditions, rename_value,
)
from lib.pattern_packs import pattern_label

ROLE = QtCore.Qt.ItemDataRole.UserRole
KINDS = {'region': '위치·영역', 'color': '색상', 'key': '키', 'sleep': '시간', 'var': '실행 상태'}


def controller_for(widget):
    while widget is not None:
        if hasattr(widget, '_shared_controller'):
            return widget._shared_controller
        widget = widget.parentWidget()
    return None


def brief(data):
    if data.get('type') == 'pixel':
        color = data.get('color')
        if isinstance(color, (tuple, list)):
            color = ''.join(f'{c:02x}' for c in color)
        return f"{data.get('region')} · {pattern_label(data.get('pixel_pattern')) or color} · 오차 {data.get('tolerance', 0)}"
    if data.get('type') in ('all', 'any'):
        return f"{'AND' if data['type'] == 'all' else 'OR'} · {len(data.get('conditions', []))}개 조건"
    return f"{data.get('type')} · {data.get('key') or data.get('var_name') or ''}"


def runtime_variable_names(data):
    names = set()
    if isinstance(data, dict):
        if data.get('type') == 'set_var' and data.get('var_name'):
            names.add(str(data['var_name']).strip())
        for value in data.values():
            names.update(runtime_variable_names(value))
    elif isinstance(data, list):
        for value in data:
            names.update(runtime_variable_names(value))
    return names


class SharedTable(QtWidgets.QTableWidget):
    def mousePressEvent(self, event):
        if event.button() == QtCore.Qt.MouseButton.LeftButton and event.modifiers() & QtCore.Qt.KeyboardModifier.AltModifier:
            index = self.indexAt(event.position().toPoint())
            if index.isValid():
                self.selectionModel().setCurrentIndex(index, QtCore.QItemSelectionModel.SelectionFlag.NoUpdate)
                self.selectionModel().select(index, QtCore.QItemSelectionModel.SelectionFlag.Toggle | QtCore.QItemSelectionModel.SelectionFlag.Rows)
                event.accept()
                return
        super().mousePressEvent(event)


class SharedDockTitle(QtWidgets.QWidget):
    """Explicit title drag with a visible target at every main-window edge."""
    def __init__(self, controller):
        super().__init__(controller.dock)
        self.controller = controller
        self.start = None
        self.dragging = False
        self.offset = QtCore.QPoint()
        row = QtWidgets.QHBoxLayout(self)
        row.setContentsMargins(8, 3, 4, 3)
        label = QtWidgets.QLabel('이 매크로의 공용 설정')
        label.setAttribute(QtCore.Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        row.addWidget(label)
        row.addStretch()
        for text, callback in [('↗', self.toggle_floating), ('×', controller.dock.hide)]:
            button = QtWidgets.QToolButton()
            button.setText(text)
            button.clicked.connect(callback)
            row.addWidget(button)
        self.setToolTip('제목줄을 드래그하여 파란 영역에 놓으면 붙습니다. 더블클릭하면 분리/오른쪽 붙이기')

    def toggle_floating(self):
        if self.controller.dock.isFloating():
            self.controller.dock_to(QtCore.Qt.DockWidgetArea.RightDockWidgetArea)
        else:
            self.controller.dock.setFloating(True)

    def mousePressEvent(self, event):
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            self.start = event.globalPosition().toPoint()
            self.offset = self.controller.dock.mapFromGlobal(self.start)
            self.dragging = False
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self.start is None:
            return
        point = event.globalPosition().toPoint()
        if not self.dragging and (point - self.start).manhattanLength() >= QtWidgets.QApplication.startDragDistance():
            self.dragging = True
            self.controller.dock.setFloating(True)
            self.controller.dock.show()
            self.grabMouse()
        if self.dragging:
            self.controller.dock.move(point - self.offset)
            self.controller.preview_dock(point)
        event.accept()

    def mouseReleaseEvent(self, event):
        if event.button() == QtCore.Qt.MouseButton.LeftButton and self.start is not None:
            area = self.controller.dock_target(event.globalPosition().toPoint()) if self.dragging else None
            self.start = None
            self.dragging = False
            self.releaseMouse()
            self.controller.dock_preview.hide()
            if area is not None:
                self.controller.dock_to(area)
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def mouseDoubleClickEvent(self, event):
        self.start = None
        self.dragging = False
        self.controller.dock_preview.hide()
        self.toggle_floating()
        event.accept()


class SharedController(QtCore.QObject):
    def __init__(self, owner):
        super().__init__(owner)
        self.owner = owner
        self.history = []
        self.last_state = None
        self.pending_before = None
        self.pending_after = None
        self._profile_identity = id(owner.profile)
        self.pick = None
        self.dialogs = []
        self.bindings = weakref.WeakSet()
        self.macro_editor = None
        self.macro_editor_row = -1
        self.dock = QtWidgets.QDockWidget('이 매크로의 공용 설정', owner)
        self.dock.setObjectName('sharedSettingsDock')
        self.dock.setAllowedAreas(QtCore.Qt.DockWidgetArea.AllDockWidgetAreas)
        self.dock.setFeatures(
            QtWidgets.QDockWidget.DockWidgetFeature.DockWidgetMovable
            | QtWidgets.QDockWidget.DockWidgetFeature.DockWidgetFloatable
            | QtWidgets.QDockWidget.DockWidgetFeature.DockWidgetClosable
        )
        self.dock_preview = QtWidgets.QFrame(owner)
        self.dock_preview.setAttribute(QtCore.Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.dock_preview.setStyleSheet('background-color: rgba(40, 115, 225, 85); border: 2px solid #2873e1;')
        self.dock_preview.hide()
        self.dock.setTitleBarWidget(SharedDockTitle(self))
        root = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(root)
        self.scope = QtWidgets.QComboBox()
        self.scope.addItems(['현재 매크로', '프로필 전체', '미사용', '연결 오류'])
        self.search = QtWidgets.QLineEdit()
        self.search.setPlaceholderText('이름·값 검색')
        self.summary = QtWidgets.QLabel()
        self.summary.setWordWrap(True)
        layout.addWidget(self.scope)
        layout.addWidget(self.search)
        layout.addWidget(self.summary)
        self.table = SharedTable(0, 4)
        self.table.setStyleSheet(
            'QTableWidget::item:selected { background-color: #245dcc; color: #ffffff; }'
            'QTableWidget::item:selected:!active { background-color: #245dcc; color: #ffffff; }'
            'QTableWidget::item:focus { border: 1px solid #123c91; }'
        )
        self.table.setHorizontalHeaderLabels(['이름', '종류', '현재 설정', '사용처'])
        self.table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.ExtendedSelection)
        self.table.setToolTip("Shift: 범위 선택 · Ctrl/Alt: 개별 선택 · Ctrl+A: 전체 선택 · Delete: 선택 삭제")
        self.table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.horizontalHeader().setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.Stretch)
        self.table.setColumnWidth(0, 130)
        self.table.setColumnWidth(1, 65)
        self.table.setColumnWidth(3, 80)
        layout.addWidget(self.table, 1)
        self.detail = QtWidgets.QLabel('항목을 선택하면 사용처를 확인하고 바로 수정할 수 있습니다.')
        self.detail.setWordWrap(True)
        layout.addWidget(self.detail)
        self.usages = QtWidgets.QListWidget()
        self.usages.setMaximumHeight(150)
        self.usages.itemDoubleClicked.connect(self.open_usage)
        layout.addWidget(self.usages)
        toolbar = QtWidgets.QHBoxLayout()
        self.single_actions = []
        def menu_button(label, actions):
            button = QtWidgets.QToolButton()
            button.setText(label)
            button.setPopupMode(QtWidgets.QToolButton.ToolButtonPopupMode.InstantPopup)
            menu = QtWidgets.QMenu(button)
            for title, callback, single in actions:
                action = menu.addAction(title)
                action.triggered.connect(callback)
                if single:
                    self.single_actions.append(action)
            button.setMenu(menu)
            toolbar.addWidget(button)
            return button
        menu_button('추가', [('새 감지', self.new_detection, False), ('새 공용 값', self.new_value, False)])
        self.edit_button = QtWidgets.QPushButton('수정')
        self.edit_button.clicked.connect(self.edit_selected)
        toolbar.addWidget(self.edit_button)
        self.single_actions.append(self.edit_button)
        self.delete_button = QtWidgets.QPushButton('삭제')
        self.delete_button.clicked.connect(self.delete_selected)
        toolbar.addWidget(self.delete_button)
        menu_button('더보기', [
            ('사용처 열기', self.open_usage, True), ('이름 변경', self.rename_selected, True),
            ('복제', self.duplicate_selected, True), ('지금 테스트', self.test_selected, True),
            ('직접 입력 / 공용화', self.show_direct, False), ('공용화 검토', self.review_shared, False),
            ('기존 미사용 값 모두 정리', self.clean_unused_values, False), ('되돌리기', self.undo, False),
            ('오른쪽에 붙이기', lambda: self.dock_to(QtCore.Qt.DockWidgetArea.RightDockWidgetArea), False),
            ('왼쪽에 붙이기', lambda: self.dock_to(QtCore.Qt.DockWidgetArea.LeftDockWidgetArea), False),
            ('별도 창으로 분리', lambda: self.dock.setFloating(True), False),
        ])
        toolbar.addStretch()
        layout.addLayout(toolbar)
        footer = QtWidgets.QHBoxLayout()
        footer.addStretch()
        self.cancel_button = QtWidgets.QPushButton('변경 취소')
        self.cancel_button.clicked.connect(self.cancel_pending)
        footer.addWidget(self.cancel_button)
        self.apply_button = QtWidgets.QPushButton('변경 적용')
        self.apply_button.clicked.connect(self.apply_runtime)
        footer.addWidget(self.apply_button)
        layout.addLayout(footer)
        self.delete_shortcut = QtGui.QShortcut(QtGui.QKeySequence('Delete'), self.table)
        self.delete_shortcut.setContext(QtCore.Qt.ShortcutContext.WidgetWithChildrenShortcut)
        self.delete_shortcut.activated.connect(self.delete_selected)
        self.status = QtWidgets.QLabel('편집 내용은 프로필 저장 시 함께 저장됩니다. 실행에는 변경 적용 후 반영됩니다.')
        self.status.setWordWrap(True)
        layout.addWidget(self.status)
        self.dock.setWidget(root)
        owner.addDockWidget(QtCore.Qt.DockWidgetArea.RightDockWidgetArea, self.dock)
        self.dock.setMinimumWidth(340)
        self.dock.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.CustomContextMenu)
        self.dock.customContextMenuRequested.connect(self.dock_menu)
        self.scope.currentIndexChanged.connect(lambda: self.refresh(True))
        self.search.textChanged.connect(lambda: self.refresh(True))
        self.table.itemSelectionChanged.connect(self.selection_changed)
        self.table.itemDoubleClicked.connect(lambda *_: self.edit_selected())
        owner.macro_table.itemSelectionChanged.connect(lambda: self.refresh(True))
        self.timer = QtCore.QTimer(self)
        self.timer.timeout.connect(self.refresh)
        self.timer.start(1500)
        QtWidgets.QApplication.instance().installEventFilter(self)
        self.update_pending_buttons()
        self._closing = False
        state = getattr(owner, '_state', {}).get('shared_settings_dock', {})
        self.dock.setVisible(bool(state.get('visible', True)))
        self.dock.visibilityChanged.connect(self.save_visibility)

    def save_visibility(self, *_):
        if self._closing:
            return
        # Parent minimization/hiding is different from explicitly closing the dock.
        visible = not self.dock.isHidden()
        state = dict(self.owner._state.get('shared_settings_dock', {}))
        if state.get('visible') != visible:
            state['visible'] = visible
            self.owner._update_state('shared_settings_dock', state)

    def prepare_app_close(self):
        self.save_visibility()
        self._closing = True

    @property
    def entries(self):
        return self.owner.profile.shared_settings

    def dock_to(self, area):
        self.dock_preview.hide()
        self.dock.setFloating(False)
        self.owner.addDockWidget(area, self.dock)
        self.dock.show()
        self.dock.raise_()
        orientation = QtCore.Qt.Orientation.Horizontal if area in (
            QtCore.Qt.DockWidgetArea.LeftDockWidgetArea, QtCore.Qt.DockWidgetArea.RightDockWidgetArea
        ) else QtCore.Qt.Orientation.Vertical
        self.owner.resizeDocks([self.dock], [400], orientation)

    def dock_target(self, global_pos):
        point = self.owner.mapFromGlobal(global_pos)
        rect = self.owner.rect()
        if not rect.adjusted(-48, -32, 48, 32).contains(point):
            return None
        edges = [(abs(rect.right() - point.x()), QtCore.Qt.DockWidgetArea.RightDockWidgetArea),
                 (abs(point.x()), QtCore.Qt.DockWidgetArea.LeftDockWidgetArea),
                 (abs(point.y()), QtCore.Qt.DockWidgetArea.TopDockWidgetArea),
                 (abs(rect.bottom() - point.y()), QtCore.Qt.DockWidgetArea.BottomDockWidgetArea)]
        distance, area = min(edges, key=lambda entry: entry[0])
        return area if distance <= 110 else None

    def preview_dock(self, global_pos):
        area = self.dock_target(global_pos)
        if area is None:
            self.dock_preview.hide()
            return
        rect = self.owner.rect().adjusted(2, 2, -2, -2)
        if area == QtCore.Qt.DockWidgetArea.RightDockWidgetArea:
            rect.setLeft(max(rect.left(), rect.right() - min(400, rect.width() // 2)))
        elif area == QtCore.Qt.DockWidgetArea.LeftDockWidgetArea:
            rect.setWidth(min(400, rect.width() // 2))
        elif area == QtCore.Qt.DockWidgetArea.TopDockWidgetArea:
            rect.setHeight(min(300, rect.height() // 2))
        else:
            rect.setTop(max(rect.top(), rect.bottom() - min(300, rect.height() // 2)))
        self.dock_preview.setGeometry(rect)
        self.dock_preview.show()
        self.dock_preview.raise_()

    def dock_menu(self, pos):
        menu = QtWidgets.QMenu(self.dock)
        for name, area in [('오른쪽에 붙이기', QtCore.Qt.DockWidgetArea.RightDockWidgetArea),
                           ('왼쪽에 붙이기', QtCore.Qt.DockWidgetArea.LeftDockWidgetArea),
                           ('위에 붙이기', QtCore.Qt.DockWidgetArea.TopDockWidgetArea),
                           ('아래에 붙이기', QtCore.Qt.DockWidgetArea.BottomDockWidgetArea)]:
            menu.addAction(name).triggered.connect(lambda _checked=False, target=area: self.dock_to(target))
        menu.addSeparator()
        menu.addAction('별도 창으로 분리').triggered.connect(lambda: self.dock.setFloating(True))
        menu.exec(self.dock.mapToGlobal(pos))

    def macros(self):
        return [m.to_dict() for m in self.owner._collect_macros()]

    def preview_macros(self):
        macros = self.macros()
        editor = self.macro_editor
        if editor is not None:
            row = self.macro_editor_row
            data = copy.deepcopy(macros[row]) if 0 <= row < len(macros) else {'name': editor.name_edit.text() or '새 매크로'}
            data['actions'] = [a.to_dict() for a in editor.main_action_tree.collect_actions() + editor.parallel_action_tree.collect_actions()]
            data['stop_actions'] = [a.to_dict() for a in editor.stop_action_tree.collect_actions()] if editor.stop_group.isChecked() else []
            if 0 <= row < len(macros):
                macros[row] = data
            else:
                macros.append(data)
        return macros

    def snapshot(self):
        return copy.deepcopy((self.entries, self.macros(), self.owner._variable_items))

    def commit(self, before, message):
        if self.pending_before is None:
            self.pending_before = copy.deepcopy(before)
        self.pending_after = self.snapshot()
        self.history.append((id(self.owner.profile), before, self.snapshot()))
        self.history = self.history[-15:]
        self.owner._refresh_variable_completers()
        self.owner._mark_dirty()
        self.refresh(True)
        self.status.setText(message + ' · 프로필 저장 필요 · 실행 반영은 변경 적용')

    def update_pending_buttons(self):
        pending = self.pending_before is not None and self.snapshot() != self.pending_before
        if not pending:
            self.pending_before = None
            self.pending_after = None
        self.apply_button.setEnabled(pending)
        self.cancel_button.setEnabled(pending)
        self.apply_button.setText('변경 적용 ●' if pending else '변경 적용')
        self.apply_button.setStyleSheet(
            'QPushButton { background: #c56a12; color: white; border: 1px solid #a65308; '
            'border-radius: 5px; padding: 5px 10px; font-weight: 600; }'
            'QPushButton:hover { background: #a65308; }' if pending else '')
        self.apply_button.setToolTip('아직 실행에 반영하지 않은 공용 설정 변경이 있습니다.' if pending else '적용할 공용 설정 변경이 없습니다.')

    def mark_applied(self):
        self.pending_before = None
        self.pending_after = None
        self.history.clear()
        self._profile_identity = id(self.owner.profile)
        self.update_pending_buttons()
        self.last_state = None

    def cancel_pending(self):
        if self.pending_before is None:
            return
        if self.pending_after != self.snapshot():
            self.error('공용 설정 변경 후 다른 편집이 있습니다. 해당 편집을 먼저 정리한 뒤 변경 취소를 사용하세요.')
            return
        entries, macros, variables = copy.deepcopy(self.pending_before)
        self.owner.profile.shared_settings = entries
        self.owner._variable_items = variables
        self.restore_macros(macros)
        self.owner._refresh_variable_completers()
        self.owner._mark_dirty()
        self.mark_applied()
        self.refresh(True)
        self.status.setText('적용 전 공용 설정 변경을 모두 취소했습니다. 파일에 저장하려면 프로필 저장을 누르세요.')

    def restore_macros(self, macros):
        from engine import Macro
        resolver = self.owner._build_variable_resolver()
        for row, data in enumerate(macros):
            self.owner._set_macro_row(row, Macro.from_dict(data, resolver))

    def undo(self):
        if not self.history:
            return
        profile_id, before, after = self.history[-1]
        if profile_id != id(self.owner.profile) or self.snapshot() != after:
            self.error('이후 다른 편집이 있어 전체 되돌리기를 적용할 수 없습니다.')
            return
        self.history.pop()
        entries, macros, variables = copy.deepcopy(before)
        self.owner.profile.shared_settings = entries
        self.owner._variable_items = variables
        self.restore_macros(macros)
        self.owner._refresh_variable_completers()
        self.owner._mark_dirty()
        self.pending_after = self.snapshot()
        self.refresh(True)
        self.status.setText('직전 공용 설정 변경을 되돌렸습니다. 실행 반영은 변경 적용을 누르세요.')

    def error(self, message):
        QtWidgets.QMessageBox.warning(self.owner, '공용 설정', str(message))

    def show(self):
        self.dock.show()
        self.dock.raise_()
        self.refresh(True)

    def reveal(self, reference):
        self.refresh(True)
        for row in range(self.table.rowCount()):
            if self.table.item(row, 0).data(ROLE) == ('condition', reference):
                self.table.selectRow(row)
                self.table.scrollToItem(self.table.item(row, 0))
                return

    def selected_keys(self):
        return [self.table.item(index.row(), 0).data(ROLE) for index in self.table.selectionModel().selectedRows()]

    def selected(self):
        keys = self.selected_keys()
        return keys[0] if len(keys) == 1 else None

    def refresh(self, force=False):
        if not hasattr(self.owner, '_variable_items') or getattr(self.owner, '_loading_profile', False):
            return
        macros = self.preview_macros()
        current = self.owner.macro_table.currentRow()
        if self.macro_editor is not None:
            current = self.macro_editor_row if self.macro_editor_row >= 0 else len(macros) - 1
        drafts = [(binding.reference, binding.dialog.name_edit.text()) for binding in self.bindings
                  if binding.reference and binding.dialog.isVisible() and not getattr(binding.dialog, '_editing_shared_definition', False)]
        for widget in QtWidgets.QApplication.topLevelWidgets():
            if not widget.isVisible() or controller_for(widget) is not self or getattr(widget, '_editing_shared_definition', False):
                continue
            condition = getattr(widget, 'root_condition', None) or getattr(widget, '_condition', None)
            if condition is not None and hasattr(condition, 'to_dict'):
                for _, _, node in walk_conditions(condition.to_dict()):
                    if node.get('shared_ref'):
                        drafts.append((node['shared_ref'], node.get('name') or '편집 중인 조건'))
        signature = json.dumps([macros, self.entries, self.owner._variable_items, current, drafts], ensure_ascii=False, sort_keys=True)
        if not force and self.last_state == signature:
            return
        self.last_state = signature
        if getattr(self, '_profile_identity', None) != id(self.owner.profile):
            self._profile_identity = id(self.owner.profile)
            self.history.clear()
            self.pick = None
            self.pending_before = None
            self.pending_after = None
        self.update_pending_buttons()
        old = set(self.selected_keys())
        self.uses, self.direct = condition_usages(macros, self.entries)
        for reference, name in drafts:
            for ref in set(dependencies({'shared_ref': reference}, self.entries)):
                if not any(use['macro'] == current for use in self.uses.get(ref, [])):
                    self.uses.setdefault(ref, []).append({'macro': current, 'path': (), 'label': (name or self.entries.get(reference, {}).get('name', '공용 조건')) + ' · 조건 편집 중', 'draft': True})
        self.var_uses = variable_usages(macros, self.entries)
        self.runtime_variables = runtime_variable_names(macros)
        # Include values referenced by other values, with the original usage path.
        from engine import VariableResolver
        values = {(kind, item['name']): item['value'] for kind, items in self.owner._variable_items.items() for item in items}
        def inherit(key, uses, stack=()):
            if key in stack:
                return
            for match in VariableResolver._pattern.finditer(values.get(key, '')):
                name = match.group('name') or match.group('name2') or match.group('name3')
                child = (key[0], name) if (key[0], name) in values else ('var', name)
                target = self.var_uses.setdefault(child, [])
                for usage in uses:
                    if usage not in target:
                        target.append(usage)
                inherit(child, uses, stack + (key,))
        for key, uses in list(self.var_uses.items()):
            inherit(key, list(uses))
        self.rows = {}
        for key in set(self.entries) | set(self.uses):
            entry = self.entries.get(key)
            error = None
            try:
                if entry is None:
                    raise ValueError('삭제된 공용 설정')
                expand_condition({'shared_ref': key}, self.entries)
            except ValueError as exc:
                error = str(exc)
            self.rows[('condition', key)] = (entry['name'] if entry else '연결 오류', '감지' if entry and entry['condition'].get('type') == 'pixel' else '조건 묶음', error or brief(entry['condition']), self.uses.get(key, []), bool(error))
        for category, items in self.owner._variable_items.items():
            for item in items:
                key = (category, item['name'])
                error = None
                try:
                    self.owner._build_variable_resolver().resolve(item['value'], category)
                except ValueError as exc:
                    error = str(exc)
                self.rows[key] = (item['name'], KINDS.get(category, category), error or item['value'], self.var_uses.get(key, []), bool(error))
        for key, uses in self.var_uses.items():
            if key not in self.rows:
                if key[0] == 'var' and key[1] in self.runtime_variables:
                    continue
                self.rows[key] = (key[1], KINDS.get(key[0], key[0]), '연결된 값 없음', uses, True)
        mode = self.scope.currentIndex()
        self.deleted_keys = set()
        changed_keys = set()
        if self.pending_before is not None:
            previous_entries, _, previous_values = self.pending_before
            changed_keys.update(('condition', ref) for ref, entry in self.entries.items() if previous_entries.get(ref) != entry)
            for category, items in self.owner._variable_items.items():
                old_values = {v['name']: v for v in previous_values.get(category, [])}
                changed_keys.update((category, item['name']) for item in items if old_values.get(item['name']) != item)
            for ref, entry in previous_entries.items():
                key = ('condition', ref)
                if ref not in self.entries:
                    self.deleted_keys.add(key)
                    self.rows[key] = (entry['name'], '감지', brief(entry['condition']), [], False)
            for category, items in previous_values.items():
                for item in items:
                    key = (category, item['name'])
                    if not any(v['name'] == item['name'] for v in self.owner._variable_items.get(category, [])):
                        self.deleted_keys.add(key)
                        self.rows[key] = (item['name'], KINDS[category], item['value'], [], False)
        query = self.search.text().casefold()
        self.table.blockSignals(True)
        self.table.setRowCount(0)
        for key, (name, kind, value, uses, error) in sorted(self.rows.items(), key=lambda pair: pair[1][0]):
            local = sum(use['macro'] == current for use in uses)
            if key not in self.deleted_keys | changed_keys and ((mode == 0 and not local) or (mode == 2 and uses) or (mode == 3 and not error)):
                continue
            if query and query not in f'{name} {value}'.casefold():
                continue
            row = self.table.rowCount()
            self.table.insertRow(row)
            for col, text in enumerate((name, kind, value, f'{local} / {len(uses)}곳')):
                cell = QtWidgets.QTableWidgetItem(str(text))
                cell.setData(ROLE, key)
                cell.setToolTip('현재 매크로 / 프로필 전체 사용처' if col == 3 else str(text))
                if error:
                    cell.setForeground(QtGui.QColor('#d94841'))
                if self.pending_before is not None:
                    previous_entries, _, previous_values = self.pending_before
                    changed = (self.entries.get(key[1]) != previous_entries.get(key[1])) if key[0] == 'condition' else (
                        next((v for v in self.owner._variable_items.get(key[0], []) if v['name'] == key[1]), None)
                        != next((v for v in previous_values.get(key[0], []) if v['name'] == key[1]), None))
                    if changed:
                        cell.setBackground(QtGui.QColor('#fff19b'))
                        cell.setForeground(QtGui.QColor('#603600'))
                        cell.setToolTip(cell.toolTip() + '\n변경 적용 대기 중')
                if key in self.deleted_keys:
                    cell.setBackground(QtGui.QColor('#ffd0d0'))
                    cell.setForeground(QtGui.QColor('#a00000'))
                    cell.setToolTip('삭제 예정 · 변경 적용 시 제거 · 변경 취소로 복원')
                    if col == 0:
                        cell.setText(name + ' · 삭제 예정')
                self.table.setItem(row, col, cell)
            if key in old:
                self.table.selectionModel().select(self.table.model().index(row, 0), QtCore.QItemSelectionModel.SelectionFlag.Select | QtCore.QItemSelectionModel.SelectionFlag.Rows)
        self.table.blockSignals(False)
        direct = sum(use['macro'] == current for use in self.direct)
        name = macros[current].get('name') if 0 <= current < len(macros) else '매크로를 선택하세요'
        self.summary.setText(f'{name}\n공용 항목 {sum(any(u["macro"] == current for u in row[3]) for row in self.rows.values())}개 · 직접 입력 픽셀 조건 {direct}곳')
        self.selection_changed()

    def selection_changed(self):
        self.usages.clear()
        keys = self.selected_keys()
        for action in self.single_actions:
            action.setEnabled(len(keys) == 1 and keys[0] not in getattr(self, 'deleted_keys', set()))
        self.delete_button.setEnabled(any(key not in getattr(self, 'deleted_keys', set()) for key in keys))
        self.delete_button.setText(f'삭제 ({len(keys)})' if len(keys) > 1 else '삭제')
        if len(keys) != 1:
            self.detail.setText(f'{len(keys)}개 선택 · 삭제 또는 Delete로 일괄 정리' if keys else '항목을 선택하거나 더블클릭하여 수정하세요.')
            self.usages.setVisible(False)
            return
        self.usages.setVisible(True)
        key = keys[0]
        if key not in getattr(self, 'rows', {}):
            return
        name, kind, value, uses, error = self.rows[key]
        current = self.owner.macro_table.currentRow()
        local = sum(use['macro'] == current for use in uses)
        self.detail.setText(f'{name}\n{value}\n현재 매크로 {local}곳 · 다른 매크로 {len(uses)-local}곳에서 사용')
        for use in uses:
            item = QtWidgets.QListWidgetItem(f"#{use['macro'] + 1} {use['label']}")
            item.setData(ROLE, use)
            self.usages.addItem(item)

    def prompt_name(self, default=''):
        name, accepted = QtWidgets.QInputDialog.getText(self.owner, '공용 설정', '이름', text=default)
        return name.strip() if accepted and name.strip() else None

    def create(self, condition, name=None):
        name = name or self.prompt_name(condition.get('name') or '새 감지')
        if not name:
            return None
        before = self.snapshot()
        key = register(self.entries, name, condition)
        self.commit(before, f'{name} 등록')
        return key

    def matching_key(self, data):
        from engine import Condition
        data = definition(data)
        resolver = self.owner._build_variable_resolver()
        def normalize(node):
            node.pop('name', None)
            if node.get('type') == 'pixel':
                if node.get('region') is not None:
                    node['region'] = list(Condition._parse_region(node['region'], resolver)[0])
                if node.get('pixel_pattern'):
                    node['color'] = None
                elif node.get('color') is not None:
                    raw = node['color']
                    raw = resolver.resolve(raw, 'color') if isinstance(raw, str) else raw
                    node['color'] = list(Condition._parse_color(raw, None)[0])
            for field in ('conditions', 'on_true', 'on_false'):
                for child in node.get(field, []):
                    normalize(child)
        normalize(data)
        return fingerprint(data)

    def offer_matching_links(self, binding, data, reference):
        """Link identical tests in the current draft, including ancestor editor copies."""
        from engine import Condition
        try:
            signature = self.matching_key(data)
        except ValueError:
            return
        macros = self.preview_macros()
        index = self.macro_editor_row if self.macro_editor is not None else self.owner.macro_table.currentRow()
        if self.macro_editor is not None and index < 0:
            index = len(macros) - 1
        if not 0 <= index < len(macros):
            return
        def matches(condition):
            if condition.get('shared_ref'):
                return False
            try:
                return self.matching_key(condition) == signature
            except ValueError:
                return False
        matches_in_macro = [(path, labels) for path, labels, condition in walk_conditions(macros[index]) if matches(condition)]
        if not matches_in_macro:
            return
        if binding.original is not None and matches(binding.original.to_dict()) and len(matches_in_macro) == 1:
            return
        box = QtWidgets.QMessageBox(binding.dialog)
        box.setWindowTitle('동일 조건 함께 연결')
        box.setText(f'현재 매크로에 동일한 검사 설정이 {len(matches_in_macro)}곳 있습니다.\n모두 이 공용 설정에 연결할까요?')
        box.setInformativeText('검색 범위·색상 또는 팩·오차·대상 창이 같은 조건을 연결합니다.\n각 조건의 있음/없음 판정과 실행 액션은 유지됩니다.')
        box.setDetailedText('\n'.join(' → '.join(labels) or str(path) for path, labels in matches_in_macro))
        yes = box.addButton('모두 연결', QtWidgets.QMessageBox.ButtonRole.AcceptRole)
        box.addButton('현재 조건만', QtWidgets.QMessageBox.ButtonRole.RejectRole)
        box.exec()
        if box.clickedButton() is not yes:
            return
        before = self.snapshot()
        seen = set()
        def link_object(value):
            if id(value) in seen:
                return
            if isinstance(value, (Condition, dict, list, tuple)) or hasattr(value, 'to_dict'):
                seen.add(id(value))
            if isinstance(value, Condition):
                if matches(value.to_dict()):
                    value.shared_ref = reference
                for key in ('conditions', 'on_true', 'on_false'):
                    link_object(getattr(value, key, []))
            elif isinstance(value, dict):
                for child in value.values():
                    link_object(child)
            elif isinstance(value, (list, tuple)):
                for child in value:
                    link_object(child)
            elif hasattr(value, 'to_dict'):
                for child in vars(value).values():
                    link_object(child)
        if self.macro_editor is not None:
            for tree in (self.macro_editor.main_action_tree, self.macro_editor.parallel_action_tree, self.macro_editor.stop_action_tree):
                iterator = QtWidgets.QTreeWidgetItemIterator(tree)
                while iterator.value():
                    link_object(iterator.value().data(0, ROLE))
                    iterator += 1
            # Inner condition/action dialogs hold independent copies until accepted.
            parent = binding.dialog.parentWidget()
            while parent is not None and parent is not self.owner:
                link_object(getattr(parent, 'root_condition', None))
                link_object(getattr(parent, '_condition', None))
                parent = parent.parentWidget()
        else:
            stored = self.macros()
            for path, _ in matches_in_macro:
                at_path(stored[index], path)['shared_ref'] = reference
            self.restore_macros(stored)
        self.commit(before, f'동일 검사 {len(matches_in_macro)}곳 공용 연결')
        self.refresh(True)

    def condition_dialog(self, data, callback, title='공용 감지 수정'):
        from main import ConditionNodeDialog, ConditionDialog
        from engine import Condition, MacroCondition
        condition = Condition.from_dict(data, self.owner._build_variable_resolver())
        is_group = condition.type in ('all', 'any')
        cls = ConditionDialog if is_group else ConditionNodeDialog
        kwargs = dict(cond=MacroCondition(condition=condition) if is_group else condition, resolver=self.owner._build_variable_resolver(),
                      variable_provider=self.owner._variable_names,
                      pattern_provider=self.owner._pattern_names,
                      open_pattern_manager=self.owner._open_pattern_manager)
        if not is_group:
            kwargs['open_debugger'] = self.owner._open_debugger_with_config
        dialog = cls(self.owner, **kwargs)
        dialog.setWindowTitle(title)
        dialog._editing_shared_definition = True
        if hasattr(dialog, '_shared_binding'):
            dialog._shared_binding.hide()
        dialog.ok_btn.clicked.disconnect()
        def accept():
            try:
                result = dialog.get_condition()
                if is_group:
                    result = result.condition
                callback(result.to_dict())
            except ValueError as exc:
                self.error(exc)
                return
            dialog.accept()
        dialog.ok_btn.clicked.connect(accept)
        self.dialogs.append(dialog)
        dialog.finished.connect(lambda *_: self.dialogs.remove(dialog) if dialog in self.dialogs else None)
        dialog.show()
        return dialog

    def new_detection(self):
        self.condition_dialog({'type': 'pixel', 'region': [0, 0, 1, 1], 'color': [255, 255, 255]}, self.create, '공용 감지 만들기')

    def edit_selected(self):
        self.edit_key(self.selected())

    def edit_key(self, key):
        if not key:
            return
        if key in getattr(self, 'deleted_keys', set()):
            self.status.setText('삭제 예정 항목입니다. 변경 취소 또는 되돌리기로 복원하세요.')
            return
        if key[0] != 'condition':
            self.edit_value(key)
            return
        entry = self.entries.get(key[1])
        if not entry:
            self.error('연결된 항목이 없습니다.')
            return
        original = copy.deepcopy(entry)
        def save(data):
            if self.entries.get(key[1]) != original:
                raise ValueError('편집 중 다른 곳에서 설정이 바뀌었습니다. 다시 열어주세요.')
            before = self.snapshot()
            self.entries[key[1]]['condition'] = definition(data)
            try:
                expand_condition({'shared_ref': key[1]}, self.entries)
            except ValueError:
                self.entries[key[1]] = original
                raise
            self.commit(before, f"{entry['name']} 변경 · {len(self.uses.get(key[1], []))}곳 반영")
        self.condition_dialog(entry['condition'], save, f"{entry['name']} · 공용 수정")

    def edit_value(self, key, pick_region=False):
        item = next((x for x in self.owner._variable_items[key[0]] if x['name'] == key[1]), None)
        if item is None:
            self.error('연결된 값이 없습니다.')
            return
        if key[0] == 'region':
            dialog = QtWidgets.QDialog(self.owner)
            dialog.setWindowTitle(key[1] + ' · 위치·영역 수정')
            dialog.setModal(False)
            layout = QtWidgets.QVBoxLayout(dialog)
            layout.addWidget(QtWidgets.QLabel('x, y, 너비, 높이 · 이미지 뷰어에서 위치 또는 범위를 선택하세요.'))
            edit = QtWidgets.QLineEdit(item['value'])
            layout.addWidget(edit)
            def pick(mode):
                self.start_pick(mode, key, lambda region: edit.setText(','.join(map(str, region))))
            for label, mode in [('이미지 뷰어에서 위치 선택 (F1)', 'position'), ('이미지 뷰어에서 범위 선택', 'region')]:
                button = QtWidgets.QPushButton(label)
                button.clicked.connect(lambda checked=False, mode=mode: pick(mode))
                layout.addWidget(button)
            buttons = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.StandardButton.Save | QtWidgets.QDialogButtonBox.StandardButton.Cancel)
            layout.addWidget(buttons)
            def save():
                if self.set_value(key, edit.text()):
                    dialog.accept()
            def cleanup():
                if self.pick and self.pick[0] == key:
                    self.pick = None
                    self.owner._image_viewer_dialog.canvas.cancel_region_selection()
            buttons.accepted.connect(save)
            buttons.rejected.connect(dialog.reject)
            dialog.finished.connect(cleanup)
            self.dialogs.append(dialog)
            dialog.show()
            if pick_region:
                pick('region')
            return
        value, ok = QtWidgets.QInputDialog.getText(self.owner, key[1], f'{KINDS[key[0]]} 값', text=item['value'])
        if not ok:
            return
        self.set_value(key, value)

    def set_value(self, key, value):
        from engine import Condition
        try:
            if key[0] == 'region':
                region = Condition._parse_region(value, self.owner._build_variable_resolver())[0]
                if region[2] <= 0 or region[3] <= 0:
                    raise ValueError('영역 크기는 1 이상이어야 합니다.')
            if key[0] == 'color':
                resolved = self.owner._build_variable_resolver().resolve(value, 'color')
                Condition._parse_color(resolved, None)
        except ValueError as exc:
            self.error(exc)
            return
        item = next((x for x in self.owner._variable_items[key[0]] if x['name'] == key[1]), None)
        if item is None:
            self.error('항목이 삭제되었습니다. 다시 열어주세요.')
            return False
        before = self.snapshot()
        item['value'] = value
        self.commit(before, f'{key[1]} 값 변경')
        return True

    def new_value(self):
        label, ok = QtWidgets.QInputDialog.getItem(self.owner, '새 공용 값', '종류', list(KINDS.values()), editable=False)
        if not ok:
            return
        category = next(k for k, v in KINDS.items() if v == label)
        name = self.prompt_name()
        if not name:
            return
        if any(c.isspace() or c in '/{}@$' for c in name):
            self.error('값 이름에는 공백이나 / { } @ $ 를 사용할 수 없습니다.')
            return
        if any(x['name'] == name for x in self.owner._variable_items[category]):
            self.error('같은 이름이 있습니다.')
            return
        defaults = {'region': '0,0,1,1', 'color': 'ffffff', 'key': 'f', 'sleep': '100', 'var': '0'}
        before = self.snapshot()
        self.owner._ensure_variable(category, name, defaults[category])
        self.commit(before, name + ' 등록')
        if category == 'region':
            self.edit_value(('region', name), pick_region=True)

    def review_shared(self):
        from shared_review import ReviewDialog
        dialog = ReviewDialog(self)
        self.dialogs.append(dialog)
        dialog.show()

    def rename_selected(self):
        key = self.selected()
        if not key:
            return
        if key[0] != 'condition':
            name = self.prompt_name(key[1])
            if not name or name == key[1]:
                return
            if any(c.isspace() or c in '/{}@$' for c in name) or any(x['name'] == name for x in self.owner._variable_items[key[0]]):
                self.error('사용할 수 없거나 중복된 이름입니다.')
                return
            before = self.snapshot()
            macros = self.macros()
            rename_value(macros, key[0], key[1], name)
            rename_value(self.entries, key[0], key[1], name)
            from engine import VariableResolver
            for category, items in self.owner._variable_items.items():
                for item in items:
                    if category == key[0]:
                        item['value'] = VariableResolver._pattern.sub(
                            lambda m: '${' + name + '}' if (m.group('name') or m.group('name2') or m.group('name3')) == key[1] else m.group(0), item['value'])
                        if item['name'] == key[1]:
                            item['name'] = name
            self.restore_macros(macros)
            self.commit(before, '이름과 연결된 참조 변경')
            return
        entry = self.entries.get(key[1])
        if entry and (name := self.prompt_name(entry['name'])):
            before = self.snapshot()
            entry['name'] = name
            self.commit(before, '이름 변경 · 연결 유지')

    def duplicate_selected(self):
        key = self.selected()
        if key and key[0] == 'condition' and key[1] in self.entries:
            entry = self.entries[key[1]]
            name = self.prompt_name(entry['name'] + ' 복사본')
            if name:
                self.create(entry['condition'], name)

    def delete_selected(self):
        self.delete_keys(self.selected_keys())

    def clean_unused_values(self):
        self.refresh(True)
        keys = [(kind, item['name']) for kind, items in self.owner._variable_items.items()
                for item in items if not self.rows.get((kind, item['name']), (None, None, None, []))[3]]
        self.delete_keys(keys)

    def delete_keys(self, keys):
        from engine import VariableResolver
        self.refresh(True)
        requested = set(keys)
        candidates = {key for key in requested if key in self.rows and (
            not self.rows[key][3] or (key[0] == 'var' and key[1] in self.runtime_variables))}
        # Recheck references from survivors, including unused definitions and values.
        # If a retained item depends on another candidate, that dependency stays too.
        while True:
            blocked = set()
            remaining_entries = {key: value for key, value in self.entries.items() if ('condition', key) not in candidates}
            for entry in remaining_entries.values():
                blocked.update(('condition', ref) for ref in dependencies(entry['condition'], self.entries))
            referenced_names = set()
            def scan(value):
                if isinstance(value, str):
                    for match in VariableResolver._pattern.finditer(value):
                        referenced_names.add(match.group('name') or match.group('name2') or match.group('name3'))
                elif isinstance(value, dict):
                    for child in value.values(): scan(child)
                elif isinstance(value, list):
                    for child in value: scan(child)
            scan(remaining_entries)
            scan(self.macros())
            scan(self.owner.profile.pixel_region_raw)
            scan(self.owner.profile.pixel_color_raw)
            for kind, items in self.owner._variable_items.items():
                for item in items:
                    if (kind, item['name']) not in candidates:
                        scan(item['value'])
            blocked.update(key for key in candidates if key[0] != 'condition' and key[1] in referenced_names)
            reduced = candidates - blocked
            if reduced == candidates:
                break
            candidates = reduced
        if not candidates:
            self.status.setText('삭제할 미사용 항목이 없습니다. 사용 중인 항목은 연결을 유지했습니다.')
            return
        before = self.snapshot()
        for kind, name in candidates:
            if kind == 'condition':
                self.entries.pop(name, None)
            else:
                self.owner._variable_items[kind] = [item for item in self.owner._variable_items[kind] if item['name'] != name]
        retained = len(requested - candidates)
        message = f'{len(candidates)}개 삭제'
        if retained:
            message += f' · 사용 중이거나 참조되는 {retained}개 유지'
        self.commit(before, message + ' · 더보기에서 되돌리기 가능')

    def show_direct(self):
        index = self.owner.macro_table.currentRow()
        macros = self.macros()
        if not 0 <= index < len(macros):
            return
        dialog = QtWidgets.QDialog(self.owner)
        dialog.setWindowTitle('직접 입력 조건 · 선택해서 공용으로 만들기')
        dialog.resize(760, 460)
        layout = QtWidgets.QVBoxLayout(dialog)
        listing = QtWidgets.QListWidget()
        for path, labels, condition in walk_conditions(macros[index]):
            if condition.get('shared_ref'):
                continue
            item = QtWidgets.QListWidgetItem((' → '.join(labels) or condition['type']) + ' | ' + brief(condition))
            item.setData(ROLE, path)
            listing.addItem(item)
        layout.addWidget(listing)
        button = QtWidgets.QPushButton('선택 항목 공용화')
        layout.addWidget(button)
        def convert():
            if not listing.currentItem():
                return
            current = self.macros()
            if current[index] != macros[index]:
                self.error('매크로가 변경되었습니다. 목록을 다시 열어주세요.')
                return
            path = listing.currentItem().data(ROLE)
            data = at_path(current[index], path)
            name = self.prompt_name(data.get('name') or '새 공용 조건')
            if not name:
                return
            before = self.snapshot()
            key = register(self.entries, name, data)
            data['shared_ref'] = key
            self.restore_macros(current)
            self.commit(before, name + ' 공용 연결')
            dialog.accept()
        button.clicked.connect(convert)
        self.dialogs.append(dialog)
        dialog.show()

    def deduplicate(self):
        index = self.owner.macro_table.currentRow()
        macros = self.macros()
        if not 0 <= index < len(macros):
            return
        groups = duplicate_groups(macros[index])
        if not groups:
            self.status.setText('현재 매크로에 동일한 직접 입력 픽셀 설정이 없습니다.')
            return
        dialog = QtWidgets.QDialog(self.owner)
        dialog.setWindowTitle('현재 매크로 중복 정리 · 선택한 설정만 연결')
        dialog.resize(800, 450)
        layout = QtWidgets.QVBoxLayout(dialog)
        table = QtWidgets.QTableWidget(len(groups), 3)
        table.setHorizontalHeaderLabels(['선택 / 사용처', '공용 이름', '검사 설정'])
        table.horizontalHeader().setSectionResizeMode(QtWidgets.QHeaderView.ResizeMode.Stretch)
        for row, group in enumerate(groups):
            paths = [' → '.join(labels) or str(path) for path, labels, _ in group]
            item = QtWidgets.QTableWidgetItem(f'{len(group)}곳 · ' + paths[0])
            item.setCheckState(QtCore.Qt.CheckState.Checked)
            item.setToolTip('\n'.join(paths))
            item.setFlags(item.flags() & ~QtCore.Qt.ItemFlag.ItemIsEditable)
            table.setItem(row, 0, item)
            table.setItem(row, 1, QtWidgets.QTableWidgetItem(group[0][2].get('name') or f'공용 감지 {row+1}'))
            settings = QtWidgets.QTableWidgetItem(brief(group[0][2]))
            settings.setFlags(settings.flags() & ~QtCore.Qt.ItemFlag.ItemIsEditable)
            table.setItem(row, 2, settings)
        layout.addWidget(table)
        button = QtWidgets.QPushButton('선택한 중복을 공용으로 연결')
        layout.addWidget(button)
        def apply():
            if self.macros() != macros:
                self.error('매크로가 변경되었습니다. 중복 정리를 다시 열어주세요.')
                return
            selected = [i for i in range(len(groups)) if table.item(i, 0).checkState() == QtCore.Qt.CheckState.Checked]
            if not selected or any(not table.item(i, 1).text().strip() for i in selected):
                self.error('항목을 선택하고 이름을 입력하세요.')
                return
            before = self.snapshot()
            changed = copy.deepcopy(macros)
            count = 0
            for i in selected:
                key = register(self.entries, table.item(i, 1).text(), groups[i][0][2])
                for path, _, _ in groups[i]:
                    at_path(changed[index], path)['shared_ref'] = key
                    count += 1
            self.restore_macros(changed)
            self.commit(before, f'중복 설정 {len(selected)}개 · {count}곳 연결')
            dialog.accept()
        button.clicked.connect(apply)
        self.dialogs.append(dialog)
        dialog.show()

    def open_usage(self, *_):
        item = self.usages.currentItem()
        if not item and self.usages.count():
            item = self.usages.item(0)
        if item is None:
            return
        location = item.data(ROLE)
        if location.get('draft'):
            target = next((binding.dialog for binding in self.bindings if binding.reference and binding.dialog.isVisible()), self.macro_editor)
            if target is not None:
                target.raise_()
                target.activateWindow()
            return
        index, path = location['macro'], location['path']
        if self.macro_editor is not None:
            if index == self.macro_editor_row:
                navigate_usage(self.macro_editor, path, self.preview_macros()[index])
            else:
                self.error('열려 있는 매크로 편집을 먼저 완료한 뒤 다른 매크로의 사용처를 여세요.')
            return
        self.owner.macro_table.selectRow(index)
        self.owner._edit_macro(usage_path=path)

    def start_pick(self, mode, key=None, callback=None):
        key = key or self.selected()
        if not key:
            return
        if key[0] == 'condition':
            entry = self.entries.get(key[1])
            if not entry or entry['condition'].get('type') != 'pixel':
                self.error('픽셀 감지를 선택하세요.')
                return
        elif key[0] != 'region':
            self.error('위치·영역 또는 픽셀 감지를 선택하세요.')
            return
        self.owner._open_image_viewer_dialog()
        viewer = self.owner._image_viewer_dialog
        if self.pick:
            viewer.canvas.cancel_region_selection()
        pack = getattr(self.owner, '_pack_manager', None)
        if pack:
            pack.record.setChecked(False)
        self.pick = (key, mode, id(self.owner.profile))
        self.pick_callback = callback
        viewer.status_label.setText(f'공용 설정 지정: {self.rows[key][0]} · F1 적용 / Esc 취소')
        self.status.setText(f'{self.rows[key][0]} 지정 중 · F1 적용 / Esc 취소')
        if mode == 'region':
            if not viewer.canvas.begin_region_selection(self.region_picked):
                self.pick = None
                self.status.setText('이미지를 먼저 열어주세요.')

    def region_picked(self, *args):
        region = args[0] if len(args) == 1 else args
        if isinstance(region, dict):
            region = region.get('region')
        if region and len(region) == 4:
            x, y = self.owner._image_viewer_dialog._recognition_position(region[0], region[1])
            self.finish_pick((x, y, region[2], region[3]))
        else:
            self.pick = None

    def finish_pick(self, region, color=None):
        if not self.pick:
            return
        key, mode, profile_id = self.pick
        self.pick = None
        if profile_id != id(self.owner.profile):
            return
        callback = getattr(self, 'pick_callback', None)
        self.pick_callback = None
        if callback is not None:
            callback(region)
            return
        if key[0] == 'region':
            self.set_value(key, ','.join(map(str, region)))
        else:
            before = self.snapshot()
            entry = self.entries.get(key[1])
            if not entry:
                return
            entry['condition']['region'] = list(region)
            if mode == 'both' and color:
                entry['condition']['color'] = list(color)
            viewer = self.owner._image_viewer_dialog
            entry['condition']['window_target'] = copy.deepcopy(viewer._capture_metadata.get('window_target'))
            self.commit(before, entry['name'] + ' 위치 변경')

    def eventFilter(self, obj, event):
        if not self.pick:
            return False
        if event.type() not in (QtCore.QEvent.Type.KeyPress, QtCore.QEvent.Type.ShortcutOverride):
            return False
        viewer = getattr(self.owner, '_image_viewer_dialog', None)
        if not isinstance(obj, QtWidgets.QWidget) or obj.window() not in (viewer, self.owner):
            return False
        if event.key() not in (QtCore.Qt.Key.Key_F1, QtCore.Qt.Key.Key_Escape):
            return False
        event.accept()
        if event.type() == QtCore.QEvent.Type.ShortcutOverride:
            return True
        if event.key() == QtCore.Qt.Key.Key_Escape:
            self.pick = None
            viewer.canvas.cancel_region_selection()
            self.status.setText('위치 지정 취소')
        elif not event.isAutoRepeat() and self.pick[1] != 'region':
            sample = viewer._last_sample
            if sample:
                x, y = sample['pos']
                color = viewer.canvas._image.pixelColor(x, y)
                x, y = viewer._recognition_position(x, y)
                key = self.pick[0]
                from engine import Condition
                previous = self.entries[key[1]]['condition'].get('region') if key[0] == 'condition' else next((v['value'] for v in self.owner._variable_items['region'] if v['name'] == key[1]), None)
                try:
                    parsed = Condition._parse_region(previous, self.owner._build_variable_resolver())[0]
                    w, h = parsed[2:]
                except (ValueError, TypeError):
                    w, h = 1, 1
                self.finish_pick((x, y, w, h), (color.red(), color.green(), color.blue()))
        return True

    def test_selected(self):
        key = self.selected()
        if key and key[0] == 'condition' and key[1] in self.entries:
            def provider():
                from engine import Condition
                resolver = self.owner._build_variable_resolver()
                data = expand_condition({'shared_ref': key[1]}, self.entries)
                return {'condition': Condition.from_dict(data, resolver), 'resolver': resolver,
                        'label': self.entries[key[1]]['name']}
            self.owner._start_condition_debug_session(provider)

    def apply_runtime(self):
        try:
            for macro in self.macros():
                for _, _, condition in walk_conditions(macro):
                    expand_condition(condition, self.entries)
            if self.owner._apply_profile():
                self.mark_applied()
                self.refresh(True)
                self.status.setText('실행에 적용했습니다. 파일 보존은 프로필 저장을 누르세요.')
        except ValueError as exc:
            self.error(exc)


class ConditionBinding(QtWidgets.QWidget):
    def __init__(self, dialog, controller, condition):
        super().__init__(dialog)
        self.dialog = dialog
        self.controller = controller
        controller.bindings.add(self)
        self.reference = None
        self.original = copy.deepcopy(condition)
        row = QtWidgets.QHBoxLayout(self)
        row.setContentsMargins(0, 0, 0, 0)
        self.combo = QtWidgets.QComboBox()
        self.combo.addItem('직접 입력', None)
        for key, entry in controller.entries.items():
            self.combo.addItem(entry['name'], key)
        row.addWidget(QtWidgets.QLabel('공용 설정'))
        row.addWidget(self.combo, 1)
        for label, callback in [('공용으로 만들기', self.create), ('공용 수정', self.edit), ('이곳만 수정', self.detach)]:
            button = QtWidgets.QPushButton(label)
            button.clicked.connect(callback)
            row.addWidget(button)
        self.combo.currentIndexChanged.connect(self.changed)
        if condition and condition.shared_ref:
            self.choose(condition.shared_ref)

    def choose(self, reference):
        index = self.combo.findData(reference)
        if index < 0:
            entry = self.controller.entries.get(reference)
            self.combo.addItem(entry['name'] if entry else '연결 오류 · 다시 선택', reference)
            index = self.combo.count() - 1
        self.combo.setCurrentIndex(index)

    def changed(self):
        from engine import Condition
        self.reference = self.combo.currentData()
        if self.reference:
            self.controller.reveal(self.reference)
            try:
                entry = self.controller.entries[self.reference]
                exists = bool(self.dialog.pixel_expect_combo.currentData())
                data = expand_condition({'shared_ref': self.reference, 'pixel_exists': exists}, self.controller.entries)
                self.dialog._load(Condition.from_dict(data, self.dialog._resolver))
            except (KeyError, ValueError):
                pass
        for i in range(self.dialog.form.count()):
            widget = self.dialog.form.itemAt(i).widget()
            if widget:
                widget.setEnabled(not bool(self.reference))
        if self.reference:
            self.dialog.pixel_expect_combo.setEnabled(True)
        self.controller.refresh(True)

    def create(self):
        try:
            data = self.dialog._get_direct_condition().to_dict()
            key = self.controller.create(data)
            if key:
                self.choose(key)
                self.controller.offer_matching_links(self, data, key)
        except ValueError as exc:
            self.controller.error(exc)

    def edit(self):
        if self.reference:
            self.controller.edit_key(('condition', self.reference))

    def detach(self):
        if self.reference:
            try:
                from engine import Condition
                data = expand_condition({'shared_ref': self.reference, 'pixel_exists': bool(self.dialog.pixel_expect_combo.currentData())}, self.controller.entries)
                self.dialog._load(Condition.from_dict(data, self.dialog._resolver))
            except ValueError as exc:
                self.controller.error(exc)
                return
        self.combo.setCurrentIndex(0)
        self.dialog._sync_type_visibility()

    def result(self):
        from engine import Condition
        if not self.reference:
            return self.dialog._get_direct_condition()
        data = expand_condition({'shared_ref': self.reference, 'pixel_exists': bool(self.dialog.pixel_expect_combo.currentData())}, self.controller.entries)
        result = Condition.from_dict(data, self.dialog._resolver)
        result.shared_ref = self.reference
        if self.original:
            result.on_true = copy.deepcopy(self.original.on_true)
            result.on_false = copy.deepcopy(self.original.on_false)
            result.enabled = self.original.enabled
        return result


def attach_condition(dialog, condition):
    controller = controller_for(dialog)
    if controller:
        dialog._shared_binding = ConditionBinding(dialog, controller, condition)
        dialog.layout().insertWidget(0, dialog._shared_binding)
        attach_value_fields(dialog)
        dialog.finished.connect(lambda *_: QtCore.QTimer.singleShot(0, lambda: controller.refresh(True)))


def attach_condition_tree(dialog):
    controller = controller_for(dialog)
    if not controller:
        return
    def current():
        return dialog._selected_condition() or dialog.root_condition
    def assign(target, data):
        from engine import Condition
        replacement = Condition.from_dict(data, dialog._resolver)
        target.__dict__.update(replacement.__dict__)
        dialog._refresh_condition_tree()
    def make_shared():
        target = current()
        if target is None or target.shared_ref:
            return
        try:
            dialog._validate_group_children(target)
            key = controller.create(target.to_dict())
            if key:
                target.shared_ref = key
                dialog._refresh_condition_tree()
        except ValueError as exc:
            controller.error(exc)
    def choose():
        target = current()
        if target is None:
            return
        menu = QtWidgets.QMenu(dialog)
        choices = {}
        for key, entry in controller.entries.items():
            action = menu.addAction(entry['name'] + ' · ' + brief(entry['condition']))
            choices[action] = key
        action = menu.exec(QtGui.QCursor.pos())
        if action in choices:
            key = choices[action]
            try:
                data = expand_condition(dict(target.to_dict(), shared_ref=key), controller.entries)
                data['shared_ref'] = key
                assign(target, data)
            except ValueError as exc:
                controller.error(exc)
    def unlink():
        target = current()
        if target and target.shared_ref:
            try:
                assign(target, expand_condition(target.to_dict(), controller.entries))
            except ValueError as exc:
                controller.error(exc)
    def context_menu(pos):
        item = dialog.condition_tree.itemAt(pos)
        if item is None or dialog._condition_from_item(item) is None:
            return
        dialog.condition_tree.setCurrentItem(item)
        target = current()
        menu = QtWidgets.QMenu(dialog)
        if not target.shared_ref:
            menu.addAction('공용으로 만들기').triggered.connect(make_shared)
        if controller.entries:
            menu.addAction('공용 조건 선택').triggered.connect(choose)
        if target.shared_ref:
            menu.addAction('공용 수정').triggered.connect(lambda: controller.edit_key(('condition', target.shared_ref)))
            menu.addAction('연결 해제 · 이곳만 수정').triggered.connect(unlink)
        menu.exec(dialog.condition_tree.viewport().mapToGlobal(pos))
    dialog.condition_tree.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.CustomContextMenu)
    dialog.condition_tree.customContextMenuRequested.connect(context_menu)
    def highlight():
        target = current()
        if target and target.shared_ref:
            controller.reveal(target.shared_ref)
    dialog.condition_tree.itemSelectionChanged.connect(highlight)


def attach_value_fields(dialog):
    controller = controller_for(dialog)
    if not controller:
        return
    fields = {'region_edit': 'region', 'color_edit': 'color', 'key_edit': 'key',
              'sleep_edit': 'sleep', 'mouse_pos_edit': 'region', 'repeat_edit': 'var',
              'pixel_region_edit': 'region', 'action_main_key_edit': 'key'}
    for attribute, category in fields.items():
        edit = getattr(dialog, attribute, None)
        if not isinstance(edit, QtWidgets.QLineEdit) or edit.property('sharedSelector'):
            continue
        edit.setProperty('sharedSelector', True)
        action = edit.addAction(dialog.style().standardIcon(QtWidgets.QStyle.StandardPixmap.SP_FileDialogDetailedView), QtWidgets.QLineEdit.ActionPosition.TrailingPosition)
        action.setToolTip('공용 값 선택 / 현재 입력을 공용으로 등록')
        def choose(_checked=False, field=edit, kind=category):
            menu = QtWidgets.QMenu(dialog)
            create_action = menu.addAction('현재 값을 공용으로 만들기…')
            detach_action = menu.addAction('연결 해제 · 현재 값으로 입력')
            menu.addSeparator()
            actions = {}
            for item in controller.owner._variable_items[kind]:
                entry_action = menu.addAction(f"{item['name']} · {item['value']}")
                actions[entry_action] = item['name']
            selected = menu.exec(field.mapToGlobal(QtCore.QPoint(0, field.height())))
            if selected in actions:
                field.setText('/' + actions[selected])
            elif selected == detach_action:
                try:
                    field.setText(controller.owner._build_variable_resolver().resolve(field.text(), kind))
                except ValueError as exc:
                    controller.error(exc)
            elif selected == create_action:
                name = controller.prompt_name()
                if not name:
                    return
                if any(c.isspace() or c in '/{}@$' for c in name):
                    controller.error('값 이름에는 공백이나 / { } @ $ 를 사용할 수 없습니다.')
                    return
                if any(x['name'] == name for x in controller.owner._variable_items[kind]):
                    controller.error('같은 이름이 있습니다. 목록에서 선택하세요.')
                    return
                try:
                    value = controller.owner._build_variable_resolver().resolve(field.text(), kind)
                except ValueError as exc:
                    controller.error(exc)
                    return
                before = controller.snapshot()
                controller.owner._ensure_variable(kind, name, value)
                # The editing dialog's resolver must immediately see newly added values.
                resolver = getattr(dialog, '_resolver', None)
                if resolver:
                    getattr(resolver.vars, kind)[name] = value
                field.setText('/' + name)
                controller.commit(before, name + ' 등록 및 연결')
        action.triggered.connect(choose)


def navigate_usage(editor, path, macro):
    """Select the real action by its structural path, including ELSE/ELIF/parallel."""
    from engine import Action
    targets = []
    def map_item(tree, item, data, prefix):
        targets.append((prefix, tree, item))
        direct = []
        else_header = None
        elif_headers = []
        for i in range(item.childCount()):
            child = item.child(i)
            marker = child.data(0, ROLE)
            if isinstance(marker, Action):
                direct.append(child)
            elif marker == '__else__':
                else_header = child
            elif isinstance(marker, dict) and marker.get('marker') == '__elif__':
                elif_headers.append(child)
        for i, (child, action) in enumerate(zip(direct, data.get('actions', []))):
            map_item(tree, child, action, prefix + ('actions', i))
        if else_header is not None:
            for i, action in enumerate(data.get('else_actions', [])):
                if i < else_header.childCount():
                    map_item(tree, else_header.child(i), action, prefix + ('else_actions', i))
        for i, (header, block) in enumerate(zip(elif_headers, data.get('elif_blocks', []))):
            block_path = prefix + ('elif_blocks', i)
            targets.append((block_path, tree, header))
            for j, action in enumerate(block.get('actions', [])):
                if j < header.childCount():
                    map_item(tree, header.child(j), action, block_path + ('actions', j))
    main_index = parallel_index = 0
    for i, action in enumerate(macro.get('actions', [])):
        if action.get('parallel_enabled'):
            tree, position = editor.parallel_action_tree, parallel_index
            parallel_index += 1
        else:
            tree, position = editor.main_action_tree, main_index
            main_index += 1
        if position < tree.topLevelItemCount():
            map_item(tree, tree.topLevelItem(position), action, ('actions', i))
    for i, action in enumerate(macro.get('stop_actions', [])):
        tree = editor.stop_action_tree
        if i < tree.topLevelItemCount():
            map_item(tree, tree.topLevelItem(i), action, ('stop_actions', i))
    matches = [target for target in targets if tuple(path[:len(target[0])]) == target[0]]
    if not matches:
        return
    prefix, tree, item = max(matches, key=lambda target: len(target[0]))
    if tree is editor.parallel_action_tree:
        editor.action_tabs.setCurrentIndex(1)
    elif tree is editor.main_action_tree:
        editor.action_tabs.setCurrentIndex(0)
    elif tree is editor.stop_action_tree:
        editor.action_tabs.setCurrentWidget(editor.stop_group)
    parent = item.parent()
    while parent is not None:
        tree.expandItem(parent)
        parent = parent.parent()
    tree.clearSelection()
    tree.setCurrentItem(item)
    tree.scrollToItem(item, QtWidgets.QAbstractItemView.ScrollHint.PositionAtCenter)
    editor.raise_()
    remaining = tuple(path[len(prefix):])
    editor._usage_condition_path = remaining[1:] if remaining and remaining[0] == 'condition' else None
    editor._with_action_tree(tree, editor._edit_action)


def prepare_usage_action(editor, action_dialog):
    if not hasattr(editor, '_usage_condition_path'):
        return
    path = editor._usage_condition_path
    del editor._usage_condition_path
    if path is not None:
        action_dialog._usage_condition_path = path
        QtCore.QTimer.singleShot(0, action_dialog._edit_condition)


def prepare_usage_condition(action_dialog, condition_dialog):
    if not hasattr(action_dialog, '_usage_condition_path'):
        return
    path = action_dialog._usage_condition_path
    del action_dialog._usage_condition_path
    def locate():
        target = condition_dialog.root_condition
        try:
            for i in range(0, len(path), 2):
                target = getattr(target, path[i])[path[i + 1]]
        except (AttributeError, IndexError, TypeError):
            return
        iterator = QtWidgets.QTreeWidgetItemIterator(condition_dialog.condition_tree)
        while iterator.value():
            item = iterator.value()
            if item.data(0, ROLE) is target:
                parent = item.parent()
                while parent is not None:
                    condition_dialog.condition_tree.expandItem(parent)
                    parent = parent.parent()
                condition_dialog.condition_tree.setCurrentItem(item)
                condition_dialog.condition_tree.scrollToItem(item)
                if target.type not in ('all', 'any') or target.shared_ref:
                    condition_dialog._edit_condition_node()
                return
            iterator += 1
    QtCore.QTimer.singleShot(0, locate)


def attach_workspace(owner):
    owner._shared_controller = SharedController(owner)
