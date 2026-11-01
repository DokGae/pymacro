"""Profile-local presentation and linked controls for the floating toggle panel."""
import copy
import json
import uuid
from pathlib import Path

from PyQt6 import QtCore, QtGui, QtWidgets

MIME = 'application/x-macro-quick-toggle'


def linked_entries(entries):
    result = {}
    for entry in entries:
        row, action, _, _ = entry
        name = (action.quick_toggle_name or '').strip()
        key = 'name:' + name if name else f'action:{row}:{action.quick_toggle_id}'
        if key not in result:
            result[key] = {'key': key, 'name': name or action.name or action.type, 'entries': []}
        result[key]['entries'].append(entry)
    return result


def enabled_state(entries):
    count = sum(bool(action.enabled) for _, action, _, _ in entries)
    return 'on' if entries and count == len(entries) else 'mixed' if count else 'off'


class DragHandle(QtWidgets.QToolButton):
    def __init__(self, panel, kind, key, parent=None):
        super().__init__(parent)
        self.panel, self.kind, self.key = panel, kind, key
        self.origin = None
        self.setText('⠿')
        self.setFixedSize(20, 25)
        self.setCursor(QtCore.Qt.CursorShape.OpenHandCursor)
        self.setToolTip('드래그하여 위치 이동 · 위/아래 방향키로 순서 이동')
        self.setAccessibleName('그룹 이동' if kind == 'group' else '토글 이동')

    def mousePressEvent(self, event):
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            self.origin = event.position().toPoint()
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if (self.origin is not None and event.buttons() & QtCore.Qt.MouseButton.LeftButton
                and (event.position().toPoint() - self.origin).manhattanLength()
                >= QtWidgets.QApplication.startDragDistance()):
            self.origin = None
            mime = QtCore.QMimeData()
            mime.setData(MIME, json.dumps([self.kind, self.key]).encode())
            drag = QtGui.QDrag(self)
            drag.setMimeData(mime)
            drag.setPixmap(self.parentWidget().grab())
            self.panel._dragging = True
            try:
                drag.exec(QtCore.Qt.DropAction.MoveAction)
            finally:
                self.panel._dragging = False
                self.panel.signature = None
                self.panel.refresh()
        else:
            super().mouseMoveEvent(event)

    def keyPressEvent(self, event):
        if event.key() in (QtCore.Qt.Key.Key_Up, QtCore.Qt.Key.Key_Down):
            self.panel.shift_item(self.kind, self.key, -1 if event.key() == QtCore.Qt.Key.Key_Up else 1)
            event.accept()
        else:
            super().keyPressEvent(event)


class DropArea(QtWidgets.QFrame):
    def __init__(self, panel, group, key=None):
        super().__init__()
        self.panel, self.group, self.key = panel, group, key
        self.setAcceptDrops(True)

    def payload(self, event):
        if not self.panel.editing or self.panel.interaction_locked:
            return None
        source = event.source()
        if not isinstance(source, DragHandle) or source.panel is not self.panel:
            return None
        try:
            return json.loads(bytes(event.mimeData().data(MIME)))
        except (ValueError, TypeError):
            return None

    def dragEnterEvent(self, event):
        if self.payload(event):
            self.setStyleSheet('DropArea {border:1px solid #65dfbd; border-radius:8px;}')
            event.acceptProposedAction()

    def dragMoveEvent(self, event):
        if self.payload(event):
            event.acceptProposedAction()

    def dragLeaveEvent(self, event):
        self.setStyleSheet('')

    def dropEvent(self, event):
        payload = self.payload(event)
        self.setStyleSheet('')
        if payload:
            kind, key = payload
            after = event.position().y() > self.height() / 2
            if kind == 'toggle':
                self.panel.move_toggle(key, self.group, self.key, after)
            elif kind == 'group':
                self.panel.move_group(key, self.group, after)
            event.acceptProposedAction()


class GroupedToggleMixin:
    def init_groups(self, layout):
        self.editing = False
        self._dragging = False
        self._batch_toggle = False
        self._layout_profile = None
        self._layout_data = None
        self.layouts = copy.deepcopy(self.owner._state.get('quick_toggle', {}).get('profiles', {}))
        self.summary = QtWidgets.QLabel()
        self.summary.setStyleSheet('font-size:12px; color:#bdcbd9;')
        layout.addWidget(self.summary)
        controls = QtWidgets.QHBoxLayout()
        self.use_button = QtWidgets.QToolButton()
        self.use_button.setText('사용')
        self.edit_button = QtWidgets.QToolButton()
        self.edit_button.setText('배치 편집')
        for button in (self.use_button, self.edit_button):
            button.setCheckable(True)
            controls.addWidget(button)
        self.use_button.setChecked(True)
        self.use_button.clicked.connect(lambda: self.set_editing(False))
        self.edit_button.clicked.connect(lambda: self.set_editing(True))
        controls.addStretch()
        self.add_group_button = QtWidgets.QToolButton()
        self.add_group_button.setText('＋ 그룹 추가')
        self.add_group_button.clicked.connect(lambda: self.edit_group())
        self.add_group_button.hide()
        controls.addWidget(self.add_group_button)
        layout.addLayout(controls)
        self.edit_hint = QtWidgets.QLabel('⠿ 드래그로 순서·그룹 이동 · 우클릭으로 그룹 선택')
        self.edit_hint.setWordWrap(True)
        self.edit_hint.setStyleSheet('font-size:12px; color:#c0e0cf;')
        self.edit_hint.hide()
        layout.addWidget(self.edit_hint)

    def profile_layout(self):
        path = getattr(self.owner, 'current_profile_path', None)
        profile = str(Path(path).resolve()).casefold() if path else '<unsaved>'
        if self._layout_profile != profile:
            self._layout_profile = profile
            self._layout_data = self.layouts.setdefault(profile, {'groups': [], 'placements': {}, 'order': []})
            self.signature = None
        return self._layout_data

    def layout_changed(self):
        self.signature = None
        self.save_state()
        if not self._dragging:
            self.refresh()

    def set_editing(self, editing):
        self.editing = bool(editing) and not self.interaction_locked
        self.use_button.setChecked(not self.editing)
        self.edit_button.setChecked(self.editing)
        self.add_group_button.setVisible(self.editing)
        self.edit_hint.setVisible(self.editing)
        self.signature = None
        self.refresh()

    def add_group(self, name):
        name = name.strip()
        data = self.profile_layout()
        if not name or name == '그룹 없음' or any(g['name'] == name for g in data['groups']):
            raise ValueError('비어 있지 않은, 다른 그룹 이름을 입력하세요.')
        key = uuid.uuid4().hex
        data['groups'].append({'id': key, 'name': name, 'collapsed': False})
        self.layout_changed()
        return key

    def edit_group(self, key=None):
        data = self.profile_layout()
        group = next((g for g in data['groups'] if g['id'] == key), None)
        name, ok = QtWidgets.QInputDialog.getText(self, '그룹 이름 변경' if group else '그룹 추가',
                                                '그룹 이름', text=group['name'] if group else '')
        if not ok:
            return
        try:
            if group:
                name = name.strip()
                if not name or name == '그룹 없음' or any(g['name'] == name and g is not group for g in data['groups']):
                    raise ValueError('비어 있지 않은, 다른 그룹 이름을 입력하세요.')
                group['name'] = name
                self.layout_changed()
            else:
                self.add_group(name)
        except ValueError as exc:
            QtWidgets.QMessageBox.information(self, '그룹 이름', str(exc))

    def remove_group(self, key):
        data = self.profile_layout()
        data['groups'] = [g for g in data['groups'] if g['id'] != key]
        data['placements'] = {k: v for k, v in data['placements'].items() if v != key}
        self.layout_changed()

    def toggle_fold(self, key):
        data = self.profile_layout()
        if key:
            group = next(g for g in data['groups'] if g['id'] == key)
            group['collapsed'] = not group.get('collapsed', False)
        else:
            data['ungrouped_collapsed'] = not data.get('ungrouped_collapsed', False)
        self.layout_changed()

    def move_toggle(self, key, group, target=None, after=False):
        data = self.profile_layout()
        if key not in self.linked or key == target:
            return
        valid = {g['id'] for g in data['groups']}
        if group and group not in valid:
            return
        order = [k for k in self.ordered_keys() if k != key]
        at = order.index(target) + int(after) if target in order else len(order)
        order.insert(at, key)
        data['order'] = order
        data['placements'][key] = group
        for g in data['groups']:
            if g['id'] == group:
                g['collapsed'] = False
        if not group:
            data['ungrouped_collapsed'] = False
        self.layout_changed()

    def move_group(self, key, target, after=False):
        data = self.profile_layout()
        group = next((g for g in data['groups'] if g['id'] == key), None)
        if group is None or key == target:
            return
        data['groups'].remove(group)
        keys = [g['id'] for g in data['groups']]
        at = keys.index(target) + int(after) if target in keys else len(keys)
        data['groups'].insert(at, group)
        self.layout_changed()

    def shift_item(self, kind, key, delta):
        data = self.profile_layout()
        if kind == 'group':
            keys = [g['id'] for g in data['groups']]
        else:
            group = data['placements'].get(key, '')
            keys = [k for k in self.ordered_keys() if data['placements'].get(k, '') == group]
        if key not in keys:
            return
        index = keys.index(key) + delta
        if not 0 <= index < len(keys):
            return
        if kind == 'group':
            self.move_group(key, keys[index], delta > 0)
        else:
            self.move_toggle(key, group, keys[index], delta > 0)

    def ordered_keys(self):
        saved = self.profile_layout()['order']
        return list(dict.fromkeys([k for k in saved if k in self.linked] + list(self.linked)))

    def move_menu(self, key, widget, point):
        if not self.editing:
            return
        menu = QtWidgets.QMenu(self)
        menu.addAction('위로 이동', lambda: self.shift_item('toggle', key, -1))
        menu.addAction('아래로 이동', lambda: self.shift_item('toggle', key, 1))
        menu.addSeparator()
        for group in self.profile_layout()['groups'] + [{'id': '', 'name': '그룹 없음'}]:
            menu.addAction('이동: ' + group['name'], lambda checked=False, gid=group['id']: self.move_toggle(key, gid))
        menu.exec(widget.mapToGlobal(point))

    def set_linked(self, keys, enabled):
        targets = {(row, action.quick_toggle_id) for key in keys if key in self.linked
                   for row, action, _, _ in self.linked[key]['entries']}
        self._batch_toggle = True
        try:
            batch = getattr(self.owner, '_set_quick_toggles', None)
            if callable(batch):
                batch(sorted(targets), enabled)
            else:
                for row, key in sorted(targets):
                    self.owner._set_quick_toggle(row, key, enabled)
        finally:
            self._batch_toggle = False
            self.signature = None
            self.refresh()

    def refresh_groups(self):
        from quick_toggle import ToggleSwitch
        if self._dragging or self._batch_toggle:
            return
        data = self.profile_layout()
        path = getattr(self.owner, 'current_profile_path', None)
        name = Path(path).stem if path else '새 매크로'
        self.profile_title.setText(name)
        self.profile_title.setToolTip(str(path or name))
        self.setWindowTitle(name)
        entries = self.entries()
        signature = (self._layout_profile, self.editing, json.dumps(data, sort_keys=True),
                     tuple((r, a.quick_toggle_id, a.quick_toggle_name, a.name, a.enabled, blocked, m)
                           for r, a, blocked, m in entries))
        if signature == self.signature:
            self.sync_clickthrough()
            return
        self.signature = signature
        self.linked = linked_entries(entries)
        self.summary.setText(f'토글 {len(self.linked)}개 · 액션 {len(entries)}개 연결')
        self.status_label.setText(f'● {sum(bool(a.enabled) for _, a, _, _ in entries)} / {len(entries)} 액션 켜짐')
        scroll = self.scroll.verticalScrollBar().value()
        while self.rows.count():
            widget = self.rows.takeAt(0).widget()
            widget.hide()
            widget.deleteLater()
        if not entries and not data['groups']:
            label = QtWidgets.QLabel('IF · 액션 편집에서\n「빠른 토글에 표시」를 선택하세요.')
            label.setStyleSheet('color:#bfccda; padding:24px 0; font-size:13px;')
            label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
            self.rows.addWidget(label)
        valid = {g['id'] for g in data['groups']}
        for group in data['groups'] + [{'id': '', 'name': '그룹 없음', 'collapsed': data.get('ungrouped_collapsed', False)}]:
            gid = group['id']
            keys = [k for k in self.ordered_keys() if (data['placements'].get(k, '') if data['placements'].get(k, '') in valid else '') == gid]
            if not gid and not keys and not self.editing:
                continue
            container = DropArea(self, gid)
            column = QtWidgets.QVBoxLayout(container)
            column.setContentsMargins(0, 0, 0, 4)
            column.setSpacing(5)
            header = QtWidgets.QHBoxLayout()
            if self.editing and gid:
                header.addWidget(DragHandle(self, 'group', gid))
            fold = QtWidgets.QToolButton()
            fold.setText(('▸ ' if group.get('collapsed') else '▾ ') + group['name'])
            fold.setToolTip('그룹 펼치기 / 접기')
            fold.clicked.connect(lambda checked=False, key=gid: self.toggle_fold(key))
            header.addWidget(fold, 1)
            count = QtWidgets.QLabel(str(len(keys)))
            count.setStyleSheet('font-size:12px; font-weight:600; color:#bdcbd9;')
            header.addWidget(count)
            if self.editing and gid:
                for text, tip, callback in [('✎', '그룹 이름 변경', lambda checked=False, key=gid: self.edit_group(key)),
                                            ('×', '그룹 해제 · 토글은 그룹 없음으로 이동', lambda checked=False, key=gid: self.remove_group(key))]:
                    button = QtWidgets.QToolButton()
                    button.setText(text)
                    button.setToolTip(tip)
                    button.clicked.connect(callback)
                    header.addWidget(button)
            combined = [entry for key in keys for entry in self.linked[key]['entries']]
            state = enabled_state(combined)
            master = QtWidgets.QToolButton()
            master.setObjectName('groupToggle')
            master.setText({'on': '전체 ON', 'off': '전체 OFF', 'mixed': '일부 ON'}[state])
            master.setAccessibleName(group['name'] + ' 모두 ' + ('끄기' if state == 'on' else '켜기'))
            master.setStyleSheet('font-size:11px; font-weight:700; padding:5px 7px; border-radius:4px; color:' +
                                ('#ffe2a6; background:#403a2a;' if state == 'mixed' else '#b0f5d4; background:#294239;' if state == 'on' else '#d0dbe8; background:#2a3440;'))
            master.setEnabled(bool(keys))
            master.clicked.connect(lambda checked=False, ids=keys, on=state != 'on': self.set_linked(ids, on))
            header.addWidget(master)
            column.addLayout(header)
            if not group.get('collapsed'):
                for key in keys:
                    item = self.linked[key]
                    state = enabled_state(item['entries'])
                    card = DropArea(self, gid, key)
                    card.setObjectName('toggleRow')
                    card.setProperty('toggleState', state)
                    card.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.CustomContextMenu)
                    card.customContextMenuRequested.connect(lambda point, k=key, w=card: self.move_menu(k, w, point))
                    line = QtWidgets.QHBoxLayout(card)
                    line.setContentsMargins(12, 12, 12, 12)
                    if self.editing:
                        line.addWidget(DragHandle(self, 'toggle', key, card))
                    text = QtWidgets.QVBoxLayout()
                    text.setSpacing(4)
                    label = QtWidgets.QLabel(item['name'])
                    label.setWordWrap(True)
                    label.setStyleSheet('font-size:14px; font-weight:700; color:#f3f6fc;')
                    text.addWidget(label)
                    meta = QtWidgets.QLabel(f'↳ 연결 액션 {len(item["entries"])}개' + (' · 일부 켜짐' if state == 'mixed' else ''))
                    meta.setStyleSheet('font-size:12px; color:' + ('#f4d595;' if state == 'mixed' else '#bad8ca;'))
                    text.addWidget(meta)
                    tooltip = '\n'.join(f'{m or "매크로"} › {a.name or a.type}' + (' · 상위 항목 꺼짐' if blocked else '')
                                        for _, a, blocked, m in item['entries'])
                    card.setToolTip(tooltip)
                    line.addLayout(text, 1)
                    switch = ToggleSwitch()
                    switch.mixed = state == 'mixed'
                    switch.setChecked(state == 'on')
                    switch.setAccessibleName(item['name'])
                    switch.setToolTip('연결 액션 모두 끄기' if state == 'on' else '연결 액션 모두 켜기')
                    switch.clicked.connect(lambda checked, k=key: self.set_linked([k], checked))
                    line.addWidget(switch)
                    column.addWidget(card)
                if self.editing and not keys:
                    empty = QtWidgets.QLabel('여기에 토글을 놓으세요')
                    empty.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
                    empty.setStyleSheet('color:#bdd3c5; border:1px dashed #58715f; border-radius:6px; padding:16px; font-size:12px;')
                    column.addWidget(empty)
            self.rows.addWidget(container)
        self.rows.activate()
        self.scroll.verticalScrollBar().setValue(scroll)
        self.update()
        QtCore.QTimer.singleShot(0, self.sync_clickthrough)
