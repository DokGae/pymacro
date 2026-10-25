"""Reusable blocks: staged with the macro editor and covered by its undo history."""
import copy

from PyQt6 import QtCore, QtWidgets
from engine import Action
from lib.shared_blocks import register, validate, usages, fingerprint, walk

ROLE = QtCore.Qt.ItemDataRole.UserRole


class BlockWorkspace(QtCore.QObject):
    def __init__(self, editor):
        super().__init__(editor)
        self.editor = editor
        self.owner = editor.parentWidget()
        self.entries = copy.deepcopy(getattr(getattr(self.owner, 'profile', None), 'shared_blocks', {}))
        self.original = copy.deepcopy(self.entries)
        self.active = None
        self.loading = False
        self.return_tree = editor.main_action_tree
        self.editing = False
        self.page = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(self.page)
        layout.addWidget(QtWidgets.QLabel('현재 파일 전체에서 공유 · 확인 후 적용 · 프로필 저장 시 함께 저장됩니다.'))
        self.search = QtWidgets.QLineEdit()
        self.search.setPlaceholderText('공용 블록 이름·설명 검색')
        layout.addWidget(self.search)
        self.list = QtWidgets.QListWidget()
        layout.addWidget(self.list, 1)
        row = QtWidgets.QGridLayout()
        for index, (label, callback) in enumerate([('새 블록', self.new), ('복제', self.duplicate), ('삭제', self.delete),
                                ('사용 위치', self.show_usages), ('동일한 묶음 찾기', self.find_matches),
                                ('공용 조건 관리', self.conditions),
                                ('공용 블록 미리보기', self.preview_selected),
                                ('공용 원본 편집', lambda: self.open(self.active, True)),
                                ('미리보기 닫기', lambda: self.panel.hide())]):
            button = QtWidgets.QPushButton(label)
            button.clicked.connect(callback)
            row.addWidget(button, index // 3, index % 3)
        layout.addLayout(row)
        self.search.textChanged.connect(self.refresh_list)
        self.list.currentItemChanged.connect(self.select_entry)
        editor.action_tabs.insertTab(2, self.page, '공용 블록')

        self.panel = QtWidgets.QWidget()
        self.panel.setMinimumWidth(440)
        panel_layout = QtWidgets.QVBoxLayout(self.panel)
        self.heading = QtWidgets.QLabel('공용 블록')
        self.heading.setWordWrap(True)
        panel_layout.addWidget(self.heading)
        self.name = QtWidgets.QLineEdit()
        self.description = QtWidgets.QLineEdit()
        self.description.setPlaceholderText('설명 / 검색용 메모')
        panel_layout.addWidget(self.name)
        panel_layout.addWidget(self.description)
        self.tree = type(editor.main_action_tree)()
        from action_workspace import build_tree_panel
        tree_panel = build_tree_panel(self.tree)
        toolbar = tree_panel.layout().itemAt(0).layout()
        for index in range(2, toolbar.count()):
            widget = toolbar.itemAt(index).widget()
            if widget:
                widget.hide()
        self.tree.setColumnWidth(1, 90)
        self.tree.setColumnWidth(2, 150)
        panel_layout.addWidget(tree_panel, 1)
        self.controls = QtWidgets.QWidget()
        buttons = QtWidgets.QGridLayout(self.controls)
        commands = [('액션 추가', lambda: editor._add_action()),
                    ('하위 추가', lambda: editor._add_action(as_child=True)),
                    ('편집', editor._edit_action), ('삭제', editor._delete_action),
                    ('복사', editor._copy_action), ('붙여넣기', editor._paste_action),
                    ('위로', lambda: self.tree.move_selected_within_parent(-1)),
                    ('아래로', lambda: self.tree.move_selected_within_parent(1))]
        for index, (label, callback) in enumerate(commands):
            button = QtWidgets.QPushButton(label)
            button.clicked.connect(lambda checked=False, fn=callback: self.edit_command(fn))
            buttons.addWidget(button, index // 4, index % 4)
        panel_layout.addWidget(self.controls)
        footer = QtWidgets.QHBoxLayout()
        self.edit_button = QtWidgets.QPushButton('공용 원본 편집')
        self.edit_button.clicked.connect(lambda: self.open(self.active, True))
        footer.addWidget(self.edit_button)
        uses = QtWidgets.QPushButton('사용 위치')
        uses.clicked.connect(self.show_usages)
        footer.addWidget(uses)
        close = QtWidgets.QPushButton('닫기 / 돌아가기')
        close.clicked.connect(self.panel.hide)
        footer.addWidget(close)
        panel_layout.addLayout(footer)
        self.name.editingFinished.connect(self.save_definition)
        self.description.editingFinished.connect(self.save_definition)
        self.tree.itemDoubleClicked.connect(lambda *_: self.edit_command(editor._edit_action))
        self.tree.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.NoContextMenu)
        self.timer = QtCore.QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.timeout.connect(self.save_definition)
        for signal in (self.tree.model().rowsInserted, self.tree.model().rowsRemoved,
                       self.tree.model().dataChanged, self.tree.model().modelReset):
            signal.connect(self.schedule)
        self.panel.hide()
        for tree in self.source_trees:
            tree.block_workspace = self
            tree.itemSelectionChanged.connect(lambda t=tree: self.selection_changed(t))
        toolbar = QtWidgets.QHBoxLayout()
        for label, callback in [('선택을 공용 블록으로', self.make_shared),
                                ('공용 블록 넣기', self.choose_insert),
                                ('이곳만 연결 해제', self.detach)]:
            button = QtWidgets.QPushButton(label)
            button.clicked.connect(callback)
            toolbar.addWidget(button)
        toolbar.addStretch()
        editor.action_controls.layout().insertLayout(0, toolbar)
        self.refresh_list()

    @property
    def source_trees(self):
        e = self.editor
        return (e.main_action_tree, e.parallel_action_tree, e.stop_action_tree)

    def mount(self):
        # Install after the history toolbar has found the original tab widget.
        layout = self.editor.layout()
        position = layout.indexOf(self.editor.action_tabs)
        layout.removeWidget(self.editor.action_tabs)
        self.splitter = QtWidgets.QSplitter()
        self.splitter.addWidget(self.editor.action_tabs)
        self.splitter.addWidget(self.panel)
        self.splitter.setStretchFactor(0, 3)
        self.splitter.setStretchFactor(1, 2)
        layout.insertWidget(position, self.splitter, 1)
        self.refresh_links()

    def error(self, message):
        self.heading.setText(str(message))
        self.panel.show()

    def flush(self):
        history = getattr(self.editor, 'action_history', None)
        if history:
            history.flush()

    def schedule(self, *_):
        if not self.loading and self.editing:
            self.timer.start(0)

    def macros(self):
        owner = self.owner
        macros = [m.to_dict() for m in owner._collect_macros()] if hasattr(owner, '_collect_macros') else []
        row = getattr(self.editor, '_block_macro_row', -1)
        current = {'name': self.editor.name_edit.text(),
                   'actions': [a.to_dict() for t in self.source_trees[:2] for a in t.collect_actions()],
                   'stop_actions': [a.to_dict() for a in self.editor.stop_action_tree.collect_actions()]}
        if 0 <= row < len(macros):
            macros[row] = current
        else:
            macros.append(current)
        return macros

    def validate(self):
        self.save_definition()
        current = getattr(getattr(self.owner, 'profile', None), 'shared_blocks', self.original)
        if current != self.original and current != self.entries:
            raise ValueError('다른 편집기에서 공용 블록이 변경되었습니다. 현재 편집을 취소하고 다시 열어주세요.')
        if self.editing and (not self.name.text().strip() or self.name.text().strip() != self.entries[self.active]['name']):
            raise ValueError('비어 있지 않은 고유한 공용 블록 이름을 입력하세요.')
        validate(self.entries, self.macros(), self.editor._resolver)

    def refresh_list(self, *_):
        selected = self.active
        blocker = QtCore.QSignalBlocker(self.list)
        self.list.clear()
        query = self.search.text().strip().casefold()
        macros = self.macros()
        for ref, entry in self.entries.items():
            if query and query not in (entry['name'] + ' ' + entry.get('description', '')).casefold():
                continue
            count = len(usages(macros, self.entries, ref))
            item = QtWidgets.QListWidgetItem(f"{entry['name']}    · 사용 {count}곳" if count else f"{entry['name']}    · 미사용")
            item.setData(ROLE, ref)
            self.list.addItem(item)
            if ref == selected:
                self.list.setCurrentItem(item)
        del blocker

    def refresh_links(self):
        for tree in self.source_trees:
            for item in tree.items():
                action = item.data(0, ROLE)
                if isinstance(action, Action) and action.type == 'shared_block':
                    entry = self.entries.get(action.block_ref)
                    action.name = entry['name'] if entry else action.name
                    item.setText(2, '🔗 ' + (action.name or '연결 없음'))
                    tree._set_type_text(item, '공용 블록')
                    item.setText(3, '공용 · 더블클릭하여 원본 편집' if entry else '공용 블록 연결 없음')
        self.refresh_list()

    def select_entry(self, item, _previous):
        if item:
            if not self.panel.isHidden():
                self.open(item.data(ROLE), False)
            else:
                self.save_definition()
                if self.editing and self.active in self.entries and self.name.text().strip() != self.entries[self.active]['name']:
                    self.error('비어 있지 않은 고유한 이름을 입력한 뒤 블록을 전환하세요.')
                    return
                self.editing = False
                self.active = item.data(ROLE)

    def preview_selected(self):
        if self.active in self.entries:
            self.open(self.active, False)

    def selection_changed(self, tree):
        if self.loading:
            return
        self.return_tree = tree

    def open(self, ref, edit=False):
        if any(child.isVisible() and child.__class__.__name__ in ('ActionEditDialog', 'ConditionDialog', 'ConditionNodeDialog')
               for child in self.editor.findChildren(QtWidgets.QDialog)):
            self.error('열린 액션·조건 편집을 확인 또는 취소한 뒤 공용 블록을 전환하세요.')
            return
        if ref not in self.entries:
            self.error('공용 블록을 찾을 수 없습니다.')
            return
        self.save_definition()
        if self.editing and self.active in self.entries and self.name.text().strip() != self.entries[self.active]['name']:
            self.error('비어 있지 않은 고유한 이름을 입력한 뒤 블록을 전환하세요.')
            return
        self.active = ref
        self.loading = True
        entry = self.entries[ref]
        self.name.setText(entry['name'])
        self.description.setText(entry.get('description', ''))
        self.tree.load_actions([Action.from_dict(a, self.editor._resolver) for a in entry['actions']])
        self.tree.expandAll()
        self.editing = edit
        self.name.setReadOnly(not edit)
        self.description.setReadOnly(not edit)
        self.controls.setVisible(edit)
        self.edit_button.setVisible(not edit)
        self.tree.setEnabled(True)
        self.tree.setDragEnabled(edit)
        self.tree.setAcceptDrops(edit)
        if not edit:
            for item in self.tree.items():
                item.setFlags(QtCore.Qt.ItemFlag.ItemIsEnabled)
        self.loading = False
        was_hidden = self.panel.isHidden()
        self.panel.show()
        if was_hidden and hasattr(self, 'splitter'):
            width = self.splitter.width()
            self.splitter.setSizes([int(width * .6), int(width * .4)])
        self.update_heading()
        self.refresh_list()

    def update_heading(self):
        count = len(usages(self.macros(), self.entries, self.active))
        self.heading.setText(f"{'공용 원본 편집' if self.editing else '공용 원본 미리보기'} · 사용 {count}곳\n"
                             '수정은 연결된 모든 곳에 반영됩니다. 매크로 편집 확인 후 적용됩니다.')

    def save_definition(self):
        self.timer.stop()
        if self.loading or not self.editing or self.active not in self.entries:
            return
        name = self.name.text().strip()
        if not name or any(ref != self.active and e['name'] == name for ref, e in self.entries.items()):
            self.heading.setText('비어 있지 않은 고유한 이름을 입력하세요.')
            return
        entry = dict(name=name, description=self.description.text().strip(),
                     actions=[a.to_dict() for a in self.tree.collect_actions()])
        if entry == self.entries[self.active]:
            return
        self.entries[self.active] = entry
        self.refresh_links()
        self.update_heading()
        history = getattr(self.editor, 'action_history', None)
        if history:
            history.schedule()

    def edit_command(self, callback):
        if not self.editing:
            return
        self.flush()
        self.editor._with_action_tree(self.tree, callback)
        self.save_definition()
        self.flush()

    def prompt(self, title, initial, callback):
        dialog = QtWidgets.QInputDialog(self.editor)
        dialog.setWindowTitle(title)
        dialog.setLabelText('공용 블록 이름')
        dialog.setTextValue(initial)
        dialog.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        dialog.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose)
        def accepted():
            try:
                callback(dialog.textValue().strip())
            except ValueError as exc:
                self.error(exc)
        dialog.accepted.connect(accepted)
        dialog.show()

    def new(self):
        self.prompt('새 공용 블록', '', lambda name: self.create(name, []))

    def create(self, name, actions):
        self.flush()
        ref = register(self.entries, name, actions)
        self.flush()
        self.open(ref, True)
        return ref

    def duplicate(self):
        self.save_definition()
        if self.active in self.entries:
            source = copy.deepcopy(self.entries[self.active])
            self.prompt('공용 블록 복제', source['name'] + ' 복사', lambda name: self.create(name, source['actions']))

    def selected(self, tree=None):
        tree = tree or self.editor.action_tree
        items = tree._top_level_selected(tree.selectedItems())
        if not items or any(not isinstance(i.data(0, ROLE), Action) for i in items):
            raise ValueError('같은 분기에 있는 연속된 액션을 선택하세요.')
        parent = items[0].parent()
        if any(i.parent() is not parent for i in items):
            raise ValueError('같은 분기의 액션만 함께 묶을 수 있습니다.')
        container = parent or tree.invisibleRootItem()
        items.sort(key=container.indexOfChild)
        indexes = [container.indexOfChild(i) for i in items]
        if indexes != list(range(indexes[0], indexes[0] + len(items))):
            raise ValueError('연속된 액션을 선택하세요.')
        if any(i.data(0, ROLE).parallel_enabled for i in items):
            raise ValueError('병렬 작업의 내부 액션을 선택하세요. 병렬 주기는 기존 작업에서 유지됩니다.')
        owner = parent.data(0, ROLE) if parent is not None else None
        if isinstance(owner, Action) and owner.type == 'group' and owner.group_mode in ('first_true', 'first_true_continue', 'first_true_return'):
            raise ValueError('우선순위 그룹은 그룹 전체를 공용으로 묶어야 실행 순서가 유지됩니다.')
        return tree, items

    def replace(self, tree, items, actions):
        parent = items[0].parent()
        container = parent or tree.invisibleRootItem()
        index = container.indexOfChild(items[0])
        for item in reversed(items):
            container.takeChild(container.indexOfChild(item))
        created = [tree._append_action_item(a, parent, index + i) for i, a in enumerate(actions)]
        tree.renumber()
        if created:
            tree.clearSelection()
            tree.setCurrentItem(created[0])
        return created

    def make_shared(self, _checked=False, tree=None):
        try:
            tree, items = self.selected(tree)
        except ValueError as exc:
            self.error(exc)
            return
        source = [tree._action_from_item(i).to_dict() for i in items]
        positions = [tree._item_path_key(i) for i in items]
        def create(name):
            # Non-modal prompts must not replace a selection modified in the meantime.
            live = list(tree.items())
            if (any(not any(i is node for node in live) for i in items)
                    or positions != [tree._item_path_key(i) for i in items]
                    or source != [tree._action_from_item(i).to_dict() for i in items]):
                raise ValueError('선택 내용이 변경되었습니다. 다시 선택해서 묶으세요.')
            self.flush()
            candidate = copy.deepcopy(self.entries)
            register(candidate, name, source)
            validate(candidate, resolver=self.editor._resolver)
            ref = register(self.entries, name, source)
            self.replace(tree, items, [Action(type='shared_block', name=name, block_ref=ref)])
            self.flush()
            self.save_definition()
            self.editing = False
            self.active = ref
            self.panel.hide()
            self.refresh_links()
            self.find_matches(automatic=True)
        self.prompt('선택을 공용 블록으로', items[0].data(0, ROLE).name or '', create)

    def choose_insert(self, _checked=False, tree=None):
        tree = tree or self.editor.action_tree
        dialog = QtWidgets.QDialog(self.editor)
        dialog.setWindowTitle('공용 블록 넣기 · 선택한 줄 다음에 삽입')
        dialog.setModal(False)
        dialog.resize(460, 420)
        layout = QtWidgets.QVBoxLayout(dialog)
        search = QtWidgets.QLineEdit()
        search.setPlaceholderText('블록 이름 검색')
        listing = QtWidgets.QListWidget()
        layout.addWidget(search)
        layout.addWidget(listing)
        def refresh():
            listing.clear()
            for ref, entry in self.entries.items():
                if search.text().casefold() in entry['name'].casefold():
                    item = QtWidgets.QListWidgetItem(entry['name'])
                    item.setData(ROLE, ref)
                    listing.addItem(item)
        def insert():
            item = listing.currentItem()
            if item:
                self.insert(tree, item.data(ROLE))
                dialog.accept()
        search.textChanged.connect(refresh)
        listing.itemDoubleClicked.connect(lambda *_: insert())
        button = QtWidgets.QPushButton('넣기')
        button.clicked.connect(insert)
        layout.addWidget(button)
        refresh()
        dialog.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose)
        dialog.show()

    def insert(self, tree, ref):
        if ref not in self.entries:
            self.error('공용 블록을 찾을 수 없습니다.')
            return
        self.flush()
        clipboard = type(self.editor)._action_clipboard
        try:
            type(self.editor)._action_clipboard = [Action(type='shared_block', block_ref=ref, name=self.entries[ref]['name'])]
            self.editor._paste_action(tree)
        finally:
            type(self.editor)._action_clipboard = clipboard
        self.refresh_links()
        self.flush()

    def detach(self, _checked=False, tree=None):
        try:
            tree, items = self.selected(tree)
            if len(items) != 1 or items[0].data(0, ROLE).type != 'shared_block':
                raise ValueError('연결을 해제할 공용 블록 한 줄을 선택하세요.')
            action = tree._action_from_item(items[0])
            entry = self.entries.get(action.block_ref)
            if entry is None:
                raise ValueError('원본이 없어 연결을 해제할 수 없습니다.')
            children = [Action.from_dict(a, self.editor._resolver) for a in entry['actions']]
            # Preserve call-site disabling and quick toggles in an ordinary group.
            action.type, action.block_ref, action.group_mode = 'group', '', 'all'
            action.actions = children
            self.flush()
            self.replace(tree, items, [action])
            self.refresh_links()
            self.flush()
        except ValueError as exc:
            self.error(exc)

    def delete(self):
        if self.active not in self.entries:
            return
        if usages(self.macros(), self.entries, self.active):
            self.error('사용 중인 공용 블록입니다. 사용 위치에서 연결을 해제하거나 호출을 삭제하세요.')
            return
        self.flush()
        del self.entries[self.active]
        self.active = None
        self.editing = False
        self.panel.hide()
        self.refresh_links()
        self.flush()

    def show_usages(self):
        if self.active not in self.entries:
            return
        dialog = QtWidgets.QDialog(self.editor)
        dialog.setWindowTitle('사용 위치 · ' + self.entries[self.active]['name'])
        dialog.setModal(False)
        dialog.resize(620, 400)
        layout = QtWidgets.QVBoxLayout(dialog)
        listing = QtWidgets.QListWidget()
        hint = QtWidgets.QLabel('더블클릭하여 이동 · 다른 매크로로 이동하면 현재 편집이 확인·적용됩니다.')
        hint.setWordWrap(True)
        layout.addWidget(hint)
        layout.addWidget(listing)
        for row, path, name in usages(self.macros(), self.entries, self.active):
            item = QtWidgets.QListWidgetItem(name + ' / ' + ' → '.join(str(p + 1) if isinstance(p, int) else p for p in path))
            item.setData(ROLE, (row, path))
            listing.addItem(item)
        def navigate(item):
            row, path = item.data(ROLE)
            if isinstance(row, str):
                self.open(row, True)
            else:
                current = getattr(self.editor, '_block_macro_row', -1)
                current = current if current >= 0 else len(self.macros()) - 1
                if row != current:
                    self.editor._block_navigation = (row, path)
                    self.editor.accept()
                    if self.editor.result() == QtWidgets.QDialog.DialogCode.Accepted:
                        dialog.close()
                    return
                from shared_ui import navigate_usage
                navigate_usage(self.editor, path, self.macros()[row])
            dialog.close()
        listing.itemDoubleClicked.connect(navigate)
        dialog.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose)
        dialog.show()

    def find_matches(self, _checked=False, *, automatic=False):
        if self.active not in self.entries:
            self.error('기준이 될 공용 블록을 먼저 선택하세요.')
            return
        self.save_definition()
        ref = self.active
        source = self.entries[ref]['actions']
        if not source:
            self.error('비어 있는 블록은 중복 검색에서 제외됩니다.')
            return
        signature = fingerprint(source)
        dialog = QtWidgets.QDialog(self.editor)
        dialog.setWindowTitle('동일한 묶음 검토 · 현재 매크로')
        dialog.setModal(False)
        dialog.resize(680, 420)
        layout = QtWidgets.QVBoxLayout(dialog)
        summary = QtWidgets.QLabel('이름뿐 아니라 조건·시간·분기까지 완전히 같은 묶음만 교체합니다.')
        summary.setWordWrap(True)
        layout.addWidget(summary)
        listing = QtWidgets.QListWidget()
        layout.addWidget(listing)
        candidates = []
        for tree in self.source_trees:
            def scan(parent):
                owner = parent.data(0, ROLE)
                priority = isinstance(owner, Action) and owner.type == 'group' and owner.group_mode in ('first_true', 'first_true_continue', 'first_true_return')
                index = 0
                while index < parent.childCount():
                    items = [parent.child(i) for i in range(index, min(parent.childCount(), index + len(source)))]
                    actions = [tree._action_from_item(i) for i in items]
                    if not priority and len(actions) == len(source) and all(actions) and fingerprint([a.to_dict() for a in actions]) == signature:
                        candidates.append((tree, items, [tree._item_path_key(i) for i in items]))
                        section = ('일반 액션', '병렬 작업', '중단 시 실행')[self.source_trees.index(tree)]
                        ancestry = []
                        node = items[0]
                        while node is not None:
                            data = node.data(0, ROLE)
                            ancestry.append(getattr(data, 'name', None) or getattr(data, 'type', None) or node.text(1))
                            node = node.parent()
                        location = ' → '.join(str(n + 1) for n in tree._item_path_key(items[0]))
                        item = QtWidgets.QListWidgetItem(f'{self.editor.name_edit.text() or "현재 매크로"} / {section} / {location}\n' + ' → '.join(reversed(ancestry)))
                        item.setCheckState(QtCore.Qt.CheckState.Unchecked)
                        listing.addItem(item)
                        index += len(source)
                    else:
                        scan(parent.child(index))
                        index += 1
            scan(tree.invisibleRootItem())
        if automatic and not candidates:
            dialog.deleteLater()
            return
        summary.setText(f'현재 매크로에서 동일한 묶음 {len(candidates)}곳을 찾았습니다.\n'
                        '아래 위치도 같은 공용 블록으로 변경할까요? 변경할 위치를 체크하세요.\n'
                        '조건·시간·분기가 다른 묶음은 제외됩니다.')
        selection = QtWidgets.QHBoxLayout()
        for label, state in [('전체 선택', QtCore.Qt.CheckState.Checked), ('전체 해제', QtCore.Qt.CheckState.Unchecked)]:
            select = QtWidgets.QPushButton(label)
            select.clicked.connect(lambda checked=False, value=state: [listing.item(i).setCheckState(value) for i in range(listing.count())])
            selection.addWidget(select)
        layout.addLayout(selection)
        button = QtWidgets.QPushButton(f'선택한 위치를 연결로 교체 · 후보 {len(candidates)}곳')
        layout.addWidget(button)
        def apply():
            chosen = [candidate for i, candidate in enumerate(candidates) if listing.item(i).checkState() == QtCore.Qt.CheckState.Checked]
            if ref not in self.entries or fingerprint(self.entries[ref]['actions']) != signature:
                self.error('검토 중 공용 원본이 변경되었습니다. 다시 검색하세요.')
                return
            for tree, items, positions in chosen:
                live = list(tree.items())
                if (any(not any(i is node for node in live) for i in items)
                        or positions != [tree._item_path_key(i) for i in items]
                        or fingerprint([tree._action_from_item(i).to_dict() for i in items]) != signature):
                    self.error('검토 중 액션이 변경되었습니다. 다시 검색하세요.')
                    return
            self.flush()
            for tree, items, _positions in chosen:
                self.replace(tree, items, [Action(type='shared_block', block_ref=ref, name=self.entries[ref]['name'])])
            self.refresh_links()
            self.flush()
            dialog.close()
        button.clicked.connect(apply)
        cancel = QtWidgets.QPushButton('나중에 / 닫기')
        cancel.clicked.connect(dialog.reject)
        layout.addWidget(cancel)
        dialog.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose)
        dialog.show()

    def conditions(self):
        controller = getattr(self.owner, '_shared_controller', None)
        if controller:
            controller.show()

    def restore(self, entries):
        visible = not self.panel.isHidden()
        self.timer.stop()
        self.loading = True
        self.editing = False
        self.entries = copy.deepcopy(entries)
        self.loading = False
        self.refresh_links()
        if visible and self.active in self.entries:
            self.open(self.active, True)
        else:
            self.panel.hide()


def attach(editor):
    editor.block_workspace = BlockWorkspace(editor)
