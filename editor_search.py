"""Non-destructive search over the editor's actual action trees."""
from PyQt6 import QtCore, QtGui, QtWidgets
from engine import Action

ROLE = QtCore.Qt.ItemDataRole.UserRole
CHILDREN = {'actions', 'else_actions', 'elif_blocks', 'transition_actions'}


def values(value):
    if isinstance(value, dict):
        return ' '.join(values(v) for k, v in value.items() if k not in CHILDREN)
    if isinstance(value, (list, tuple)):
        return ' '.join(values(v) for v in value)
    return '' if value is None or isinstance(value, bool) else str(value)


class EditorSearch(QtWidgets.QWidget):
    def __init__(self, dialog):
        super().__init__(dialog)
        self.dialog = dialog
        self.trees = (dialog.main_action_tree, dialog.parallel_action_tree, dialog.stop_action_tree)
        self.saved = None
        self.query = ''
        self.matches = {}
        self.visible = {}
        self.position = -1
        row = QtWidgets.QHBoxLayout(self)
        row.setContentsMargins(0, 3, 0, 3)
        self.edit = QtWidgets.QLineEdit()
        self.edit.setPlaceholderText('현재 매크로 검색 · 이름, 설명, 조건, 액션, 키, 값 (Ctrl+F)')
        self.edit.setClearButtonEnabled(True)
        self.only = QtWidgets.QCheckBox('결과만 보기')
        self.only.setChecked(True)
        self.enabled = QtWidgets.QCheckBox('활성 항목만')
        self.enabled.setToolTip('상위 그룹이나 분기가 꺼진 항목도 제외합니다. 게임 조건 충족 여부와는 별개입니다.')
        self.count = QtWidgets.QLabel('')
        for widget in (self.edit, self.only, self.enabled, self.count):
            row.addWidget(widget)
        for title, delta in [('이전', -1), ('다음', 1)]:
            button = QtWidgets.QPushButton(title)
            button.clicked.connect(lambda _, d=delta: self.navigate(d))
            row.addWidget(button)
        self.timer = QtCore.QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.setInterval(160)
        self.timer.timeout.connect(self.apply)
        self.edit.textChanged.connect(lambda: self.timer.start())
        self.only.toggled.connect(self.apply)
        self.enabled.toggled.connect(self.apply)
        self.edit.returnPressed.connect(lambda: self.navigate(1))
        self.edit.installEventFilter(self)
        shortcut = QtGui.QShortcut(QtGui.QKeySequence('Ctrl+F'), dialog)
        shortcut.activated.connect(self.focus_search)
        for tree in self.trees:
            tree.editor_search = self
            tree.itemSelectionChanged.connect(self.update_count)

    def focus_search(self):
        self.edit.setFocus()
        self.edit.selectAll()

    def eventFilter(self, obj, event):
        if event.type() == QtCore.QEvent.Type.KeyPress:
            if event.key() == QtCore.Qt.Key.Key_Escape and self.edit.text():
                self.edit.clear()
                self.apply()
                return True
            if event.key() in (QtCore.Qt.Key.Key_Return, QtCore.Qt.Key.Key_Enter):
                self.apply()
                self.navigate(-1 if event.modifiers() & QtCore.Qt.KeyboardModifier.ShiftModifier else 1)
                return True
        return super().eventFilter(obj, event)

    def apply(self, *_):
        self.timer.stop()
        query = self.edit.text().strip().casefold()
        if query and self.saved is None:
            self.saved = [(t.view_state(), t._focus_item, t._focus_view,
                           t.horizontalScrollBar().value(), t.isColumnHidden(4)) for t in self.trees]
            self.saved_tab = self.dialog.action_tabs.currentIndex()
            for tree in self.trees:
                tree._focus_item = None
                tree.setRootIndex(QtCore.QModelIndex())
                tree.setColumnHidden(4, False)
                tree.setDragEnabled(False)
                tree.setAcceptDrops(False)
        changed = query != self.query
        self.query = query
        if not query and self.saved is not None:
            for tree, (view, focus, focus_view, horizontal, hidden) in zip(self.trees, self.saved):
                tree._focus_item, tree._focus_view = focus, focus_view
                if focus is not None and any(i is focus for i in tree.items()):
                    tree.setRootIndex(tree.indexFromItem(focus.parent()) if focus.parent() else QtCore.QModelIndex())
                else:
                    tree._focus_item = None
                tree.setColumnHidden(4, hidden)
                tree.setDragEnabled(True)
                tree.setAcceptDrops(True)
                tree.refresh_workspace()
                tree.restore_view(view)
                tree.horizontalScrollBar().setValue(horizontal)
            self.dialog.action_tabs.setCurrentIndex(self.saved_tab)
            self.saved = None
        else:
            for tree in self.trees:
                tree.refresh_workspace()
                if query:
                    blocker = QtCore.QSignalBlocker(tree)
                    for item in tree.items():
                        item.setExpanded(any(id(item.child(i)) in self.visible.get(tree, set()) for i in range(item.childCount())))
                    del blocker
                    tree.refresh_workspace()
        if changed:
            self.position = -1
        self.update_count()

    def prepare(self, tree, items):
        hits, visible = {}, set()
        if self.query:
            for item in items:
                data = item.data(0, ROLE)
                text = ' '.join(item.text(c) for c in range(tree.columnCount()))
                if isinstance(data, Action):
                    text += ' ' + values(data.to_dict())
                elif isinstance(data, dict):
                    text += ' ' + values({k: v.to_dict() if hasattr(v, 'to_dict') else v for k, v in data.items()})
                if self.query not in text.casefold():
                    continue
                disabled = tree._disabled_depth(item) is not None
                if self.enabled.isChecked() and disabled:
                    continue
                hits[id(item)] = '상위 또는 해당 항목 꺼짐' if disabled else '검색 일치'
                parent = item
                while parent is not None:
                    visible.add(id(parent))
                    parent = parent.parent()
        self.matches[tree], self.visible[tree] = hits, visible

    def hidden(self, tree, item):
        return bool(self.query and self.only.isChecked() and id(item) not in self.visible.get(tree, set()))

    def results(self):
        return [(tree, item) for tree in self.trees for item in tree.items()
                if id(item) in self.matches.get(tree, {})]

    def update_count(self):
        meta = ' '.join((self.dialog.name_edit.text(), self.dialog.desc_edit.text()))
        suffix = ' · 매크로 이름/설명 일치' if self.query and self.query in meta.casefold() else ''
        self.count.setText((f'{len(self.results())}건' + suffix) if self.query else '')

    def navigate(self, delta):
        results = self.results()
        if not results:
            return
        self.position = (self.position + delta) % len(results)
        tree, item = results[self.position]
        for index in range(self.dialog.action_tabs.count()):
            page = self.dialog.action_tabs.widget(index)
            if page is tree or page.isAncestorOf(tree):
                self.dialog.action_tabs.setCurrentIndex(index)
                break
        parent = item.parent()
        while parent is not None:
            parent.setExpanded(True)
            parent = parent.parent()
        tree.setCurrentItem(item)
        tree.scrollToItem(item)
        self.count.setText(f'{self.position + 1}/{len(results)}건')
