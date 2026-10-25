"""Small, explicit review of identical action bundles in the current editor."""
import copy
from dataclasses import dataclass

from PyQt6 import QtCore, QtWidgets
from engine import Action
from lib.shared_blocks import fingerprint, register, validate, walk

ROLE = QtCore.Qt.ItemDataRole.UserRole
PRIORITY = ('first_true', 'first_true_continue', 'first_true_return')


def safe(actions):
    # Moving these nodes under a new group could change their scope or retry behavior.
    return all(a.get('type') not in ('label', 'goto', 'shared_block')
               and not a.get('parallel_enabled') and int(a.get('confirm_fails', 1)) <= 1
               for _, a in walk(actions))


@dataclass
class Location:
    tree: object
    items: list
    paths: list
    actions: list
    label: str

    def current(self):
        live = list(self.tree.items())
        return (all(any(item is node for node in live) for item in self.items)
                and self.paths == [self.tree._item_path_key(i) for i in self.items]
                and fingerprint(self.actions) == fingerprint([self.tree._action_from_item(i).to_dict() for i in self.items]))

    def covered(self):
        def children(item):
            yield id(item)
            for i in range(item.childCount()):
                yield from children(item.child(i))
        return {node for item in self.items for node in children(item)}


def location(blocks, tree, items, actions):
    section = ('일반 액션', '병렬 작업', '중단 시 실행')[blocks.source_trees.index(tree)]
    names = []
    node = items[0]
    while node is not None:
        data = node.data(0, ROLE)
        names.append(getattr(data, 'name', None) or getattr(data, 'type', None) or node.text(1))
        node = node.parent()
    label = f'{section} · ' + ' › '.join(reversed(names))
    if len(items) > 1:
        label += f' 외 {len(items) - 1}개'
    return Location(tree, items, [tree._item_path_key(i) for i in items], copy.deepcopy(actions), label)


def suggested_name(occurrence):
    source = occurrence.actions
    if source[0].get('name'):
        return source[0]['name']
    node = occurrence.items[0].parent()
    while node is not None:
        name = getattr(node.data(0, ROLE), 'name', None)
        if name:
            return name + ' 내부 묶음'
        node = node.parent()
    return '액션 묶음'


def discover(blocks, selected=None):
    """Prefer larger non-overlapping bundles; do not guess semantic equivalence."""
    groups = {}
    target = None
    if selected:
        tree, items = selected
        target = [tree._action_from_item(i).to_dict() for i in items]
        if not safe(target):
            raise ValueError('라벨 이동·병렬 실행·조건 재확인·공용 호출이 포함된 묶음은 자동 정리에서 제외됩니다.')
        target_key = tuple(fingerprint([a]) for a in target)
    for tree in blocks.source_trees:
        def scan(parent):
            owner = parent.data(0, ROLE)
            priority = isinstance(owner, Action) and owner.type == 'group' and owner.group_mode in PRIORITY
            items = [parent.child(i) for i in range(parent.childCount())]
            actions = [tree._action_from_item(i) for i in items]
            data = [a.to_dict() if a else None for a in actions]
            tokens = [fingerprint([a]) if a is not None and safe([a]) else None for a in data]
            if not priority:
                for start in range(len(items)):
                    sizes = [len(target)] if target is not None else range(1, min(8, len(items) - start) + 1)
                    for size in sizes:
                        if start + size > len(items):
                            continue
                        key = tuple(tokens[start:start + size])
                        if None in key or (target is not None and key != target_key):
                            continue
                        source = data[start:start + size]
                        if target is None and sum(1 for _ in walk(source)) < 2:
                            continue
                        groups.setdefault(key, []).append(location(blocks, tree, items[start:start + size], source))
            for item in items:
                scan(item)
        scan(tree.invisibleRootItem())
    ranked = sorted(groups.items(), key=lambda pair: sum(1 for _ in walk(pair[1][0].actions)), reverse=True)
    claimed = set()
    result = []
    for key, occurrences in ranked:
        accepted, occupied = [], set(claimed)
        for occurrence in occurrences:
            covered = occurrence.covered()
            if not covered & occupied:
                accepted.append(occurrence)
                occupied.update(covered)
        if len(accepted) < (1 if selected else 2):
            continue
        claimed = occupied
        result.append(accepted)
    return result


class SuggestionDialog(QtWidgets.QDialog):
    def __init__(self, blocks, selected=None):
        super().__init__(blocks.editor)
        self.blocks = blocks
        self.selected = selected
        self.setWindowTitle('묶음 추천 · 현재 매크로')
        self.setModal(False)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose)
        self.resize(800, 620)
        layout = QtWidgets.QVBoxLayout(self)
        self.status = QtWidgets.QLabel('동일한 내용만 추천합니다. 원하는 후보와 위치를 선택하세요.')
        self.status.setWordWrap(True)
        layout.addWidget(self.status)
        self.candidates = QtWidgets.QComboBox()
        self.candidates.currentIndexChanged.connect(self.select)
        layout.addWidget(self.candidates)
        self.preview = QtWidgets.QTreeWidget()
        self.preview.setHeaderLabels(['묶음 내용', '설정'])
        self.preview.setColumnWidth(0, 250)
        layout.addWidget(self.preview, 2)
        self.locations = QtWidgets.QListWidget()
        layout.addWidget(self.locations, 1)
        self.locations.itemChanged.connect(self.update_buttons)
        row = QtWidgets.QHBoxLayout()
        for title, callback in [('전체 선택', lambda: self.check_all(True)), ('전체 해제', lambda: self.check_all(False)),
                                ('위치 보기', self.reveal), ('다시 찾기', self.reload)]:
            button = QtWidgets.QPushButton(title)
            button.clicked.connect(callback)
            row.addWidget(button)
        layout.addLayout(row)
        self.locations.itemDoubleClicked.connect(lambda *_: self.reveal())
        name_row = QtWidgets.QHBoxLayout()
        name_row.addWidget(QtWidgets.QLabel('묶음 이름'))
        self.name = QtWidgets.QLineEdit()
        self.name.textChanged.connect(self.update_buttons)
        name_row.addWidget(self.name)
        layout.addLayout(name_row)
        row = QtWidgets.QHBoxLayout()
        self.group_button = QtWidgets.QPushButton('일반 그룹으로 정리')
        self.group_button.setToolTip('각 위치를 독립적인 그룹으로 묶습니다.')
        self.shared_button = QtWidgets.QPushButton('하나의 공용 블록으로')
        self.shared_button.setToolTip('선택한 모든 위치가 하나의 원본을 공유합니다.')
        self.group_button.clicked.connect(lambda: self.apply(False))
        self.shared_button.clicked.connect(lambda: self.apply(True))
        close = QtWidgets.QPushButton('닫기')
        close.clicked.connect(self.close)
        for button in (self.group_button, self.shared_button, close):
            row.addWidget(button)
        layout.addLayout(row)
        self.reload()

    def reload(self):
        # The selected source is captured on first search; subsequent searches cover the macro.
        error = None
        try:
            self.results = discover(self.blocks, self.selected)
        except ValueError as exc:
            self.results = []
            error = str(exc)
        self.selected = None
        blocker = QtCore.QSignalBlocker(self.candidates)
        self.candidates.clear()
        for occurrences in self.results:
            source = occurrences[0].actions
            title = suggested_name(occurrences[0])
            self.candidates.addItem(f'{title} · 동일 {len(occurrences)}곳 · 액션 {sum(1 for _ in walk(source))}개')
        del blocker
        self.select()
        if error:
            self.status.setText(error)

    def select(self, *_):
        self.preview.clear()
        self.locations.clear()
        index = self.candidates.currentIndex()
        self.occurrences = self.results[index] if 0 <= index < len(self.results) else []
        if not self.occurrences:
            self.status.setText('추천할 동일 묶음이 없습니다. 원하는 연속 액션을 선택한 뒤 우클릭 → 이 부분과 같은 묶음 찾기도 사용할 수 있습니다.')
            self.update_buttons()
            return
        source = self.occurrences[0].actions
        title = suggested_name(self.occurrences[0])
        names = {e['name'] for e in self.blocks.entries.values()}
        suggested = title
        number = 2
        while suggested in names:
            suggested = f'{title} {number}'
            number += 1
        self.name.setText(suggested)
        def add(actions, parent):
            for data in actions:
                action = Action.from_dict(data, self.blocks.editor._resolver)
                item = QtWidgets.QTreeWidgetItem([action.name or action.type, self.blocks.editor.main_action_tree._format_value(action)])
                parent.addChild(item)
                add(data.get('actions', []), item)
                for branch in data.get('elif_blocks', []):
                    child = QtWidgets.QTreeWidgetItem(['ELIF', ''])
                    item.addChild(child)
                    add(branch.get('actions', []), child)
                for key, title in [('else_actions', 'IF NOT'), ('transition_actions', '참 → 거짓')]:
                    if data.get(key):
                        child = QtWidgets.QTreeWidgetItem([title, ''])
                        item.addChild(child)
                        add(data[key], child)
        add(source, self.preview.invisibleRootItem())
        self.preview.expandAll()
        for occurrence in self.occurrences:
            item = QtWidgets.QListWidgetItem(occurrence.label)
            item.setCheckState(QtCore.Qt.CheckState.Checked)
            self.locations.addItem(item)
        self.update_buttons()

    def check_all(self, checked):
        for index in range(self.locations.count()):
            self.locations.item(index).setCheckState(QtCore.Qt.CheckState.Checked if checked else QtCore.Qt.CheckState.Unchecked)

    def chosen(self):
        return [o for i, o in enumerate(getattr(self, 'occurrences', []))
                if i < self.locations.count() and self.locations.item(i).checkState() == QtCore.Qt.CheckState.Checked]

    def update_buttons(self, *_):
        if not hasattr(self, 'group_button'):
            return
        count = len(self.chosen())
        enabled = bool(count and self.name.text().strip())
        self.group_button.setEnabled(enabled)
        self.shared_button.setEnabled(enabled)
        if getattr(self, 'occurrences', []):
            self.status.setText(f'선택 {count}곳을 각각 한 줄로 묶습니다. 일반 그룹은 개별 수정, 공용 블록은 원본을 함께 사용합니다.')

    def reveal(self):
        row = self.locations.currentRow()
        if not 0 <= row < len(self.occurrences):
            return
        occurrence = self.occurrences[row]
        if not occurrence.current():
            self.status.setText('편집 내용이 변경되었습니다. 다시 찾기를 눌러주세요.')
            return
        editor, tree = self.blocks.editor, occurrence.tree
        page = (editor.main_action_page if tree is editor.main_action_tree else
                editor.parallel_action_page if tree is editor.parallel_action_tree else editor.stop_group)
        editor.action_tabs.setCurrentWidget(page)
        if tree._focus_item is not None:
            tree.toggle_focus()
        tree.hide_disabled_button.setChecked(False)
        node = occurrence.items[0].parent()
        while node is not None:
            node.setExpanded(True)
            node = node.parent()
        tree.clearSelection()
        tree.setCurrentItem(occurrence.items[0])
        tree.scrollToItem(occurrence.items[0], QtWidgets.QAbstractItemView.ScrollHint.PositionAtCenter)

    def apply(self, shared):
        chosen = self.chosen()
        name = self.name.text().strip()
        if not chosen or not name:
            return
        if any(child.isVisible() and child.__class__.__name__ in ('ActionEditDialog', 'ConditionDialog', 'ConditionNodeDialog')
               for child in self.blocks.editor.findChildren(QtWidgets.QDialog)):
            self.status.setText('열린 액션·조건 편집을 확인 또는 취소한 뒤 적용하세요.')
            return
        if not all(o.current() for o in chosen):
            self.status.setText('검토 중 액션이 변경되었습니다. 다시 찾기를 눌러주세요.')
            return
        entries = copy.deepcopy(self.blocks.entries)
        try:
            ref = register(entries, name, chosen[0].actions) if shared else None
            if shared:
                validate(entries, resolver=self.blocks.editor._resolver)
            replacements = [Action(type='shared_block', block_ref=ref, name=name) if shared else
                            Action(type='group', name=name, group_mode='all',
                                   actions=[Action.from_dict(a, self.blocks.editor._resolver) for a in o.actions])
                            for o in chosen]
        except ValueError as exc:
            self.status.setText(str(exc))
            return
        self.blocks.flush()
        if shared:
            self.blocks.entries = entries
        for occurrence, replacement in zip(chosen, replacements):
            self.blocks.replace(occurrence.tree, occurrence.items, [replacement])
        self.blocks.refresh_links()
        self.blocks.flush()
        self.close()


def show(blocks, tree=None):
    selected = None
    if tree is not None:
        try:
            selected = blocks.selected(tree)
        except ValueError as exc:
            blocks.error(exc)
            return
    dialog = SuggestionDialog(blocks, selected)
    dialog.show()
    return dialog
