"""IF test controls, runtime badges and execution position in the action tree."""
import copy

from PyQt6 import QtCore, QtWidgets, sip

from if_test_runtime import locate


MODE_LABELS = {'actual': '실제 조건 사용', 'once': '다음 1회 강제 참', 'always': '계속 강제 참'}
ROLE = QtCore.Qt.ItemDataRole.UserRole


def tree_paths(tree, root_offset=0):
    """Branch headers do not consume runner action indices."""
    from engine import Action

    def walk(items, prefix=(), offset=0):
        position = offset
        for item in items:
            data = item.data(0, ROLE)
            children = [item.child(i) for i in range(item.childCount())]
            if isinstance(data, Action):
                path = prefix + (position,)
                yield path, item
                yield from walk(children, path)
                position += 1
            else:
                nested = list(walk(children, prefix, position))
                yield from nested
                position += sum(len(path) == len(prefix) + 1 for path, _ in nested)

    yield from walk([tree.topLevelItem(i) for i in range(tree.topLevelItemCount())], offset=root_offset)


def add_test_panel(dialog, layout):
    from action_editor_ui import FoldSection

    panel = FoldSection('IF 실행 테스트')
    panel.toggle.setToolTip('필요할 때 펼쳐서 IF 강제 판정과 실행 테스트를 사용합니다.')
    box = QtWidgets.QVBoxLayout(panel.body)
    box.setContentsMargins(8, 4, 8, 4)
    row = QtWidgets.QHBoxLayout()
    row.addWidget(QtWidgets.QLabel('조건 판정'))
    combo = QtWidgets.QComboBox()
    for mode, label in MODE_LABELS.items():
        combo.addItem(label, mode)
    row.addWidget(combo, 1)
    box.addLayout(row)
    buttons = QtWidgets.QHBoxLayout()
    start = QtWidgets.QPushButton('▶ 이 IF부터 실행')
    stop = QtWidgets.QPushButton('■ 중지 / 강제 해제')
    buttons.addWidget(start)
    buttons.addWidget(stop)
    box.addLayout(buttons)
    hint = QtWidgets.QLabel('선택한 IF부터 사이클 끝까지 1회 실행합니다. 실제 키 입력이 발생합니다.\n'
                            '강제 판정은 임시 설정이며, 실행 종료·정지·파일 전환 시 해제됩니다.')
    hint.setWordWrap(True)
    box.addWidget(hint)
    status = QtWidgets.QLabel('액션을 추가하고 매크로를 적용한 뒤 사용할 수 있습니다.')
    status.setWordWrap(True)
    box.addWidget(status)
    history = QtWidgets.QPlainTextEdit()
    history.setReadOnly(True)
    history.setMaximumHeight(100)
    history.setPlaceholderText('실행한 액션과 IF 판정 결과가 여기에 표시됩니다.')
    box.addWidget(history)
    layout.addWidget(panel)
    dialog.if_test_panel = panel
    dialog.if_test_combo = combo
    dialog.if_test_start = start
    dialog.if_test_stop = stop
    dialog.if_test_status = status
    dialog.if_test_history = history
    dialog._if_test_message = ''
    combo.setEnabled(False)
    start.setEnabled(False)
    stop.setEnabled(False)


class EditorTests(QtCore.QObject):
    def __init__(self, editor, engine):
        super().__init__(editor)
        self.editor = editor
        self.engine = engine
        self.panels = []
        self.timer = QtCore.QTimer(self)
        self.timer.setInterval(250)
        self.timer.timeout.connect(self.refresh)
        self.timer.start()
        editor.finished.connect(self.closed)
        self.owned_runner = None

    @property
    def index(self):
        return getattr(self.editor, '_block_macro_row', -1)

    def trees(self):
        editor = self.editor
        return ((editor.main_action_tree, False, 0),
                (editor.parallel_action_tree, False, editor.main_action_tree.topLevelItemCount()),
                (editor.stop_action_tree, True, 0))

    def bind(self, dialog, item, tree):
        selected = next(((stop, path) for candidate, stop, offset in self.trees()
                         if candidate is tree for path, node in tree_paths(tree, offset) if node is item), None)
        if selected is None or self.index < 0:
            return
        stop, path = selected
        dialog._if_test_binding = (stop, path, item, tree)
        self.panels.append(dialog)
        dialog.if_test_combo.setEnabled(True)
        dialog.if_test_stop.setEnabled(True)
        can_start = tree is self.editor.main_action_tree
        dialog.if_test_start.setEnabled(can_start)
        if not can_start:
            dialog.if_test_start.setToolTip('선택 위치부터 실행은 메인사이클의 IF에서 사용합니다.')
        dialog.if_test_combo.currentIndexChanged.connect(lambda *_: self.set_mode(dialog))
        dialog.if_test_start.clicked.connect(lambda: self.start(dialog))
        dialog.if_test_stop.clicked.connect(self.stop)
        dialog.finished.connect(lambda code: self.finished(dialog, code))
        self.refresh()

    def source(self, dialog):
        stop, path, item, tree = dialog._if_test_binding
        if sip.isdeleted(item) or item.treeWidget() is not tree:
            raise ValueError('액션이 변경되었습니다. 설정창을 다시 열어 주세요.')
        offset = self.editor.main_action_tree.topLevelItemCount() if tree is self.editor.parallel_action_tree else 0
        actual_path = next((p for p, node in tree_paths(tree, offset) if node is item), None)
        if actual_path != path:
            raise ValueError('액션 위치가 변경되었습니다. 설정창을 다시 열어 주세요.')
        return tree._action_from_item(item)

    def set_mode(self, dialog):
        try:
            dialog._if_test_message = ''
            action = self.source(dialog)
            stop, path, _, _ = dialog._if_test_binding
            self.engine.if_test_state.set(self.index, stop, path, action, dialog.if_test_combo.currentData())
            self.refresh()
        except ValueError as exc:
            dialog._if_test_message = str(exc)
            dialog.if_test_status.setText(str(exc))

    def finished(self, dialog, code):
        # Applying ordinary action edits must keep the pending test attached to
        # the new definition, without adding any fields to the saved action.
        stop, path, _, _ = dialog._if_test_binding
        state = self.engine.if_test_state
        mode = state.mode(self.index, stop, path)
        if mode != 'actual' and code == QtWidgets.QDialog.DialogCode.Accepted:
            try:
                action = dialog.get_action()
                state.set(self.index, stop, path, action, mode if action.type == 'if' else 'actual')
            except ValueError:
                state.set(self.index, stop, path, None, 'actual')
        if dialog in self.panels:
            self.panels.remove(dialog)

    def start(self, dialog):
        try:
            dialog._if_test_message = ''
            self.source(dialog)
            stop, path, _, _ = dialog._if_test_binding
            macro = self.editor.get_macro()
            actions, position, _ = locate(macro.actions, path)
            action = dialog.get_action()
            if action.type != 'if':
                raise ValueError('IF 액션에서만 실행할 수 있습니다.')
            actions[position] = copy.deepcopy(action)
            mode = dialog.if_test_combo.currentData()
            ok, reason = self.engine.run_macro_from_if_manual(
                self.index, macro, path, shared_blocks=self.editor.block_workspace.entries, test_mode=mode)
            if not ok:
                messages = {'engine_not_running': '먼저 엔진을 시작해 주세요.',
                            'engine_inactive': '엔진을 활성화하고 일시정지를 해제해 주세요.',
                            'already_running': '이 매크로가 실행 중입니다. 중지 후 테스트해 주세요.',
                            'macro_disabled': '매크로 사용을 켜 주세요.',
                            'not_found': '매크로를 먼저 적용해 주세요.'}
                dialog._if_test_message = messages.get(reason, reason)
                dialog.if_test_status.setText(dialog._if_test_message)
                return
            self.owned_runner = self.engine._macro_runners.get(self.index)
            dialog.if_test_status.setText('선택한 IF부터 실행 중')
        except (ValueError, RuntimeError) as exc:
            dialog._if_test_message = str(exc)
            dialog.if_test_status.setText(str(exc))

    def stop(self):
        runner = self.engine._macro_runners.get(self.index)
        if runner is not None and runner.is_alive():
            runner.stop()
        self.engine.if_test_state.clear(self.index)
        for dialog in self.panels:
            dialog._if_test_message = ''
        self.refresh()

    def closed(self, *_):
        self.timer.stop()
        if self.owned_runner is not None and self.owned_runner.is_alive():
            self.owned_runner.stop()

    def refresh(self):
        if self.index < 0:
            return
        state = self.engine.if_test_state
        current = state.current(self.index)
        for tree, stop, offset in self.trees():
            for path, item in tree_paths(tree, offset):
                mode = state.mode(self.index, stop, path)
                badge = ' [1회 강제 참 · 대기]' if mode == 'once' else ' [계속 강제 참]' if mode == 'always' else ''
                if current and current[:2] == (stop, path) and current[2] == 'action_start':
                    badge += ' [▶ 실행 중]'
                # Keep transient text out of the definition and undo history.
                base_role, rendered_role = ROLE + 201, ROLE + 202
                if item.text(3) != item.data(3, rendered_role):
                    with QtCore.QSignalBlocker(tree):
                        item.setData(3, base_role, item.text(3))
                base = item.data(3, base_role) or ''
                rendered = (badge.strip() + ' ' if badge else '') + base
                if item.text(3) != rendered:
                    with QtCore.QSignalBlocker(tree):
                        item.setData(3, rendered_role, rendered)
                        item.setText(3, rendered)
        for dialog in list(self.panels):
            if sip.isdeleted(dialog):
                self.panels.remove(dialog)
                continue
            stop, path, _, _ = dialog._if_test_binding
            mode = state.mode(self.index, stop, path)
            with QtCore.QSignalBlocker(dialog.if_test_combo):
                dialog.if_test_combo.setCurrentIndex(dialog.if_test_combo.findData(mode))
            if dialog._if_test_message:
                dialog.if_test_status.setText(dialog._if_test_message)
            elif current:
                label = '실행 중: ' if current[2] == 'action_start' else '최근 실행: '
                dialog.if_test_status.setText(label + current[3])
            else:
                dialog.if_test_status.setText(MODE_LABELS[mode] + ' · 강제 판정은 선택 즉시 적용됩니다.')
            history = '\n'.join(state.history(self.index))
            if dialog.if_test_history.toPlainText() != history:
                dialog.if_test_history.setPlainText(history)
                bar = dialog.if_test_history.verticalScrollBar()
                bar.setValue(bar.maximum())


def bind_test_panel(dialog, editor, item, tree):
    action = item.data(0, ROLE)
    if getattr(action, 'type', None) != 'if':
        return
    owner = editor.parentWidget()
    while owner is not None and not hasattr(owner, 'engine'):
        owner = owner.parentWidget()
    if owner is None or not hasattr(owner.engine, 'if_test_state'):
        return
    session = getattr(editor, '_if_tests', None)
    if session is None:
        session = editor._if_tests = EditorTests(editor, owner.engine)
    session.bind(dialog, item, tree)
