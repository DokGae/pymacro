"""Readable condition structure without changing condition or drag/drop data."""
from PyQt6 import QtCore, QtGui, QtWidgets

TYPE_LABEL_ROLE = QtCore.Qt.ItemDataRole.UserRole + 51
STRUCTURE_COLORS = {
    'all': ('#537BA6', '#EFF4FA'),
    'any': ('#8970AA', '#F5F1FA'),
    'branch_true': ('#508574', '#EFF7F3'),
    'branch_false': ('#A17D49', '#FAF5EC'),
}


def structure_palette(item):
    node = item
    while node is not None:
        data = node.data(0, QtCore.Qt.ItemDataRole.UserRole)
        key = data if isinstance(data, str) else getattr(data, 'type', None)
        if key in STRUCTURE_COLORS:
            return STRUCTURE_COLORS[key]
        node = node.parent()
    return '#8C9AA8', '#FFFFFF'


def structure_disabled(item):
    while item is not None:
        if item.flags() & QtCore.Qt.ItemFlag.ItemIsUserCheckable and item.checkState(3) == QtCore.Qt.CheckState.Unchecked:
            return True
        item = item.parent()
    return False


class ConditionStructureTreeMixin:
    """Draw ownership rails in the existing indentation area, without marker rows."""
    def drawBranches(self, painter, rect, index):
        item = self.itemFromIndex(index)
        if item is None:
            return
        selected = self.currentItem()
        chain = []
        while selected is not None:
            chain.append(selected)
            selected = selected.parent()
        step = self.indentation()
        x, y = rect.right() - step // 2, rect.center().y()
        active = item in chain
        painter.save()
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
        def rail_pen(owner):
            color = '#C2C7CC' if structure_disabled(owner) else structure_palette(owner)[0]
            painter.setPen(QtGui.QPen(QtGui.QColor(color), 2 if active else 1.3))
        parent = item.parent()
        if parent is not None:
            rail_pen(parent)
            rail = x - step
            last = parent.indexOfChild(item) == parent.childCount() - 1
            painter.drawLine(rail, rect.top(), rail, y if last else rect.bottom() + 1)
            painter.drawLine(rail, y, x - 5, y)
            # A small arrow makes the direction of membership explicit.
            painter.drawLine(x - 8, y - 3, x - 5, y)
            painter.drawLine(x - 8, y + 3, x - 5, y)
            ancestor, rail = parent, rail - step
            while ancestor.parent() is not None:
                owner = ancestor.parent()
                if owner.indexOfChild(ancestor) < owner.childCount() - 1:
                    rail_pen(owner)
                    painter.drawLine(rail, rect.top(), rail, rect.bottom() + 1)
                ancestor, rail = owner, rail - step
        if item.childCount():
            rail_pen(item)
            if item.isExpanded():
                painter.drawLine(x, y + 6, x, rect.bottom() + 1)
            painter.setPen(QtCore.Qt.PenStyle.NoPen)
            painter.setBrush(QtGui.QColor('#C2C7CC' if structure_disabled(item) else structure_palette(item)[0]))
            points = ([(x - 4, y - 2), (x + 4, y - 2), (x, y + 3)] if item.isExpanded() else
                      [(x - 2, y - 4), (x - 2, y + 4), (x + 3, y)])
            painter.drawPolygon(QtGui.QPolygon([QtCore.QPoint(*point) for point in points]))
        painter.restore()


def arrange_condition_editor(dialog, group, toolbar, organize_row):
    tree = dialog.condition_tree
    dialog.setObjectName('conditionEditor')
    dialog.setMinimumSize(500, 360)
    dialog.resize(680, 500)
    dialog.layout().setContentsMargins(10, 10, 10, 10)
    dialog.layout().setSpacing(8)
    group.setTitle('')
    group.setObjectName('conditionCanvas')
    group.layout().setContentsMargins(8, 8, 8, 8)
    group.layout().setSpacing(6)
    hint = group.layout().itemAt(group.layout().count() - 1).widget()
    if isinstance(hint, QtWidgets.QLabel):
        tree.setToolTip(hint.text())
        hint.hide()
    group.layout().removeItem(toolbar)
    group.layout().insertLayout(0, toolbar)
    dialog.add_group_btn.setText('그룹 추가')
    dialog.add_group_btn.setToolTip('AND: 모두 만족 / OR: 하나라도 만족하는 조건 묶음')
    dialog.edit_node_btn.setText('편집')

    # Keep frequent editing commands beside the ordering controls.
    toolbar.removeWidget(dialog.delete_node_btn)
    dialog.delete_node_btn.setText('삭제')
    organize_row.insertWidget(3, dialog.delete_node_btn)

    view = QtWidgets.QToolButton()
    view.setProperty('editorCommand', True)
    view.setText('보기')
    view.setPopupMode(QtWidgets.QToolButton.ToolButtonPopupMode.InstantPopup)
    view_menu = QtWidgets.QMenu(view)
    view_menu.addAction('모두 펼치기', tree.expandAll)
    view_menu.addAction('모두 접기', tree.collapseAll)
    view.setMenu(view_menu)
    toolbar.addWidget(view)

    dialog.viewer_btn.setText('뷰어')
    dialog.viewer_btn.setToolTip('이미지 뷰어 / 피커 · ' + dialog.viewer_status.text())
    dialog.debug_test_btn.setText('테스트')
    toolbar.addWidget(dialog.debug_test_btn)
    toolbar.addWidget(dialog.viewer_btn)
    dialog.viewer_status.hide()

    dialog.condition_logic = QtWidgets.QLabel()
    dialog.condition_logic.setObjectName('conditionLogic')
    dialog.condition_logic.setWordWrap(True)
    group.layout().insertWidget(1, dialog.condition_logic)
    dialog.condition_selection = QtWidgets.QLabel('조건을 선택하면 전체 내용과 위치를 확인할 수 있습니다.')
    dialog.condition_selection.setWordWrap(True)
    dialog.condition_selection.setTextFormat(QtCore.Qt.TextFormat.PlainText)
    dialog.condition_selection.setObjectName('conditionSelection')
    group.layout().insertWidget(group.layout().count() - 1, dialog.condition_selection)
    tree.currentItemChanged.connect(lambda *_: (update_selection(dialog), tree.viewport().update()))

    tree.setHeaderLabels(['조건 구조', '', '판정 기준', ''])
    tree.setColumnHidden(1, True)
    header = tree.header()
    header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.Interactive)
    header.resizeSection(0, 240)
    header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.Fixed)
    header.resizeSection(3, 28)
    header.moveSection(header.visualIndex(3), 0)
    header.setSectionsMovable(False)
    tree.setTreePosition(0)
    from editor_theme import ConditionCheckDelegate
    tree.setItemDelegateForColumn(3, ConditionCheckDelegate(tree))
    tree.headerItem().setToolTip(3, '체크하면 조건을 사용합니다. 해제하면 건너뜁니다. 활성 조건이 없으면 참으로 통과합니다.')
    tree.setAlternatingRowColors(False)
    tree.setIndentation(22)
    tree.setUniformRowHeights(True)
    tree.setMinimumHeight(140)
    tree.setTextElideMode(QtCore.Qt.TextElideMode.ElideRight)
    dialog.condition_up_btn.setText('↑ 위로')
    dialog.condition_down_btn.setText('↓ 아래로')
    dialog.ok_btn.setObjectName('saveConditions')
    dialog.ok_btn.setText('저장')
    dialog.ok_btn.setDefault(True)
    footer = dialog.layout().itemAt(dialog.layout().count() - 1).layout()
    footer.removeWidget(dialog.ok_btn)
    footer.removeWidget(dialog.cancel_btn)
    footer.addWidget(dialog.cancel_btn)
    footer.addWidget(dialog.ok_btn)
    from editor_theme import apply_editor_theme
    dialog.ok_btn.setProperty('editorPrimary', True)
    dialog.delete_node_btn.setProperty('editorDanger', True)
    apply_editor_theme(dialog)
    # Use the same state store as the action editor, with independent geometry.
    from action_editor_ui import ActionEditorGeometry
    dialog._saved_geometry = ActionEditorGeometry(dialog, 'condition_editor')
    refresh_condition_presentation(dialog)


def update_selection(dialog):
    item = dialog.condition_tree.currentItem()
    if item is None:
        dialog.condition_selection.setText('조건을 선택하면 전체 내용과 위치를 확인할 수 있습니다.')
        return
    path = ['전체 조건']
    ancestry = []
    node = item
    while node is not None:
        ancestry.append(node.text(0))
        node = node.parent()
    path.extend(reversed(ancestry))
    dialog.condition_selection.setText('소속  ' + ' › '.join(path) + '\n' + item.text(2))


def refresh_condition_presentation(dialog):
    if not hasattr(dialog, 'condition_logic'):
        return
    tree = dialog.condition_tree
    blocker = QtCore.QSignalBlocker(tree)
    text = QtGui.QColor('#293541')

    def walk(item, inherited_disabled=False):
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        kind = getattr(data, 'type', None)
        disabled = inherited_disabled or (kind is not None and not dialog._item_enabled_state(item))
        original = item.data(0, TYPE_LABEL_ROLE)
        if original is None:
            original = item.text(0)
            item.setData(0, TYPE_LABEL_ROLE, original)
        accent = None
        if kind in ('all', 'any'):
            prefix = 'AND · 모두 만족' if kind == 'all' else 'OR · 하나라도 만족'
            item.setText(0, prefix + (' · ' + data.name if data.name else ''))
            if not data.shared_ref:
                item.setText(2, f'{len(data.conditions)}개 조건' + (' 모두 만족해야 참' if kind == 'all' else ' 중 하나라도 만족하면 참'))
            accent = QtGui.QColor(STRUCTURE_COLORS[kind][0])
        elif data in ('branch_true', 'branch_false'):
            item.setText(0, '참이면 →' if data == 'branch_true' else '거짓이면 →')
            item.setText(2, f'이 아래 {item.childCount()}개 조건 판정')
            accent = QtGui.QColor(STRUCTURE_COLORS[data][0])
        elif kind is not None:
            item.setText(0, f'{data.name} · {original}' if data.name else original)
        font = item.font(0)
        font.setBold(accent is not None)
        item.setFont(0, font)
        if accent is not None:
            tint = QtGui.QColor('#F4F6F8' if disabled else structure_palette(item)[1])
            for column in range(4):
                item.setBackground(column, tint)
        item.setForeground(0, QtGui.QColor('#9aa0a6') if disabled else accent or text)
        for column in (0, 2):
            item.setToolTip(column, item.text(column))
        if kind is not None:
            item.setToolTip(3, '사용 중 · 체크 해제하면 건너뜁니다.' if data.enabled else '사용 안 함 · 체크하면 사용합니다.')
        for i in range(item.childCount()):
            walk(item.child(i), disabled)

    for i in range(tree.topLevelItemCount()):
        walk(tree.topLevelItem(i))
    root = dialog.root_condition
    if root is None or (root.type == 'any' and not root.conditions):
        dialog.condition_logic.setText('조건 추가로 시작하세요. AND는 모두 만족, OR는 하나라도 만족하면 참입니다.')
    elif root.type == 'any':
        dialog.condition_logic.setText(f'전체 판정  OR · 최상위 {len(root.conditions)}개 중 하나라도 만족하면 참')
    else:
        dialog.condition_logic.setText('AND · 모두 만족    /    OR · 하나라도 만족    /    들여쓰기 · 같은 그룹 또는 분기')
    del blocker
    update_selection(dialog)
