"""Action-list presentation and editor-local history; no executable marker nodes."""
from __future__ import annotations

import copy
import uuid
from PyQt6 import QtCore, QtGui, QtWidgets
from engine import Action
from action_controls import if_scope_label

ROLE = QtCore.Qt.ItemDataRole.UserRole


class ScopeDelegate(QtWidgets.QStyledItemDelegate):
    def __init__(self, tree, original):
        super().__init__(tree)
        self.tree, self.original = tree, original

    def sizeHint(self, option, index):
        size = self.original.sizeHint(option, index)
        size.setHeight(self.tree.row_height)
        return size

    def paint(self, painter, option, index):
        self.tree.paint_html_cell(painter, option, index)


class ActionWorkspaceMixin:
    """Layer readable scopes over the original tree without changing its hierarchy."""
    def __init__(self, parent=None):
        super().__init__(parent)
        self.row_height, self.footer_height = 24, 19
        self._scope_ids, self._ends, self._bands = {}, {}, {}
        self._focus_item = None
        self._focus_view = None
        self._hide_disabled = False
        self._destination_items = []
        self._workspace_pending = False
        self._workspace_updating = False
        self.history = None
        self._grip_pressed = False
        self._move_target = None
        self._type_indent = 17
        self.setMouseTracking(True)
        self.viewport().setMouseTracking(True)
        self.setUniformRowHeights(False)
        self.setItemDelegateForColumn(5, QtWidgets.QStyledItemDelegate(self))
        self._scope_delegates = []
        for column in range(6):
            original = self.itemDelegateForColumn(column) or self.itemDelegate()
            delegate = ScopeDelegate(self, original)
            self._scope_delegates.append(delegate)
            self.setItemDelegateForColumn(column, delegate)
        self.header().setStretchLastSection(False)
        self.header().setSectionResizeMode(QtWidgets.QHeaderView.ResizeMode.Interactive)
        self.header().setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.Interactive)
        self.header().setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeMode.Interactive)
        self.header().setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.Interactive)
        self.setColumnWidth(0, 44)
        self.setColumnWidth(1, 142)
        self.setColumnWidth(2, 310)
        self.header().setSectionResizeMode(5, QtWidgets.QHeaderView.ResizeMode.Interactive)
        self.header().setMinimumSectionSize(28)
        self.setColumnWidth(5, 28)
        self.headerItem().setText(5, '')
        self.headerItem().setToolTip(5, '활성')
        self.setColumnHidden(4, True)
        self.header().setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.Interactive)
        self.setColumnWidth(3, 360)
        self.setStyleSheet(self.styleSheet() +
            'QTreeWidget {border:1px solid #cbd5e2;background:white;color:#24364e;}'
            'QHeaderView::section {background:#f6f8fb;color:#4e5e74;border:0;'
            'border-bottom:1px solid #cdd7e3;padding:6px;}'
            'QTreeWidget::item {border:0;}')
        self.itemSelectionChanged.connect(self._selection_updated)
        self.itemExpanded.connect(self.schedule_workspace)
        self.itemCollapsed.connect(self.schedule_workspace)
        self.verticalScrollBar().valueChanged.connect(self.update_location)
        for signal in (self.model().rowsInserted, self.model().rowsRemoved,
                       self.model().modelReset, self.model().dataChanged):
            signal.connect(self.schedule_workspace)
        self.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.CustomContextMenu)
        self.customContextMenuRequested.connect(self.workspace_menu)

    def items(self):
        def walk(item):
            yield item
            for i in range(item.childCount()):
                yield from walk(item.child(i))
        for i in range(self.topLevelItemCount()):
            yield from walk(self.topLevelItem(i))

    def is_if(self, item):
        return item is not None and isinstance(item.data(0, ROLE), Action) and item.data(0, ROLE).type == 'if'

    def owner_if(self, item):
        while item is not None:
            if self.is_if(item):
                return item
            item = item.parent()
        return None

    def scope_name(self, item):
        if item is None:
            return '일반 액션'
        data = item.data(0, ROLE)
        return if_scope_label(self._scope_ids.get(id(item), '?'), getattr(data, 'name', ''))

    def ends_for(self, index):
        return self._bands.get(id(self.itemFromIndex(index)), [])

    def schedule_workspace(self, *_):
        if self._workspace_updating or self._workspace_pending:
            return
        self._workspace_pending = True
        QtCore.QTimer.singleShot(0, self.refresh_workspace)

    def refresh_workspace(self):
        self._workspace_pending = False
        if self._workspace_updating:
            return
        self._workspace_updating = True
        try:
            items = list(self.items())
            if self._focus_item is not None and not any(i is self._focus_item for i in items):
                self._focus_item = None
                self._focus_view = None
                self.setRootIndex(QtCore.QModelIndex())
                for item in items:
                    item.setHidden(False)
            scopes = [i for i in items if self.is_if(i)]
            self._scope_ids = {id(item): f'{n:02}' for n, item in enumerate(scopes, 1)}
            self._ends = {}
            self._bands = {}
            blocker = QtCore.QSignalBlocker(self)
            for item in items:
                in_focus = (self._focus_item is None or item is self._focus_item
                            or self._is_descendant(item, self._focus_item)
                            or self._is_descendant(self._focus_item, item))
                hidden = not in_focus or (self._hide_disabled and self._disabled_depth(item) is not None)
                item.setHidden(hidden)
                if hidden and item.isSelected():
                    item.setSelected(False)
                if hidden and item is self.currentItem():
                    self.setCurrentItem(None)
                data = item.data(0, ROLE)
                if data in ('__else__', '__transition__') or isinstance(data, dict) and data.get('marker') == '__elif__':
                    if item.data(2, ROLE + 61) is None:
                        item.setData(2, ROLE + 61, item.text(2))
                    item.setText(2, self.scope_name(item.parent()))
                elif self.is_if(item):
                    item.setText(2, self.scope_name(item))
                description = item.text(4).strip()
                for column in range(self.columnCount()):
                    item.setToolTip(column, description)
            # Inner ends precede outer ends when they share the same last visible row.
            def last_visible(item):
                last = item
                while last.isExpanded():
                    children = [last.child(i) for i in range(last.childCount()) if not last.child(i).isHidden()]
                    if not children:
                        break
                    last = children[-1]
                return last

            live_ids = {id(i) for i in items}
            self._destination_items = [i for i in self._destination_items if id(i) in live_ids]
            if any(target is not None and id(target) not in live_ids for target, _ in getattr(self, '_targets', [])):
                self._targets = []
                self._destination_items = []
                self.destination_panel.hide()
                self.target_card.hide()
            for scope in reversed(scopes):
                if self._focus_item and scope is not self._focus_item and not self._is_descendant(scope, self._focus_item):
                    continue
                if scope.isHidden() or not scope.isExpanded():
                    continue
                last = last_visible(scope)
                self._ends.setdefault(id(last), []).append(scope)
            del blocker
            self.doItemsLayout()
            self.viewport().update()
            self.update_location()
            self._update_controls()
        finally:
            self._workspace_updating = False

    def renumber(self):
        super().renumber()
        if hasattr(self, '_scope_ids'):
            blocker = QtCore.QSignalBlocker(self)
            for item in self.items():
                if item.data(0, ROLE) in ('__else__', '__transition__'):
                    item.setText(0, '↳')
            del blocker
            self.schedule_workspace()

    def original_name(self, item):
        data = item.data(0, ROLE)
        if isinstance(data, Action):
            return data.name or ''
        saved = item.data(2, ROLE + 61)
        return saved if saved is not None else item.text(2)

    def _handle_item_changed(self, item, column):
        if column != 5:
            return
        data = item.data(0, ROLE)
        enabled = item.checkState(5) == QtCore.Qt.CheckState.Checked
        if isinstance(data, Action):
            data.enabled = enabled
        elif data == '__else__':
            owner = item.parent()
            owner_data = owner.data(0, ROLE) if owner else None
            if isinstance(owner_data, Action):
                owner_data.else_enabled = enabled
        elif data == '__transition__':
            owner = item.parent()
            owner_data = owner.data(0, ROLE) if owner else None
            if isinstance(owner_data, Action):
                owner_data.transition_enabled = enabled
        elif isinstance(data, dict) and data.get('marker') == '__elif__':
            data['enabled'] = enabled
            if data.get('condition') is not None:
                data['condition'].enabled = enabled
        self._apply_enabled_styles()
        self.viewport().update()

    def load_actions(self, actions):
        self.setRootIndex(QtCore.QModelIndex())
        self._focus_item = None
        self._focus_view = None
        self._destination_items = []
        self._move_target = None
        self._targets = []
        if hasattr(self, 'target_card'):
            self.target_card.hide()
            self.destination_panel.hide()
        super().load_actions(actions)
        self.schedule_workspace()

    def _selection_updated(self):
        self.viewport().update()
        self.update_location()
        self._update_controls()

    def _disabled_text_brush(self, depth):
        return QtGui.QBrush(QtGui.QColor('#c4c4c4'))

    def _apply_enabled_styles(self):
        super()._apply_enabled_styles()
        blocker = QtCore.QSignalBlocker(self)
        for item in self.items():
            if self._disabled_depth(item) is not None:
                item.setText(1, self._orig_text(item, 1) + ' ×')
        del blocker

    def _draw_disabled_overlay(self, painter, option, index):
        # Draw the background before text, not a translucent layer over the letters.
        pass

    def _draw_block_background(self, painter, option, index):
        item = self.itemFromIndex(index)
        selected_scope = self.owner_if(self.currentItem())
        rect = QtCore.QRect(option.rect)
        rect.setHeight(self.row_height)
        color = '#ffffff'
        if self.is_if(item):
            color = '#edf2f8'
        if selected_scope and (item is selected_scope or self._is_descendant(item, selected_scope)):
            color = '#eef4ff'
        if item and item.data(0, ROLE) == '__else__':
            color = '#fff0d8'
        if item and self._disabled_depth(item) is not None:
            color = '#ffffff'
        painter.fillRect(rect, QtGui.QColor(color))

    def _item_level(self, index):
        item = self.itemFromIndex(index)
        if item is None:
            return 0
        if not isinstance(item.data(0, ROLE), Action):
            item = item.parent()
        level = 0
        parent = item.parent() if item else None
        while parent:
            if isinstance(parent.data(0, ROLE), Action):
                level += 1
            parent = parent.parent()
        return level

    def scope_palette(self, scope):
        if self._disabled_depth(scope) is not None:
            return '#dddddd', '#ffffff'
        depth = self._item_level(self.indexFromItem(scope))
        return [('#9cb1cc', '#f0f5fc'), ('#9eafa1', '#f1f5ef'),
                ('#b5a0bf', '#f6f1f8')][min(depth, 2)]

    def html_row_color(self, item):
        marker = item.data(0, ROLE)
        if self._disabled_depth(item) is not None:
            return '#ffffff'
        if item.isSelected():
            return '#d5f0ec'
        if marker == '__else__':
            return '#fff4e2'
        if marker == '__transition__':
            return '#edf7f3'
        if isinstance(marker, dict) and marker.get('marker') == '__elif__':
            return '#f5f1e9'
        if self.is_if(item):
            return self.scope_palette(item)[1]
        owner = self.owner_if(self.currentItem())
        parent = item.parent()
        negative = False
        while parent:
            if parent.data(0, ROLE) == '__else__':
                negative = True
            parent = parent.parent()
        if owner and self._is_descendant(item, owner):
            return '#fff5e6' if negative else '#f0f5ff'
        return '#fffdf9' if negative else '#ffffff'

    def fold_rect(self, item):
        row = self.visualItemRect(item)
        x = self.columnViewportPosition(1) + 12 + self._item_level(self.indexFromItem(item))*17
        return QtCore.QRect(x, row.top()+(self.row_height-15)//2, 15, 15)

    def grip_rect(self, item):
        if self._can_have_children_item(item):
            row = self.visualItemRect(item)
            return QtCore.QRect(self.columnViewportPosition(0)+3,
                                row.top()+(self.row_height-15)//2, 15, 15)
        return self.fold_rect(item)

    def check_rect(self, item):
        row = self.visualItemRect(item)
        x = self.columnViewportPosition(5) + (self.columnWidth(5)-14)//2
        return QtCore.QRect(x, row.top()+(self.row_height-14)//2, 14, 14)

    def paint_html_cell(self, painter, option, index):
        """Own the pixels: native/QSS item painting must not cover HTML colors."""
        item = self.itemFromIndex(index)
        if item is None:
            return
        column = index.column()
        rect = QtCore.QRect(option.rect)
        rect.setHeight(self.row_height)
        data = item.data(0, ROLE)
        disabled = self._disabled_depth(item) is not None
        is_branch = data in ('__else__', '__transition__') or isinstance(data, dict) and data.get('marker') == '__elif__'
        painter.save()
        painter.setClipRect(rect)
        painter.fillRect(rect, QtGui.QColor(self.html_row_color(item)))
        if item in self._destination_items:
            painter.setPen(QtGui.QPen(QtGui.QColor('#a35b14'), 1, QtCore.Qt.PenStyle.DashLine))
            painter.drawLine(rect.left(), rect.top(), rect.right(), rect.top())
            painter.drawLine(rect.left(), rect.bottom(), rect.right(), rect.bottom())
        if not disabled and (self.is_if(item) or is_branch):
            painter.setPen(QtGui.QColor('#e8d3b1' if data == '__else__' else '#e1e7ef'))
            painter.drawLine(rect.topLeft(), rect.topRight())
        if column == 5:
            if item.flags() & QtCore.Qt.ItemFlag.ItemIsUserCheckable:
                check = self.check_rect(item)
                checked = item.checkState(5) == QtCore.Qt.CheckState.Checked
                color = '#c4c4c4' if disabled else '#1673bf'
                painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
                painter.setPen(QtGui.QPen(QtGui.QColor(color if checked or disabled else '#8391a2'), 1))
                painter.setBrush(QtGui.QColor(color if checked else '#ffffff'))
                painter.drawRoundedRect(QtCore.QRectF(check).adjusted(.5,.5,-.5,-.5), 3, 3)
                if checked:
                    pen = QtGui.QPen(QtGui.QColor('#ffffff'), 1.8)
                    pen.setCapStyle(QtCore.Qt.PenCapStyle.RoundCap)
                    pen.setJoinStyle(QtCore.Qt.PenJoinStyle.RoundJoin)
                    painter.setPen(pen)
                    painter.drawPolyline(QtGui.QPolygonF([QtCore.QPointF(check.x()+3,check.y()+7),
                        QtCore.QPointF(check.x()+6,check.y()+10), QtCore.QPointF(check.x()+11,check.y()+4)]))
            painter.restore()
            return
        font = QtGui.QFont('Malgun Gothic')
        font.setPixelSize(12 if column == 2 else 11)
        painter.setFont(font)
        text = item.text(column)
        text_rect = rect.adjusted(9, 0, -9, 0)
        color = {0:'#8a96a6', 1:'#2d66a5', 2:'#24364e', 3:'#335f99', 4:'#8c96a4'}[column]
        if disabled:
            color = '#c4c4c4'
        if not disabled and data == '__else__' and column in (1, 2):
            color = '#885c26'
        if column == 0:
            font.setPixelSize(10)
            painter.setFont(font)
            if isinstance(data, Action) and self._can_have_children_item(item):
                position = self.grip_rect(item)
                text_rect.setLeft(position.right()+2)
                painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
                painter.setPen(QtCore.Qt.PenStyle.NoPen)
                painter.setBrush(QtGui.QColor('#c4c4c4' if disabled else '#8393a9'))
                for dx in (5, 9):
                    for dy in (3, 7, 11):
                        painter.drawEllipse(QtCore.QPointF(position.x()+dx, position.y()+dy), 1.1, 1.1)
        if column == 1:
            position = self.fold_rect(item)
            if self._can_have_children_item(item):
                painter.setPen(QtGui.QColor('#c4c4c4' if disabled else '#b3c2d5'))
                painter.setBrush(QtGui.QColor('#ffffff'))
                painter.drawRoundedRect(position, 2, 2)
                cx, cy = position.center().x(), position.center().y()
                points = [(cx-3,cy-1),(cx+3,cy-1),(cx,cy+3)] if item.isExpanded() else [(cx-1,cy-3),(cx-1,cy+3),(cx+3,cy)]
                painter.setPen(QtCore.Qt.PenStyle.NoPen)
                painter.setBrush(QtGui.QColor('#c4c4c4' if disabled else '#577192'))
                painter.drawPolygon(QtGui.QPolygon([QtCore.QPoint(x,y) for x,y in points]))
            elif isinstance(data, Action):
                painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
                painter.setPen(QtCore.Qt.PenStyle.NoPen)
                painter.setBrush(QtGui.QColor('#c4c4c4' if disabled else '#8393a9'))
                for dx in (5, 9):
                    for dy in (3, 7, 11):
                        painter.drawEllipse(QtCore.QPointF(position.x()+dx, position.y()+dy), 1.1, 1.1)
            text_rect.setLeft(position.right()+6)
        if column == 2 and (self.is_if(item) or is_branch):
            owner = item if self.is_if(item) else item.parent()
            badge_text = '#'+self._scope_ids.get(id(owner), '?')
            badge_font = QtGui.QFont(font)
            badge_font.setPixelSize(10)
            painter.setFont(badge_font)
            badge = QtCore.QRect(text_rect.left(), rect.top()+(self.row_height-16)//2, 31, 16)
            painter.setPen(QtGui.QColor('#dddddd' if disabled else '#dfc49a' if data == '__else__' else '#c3d1e1'))
            painter.setBrush(QtGui.QColor('#ffffff' if disabled else '#fff9ee' if data == '__else__' else '#ffffff'))
            painter.drawRoundedRect(badge, 3, 3)
            painter.setPen(QtGui.QColor('#c4c4c4' if disabled else '#8a652e' if data == '__else__' else '#577291'))
            painter.drawText(badge, QtCore.Qt.AlignmentFlag.AlignCenter, badge_text)
            text_rect.setLeft(badge.right()+8)
            text = self.original_name(item)
            font.setWeight(QtGui.QFont.Weight.DemiBold if self.is_if(item) else QtGui.QFont.Weight.Normal)
            painter.setFont(font)
            if self.is_if(item) and self._find_else_header(item):
                text_rect.setRight(self.jump_rect(item).left()-7)
        if column == 2 and isinstance(data, Action) and data.quick_toggle_id:
            # Paint a bolt directly so it remains visible without an emoji font.
            x, y = text_rect.left(), rect.center().y()
            painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
            painter.setPen(QtCore.Qt.PenStyle.NoPen)
            painter.setBrush(QtGui.QColor('#bba66a' if disabled else '#d99100'))
            painter.drawPolygon(QtGui.QPolygonF([
                QtCore.QPointF(x+8, y-8), QtCore.QPointF(x+1, y+1),
                QtCore.QPointF(x+6, y+1), QtCore.QPointF(x+4, y+8),
                QtCore.QPointF(x+12, y-2), QtCore.QPointF(x+7, y-2),
            ]))
            text_rect.setLeft(x+18)
        if item.isSelected() and not disabled:
            color = '#164e47'
        painter.setPen(QtGui.QColor(color))
        align = QtCore.Qt.AlignmentFlag.AlignVCenter | (QtCore.Qt.AlignmentFlag.AlignRight if column == 0 else QtCore.Qt.AlignmentFlag.AlignLeft)
        # No special glyph dependency for the branch marker.
        if column == 0 and is_branch:
            x, y = text_rect.right()-7, rect.center().y()
            painter.drawLine(x-3,y-4,x-3,y+2)
            painter.drawLine(x-3,y+2,x+4,y+2)
        else:
            text = painter.fontMetrics().elidedText(text, QtCore.Qt.TextElideMode.ElideRight, max(0, text_rect.width()))
            painter.drawText(text_rect, align, text)
        painter.restore()

    def paint_scope_lines(self, painter, item, rect, closing=None):
        if self._disabled_depth(item) is not None:
            return
        scope = item if self.is_if(item) else item.parent()
        painter.save()
        while scope:
            if self.is_if(scope) and not (self._focus_item and scope is not self._focus_item and not self._is_descendant(scope, self._focus_item)):
                x = self.columnViewportPosition(1)+10+self._item_level(self.indexFromItem(scope))*17
                line, _ = self.scope_palette(scope)
                painter.setPen(QtGui.QPen(QtGui.QColor(line), 2))
                if scope in self._ends.get(id(item), []):
                    painter.drawLine(x, rect.top(), x, rect.center().y())
                    painter.drawLine(x, rect.center().y(), x+9, rect.center().y())
                elif scope is not item or closing is not None:
                    painter.drawLine(x, rect.top(), x, rect.bottom()+1)
            scope = scope.parent()
        painter.restore()

    def drawRow(self, painter, option, index):
        # Scope endings share the final action row; no extra footer height.
        opt = QtWidgets.QStyleOptionViewItem(option)
        opt.rect.setHeight(self.row_height)
        QtWidgets.QTreeWidget.drawRow(self, painter, opt, index)
        item = self.itemFromIndex(index)
        self.paint_scope_lines(painter, item, opt.rect)
        disabled = self._disabled_depth(item) is not None
        if item.isSelected():
            painter.save()
            painter.setPen(QtGui.QPen(QtGui.QColor('#dddddd' if disabled else '#70bfb3'), 1))
            painter.drawLine(0, opt.rect.top(), self.viewport().width()-1, opt.rect.top())
            painter.drawLine(0, opt.rect.bottom(), self.viewport().width()-1, opt.rect.bottom())
            painter.fillRect(QtCore.QRect(0,opt.rect.top(),4,self.row_height),QtGui.QColor('#c4c4c4' if disabled else '#159a87'))
            painter.restore()
        if self.is_if(item) and self._find_else_header(item):
            painter.save()
            jump_rect = self.jump_rect(item)
            painter.setBrush(QtGui.QColor('#ffffff' if disabled else '#fffaf2'))
            painter.setPen(QtGui.QColor('#c4c4c4' if disabled else '#dfc9a6'))
            painter.drawRoundedRect(jump_rect, 3, 3)
            painter.setPen(QtGui.QColor('#c4c4c4' if disabled else '#865b20'))
            font = painter.font()
            font.setPointSizeF(max(8, font.pointSizeF()-1))
            painter.setFont(font)
            painter.drawText(jump_rect, QtCore.Qt.AlignmentFlag.AlignCenter, '거짓 분기로 ↓')
            painter.restore()
        owner = self.owner_if(self.currentItem())
        if not disabled and owner and (item is owner or self._is_descendant(item, owner)):
            painter.save()
            painter.setPen(QtGui.QPen(QtGui.QColor('#4b80bd'), 2))
            painter.drawLine(1, opt.rect.top(), 1, option.rect.bottom())
            painter.drawLine(self.viewport().width()-2, opt.rect.top(), self.viewport().width()-2, option.rect.bottom())
            if item is owner:
                painter.drawLine(1, opt.rect.top(), self.viewport().width()-2, opt.rect.top())
            painter.restore()
        if not disabled and owner in self._ends.get(id(item), []):
            painter.save()
            painter.setPen(QtGui.QPen(QtGui.QColor('#4b80bd'), 2))
            painter.drawLine(1, opt.rect.bottom(), self.viewport().width()-2, opt.rect.bottom())
            painter.restore()

    def path_text(self, item):
        pieces = []
        while item is not None:
            data = item.data(0, ROLE)
            if data == '__else__':
                pieces.append('거짓 · IF NOT')
            elif data == '__transition__':
                pieces.append('참→거짓 · 1회')
            elif isinstance(data, dict) and data.get('marker') == '__elif__':
                pieces.append('ELIF')
            elif self.is_if(item):
                pieces.append('IF '+self.scope_name(item))
            elif isinstance(data, Action) and not pieces:
                pieces.append(data.name or f'{data.type} {self._format_value(data)}')
            parent = item.parent()
            if parent and self.is_if(parent) and data not in ('__else__', '__transition__') and not isinstance(data, dict):
                pieces.append('참')
            item = parent
        return '일반 액션 → ' + ' → '.join(reversed(pieces))

    def update_location(self, *_):
        if not hasattr(self, 'location_label'):
            return
        top = self.itemAt(QtCore.QPoint(4, 2))
        text = '화면 위쪽 위치: ' + (self.path_text(top) if top else '일반 액션')
        self.location_label.setText(text)
        self.location_label.setToolTip(text)
        selection = self._top_level_selected(self.selectedItems())
        included = sum(1 for item in self.items() if isinstance(item.data(0, ROLE), Action) and any(item is root or self._is_descendant(item, root) for root in selection))
        text = f'액션 {len(selection)}개 선택 · 하위 포함 총 {included}개 · '+self.path_text(self.currentItem()) if selection else '선택 위치: 행을 선택하세요. Ctrl / Shift로 여러 행 선택'
        if self._focus_item:
            text = '집중 보기 · ' + text
        self.selection_label.setText(text)
        self.selection_label.setToolTip(text)

    def _update_controls(self):
        if not hasattr(self, 'focus_button'):
            return
        owner = self.owner_if(self.currentItem())
        self.focus_button.setText('전체 목록으로' if self._focus_item else '이 IF만 보기')
        self.focus_button.setEnabled(bool(owner or self._focus_item))
        self.jump_button.setEnabled(bool(owner and self._find_else_header(owner)))
        self.destination_button.setEnabled(bool(self.selectedItems()))

    def view_state(self):
        return dict(expanded=self._expanded_keys(), selected=[self._item_path_key(i) for i in self.selectedItems()],
                    current=self._item_path_key(self.currentItem()) if self.currentItem() else None,
                    scroll=self.verticalScrollBar().value())

    def at_path(self, path):
        if path is None:
            return None
        parent = self.invisibleRootItem()
        for row in path:
            if row >= parent.childCount():
                return None
            parent = parent.child(row)
        return parent

    def restore_view(self, state):
        self._restore_expanded(state['expanded'])
        self.clearSelection()
        current = self.at_path(state['current'])
        if current:
            self.setCurrentItem(current, 0, QtCore.QItemSelectionModel.SelectionFlag.NoUpdate)
        for path in state['selected']:
            item = self.at_path(path)
            if item:
                item.setSelected(True)
        self.verticalScrollBar().setValue(state['scroll'])

    def toggle_hide_disabled(self, checked):
        self._hide_disabled = checked
        self.hide_disabled_button.setText('비활성 숨기기: ' + ('켜짐' if checked else '꺼짐'))
        self.refresh_workspace()

    def toggle_focus(self):
        if self._focus_item:
            self._focus_item = None
            self.setRootIndex(QtCore.QModelIndex())
            for item in self.items():
                item.setHidden(False)
            if self._focus_view:
                self.restore_view(self._focus_view)
            self._focus_view = None
        else:
            target = self.owner_if(self.currentItem())
            if target is None:
                return
            self._focus_view = self.view_state()
            self._focus_item = target
            self.setRootIndex(self.indexFromItem(target.parent()) if target.parent() else QtCore.QModelIndex())
            for item in self.items():
                keep = item is target or self._is_descendant(item, target) or self._is_descendant(target, item)
                item.setHidden(not keep)
                if keep:
                    item.setExpanded(True)
            self.scrollToItem(target, QtWidgets.QAbstractItemView.ScrollHint.PositionAtTop)
        self.refresh_workspace()

    def jump_else(self):
        owner = self.owner_if(self.currentItem())
        branch = self._find_else_header(owner) if owner else None
        if branch:
            current = branch
            while current:
                current.setExpanded(True)
                current = current.parent()
            self.setCurrentItem(branch)
            self.scrollToItem(branch, QtWidgets.QAbstractItemView.ScrollHint.PositionAtCenter)

    def jump_rect(self, item):
        rect = self.visualRect(self.indexFromItem(item).siblingAtColumn(2))
        return QtCore.QRect(rect.right()-94, rect.top()+3, 90, self.row_height-6)

    def mousePressEvent(self, event):
        item = self.itemAt(event.position().toPoint())
        self._grip_pressed = bool(item and isinstance(item.data(0,ROLE),Action) and self.grip_rect(item).contains(event.position().toPoint()))
        if self._destination_items:
            if item:
                self.choose_destination(item)
            event.accept()
            return
        if item:
            if self.is_if(item) and self._find_else_header(item) and self.jump_rect(item).contains(event.position().toPoint()):
                self.setCurrentItem(item)
                self.jump_else()
                event.accept()
                return
            index = self.indexFromItem(item)
            if self._can_have_children_item(item) and self.fold_rect(item).contains(event.position().toPoint()):
                item.setExpanded(not item.isExpanded())
                event.accept()
                return
            if self.columnAt(int(event.position().x())) == 5:
                if item.flags() & QtCore.Qt.ItemFlag.ItemIsUserCheckable:
                    if self.history:
                        self.history.flush()
                    selected = self._top_level_selected(self.selectedItems()) if item.isSelected() else [item]
                    state = QtCore.Qt.CheckState.Unchecked if item.checkState(5) == QtCore.Qt.CheckState.Checked else QtCore.Qt.CheckState.Checked
                    for selected_item in selected:
                        if selected_item.flags() & QtCore.Qt.ItemFlag.ItemIsUserCheckable:
                            selected_item.setCheckState(5, state)
                    self.renumber()
                    if self.history:
                        self.history.flush()
                else:
                    self.setCurrentItem(item)
                event.accept()
                return
        QtWidgets.QTreeWidget.mousePressEvent(self, event)

    def mouseMoveEvent(self, event):
        item = self.itemAt(event.position().toPoint())
        grip = item is not None and isinstance(item.data(0, ROLE), Action) and self.grip_rect(item).contains(event.position().toPoint())
        self.viewport().setCursor(QtCore.Qt.CursorShape.OpenHandCursor if grip else QtCore.Qt.CursorShape.ArrowCursor)
        super().mouseMoveEvent(event)

    def _first_column_rect(self, index):
        rect = super()._first_column_rect(index)
        rect.setHeight(self.row_height)
        return rect

    def cancel_destination(self):
        self._destination_items = []
        self._targets = []
        self.destination_panel.hide()
        self.target_card.hide()
        self._move_target = None
        self.refresh_workspace()

    def transfer_items(self, items, target, where, copy_mode=False):
        """Move/copy ordered selection transactionally; reject structural cycles."""
        live = {id(i) for i in self.items()}
        items = self._top_level_selected([i for i in items if id(i) in live and isinstance(i.data(0, ROLE), Action)])
        if not items:
            return False, '실행 액션을 선택하세요. IF NOT·ELIF 구분 행은 이동 대상이 아닙니다.'
        if target is not None and id(target) not in live:
            return False, '도착 위치가 변경되었습니다. 다시 선택하세요.'
        if target is not None and where in ('before', 'after') and not isinstance(target.data(0, ROLE), Action):
            return False, '분기 구분 행 앞뒤 대신, 참·거짓 분기 안이나 분기 끝 위치를 선택하세요.'
        if where in ('yes', 'no') and not self.is_if(target):
            return False, '참·거짓 분기는 IF에만 넣을 수 있습니다.'
        if target and any(target is i or self._is_descendant(target, i) for i in items):
            return False, '선택한 IF 자신이나 그 하위로 넣을 수 없습니다.'
        parent = target if where == 'yes' else (target.parent() if target and where in ('before', 'after') else None)
        if where == 'no':
            parent = self._find_else_header(target)
            if not parent:
                return False, 'IF NOT 분기를 먼저 추가하세요.'
        if where == 'child':
            parent = target
        if parent is not None and not self._can_have_children_item(parent):
            return False, '이 항목에는 하위 액션을 넣을 수 없습니다.'
        if parent is not None and any(getattr(i.data(0, ROLE), 'parallel_enabled', False) for i in items):
            return False, '병렬 작업은 최상위에 배치하세요.'
        if parent is None and getattr(self, 'parallel_roots', False) and any(not getattr(i.data(0, ROLE), 'parallel_enabled', False) for i in items):
            return False, '병렬 탭 최상위에는 병렬 작업만 넣을 수 있습니다.'
        if self.history:
            self.history.flush()
        expanded = {id(i): i.isExpanded() for i in self.items()}
        new_items = [self._clone_tree_item(i) for i in items] if copy_mode else items
        blocker = QtCore.QSignalBlocker(self)
        if not copy_mode:
            for item in reversed(items):
                p = item.parent()
                p.takeChild(p.indexOfChild(item)) if p else self.takeTopLevelItem(self.indexOfTopLevelItem(item))
        container = parent or self.invisibleRootItem()
        if where in ('after', 'before') and target:
            row = container.indexOfChild(target) + (where == 'after')
        elif parent and self.is_if(parent):
            row = self._default_child_insert_row(parent)
            if row is None:
                row = container.childCount()
        else:
            row = container.childCount()
        for item in new_items:
            container.insertChild(row, item)
            row += 1
        for item in self.items():
            item.setExpanded(expanded.get(id(item), True))
        self.clearSelection()
        self.setCurrentItem(new_items[0], 0, QtCore.QItemSelectionModel.SelectionFlag.NoUpdate)
        for item in new_items:
            item.setSelected(True)
        if parent:
            parent.setExpanded(True)
        del blocker
        self.renumber()
        if self._focus_item and not any(new is self._focus_item or self._is_descendant(new, self._focus_item) for new in new_items):
            self._focus_item = None
            self._focus_view = None
            self.setRootIndex(QtCore.QModelIndex())
            for item in self.items():
                item.setHidden(False)
        self.refresh_workspace()
        self.scrollToItem(new_items[0])
        if self.history:
            self.history.flush()
        return True, f'{len(new_items)}개 '+('복사' if copy_mode else '이동')+' 완료'

    def destination_text(self, target, where, copy_mode=False):
        name = self.scope_name(target) if self.is_if(target) else (target.text(2) or target.text(1)) if target else '목록'
        suffix = {'yes':'참 분기 끝에', 'no':'거짓 분기 끝에', 'after':'다음에 (IF 밖)',
                  'before':'앞에', 'child':'하위 끝에', 'end':'끝에'}[where]
        return f'{name} · {suffix} '+('복사' if copy_mode else '넣기')

    def begin_destination(self):
        self._destination_items = self._top_level_selected([i for i in self.selectedItems() if isinstance(i.data(0, ROLE), Action)])
        if not self._destination_items:
            self.selection_label.setText('이동·복사할 실행 액션을 선택하세요.')
            return
        self._targets = []
        self._move_target = None
        self.target_card.hide()
        self.destination_panel.show()
        self.move_instruction.setText(f'액션 {len(self._destination_items)}개 이동 준비 · 목적지 행을 클릭하세요. 원본은 완료 전까지 유지됩니다. · Esc 취소')
        self.refresh_workspace()

    def choose_destination(self, target):
        if any(target is src or self._is_descendant(target,src) for src in self._destination_items):
            self.selection_label.setText('이동할 항목 자신이나 하위는 목적지로 선택할 수 없습니다.')
            return
        self._move_target = target
        self.destination_list.clear()
        data = target.data(0,ROLE)
        choices = ['before','after'] if isinstance(data,Action) else ['child']
        if self.is_if(target):
            choices += ['yes'] + (['no'] if self._find_else_header(target) else [])
        elif self._can_have_children_item(target) and isinstance(data,Action):
            choices += ['child']
        self._targets = [(target,where) for where in choices]
        for _,where in self._targets:
            self.destination_list.addItem(self.destination_text(target,where))
        self.destination_list.setCurrentRow(0)
        self.target_title.setText(f'액션 {len(self._destination_items)}개 → '+(self.scope_name(target) if self.is_if(target) else target.text(2) or target.text(1)))
        self.target_card.adjustSize()
        rect = self.visualItemRect(target)
        self.target_card.move(max(0,min(self.columnViewportPosition(2),self.viewport().width()-self.target_card.width())),
                              max(0,min(rect.top()+self.row_height,self.viewport().height()-self.target_card.height())))
        self.target_card.show()
        self.target_card.raise_()
        self.update_alt_labels()

    def startDrag(self, supported_actions):
        if not self._grip_pressed:
            return
        self._grip_pressed = False
        super().startDrag(supported_actions)

    def _clone_tree_item(self, item):
        clone = super()._clone_tree_item(item)
        def restore_type(source, dest):
            dest.setData(1, ROLE + 5, self._orig_text(source, 1))
            dest.setData(2, ROLE + 61, source.data(2, ROLE + 61))
            for i in range(source.childCount()):
                restore_type(source.child(i), dest.child(i))
        restore_type(item, clone)
        return clone

    def move_selected_within_parent(self, offset):
        items = self._top_level_selected(self.selectedItems())
        if any(not isinstance(item.data(0, ROLE), Action) for item in items):
            return False, '분기 구분 행은 이동할 수 없습니다.', items[0] if items else None
        for item in items:
            parent = item.parent() or self.invisibleRootItem()
            row = parent.indexOfChild(item) + offset
            if 0 <= row < parent.childCount() and not isinstance(parent.child(row).data(0, ROLE), Action):
                return False, '분기를 넘기려면 이동 / 복사에서 도착 분기를 선택하세요.', item
        if self.history:
            self.history.flush()
        result = super().move_selected_within_parent(offset)
        if self.history:
            self.history.flush()
        return result

    def update_alt_labels(self):
        if not hasattr(self, 'destination_list'):
            return
        copying = bool(QtWidgets.QApplication.keyboardModifiers() & QtCore.Qt.KeyboardModifier.AltModifier)
        for row, (target, where) in enumerate(getattr(self, '_targets', [])):
            self.destination_list.item(row).setText(self.destination_text(target, where, copying))
        self.destination_apply.setText(f'액션 {len(self._destination_items)}개 '+('복사본 넣기' if copying else '여기로 이동'))
        self.viewport().update()

    def apply_destination(self, force_copy=False):
        row = self.destination_list.currentRow()
        if row < 0 or row >= len(getattr(self, '_targets', [])):
            return
        copying = force_copy or bool(QtWidgets.QApplication.keyboardModifiers() & QtCore.Qt.KeyboardModifier.AltModifier)
        target, where = self._targets[row]
        ok, message = self.transfer_items(self._destination_items, target, where, copying)
        self.selection_label.setText(message)
        if ok:
            self.cancel_destination()

    def _drop_target(self, event):
        pos = event.position().toPoint()
        target = self.itemAt(pos)
        if not target:
            return None, 'end'
        rect = self.visualItemRect(target)
        # The expander and row center are explicit child targets, even for empty IFs.
        if self._can_have_children_item(target):
            if self.fold_rect(target).contains(pos) or rect.top()+5 <= pos.y() < rect.top()+self.row_height-5:
                return target, 'yes' if self.is_if(target) else 'child'
        if not isinstance(target.data(0,ROLE),Action):
            return target, 'invalid'
        return target, 'before' if pos.y()<rect.top()+self.row_height/2 else 'after'

    def dragMoveEvent(self, event):
        if event.source() not in (self, self.viewport()):
            event.ignore()
            return
        super().dragMoveEvent(event)
        # Qt's native drop rules do not describe our branch insertion targets.
        if self._drop_target(event)[1] != 'invalid':
            event.setDropAction(self._drag_default_action(event))
            event.accept()

    def _update_drop_feedback(self, event):
        if not event:
            self._clear_drop_feedback()
            return
        target,where = self._drop_target(event)
        self._drop_feedback = {'target':target,'where':where}
        self.viewport().update()
        if hasattr(self,'selection_label'):
            self.selection_label.setText('분기 행 중앙에 놓으면 분기 안으로 들어갑니다.' if where=='invalid' else '도착 위치: '+self.destination_text(target,where,self._copy_drag_requested(event)))

    def _paint_drop_feedback(self):
        if not self._drop_feedback:
            return
        target,where = self._drop_feedback['target'],self._drop_feedback['where']
        if where=='invalid':
            return
        rect = self.visualItemRect(target) if target else self.viewport().rect()
        y = rect.top() if where=='before' else rect.bottom()
        painter = QtGui.QPainter(self.viewport())
        painter.setPen(QtGui.QPen(QtGui.QColor('#7c3aed'),3))
        if where in ('yes', 'child'):
            painter.setBrush(QtGui.QColor(124, 58, 237, 28))
            painter.drawRoundedRect(rect.adjusted(2, 1, -2, -1), 3, 3)
        else:
            painter.drawLine(6,y,self.viewport().width()-6,y)
        painter.end()

    def dropEvent(self, event):
        if event.source() not in (self, self.viewport()):
            event.ignore()
            return
        target, where = self._drop_target(event)
        if where == 'invalid':
            event.ignore()
            self._clear_drop_feedback()
            return
        copying = self._copy_drag_requested(event)
        ok, message = self.transfer_items(self.selectedItems(), target, where, copying)
        self._clear_drop_feedback()
        if hasattr(self, 'selection_label'):
            self.selection_label.setText(message)
        if ok:
            event.setDropAction(QtCore.Qt.DropAction.CopyAction if copying else QtCore.Qt.DropAction.MoveAction)
            event.accept()
        else:
            event.ignore()

    def workspace_menu(self, point):
        menu = QtWidgets.QMenu(self)
        item = self.itemAt(point)
        action = item.data(0, ROLE) if item is not None else None
        blocks = getattr(self, 'block_workspace', None)
        if blocks:
            if item is not None and not item.isSelected():
                self.clearSelection()
                self.setCurrentItem(item)
            menu.addAction('선택을 공용 블록으로 묶기', lambda: blocks.make_shared(tree=self))
            if not isinstance(action, Action) or action.type != 'shared_block':
                menu.addAction('이 부분과 같은 묶음 찾기', lambda: blocks.suggest(tree=self))
            if isinstance(action, Action) and action.type == 'shared_block':
                menu.addAction('같은 내용 찾기…', lambda: blocks.find_matches(reference=action.block_ref))
                menu.addAction('공용 블록 미리보기', lambda: blocks.open(action.block_ref, False))
                if not blocks.panel.isHidden():
                    menu.addAction('공용 블록 미리보기 닫기', blocks.panel.hide)
                menu.addAction('공용 원본 편집', lambda: blocks.open(action.block_ref, True))
                menu.addAction('이곳만 연결 해제', lambda: blocks.detach(tree=self))
            menu.addSeparator()
        if isinstance(action, Action):
            toggle = menu.addAction('빠른 토글에 표시')
            toggle.setCheckable(True)
            toggle.setChecked(bool(action.quick_toggle_id))
            def register(checked):
                if self.history:
                    self.history.flush()
                action.quick_toggle_id = (action.quick_toggle_id or uuid.uuid4().hex) if checked else ''
                self.model().dataChanged.emit(self.indexFromItem(item), self.indexFromItem(item))
                if self.history:
                    self.history.flush()
            toggle.triggered.connect(register)
            menu.addSeparator()
        if self.history:
            undo = menu.addAction('실행 취소  Ctrl+Z', self.history.undo)
            undo.setEnabled(bool(self.history.position))
            redo = menu.addAction('다시 실행  Ctrl+Y', self.history.redo)
            redo.setEnabled(self.history.position < len(self.history.states)-1)
            menu.addSeparator()
        menu.addAction('이동 준비 / 복사…', self.begin_destination)
        menu.addAction('이 IF만 보기 / 전체 목록으로', self.toggle_focus)
        menu.addAction('거짓 분기로 이동', self.jump_else)
        menu.exec(self.viewport().mapToGlobal(point))

    def keyPressEvent(self, event):
        if event.matches(QtGui.QKeySequence.StandardKey.Cut):
            self.begin_destination()
            event.accept()
            return
        if event.key() == QtCore.Qt.Key.Key_Escape:
            if self._destination_items:
                self.cancel_destination()
                event.accept()
                return
            if self._focus_item:
                self.toggle_focus()
                event.accept()
                return
        super().keyPressEvent(event)


def build_tree_panel(tree):
    panel = QtWidgets.QWidget()
    layout = QtWidgets.QVBoxLayout(panel)
    layout.setContentsMargins(0, 0, 0, 0)
    layout.setSpacing(0)
    toolbar = QtWidgets.QHBoxLayout()
    toolbar.setContentsMargins(4, 5, 4, 5)
    for text, callback in [('모두 펼치기', tree.expandAll), ('모두 접기', tree.collapse_all)]:
        button = QtWidgets.QPushButton(text)
        button.clicked.connect(callback)
        toolbar.addWidget(button)
    density = QtWidgets.QPushButton('더 촘촘하게')
    density.setCheckable(True)
    def set_density(on):
        tree.row_height = 20 if on else 24
        density.setText('기본 행 간격' if on else '더 촘촘하게')
        tree.refresh_workspace()
    density.toggled.connect(set_density)
    toolbar.addWidget(density)
    tree.hide_disabled_button = QtWidgets.QPushButton('비활성 숨기기: 꺼짐')
    tree.hide_disabled_button.setCheckable(True)
    tree.hide_disabled_button.setToolTip('비활성 액션과 IF NOT·ELIF 분기 및 그 하위 항목을 숨깁니다.')
    tree.hide_disabled_button.toggled.connect(tree.toggle_hide_disabled)
    toolbar.addWidget(tree.hide_disabled_button)
    tree.focus_button = QtWidgets.QPushButton('이 IF만 보기')
    tree.focus_button.clicked.connect(tree.toggle_focus)
    toolbar.addWidget(tree.focus_button)
    tree.jump_button = QtWidgets.QPushButton('거짓 분기로 ↓')
    tree.jump_button.clicked.connect(tree.jump_else)
    toolbar.addWidget(tree.jump_button)
    tree.destination_button = QtWidgets.QPushButton('이동 준비 (Ctrl+X)')
    tree.destination_button.clicked.connect(tree.begin_destination)
    toolbar.addWidget(tree.destination_button)
    toolbar.addStretch()
    layout.addLayout(toolbar)
    tree.location_label = QtWidgets.QLabel('화면 위쪽 위치: 일반 액션')
    tree.selection_label = QtWidgets.QLabel('선택 위치: 행을 선택하세요.')
    for label in (tree.location_label, tree.selection_label):
        label.setTextFormat(QtCore.Qt.TextFormat.PlainText)
        label.setWordWrap(True)
        label.setStyleSheet('background:#edf3fb;color:#496282;padding:6px;border:1px solid #d2dce9;')
    layout.addWidget(tree.location_label)
    tree.destination_panel = QtWidgets.QWidget()
    target_layout = QtWidgets.QVBoxLayout(tree.destination_panel)
    target_layout.setContentsMargins(8, 5, 8, 5)
    instruction_row = QtWidgets.QHBoxLayout()
    tree.move_instruction = QtWidgets.QLabel()
    tree.move_instruction.setWordWrap(True)
    instruction_row.addWidget(tree.move_instruction,1)
    cancel = QtWidgets.QPushButton('취소 (Esc)')
    cancel.clicked.connect(tree.cancel_destination)
    instruction_row.addWidget(cancel)
    target_layout.addLayout(instruction_row)
    tree.target_card = QtWidgets.QFrame(tree.viewport())
    tree.target_card.setObjectName('moveTargetCard')
    tree.target_card.setStyleSheet('QFrame#moveTargetCard {background:#faf7ff;border:2px solid #8b5cf6;border-radius:5px;}')
    card_layout = QtWidgets.QVBoxLayout(tree.target_card)
    tree.target_title = QtWidgets.QLabel()
    tree.target_title.setTextFormat(QtCore.Qt.TextFormat.PlainText)
    card_layout.addWidget(tree.target_title)
    tree.destination_list = QtWidgets.QListWidget()
    tree.destination_list.setFixedSize(395,110)
    card_layout.addWidget(tree.destination_list)
    buttons = QtWidgets.QHBoxLayout()
    tree.destination_apply = QtWidgets.QPushButton('여기로 이동')
    tree.destination_apply.clicked.connect(lambda:tree.apply_destination())
    buttons.addWidget(tree.destination_apply)
    explicit_copy = QtWidgets.QPushButton('복사본 넣기')
    explicit_copy.clicked.connect(lambda:tree.apply_destination(True))
    buttons.addWidget(explicit_copy)
    cancel_local = QtWidgets.QPushButton('취소')
    cancel_local.clicked.connect(tree.cancel_destination)
    buttons.addWidget(cancel_local)
    card_layout.addLayout(buttons)
    tree.target_card.hide()
    tree.destination_panel.hide()
    layout.addWidget(tree.destination_panel)
    layout.addWidget(tree, 1)
    layout.addWidget(tree.selection_label)
    return panel


class EditorHistory(QtCore.QObject):
    """One history across normal, parallel and stop actions. UI-only state is excluded."""
    def __init__(self, dialog):
        super().__init__(dialog)
        self.dialog = dialog
        self.trees = [dialog.main_action_tree, dialog.parallel_action_tree, dialog.stop_action_tree]
        self.restoring = False
        self.timer = QtCore.QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.timeout.connect(self.flush)
        self.states = [self.snapshot()]
        self.position = 0
        for tree in self.trees:
            tree.history = self
            model = tree.model()
            for signal in (model.rowsInserted, model.rowsRemoved, model.dataChanged, model.modelReset):
                signal.connect(self.schedule)
        dialog.stop_group.toggled.connect(self.schedule)
        bar = QtWidgets.QHBoxLayout()
        self.undo_button = QtWidgets.QPushButton('실행 취소 (Ctrl+Z)')
        self.redo_button = QtWidgets.QPushButton('다시 실행 (Ctrl+Y)')
        self.undo_button.clicked.connect(self.undo)
        self.redo_button.clicked.connect(self.redo)
        bar.addWidget(self.undo_button)
        bar.addWidget(self.redo_button)
        bar.addWidget(QtWidgets.QLabel('액션 편집 기록 · 일반 / 병렬 / 중단 액션'))
        bar.addStretch()
        dialog.layout().insertLayout(dialog.layout().indexOf(dialog.action_tabs), bar)
        self.shortcuts = []
        for key, callback in [('Ctrl+Z', self.undo), ('Ctrl+Y', self.redo), ('Ctrl+Shift+Z', self.redo)]:
            shortcut = QtGui.QShortcut(QtGui.QKeySequence(key), dialog)
            shortcut.setContext(QtCore.Qt.ShortcutContext.WidgetWithChildrenShortcut)
            shortcut.activated.connect(callback)
            self.shortcuts.append(shortcut)
        QtWidgets.QApplication.instance().installEventFilter(self)
        self.update_buttons()

    def eventFilter(self, obj, event):
        if event.type() in (QtCore.QEvent.Type.KeyPress, QtCore.QEvent.Type.KeyRelease,
                            QtCore.QEvent.Type.ApplicationDeactivate):
            for tree in self.trees:
                if tree.destination_panel.isVisible():
                    QtCore.QTimer.singleShot(0, tree.update_alt_labels)
        return False

    def snapshot(self):
        return dict(actions=[tree.collect_actions() for tree in self.trees],
                    stop=self.dialog.stop_group.isChecked(), views=[tree.view_state() for tree in self.trees],
                    blocks=copy.deepcopy(getattr(getattr(self.dialog, 'block_workspace', None), 'entries', {})))

    def schedule(self, *_):
        if not self.restoring:
            self.timer.start(0)

    def flush(self):
        self.timer.stop()
        if self.restoring:
            return
        blocks = getattr(self.dialog, 'block_workspace', None)
        if blocks and blocks.timer.isActive():
            blocks.save_definition()
        state = self.snapshot()
        last = self.states[self.position]
        if state['actions'] == last['actions'] and state['stop'] == last['stop'] and state['blocks'] == last['blocks']:
            last['views'] = state['views']
            return
        del self.states[self.position+1:]
        self.states.append(state)
        if len(self.states) > 101:
            self.states.pop(0)
        self.position = len(self.states)-1
        self.update_buttons()

    def update_buttons(self):
        self.undo_button.setEnabled(self.position > 0)
        self.redo_button.setEnabled(self.position < len(self.states)-1)

    def undo(self):
        self.flush()
        if self.position:
            self.restore(self.position-1)

    def redo(self):
        self.flush()
        if self.position < len(self.states)-1:
            self.restore(self.position+1)

    def restore(self, position):
        # Existing non-modal action editors hold item references until acceptance.
        # Replacing those items mid-edit would discard edits or access deleted Qt objects.
        if any(child.isVisible() and child.__class__.__name__ in ('ActionEditDialog', 'ConditionDialog', 'ConditionNodeDialog')
               for child in self.dialog.findChildren(QtWidgets.QDialog)):
            self.dialog.action_tree.selection_label.setText('열린 액션·조건 편집을 확인 또는 취소한 뒤 실행 취소·다시 실행하세요.')
            return
        self.restoring = True
        try:
            self.position = position
            state = self.states[position]
            if hasattr(self.dialog, 'block_workspace'):
                self.dialog.block_workspace.loading = True
            for tree, actions, view in zip(self.trees, state['actions'], state['views']):
                tree.cancel_destination()
                tree.load_actions(copy.deepcopy(actions))
                tree.restore_view(view)
                tree.refresh_workspace()
            self.dialog.stop_group.setChecked(state['stop'])
            if hasattr(self.dialog, 'block_workspace'):
                self.dialog.block_workspace.restore(state['blocks'])
            self.dialog._refresh_action_workspace()
        finally:
            self.restoring = False
        self.update_buttons()


def install_editor_history(dialog):
    dialog.action_history = EditorHistory(dialog)
