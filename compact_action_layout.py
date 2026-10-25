"""One-page action settings with fields sized to the values they contain."""
from PyQt6 import QtCore, QtWidgets, sip
from editor_theme import apply_editor_theme


class FieldFlow(QtWidgets.QLayout):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.entries = []
        self.setContentsMargins(0, 0, 0, 0)
        self.setSpacing(8)

    def addItem(self, item):
        self.entries.append(item)

    def count(self):
        return len(self.entries)

    def itemAt(self, index):
        return self.entries[index] if 0 <= index < len(self.entries) else None

    def takeAt(self, index):
        return self.entries.pop(index) if 0 <= index < len(self.entries) else None

    def hasHeightForWidth(self):
        return True

    def heightForWidth(self, width):
        return self.arrange(QtCore.QRect(0, 0, width, 0), False)

    def setGeometry(self, rect):
        super().setGeometry(rect)
        self.arrange(rect, True)

    def sizeHint(self):
        return QtCore.QSize(350, self.heightForWidth(500))

    def minimumSize(self):
        return QtCore.QSize(0, 0)

    def expandingDirections(self):
        return QtCore.Qt.Orientation.Horizontal

    def arrange(self, rect, paint):
        x, y, row_height = rect.x(), rect.y(), 0
        pending = []
        def flush():
            if paint:
                for entry, left, width, height in pending:
                    entry.setGeometry(QtCore.QRect(left, y + (row_height - height) // 2, width, height))
            pending.clear()
        for item in self.entries:
            widget = item.widget()
            if widget.isHidden():
                continue
            full = bool(widget.property('fullRow'))
            width = rect.width() if full else min(rect.width(), item.sizeHint().width())
            if x > rect.x() and (full or x + width > rect.right() + 1):
                flush()
                x, y, row_height = rect.x(), y + row_height + self.spacing(), 0
            height = item.heightForWidth(width) if item.hasHeightForWidth() else item.sizeHint().height()
            pending.append((item, x, width, height))
            row_height = max(row_height, height)
            x += width + self.spacing()
            if full:
                flush()
                x, y, row_height = rect.x(), y + row_height + self.spacing(), 0
        flush()
        return max(0, y + row_height - rect.y())


class SettingsSection(QtWidgets.QWidget):
    def __init__(self, title):
        super().__init__()
        self.stack = QtWidgets.QVBoxLayout(self)
        self.stack.setContentsMargins(0, 0, 0, 0)
        self.stack.setSpacing(7)
        heading = QtWidgets.QHBoxLayout()
        self.heading = QtWidgets.QLabel(title)
        self.heading.setStyleSheet('font-weight: 600; color: #526778;')
        line = QtWidgets.QFrame()
        line.setFrameShape(QtWidgets.QFrame.Shape.HLine)
        line.setStyleSheet('color: #DCE2E7;')
        heading.addWidget(self.heading)
        heading.addWidget(line, 1)
        self.stack.addLayout(heading)


def arrange_compact_action(dialog):
    from action_editor_ui import FoldSection
    dialog.setObjectName('actionEditor')
    dialog.setMinimumSize(400, 340)
    dialog.resize(560, 480)
    outer = dialog.layout()
    outer.setContentsMargins(12, 10, 12, 10)
    outer.setSpacing(10)
    header = outer.itemAt(0).layout()
    type_row = header.takeRow(0)
    sip.delete(header)
    rows = []
    for form in dialog._settings_forms:
        while form.rowCount():
            row = form.takeRow(0)
            rows.append((row.labelItem.widget() if row.labelItem else None, row.fieldItem.widget()))
    labels = {id(field): label for label, field in rows}
    labels[id(dialog.type_combo)] = type_row.labelItem.widget()
    dialog._field_labels = labels
    dialog._compact_pairs = []
    dialog._setting_rows = []
    dialog._numeric_fields = []
    used = set()

    header_widget = QtWidgets.QWidget(dialog)
    header_layout = QtWidgets.QVBoxLayout(header_widget)
    header_layout.setContentsMargins(0, 0, 0, 0)
    outer.insertWidget(0, header_widget)
    scroll = QtWidgets.QScrollArea()
    scroll.setWidgetResizable(True)
    scroll.setFrameShape(QtWidgets.QFrame.Shape.NoFrame)
    page = QtWidgets.QWidget()
    page.setObjectName('editorPage')
    page.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)
    stack = QtWidgets.QVBoxLayout(page)
    stack.setContentsMargins(0, 2, 2, 2)
    stack.setSpacing(12)
    dialog.primary_section = SettingsSection('동작 설정')
    dialog.options_section = SettingsSection('실행 옵션')
    stack.addWidget(dialog.primary_section)
    dialog.transition_section = FoldSection('참 → 거짓 변화 감지')
    transition_layout = QtWidgets.QVBoxLayout(dialog.transition_section.body)
    transition_layout.setContentsMargins(10, 2, 0, 0)
    transition_layout.setSpacing(7)
    stack.addWidget(dialog.transition_section)
    stack.addWidget(dialog.options_section)
    dialog.delay_section = FoldSection('입력 간격')
    delay_layout = QtWidgets.QVBoxLayout(dialog.delay_section.body)
    delay_layout.setContentsMargins(0, 0, 0, 0)
    stack.addWidget(dialog.delay_section)
    dialog.transition_check.toggled.connect(dialog.transition_section.setExpanded)
    dialog.delay_override_check.toggled.connect(dialog.delay_section.setExpanded)
    scroll.setWidget(page)
    dialog.action_scroll = scroll
    outer.insertWidget(1, scroll, 1)

    def add_row(target, *specs, full=False):
        row_widget = QtWidgets.QWidget()
        row_flow = FieldFlow(row_widget)
        fields = []
        for attr, title, width in specs:
            field = getattr(dialog, attr)
            used.add(id(field))
            fields.append(field)
            label = labels.get(id(field))
            if title is None:
                if label is not None:
                    label.setParent(dialog)
                    label.hide()
                    labels[id(field)] = None
                label = None
            else:
                if not isinstance(label, QtWidgets.QLabel):
                    label = QtWidgets.QLabel()
                    labels[id(field)] = label
                label.setText(title)
                label.setWordWrap(False)
                label.setSizePolicy(QtWidgets.QSizePolicy.Policy.Maximum, QtWidgets.QSizePolicy.Policy.Preferred)
            wrapper = QtWidgets.QWidget()
            pack = QtWidgets.QHBoxLayout(wrapper)
            pack.setContentsMargins(0, 0, 0, 0)
            pack.setSpacing(7)
            if label is not None:
                pack.addWidget(label)
            pack.addWidget(field)
            wrapper.setProperty('fullRow', full)
            if isinstance(field, (QtWidgets.QLineEdit, QtWidgets.QComboBox)):
                field.setMinimumWidth(0)
                field.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Fixed)
            if isinstance(field, QtWidgets.QComboBox):
                field.setSizeAdjustPolicy(QtWidgets.QComboBox.SizeAdjustPolicy.AdjustToMinimumContentsLengthWithIcon)
                field.setMinimumContentsLength(8)
            if isinstance(field, QtWidgets.QAbstractSpinBox):
                field.setSizePolicy(QtWidgets.QSizePolicy.Policy.Fixed, QtWidgets.QSizePolicy.Policy.Fixed)
                dialog._numeric_fields.append((field, width or 82))
                field.valueChanged.connect(lambda *_: fit_numeric_fields(dialog))
            elif width:
                field.setFixedWidth(width)
                field.setSizePolicy(QtWidgets.QSizePolicy.Policy.Fixed, QtWidgets.QSizePolicy.Policy.Fixed)
            row_flow.addWidget(wrapper)
            dialog._compact_pairs.append((wrapper, field, row_flow))
        target.addWidget(row_widget)
        dialog._setting_rows.append((row_widget, fields))
        return row_widget

    dialog.enabled_check.setText('사용')
    dialog.once_check.setText('첫 사이클만')
    dialog.force_first_check.setText('첫 입력 보장')
    dialog.force_first_check.setToolTip('트리거가 풀려도 첫 사이클을 한 번은 끝까지 실행합니다.')
    dialog.quick_toggle_check.setText('빠른 토글')
    dialog.quick_toggle_name.setPlaceholderText('표시 이름 (선택)')
    # Detach the checkbox formerly used as the name field's form label.
    labels[id(dialog.quick_toggle_name)] = None
    labels[id(dialog.quick_toggle_check)] = None
    add_row(header_layout, ('type_combo', '종류', 190), ('name_edit', '이름', 150), ('enabled_check', None, None))
    primary = dialog.primary_section.stack
    add_row(primary, ('key_edit', '키', 110), ('repeat_edit', '반복', 80))
    dialog.action_main_key_edit.hide()
    old = dialog.action_key_builder_row.layout()
    while old.count():
        old.takeAt(0)
    sip.delete(old)
    modifiers = QtWidgets.QHBoxLayout(dialog.action_key_builder_row)
    modifiers.setContentsMargins(0, 0, 0, 0)
    for check in (dialog.action_mod_ctrl, dialog.action_mod_shift, dialog.action_mod_alt, dialog.action_mod_win):
        modifiers.addWidget(check)
    modifiers.addStretch()
    add_row(primary, ('action_key_builder_row', '보조키', None), full=True)
    add_row(primary, ('key_source_combo', '입력 방식', 220))
    add_row(primary, ('aion2_key_skill', '스킬', None), ('aion2_key_item', '소모품', None), full=True)
    add_row(primary, ('aion2_key_source', '프로그램 ID', 190), ('aion2_key_port', '포트', 90))
    add_row(primary, ('aion2_key_status', '연결 키', None), full=True)
    add_row(primary, ('key_warn_label', None, None), full=True)
    add_row(primary, ('mouse_button_combo', '버튼', 165), ('mouse_pos_mode_combo', '이동 기준', 165))
    add_row(primary, ('mouse_pos_edit', '좌표 x,y', 190), ('mouse_move_duration_spin', '이동 시간', 110))
    add_row(primary, ('wheel_direction_combo', '방향', 95), ('wheel_amount_spin', '횟수', 80), ('wheel_interval_spin', '간격', 100))
    add_row(primary, ('skip_pressed_check', None, None), ('release_pressed_check', None, None), ('pause_keep_check', None, None))
    add_row(primary, ('sleep_wrap', '대기 시간', None), full=True)
    add_row(primary, ('sound_file_wrap', '파일', None), full=True)
    add_row(primary, ('sound_wait_mode_combo', '재생 방식', 190))
    add_row(primary, ('sound_duration_spin', '재생 시간', 105), ('sound_repeat_spin', '반복', 90))
    add_row(primary, ('label_edit', '라벨 이름', None), ('goto_combo', '이동할 라벨', None), full=True)
    add_row(primary, ('macro_target_combo', '실행할 매크로', None), full=True)
    add_row(primary, ('block_target_combo', '공용 블록', None), full=True)
    add_row(primary, ('process_control_action_combo', '동작', 170), ('window_pick_btn', None, None))
    add_row(primary, ('process_path_wrap', '실행 파일', None), full=True)
    add_row(primary, ('process_args_edit', '실행 인자', None), full=True)
    add_row(primary, ('process_cwd_edit', '작업 폴더', None), full=True)
    add_row(primary, ('window_match_mode_combo', '창 찾기', 200))
    add_row(primary, ('window_title_edit', '창 제목', None), full=True)
    add_row(primary, ('window_process_edit', '프로세스', None), full=True)
    add_row(primary, ('window_class_edit', '클래스', None), full=True)
    add_row(primary, ('window_restore_check', None, None), ('window_fail_stop_check', None, None))
    add_row(primary, ('window_wait_spin', '포커스 후 대기', 110))
    add_row(primary, ('var_name_edit', '변수', 170), ('var_update_mode_combo', '동작', 160))
    add_row(primary, ('var_value_edit', '값', None), full=True)
    add_row(primary, ('telegram_token_edit', '봇 토큰', None), full=True)
    add_row(primary, ('telegram_chat_id_edit', '챗 ID', None), full=True)
    add_row(primary, ('telegram_message_edit', '메시지', None), full=True)
    add_row(primary, ('telegram_ssl_verify_check', None, None), ('telegram_test_btn', None, None))
    add_row(primary, ('timer_slot_combo', '슬롯', 90))
    add_row(primary, ('timer_value_wrap', '타이머 값', None), full=True)
    add_row(primary, ('region_edit', '범위 x,y,w,h', None), full=True)
    add_row(primary, ('region_offset_edit', '추가 범위', None), full=True)
    add_row(primary, ('pixel_target_edit', '저장할 변수', None), full=True)
    add_row(primary, ('group_mode_combo', '실행 방식', 220), ('group_repeat_spin', '반복', 90))

    dialog.condition_summary_panel = QtWidgets.QFrame()
    dialog.condition_summary_panel.setObjectName('actionConditionSummary')
    summary_layout = QtWidgets.QVBoxLayout(dialog.condition_summary_panel)
    summary_layout.setContentsMargins(10, 8, 10, 8)
    dialog.cond_label.setWordWrap(True)
    dialog.cond_label.setTextFormat(QtCore.Qt.TextFormat.PlainText)
    add_row(summary_layout, ('cond_label', None, None), full=True)
    used.add(id(dialog.edit_cond_btn))
    summary_layout.addWidget(dialog.edit_cond_btn, 0, QtCore.Qt.AlignmentFlag.AlignRight)
    primary.addWidget(dialog.condition_summary_panel)
    dialog.if_confirm_spin.setSuffix(' 회 연속')
    add_row(primary, ('if_confirm_spin', '거짓 확정', 110))
    add_row(transition_layout, ('transition_check', None, None))
    add_row(transition_layout, ('transition_target_combo', '감지 기준', None), full=True)
    add_row(transition_layout, ('transition_confirm_combo', '확정 방식', 190))
    add_row(transition_layout, ('transition_count_spin', '확인 횟수', 110), ('transition_ms_spin', '유지 시간', 110))
    options = dialog.options_section.stack
    add_row(options, ('parallel_check', None, None), ('parallel_interval_spin', '주기', 120))
    add_row(options, ('once_check', None, None), ('force_first_check', None, None))
    add_row(options, ('quick_toggle_check', None, None), ('quick_toggle_name', '이름', 200))
    add_row(delay_layout, ('delay_override_group', None, None), full=True)
    add_row(stack, ('desc_edit', '설명', None), full=True)
    stack.addStretch(1)

    # Lengthy explanations remain available beside the corresponding control.
    dialog._help_fields = {
        'aion2_key_hint': 'key_source_combo', 'mouse_pos_hint_label': 'mouse_pos_edit',
        'sleep_hint_label': 'sleep_wrap', 'var_help_label': 'var_value_edit',
        'parallel_hint': 'parallel_check', 'transition_hint': 'transition_check',
    }
    for hint_name in dialog._help_fields:
        hint = getattr(dialog, hint_name)
        used.add(id(hint))
        hint.setParent(dialog)
        hint.hide()
        label = labels.get(id(hint))
        if label is not None:
            label.setParent(dialog)
            label.hide()
            labels[id(hint)] = None
    missing = [field for _, field in rows if id(field) not in used]
    if missing:
        raise RuntimeError('Action fields missing from layout: ' + repr(missing))
    dialog.empty_action_hint = QtWidgets.QLabel('이 액션은 추가 입력값 없이 실행됩니다.')
    dialog.empty_action_hint.setStyleSheet('color: #74808C;')
    primary.addWidget(dialog.empty_action_hint)
    dialog.quick_toggle_check.toggled.connect(lambda *_: refresh_compact_action(dialog))
    dialog.edit_cond_btn.setProperty('editorPrimary', True)
    dialog.ok_btn.setProperty('editorPrimary', True)
    dialog.ok_btn.setText('저장')
    dialog.ok_btn.setDefault(True)
    footer = outer.itemAt(outer.count() - 1).layout()
    footer.removeWidget(dialog.ok_btn)
    footer.removeWidget(dialog.cancel_btn)
    footer.addWidget(dialog.cancel_btn)
    footer.addWidget(dialog.ok_btn)
    outer.removeWidget(dialog.settings_tabs)
    dialog.settings_tabs.hide()
    dialog.settings_tabs.deleteLater()
    apply_editor_theme(dialog)
    install_action_tooltips(dialog)
    fit_numeric_fields(dialog)


def fit_numeric_fields(dialog):
    for field, base_width in dialog._numeric_fields:
        # Account for the complete displayed number, suffix and native step buttons.
        needed = field.fontMetrics().horizontalAdvance(field.text()) + 42
        field.setFixedWidth(max(base_width, needed))


def refresh_condition_summary(dialog):
    condition = dialog._condition
    draft = getattr(dialog, '_condition_preview_dialog', None)
    if draft is not None:
        import copy
        condition = copy.deepcopy(draft.root_condition)
        if condition is not None:
            condition.name = draft.cond_name_edit.text().strip() or None
    from shared_ui import controller_for
    controller = controller_for(dialog)
    if condition is not None and controller is not None:
        from engine import Condition
        from lib.shared_settings import expand_condition
        try:
            condition = Condition.from_dict(
                expand_condition(condition.to_dict(), controller.entries), dialog._resolver)
        except (ValueError, KeyError) as exc:
            message = f'조건 연결 오류: {exc}'
            dialog.cond_label.setText(message)
            dialog.cond_label.setToolTip(message)
            return
    if condition is None or (condition.type in ('all', 'any') and not condition.shared_ref
                             and not condition.conditions):
        dialog.cond_label.setText('조건이 없습니다. 조건 편집에서 추가하세요.')
        dialog.cond_label.setToolTip('')
        return
    describe = dialog._describe_condition
    lines = []
    def walk(node, depth=0):
        prefix = '  ' * depth
        if node.type in ('all', 'any') and not node.shared_ref:
            title = 'AND · 모두 만족' if node.type == 'all' else 'OR · 하나라도 만족'
            lines.append(prefix + title + (' · ' + node.name if node.name else ''))
            for child in node.conditions:
                walk(child, depth + 1)
        else:
            name = (node.name + ' · ') if node.name else ''
            lines.append(prefix + name + describe(node))
        for title, children in (('참이면', node.on_true), ('거짓이면', node.on_false)):
            if children:
                lines.append(prefix + '  ' + title)
                for child in children:
                    walk(child, depth + 2)
    walk(condition)
    dialog.cond_label.setToolTip('\n'.join(lines))
    shown = lines[:5]
    if len(lines) > 5:
        shown.append(f'… 추가 {len(lines) - 5}개 항목 · 조건 편집에서 전체 보기')
    dialog.cond_label.setText('\n'.join(shown))


def refresh_compact_action(dialog):
    for hint_name, target_name in dialog._help_fields.items():
        hint = getattr(dialog, hint_name)
        getattr(dialog, target_name).setToolTip(hint.text())
        hint.hide()
    dialog.quick_toggle_name.setVisible(dialog.quick_toggle_check.isChecked())
    label = dialog._field_labels.get(id(dialog.quick_toggle_name))
    if label is not None:
        label.setVisible(dialog.quick_toggle_check.isChecked())
    parallel = dialog.parallel_check.isChecked()
    dialog.parallel_interval_spin.setEnabled(parallel and dialog._parallel_allowed)
    for wrapper, field, layout in dialog._compact_pairs:
        wrapper.setVisible(not field.isHidden())
        layout.invalidate()
    for row, fields in dialog._setting_rows:
        row.setVisible(any(not field.isHidden() for field in fields))
    dialog.transition_section.setVisible(not dialog.transition_check.isHidden())
    dialog.delay_section.setVisible(not dialog.delay_override_group.isHidden())
    dialog.condition_summary_panel.setVisible(not dialog.cond_label.isHidden())
    typ = dialog._current_type()
    titles = {'press': '키 입력', 'down': '키 누르기', 'up': '키 떼기',
        'if': '조건', 'elif': '조건', 'group': '그룹 실행', 'sleep': '대기 시간',
        'mouse_click': '마우스 클릭', 'mouse_down': '마우스 누르기', 'mouse_up': '마우스 떼기',
        'mouse_move': '마우스 이동', 'mouse_wheel': '마우스 휠', 'sound_alert': '소리 알림',
        'process_control': '프로그램 제어', 'window_focus': '프로그램 제어',
        'set_var': '변수 설정', 'timer': '타이머', 'pixel_get': '픽셀 저장',
        'telegram_message': '텔레그램 메시지', 'label': '라벨', 'goto': '이동할 라벨',
        'macro_cycle': '매크로 실행', 'shared_block': '공용 블록 실행'}
    dialog.primary_section.heading.setText(titles.get(typ, dialog.type_combo.currentText().strip()))
    dialog.empty_action_hint.hide()
    dialog.primary_section.setVisible(typ in titles)
    if typ not in titles:
        dialog.type_combo.setToolTip('이 액션은 추가 입력값 없이 실행됩니다.')
    else:
        dialog.type_combo.setToolTip('실행할 액션 종류를 선택합니다.')
    refresh_condition_summary(dialog)
    fit_numeric_fields(dialog)
    install_action_tooltips(dialog)


def install_action_tooltips(dialog):
    descriptions = {
        'type_combo': '실행할 동작 종류를 선택합니다. 종류에 따라 필요한 설정이 표시됩니다.',
        'name_edit': '액션 목록에 표시할 이름입니다. 비워 두어도 실행할 수 있습니다.',
        'enabled_check': '체크하면 이 액션을 실행합니다. 해제하면 실행 순서에서 건너뜁니다.',
        'once_check': '매크로의 첫 사이클에서만 이 액션을 실행하고 이후 반복에서는 건너뜁니다.',
        'force_first_check': '트리거가 풀려도 첫 사이클을 한 번은 끝까지 실행하도록 하는 옵션입니다.',
        'quick_toggle_check': '이 액션을 빠른 토글 창에 표시하여 사용 여부를 빠르게 켜고 끌 수 있게 합니다.',
        'quick_toggle_name': '빠른 토글 창에 표시할 이름입니다. 비워 두면 액션 이름을 사용합니다.',
        'desc_edit': '액션의 목적이나 주의사항을 기록하는 메모입니다. 실행 동작에는 영향을 주지 않습니다.',
        'key_edit': '누를 키를 입력합니다. 예: k, space, f1, ctrl+2. 아래 보조키 체크와 서로 연동됩니다.',
        'repeat_edit': '키 또는 마우스 입력의 반복 횟수입니다. 1이면 한 번 실행합니다.',
        'action_key_builder_row': '입력한 키와 함께 누를 Ctrl·Shift·Alt·Win을 선택합니다.',
        'key_source_combo': '직접 입력한 키를 사용할지, 연결된 모니터의 스킬·소모품 단축키를 사용할지 선택합니다.',
        'edit_cond_btn': '조건 편집창을 열어 AND·OR 묶음과 개별 조건, 참·거짓 하위 조건을 수정합니다.',
        'if_confirm_spin': 'IF와 ELIF가 모두 연속으로 거짓인 횟수가 이 값에 도달하면 ELSE를 실행합니다. 참이 나오면 횟수를 초기화합니다.',
        'ok_btn': '현재 설정을 저장하고 창을 닫습니다.',
        'cancel_btn': '편집한 액션 설정을 적용하지 않고 창을 닫습니다.',
        'mouse_button_combo': '입력할 마우스 버튼을 선택합니다.',
        'wheel_direction_combo': '마우스 휠을 위 또는 아래로 돌릴 방향을 선택합니다.',
        'wheel_amount_spin': '휠을 돌릴 횟수를 설정합니다.',
        'wheel_interval_spin': '연속 휠 입력 사이의 대기 시간을 밀리초 단위로 설정합니다.',
        'mouse_move_duration_spin': '마우스가 지정 좌표까지 이동하는 시간입니다. 0이면 즉시 이동합니다.',
        'sound_wait_mode_combo': '사운드를 한 번 재생할지, 지정 시간 또는 횟수만큼 재생할지 선택합니다.',
        'sound_duration_spin': '사운드 재생 시간을 초 단위로 지정합니다.',
        'sound_repeat_spin': '사운드 반복 재생 횟수를 지정합니다.',
        'group_mode_combo': '그룹 안의 액션을 모두 실행할지, 조건에 따라 실행하거나 반복할지 선택합니다.',
        'transition_target_combo': '참에서 거짓으로 바뀌는지 감시할 조건을 선택합니다.',
        'transition_confirm_combo': '거짓을 즉시 확정할지, 연속 횟수 또는 유지 시간으로 확정할지 선택합니다.',
        'transition_count_spin': '변화 감지 대상이 연속으로 거짓이어야 하는 횟수입니다.',
        'transition_ms_spin': '변화 감지 대상이 거짓 상태를 유지해야 하는 시간입니다. 단위는 ms입니다.',
        'delay_override_check': '기본 입력 간격 대신 이 액션에만 지정한 누름·키 사이 간격을 적용합니다.',
        'aion2_key_source': '단축키 정보를 제공하는 외부 프로그램의 ID입니다.',
        'aion2_key_port': '같은 PC에서 모니터와 통신할 TCP 포트입니다. 모니터의 설정과 맞춰야 합니다.',
        'aion2_key_skill': '모니터가 전달하는 단축키를 사용할 스킬을 선택합니다.',
        'aion2_key_item': '모니터의 소모품 슬롯에서 단축키를 가져올 소모품 종류를 선택합니다.',
        'process_control_action_combo': '프로그램의 실행·종료·재실행 또는 창 포커스 동작을 선택합니다.',
        'window_pick_btn': '현재 열려 있는 창을 선택하여 대상 창과 프로그램 정보를 채웁니다.',
        'process_path_wrap': '실행하거나 제어할 프로그램의 실행 파일 경로를 지정합니다.',
        'process_args_edit': '프로그램 실행 시 전달할 명령줄 인자입니다. 필요하지 않으면 비워 둡니다.',
        'process_cwd_edit': '프로그램 실행 시 사용할 작업 폴더입니다. 비워 두면 기본 폴더를 사용합니다.',
        'window_match_mode_combo': '대상 창을 찾을 때 제목·프로세스 등의 정보를 비교하는 방식을 선택합니다.',
        'window_title_edit': '찾을 창의 제목을 입력합니다. 선택한 창 찾기 방식에 따라 비교합니다.',
        'window_process_edit': '대상 프로그램의 프로세스 이름입니다. 예: program.exe.',
        'window_class_edit': '대상 창의 클래스 이름입니다. 창 선택 기능으로 가져올 수 있습니다.',
        'window_restore_check': '대상 창이 최소화되어 있으면 복원한 뒤 포커스를 이동합니다.',
        'window_fail_stop_check': '대상 창이나 프로그램을 찾지 못하면 현재 매크로를 중단합니다.',
        'window_wait_spin': '창에 포커스를 이동한 뒤 다음 액션까지 기다릴 시간입니다. 단위는 ms입니다.',
        'var_name_edit': '값을 변경할 변수를 선택하거나 이름을 입력합니다.',
        'var_update_mode_combo': '변수 값을 대입하거나 증감하는 등 변경 방식을 선택합니다.',
        'telegram_token_edit': '메시지를 전송할 텔레그램 봇의 토큰입니다.',
        'telegram_chat_id_edit': '메시지를 받을 텔레그램 대화방 또는 사용자의 챗 ID입니다.',
        'telegram_message_edit': '텔레그램으로 전송할 메시지 내용을 입력합니다.',
        'telegram_ssl_verify_check': '텔레그램 연결 시 서버의 SSL 인증서를 검증합니다.',
        'telegram_test_btn': '입력한 봇 토큰·챗 ID·메시지로 실제 테스트 메시지를 전송합니다.',
        'timer_slot_combo': '설정할 타이머 슬롯을 선택합니다. 조건에서는 같은 슬롯의 타이머를 확인합니다.',
        'timer_value_wrap': '선택한 타이머에 설정할 값과 시간 단위를 지정합니다.',
        'region_edit': '픽셀을 읽을 화면 범위를 x,y,너비,높이 순서로 입력합니다.',
        'region_offset_edit': '기준 범위에 더할 좌표·크기 보정값입니다. 필요하지 않으면 비워 둡니다.',
        'pixel_target_edit': '읽은 픽셀 정보를 저장할 변수 이름입니다.',
        'label_edit': '이 위치에 붙일 라벨 이름입니다. 점프 액션에서 이 이름을 선택합니다.',
        'goto_combo': '실행 위치를 이동할 라벨을 선택합니다.',
        'macro_target_combo': '한 사이클 실행할 다른 매크로를 선택합니다.',
        'skip_pressed_check': '키가 이미 눌린 상태이면 중복 누름 입력을 건너뜁니다.',
        'release_pressed_check': '현재 눌린 상태인 키에 대해서만 떼기 입력을 보냅니다.',
        'pause_keep_check': '매크로를 일시중지해도 이 액션으로 누른 키 또는 마우스 버튼을 유지합니다.',
        'sound_file_wrap': '재생할 사운드 파일을 선택합니다. 선택 해제 버튼으로 파일 지정을 지울 수 있습니다.',
    }
    for name, description in descriptions.items():
        field = getattr(dialog, name, None)
        if field is not None:
            field.setToolTip(description)
    for name in ('ctrl', 'shift', 'alt', 'win'):
        getattr(dialog, 'action_mod_' + name).setToolTip(f'{name.title()} 키를 입력 키와 함께 누릅니다. 체크 변경은 위의 키 입력에 반영됩니다.')
    for wrapper, field, _ in dialog._compact_pairs:
        label = dialog._field_labels.get(id(field))
        text = field.toolTip()
        if not text:
            title = label.text() if isinstance(label, QtWidgets.QLabel) else field.text() if isinstance(field, QtWidgets.QAbstractButton) else ''
            text = f'{title} 설정입니다.' if title else '이 액션에 사용할 값을 설정합니다.'
            if isinstance(field, QtWidgets.QLineEdit) and field.placeholderText():
                text += '\n입력 안내: ' + field.placeholderText()
            field.setToolTip(text)
        wrapper.setToolTip(text)
        if label is not None:
            label.setToolTip(text)
        for child in field.findChildren(QtWidgets.QWidget):
            if isinstance(child, (QtWidgets.QAbstractButton, QtWidgets.QLineEdit, QtWidgets.QComboBox, QtWidgets.QAbstractSpinBox)) and not child.toolTip():
                child.setToolTip(text)
    dialog.delay_section.toggle.setToolTip('이 액션에 적용할 입력 간격 설정을 펼치거나 접습니다.')
    dialog.transition_section.toggle.setToolTip('IF 실행 후 참→거짓 변화를 감지하는 설정을 펼치거나 접습니다. 일반 ELSE의 거짓 확인과 별개입니다.')
