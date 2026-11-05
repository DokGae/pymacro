"""Readable summaries of optional action settings in the macro editor."""


def action_notes(action):
    notes = []
    for field, text in (
        ('var_keep_between_runs', '버튼 해제 후 변수 유지'),
        ('once_per_macro', '첫 사이클만 실행'),
        ('force_first_run', '첫 입력 1회 무조건 실행'),
        ('skip_if_pressed', '이미 눌렸으면 건너뜀'),
        ('release_only_pressed', '눌린 키만 해제'),
        ('hold_keep_on_pause', '일시중지 중 누름 유지'),
        ('key_delay_override_enabled', '개별 입력 간격'),
    ):
        if getattr(action, field, False):
            notes.append(text)
    if action.type == 'if':
        low, high = sorted((action.reaction_delay_min, action.reaction_delay_max))
        if high > 0:
            notes.append(f'반응 지연 {low:g}~{high:g}초')
        if action.confirm_fails > 1:
            notes.append(f'거짓 {action.confirm_fails}회 확인')
        if not action.else_enabled:
            notes.append('ELSE 비활성')
        if action.transition_enabled:
            notes.append('참→거짓 감지')
    if action.parallel_enabled:
        notes.append('병렬 기본 속도' if action.parallel_interval_sec == 0 else f'병렬 {action.parallel_interval_sec:g}초마다')
    if action.repeat_range:
        notes.append(f'랜덤 반복 {action.repeat_range[0]}~{action.repeat_range[1]}회')
    elif action.repeat > 1:
        notes.append(f'반복 {action.repeat}회')
    if getattr(action, 'quick_toggle_id', ''):
        notes.append('빠른 토글: ' + (action.quick_toggle_name or action.quick_toggle_id))
    return notes
