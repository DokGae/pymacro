"""Small, value-only snapshots of actual condition evaluations. Never re-evaluates."""

OPERATORS = {'eq': '=', 'ne': '≠', 'gt': '>', 'ge': '≥', 'lt': '<', 'le': '≤',
             'even': '짝수', 'odd': '홀수', 'true': '참', 'false': '거짓', 'range': '범위'}
TYPES = {'all': '모두 충족 (AND)', 'any': '하나 이상 충족 (OR)', 'key': '키 상태',
         'var': '변수 비교', 'timer': '타이머', 'schedule': '날짜·시간',
         'pixel': '이미지·픽셀', 'external': '외부 프로그램 상태', 'aion2': 'AION2 전용'}
STATES = {'true': '참', 'false': '거짓', 'not_evaluated': '미검사', 'disabled': '비활성',
          'unavailable': '검사 불가', 'error': '검사 오류'}


def text(value):
    if value is None:
        return '없음'
    if type(value) is bool:
        return '참' if value else '거짓'
    value = str(value)
    return value if len(value) <= 500 else value[:497] + '…'


def condition_template(cond, inherited_reason=None):
    typ = getattr(cond, 'type', '')
    title = TYPES.get(typ, '조건')
    name = getattr(cond, 'name', '')
    criterion = ''
    if typ == 'key':
        mode = getattr(cond, 'key_mode', None) or 'hold'
        mode = {'hold': '눌려 있음', 'press': '새로 누름', 'down': '새로 누름',
                'up': '방금 뗌', 'released': '눌리지 않음'}.get(mode, mode)
        criterion = f'{text(cond.key)} · {mode}'
    elif typ == 'var':
        criterion = f'{text(cond.var_name)} {OPERATORS.get(cond.var_operator, cond.var_operator)} {text(cond.var_value_raw if cond.var_value_raw is not None else cond.var_value)}'
    elif typ == 'timer':
        criterion = f'타이머 {cond.timer_index} {OPERATORS.get(cond.timer_operator, cond.timer_operator)} {cond.timer_value_text()}'
    elif typ == 'aion2':
        from aion2_conditions import condition_summary
        criterion=condition_summary(cond)
    elif typ == 'external':
        criterion = f'{text(cond.external_key)} · {OPERATORS.get(cond.external_operator, cond.external_operator)} {text(cond.external_value)}'
    elif typ == 'pixel':
        criterion = f"{'일치 항목 있어야 함' if cond.pixel_exists else '일치 항목 없어야 함'} · 영역 {text(cond.region_raw or cond.region)}"
    elif typ == 'schedule':
        criterion = f'{OPERATORS.get(cond.schedule_operator, cond.schedule_operator)} {text(cond.schedule_value_raw)}'
    enabled = getattr(cond, 'enabled', True)
    reason = inherited_reason or '앞선 조건 또는 분기 결과로 검사하지 않았습니다.'
    node = dict(type=typ, name=f'{text(name)} · {title}' if name else title,
                state='not_evaluated' if enabled else 'disabled', result=None, base_result=None,
                actual='—', criterion=criterion,
                reason=reason if enabled else '비활성 조건이라 검사하지 않았습니다.',
                children=[], on_true=[], on_false=[])
    child_reason = inherited_reason if enabled else '상위 조건이 비활성이라 검사하지 않았습니다.'
    for field, source in (('children', 'conditions'), ('on_true', 'on_true'), ('on_false', 'on_false')):
        node[field] = [condition_template(child, child_reason) for child in (getattr(cond, source, []) or [])]
    return node


def finish_condition_evidence(node, base, result, detail):
    node.update(base_result=base, result=result, state='true' if result else 'false')
    typ = node['type']
    node['unavailable'] = any(detail.get(kind, {}).get('unavailable') or detail.get(kind, {}).get('error')
                              for kind in ('external', 'pixel'))
    comparison = None
    if typ == 'key':
        d = detail.get('key', {})
        node['actual'] = f"현재 {'눌림' if d.get('pressed') else '뗌'} / 직전 {'눌림' if d.get('prev') else '뗌'}"
        comparison = f"{node['actual']} · 기준 {node['criterion']}"
    elif typ == 'var':
        d = detail.get('var', {})
        node['actual'] = text(d.get('actual'))
        node['criterion'] = f"{text(d.get('name'))} {OPERATORS.get(d.get('operator'), d.get('operator'))} {text(d.get('expected'))}"
        comparison = f"실제 값 {node['actual']} · 기준 {node['criterion']}"
    elif typ == 'timer':
        d = detail.get('timer', {})
        node['actual'] = text(d.get('actual_text', d.get('actual')))
        node['criterion'] = f"타이머 {d.get('slot')} {OPERATORS.get(d.get('operator'), d.get('operator'))} {text(d.get('expected_text'))}"
        comparison = f"현재 {node['actual']} · 기준 {node['criterion']}"
    elif typ == 'aion2':
        d=detail.get('external',{})
        elapsed=d.get('actual')
        node['actual']=(f"남은 {text(elapsed)}초" if d.get('aion2_kind')=='cooldown' else
                        '감시 시작 후 사용 미감지' if elapsed==-1 else f'{text(elapsed)}초 경과')
        comparison=d.get('status')
        if d.get('unavailable'):
            node['actual']='미수신'
            comparison=f"{text(d.get('status') or '외부값 수신 대기')} · 미수신은 거짓으로 처리"
    elif typ == 'schedule':
        d = detail.get('schedule', {})
        node['actual'] = text(d.get('current_text'))
        node['criterion'] = f"{d.get('operator_text', '')} {text(d.get('expected_text'))}"
        comparison = f"검사 시각 {node['actual']} · 기준 {node['criterion']}"
    elif typ == 'pixel':
        d = detail.get('pixel', {})
        node['actual'] = f"일치 {text(d.get('match_count'))}개 · 표본 색상 {text(d.get('sample_color'))}"
        node['criterion'] = (f"{'최소 ' + text(d.get('min_count')) + '개 일치' if d.get('expect_exists') else '일치 0개'}"
                             f" · 오차 {text(d.get('tolerance'))} · 영역 {text(d.get('region'))}"
                             f" · {'패턴 ' + text(d.get('pattern')) if d.get('pattern') else '색상 ' + text(d.get('color'))}")
        if d.get('unavailable') or d.get('error'):
            node.update(state='unavailable', reason=text(d.get('error') or '화면 영역을 검사할 수 없습니다.'))
        else:
            comparison = f"일치 {text(d.get('match_count'))}개 · 기준 " + (
                f"최소 {text(d.get('min_count'))}개 일치" if d.get('expect_exists') else '일치 항목 없음')
    elif typ == 'external':
        d = detail.get('external', {})
        actual = d.get('actual')
        expected = d.get('expected')
        value_type = lambda value: ('참·거짓' if type(value) is bool else '숫자' if type(value) in (int, float)
                                   else '문자열' if isinstance(value, str) else '없음')
        node['actual'] = f'{text(actual)} ({value_type(actual)})'
        op = d.get('operator')
        target = f'{text(expected)} ({value_type(expected)})' if op not in ('true', 'false') else ''
        node['criterion'] = f"{text(d.get('key'))} {OPERATORS.get(op, op)} {target}".strip()
        comparison = f"수신값 {node['actual']} · 기준 {node['criterion']}"
        if d.get('unavailable'):
            node['actual']='미수신'
            comparison=f"{text(d.get('status') or d.get('connection_status') or '외부값 수신 대기')} · 미수신은 거짓으로 처리"
    elif typ in ('all', 'any'):
        group = detail.get('group', {})
        node['actual'] = f"활성 {group.get('count', 0)}개 / 전체 {group.get('total', 0)}개"
        node['criterion'] = '활성 조건 모두 참' if typ == 'all' else '활성 조건 중 하나 이상 참'
    if node['state'] in ('true', 'false'):
        if typ in ('all', 'any'):
            count = detail.get('group', {}).get('count', 0)
            reason = ('활성 조건이 없어 거짓으로 판정했습니다.' if not count else
                      '검사한 조건을 결합한 결과입니다.')
        else:
            reason = f"{comparison or '검사값과 기준 비교'} → {'충족' if base else '미충족'}."
        if base != result:
            reason += f" 본 조건은 {'참' if base else '거짓'}이지만 후속 조건으로 최종 {'참' if result else '거짓'}이 됐습니다."
        node['reason'] = reason
    for child in node['children']:
        if child['state'] == 'not_evaluated':
            child['reason'] = ('앞선 조건이 거짓이라 AND 검사를 종료했습니다.' if typ == 'all' and not base else
                               '앞선 조건이 참이라 OR 검사를 종료했습니다.' if typ == 'any' and base else
                               '이 조건은 검사하지 않았습니다.')
    for field, selected in (('on_true', bool(base)), ('on_false', not bool(base))):
        for child in node[field]:
            if child['state'] == 'not_evaluated':
                child['reason'] = ('앞선 후속 조건이 참이라 검사를 종료했습니다.' if selected else
                                   '본 조건의 결과와 맞지 않는 후속 분기라 검사하지 않았습니다.')
    if typ in ('all', 'any') and not base and base == result and any(
            child['state'] in ('unavailable', 'error') for child in node['children']):
        node.update(state='unavailable', reason='하위 조건을 검사할 수 없었습니다. 실행 시에는 거짓으로 처리됐습니다.')
    selected_branch = node['on_true'] if base else node['on_false']
    if node['state'] in ('true', 'false') and not result and any(
            child['state'] in ('unavailable', 'error') for child in selected_branch):
        node.update(state='unavailable', reason='후속 조건을 검사할 수 없었습니다. 실행 시에는 거짓으로 처리됐습니다.')
    if node['state'] == 'unavailable' and base != result:
        node['reason'] += f" 실행 시 기본 판정 {'참' if base else '거짓'}에 후속 조건을 적용해 최종 {'참' if result else '거짓'}이 됐습니다."


