"""Condition selection for IF true-to-false actions."""
import hashlib
import json
from lib.shared_settings import expand_condition, has_shared


TRANSITION_STATES = {
    'waiting': '감지 대기 · IF 참 실행 전',
    'waiting_true': '감지 중 · 대상의 참 상태 대기',
    'watching': '감지 중 · 참→거짓 대기',
    'confirming': '거짓 확정 중',
    'unavailable': '감지 대기 · 검사값 확인 불가',
    'target_error': '대상 조건 확인 필요',
    'executing': '변화 액션 실행 중',
    'completed': '변화 액션 실행 완료',
    'cancelled': '감지 종료 · 매크로 종료',
    'disabled': '감지 비활성',
}


def condition_identity(condition):
    """Identify criteria rather than a position; ignore names and group ordering."""
    def canonical(value):
        if isinstance(value, dict):
            result = {key: canonical(child) for key, child in value.items()
                      if key not in ('name', 'enabled', 'shared_ref')}
            for field in ('region', 'color', 'timer_value'):
                if result.get(field + '_raw') is not None:
                    result.pop(field, None)
            for field in ('conditions', 'on_true', 'on_false'):
                if field in result:
                    result[field].sort(key=lambda child: json.dumps(child, sort_keys=True, ensure_ascii=False))
            return result
        if isinstance(value, list):
            return [canonical(child) for child in value]
        return value
    payload = json.dumps(canonical(condition.to_dict()), sort_keys=True, ensure_ascii=False)
    return hashlib.sha256(payload.encode('utf-8')).hexdigest()


def expanded_root(condition, entries, resolver=None):
    from engine import Condition
    if condition is None:
        raise ValueError('변화 감지에 사용할 IF 조건이 없습니다.')
    if not condition.enabled:
        data = condition.to_dict()
        data['enabled'] = True
        expanded = Condition.from_dict(expand_condition(data, entries), resolver)
        expanded.enabled = False
        return expanded
    if has_shared(condition):
        return Condition.from_dict(expand_condition(condition.to_dict(), entries), resolver)
    return condition


def target_condition(condition, target, entries, resolver=None, *, allow_disabled=False, identity=''):
    if target and identity:
        matches = [(path, node) for path, _, node in target_choices(condition, entries, resolver)
                   if path and condition_identity(node) == identity]
        if len(matches) != 1:
            raise ValueError('감지 대상이 삭제·변경되었거나 동일한 조건이 여러 개입니다. IF에서 대상을 다시 선택하세요.')
        target = matches[0][0]
    node = expanded_root(condition, entries, resolver)
    for index in target:
        if not node.enabled and not allow_disabled:
            raise ValueError('비활성 조건 묶음 안의 조건은 변화 감지 대상으로 사용할 수 없습니다.')
        if type(index) is not int or index < 0 or index >= len(node.conditions):
            raise ValueError('변화 감지 대상 조건이 변경되거나 삭제되었습니다. IF에서 다시 선택하세요.')
        node = node.conditions[index]
    if not node.enabled and not allow_disabled:
        raise ValueError('비활성 조건은 변화 감지 대상으로 사용할 수 없습니다.')
    return node


def bind_target(action, entries, resolver=None):
    """Upgrade positional selections once, before shared definitions can be edited."""
    if not action.transition_target:
        action.transition_target_key = ''
        action.transition_target_label = '전체 IF 결과'
        return
    condition = target_condition(action.condition, action.transition_target, entries, resolver,
        allow_disabled=not action.enabled, identity=action.transition_target_key)
    identity = action.transition_target_key or condition_identity(condition)
    matches = [(path, label) for path, label, node in target_choices(action.condition, entries, resolver)
               if path and condition_identity(node) == identity]
    if len(matches) != 1:
        raise ValueError('동일한 조건이 여러 개라 감지 대상을 구분할 수 없습니다. 조건 묶음을 선택하세요.')
    action.transition_target = list(matches[0][0])
    action.transition_target_key = identity
    action.transition_target_label = matches[0][1].split('  ', 1)[-1]


def confirmation_settings(mode, count, duration_ms):
    if mode not in ('immediate', 'count', 'duration'):
        raise ValueError('거짓 확정 방식이 올바르지 않습니다.')
    if type(count) is not int or not 1 <= count <= 1000000:
        raise ValueError('거짓 연속 확인 횟수는 1~1000000회여야 합니다.')
    if type(duration_ms) is not int or not 1 <= duration_ms <= 86400000:
        raise ValueError('거짓 유지 시간은 1~86400000ms여야 합니다.')
    return mode, count, duration_ms


def target_choices(condition, entries, resolver=None):
    from condition_evidence import condition_template
    root = expanded_root(condition, entries, resolver)
    result = [((), '전체 IF 결과', root)]

    def walk(node, prefix=()):
        for index, child in enumerate(node.conditions):
            path = prefix + (index,)
            detail = condition_template(child)
            label = ' · '.join(part for part in (detail['name'], detail['criterion']) if part)
            result.append((path, '.'.join(str(i + 1) for i in path) + '  ' + label, child))
            walk(child, path)
    walk(root)
    return result


def reliable_result(evidence):
    if evidence.get('unavailable') or evidence.get('state') in ('unavailable', 'error', 'disabled'):
        return False
    return all(reliable_result(child) for field in ('children', 'on_true', 'on_false')
               for child in evidence.get(field, []) if child.get('state') != 'not_evaluated')
