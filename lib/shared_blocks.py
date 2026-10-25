"""Profile-local reusable action definitions and immutable execution expansion."""
from __future__ import annotations

import copy
import json
import uuid


def branches(action):
    for key in ('actions', 'else_actions', 'transition_actions'):
        yield key, action.get(key, [])
    for index, branch in enumerate(action.get('elif_blocks', [])):
        yield ('elif_blocks', index, 'actions'), branch.get('actions', [])


def walk(actions, prefix=()):
    for index, action in enumerate(actions):
        path = prefix + (index,)
        yield path, action
        for key, children in branches(action):
            yield from walk(children, path + (key if isinstance(key, tuple) else (key,)))


def usages(macros, entries, reference):
    result = []
    for row, macro in enumerate(macros):
        for key in ('actions', 'stop_actions'):
            for path, action in walk(macro.get(key, []), (key,)):
                if action.get('type') == 'shared_block' and action.get('block_ref') == reference:
                    result.append((row, path, macro.get('name') or f'매크로 {row + 1}'))
    for ref, entry in entries.items():
        for path, action in walk(entry.get('actions', []), ('actions',)):
            if action.get('type') == 'shared_block' and action.get('block_ref') == reference:
                result.append((ref, path, '공용 블록 · ' + entry['name']))
    return result


def register(entries, name, actions):
    name = name.strip()
    if not name:
        raise ValueError('공용 블록 이름을 입력하세요.')
    if any(entry.get('name') == name for entry in entries.values()):
        raise ValueError('같은 이름의 공용 블록이 있습니다.')
    ref = uuid.uuid4().hex
    entries[ref] = {'name': name, 'description': '', 'actions': copy.deepcopy(actions)}
    return ref


def expand_actions(actions, entries, stack=(), budget=None):
    budget = [50000] if budget is None else budget
    expanded = []
    for original in actions:
        budget[0] -= 1
        if budget[0] < 0:
            raise ValueError('공용 블록을 펼친 액션이 너무 많습니다 (50,000개 제한).')
        action = copy.deepcopy(original)
        if action.get('type') == 'shared_block':
            ref = action.get('block_ref')
            if ref not in entries:
                raise ValueError(f"공용 블록을 찾을 수 없습니다: {action.get('name') or ref}")
            if ref in stack or len(stack) >= 32:
                raise ValueError('공용 블록 순환 호출 또는 과도한 중첩: ' + entries[ref]['name'])
            action['name'] = entries[ref]['name']
            action['actions'] = expand_actions(entries[ref]['actions'], entries, stack + (ref,), budget)
        else:
            for key in ('actions', 'else_actions', 'transition_actions'):
                if key in action:
                    action[key] = expand_actions(action[key], entries, stack, budget)
            for branch in action.get('elif_blocks', []):
                branch['actions'] = expand_actions(branch.get('actions', []), entries, stack, budget)
        expanded.append(action)
    return expanded


def validate(entries, macros=(), resolver=None):
    from engine import Action
    if not isinstance(entries, dict):
        raise ValueError('공용 블록 목록 형식이 올바르지 않습니다.')
    names = set()
    for ref, entry in entries.items():
        if not isinstance(entry, dict) or not str(entry.get('name', '')).strip() or not isinstance(entry.get('actions'), list):
            raise ValueError(f'공용 블록 형식이 올바르지 않습니다: {ref}')
        if entry['name'] in names:
            raise ValueError('공용 블록 이름이 중복됩니다: ' + entry['name'])
        names.add(entry['name'])
        expanded = expand_actions(entry['actions'], entries, (ref,))
        if any(action.get('type') == 'label' for _, action in walk(expanded)):
            raise ValueError('이동 대상 라벨은 공용 블록 바깥에 두세요: ' + entry['name'])
        parsed = [Action.from_dict(a, resolver) for a in expanded]
        Action.validate_parallel_actions(parsed, allow_parallel=False)
    for macro in macros:
        for key in ('actions', 'stop_actions'):
            expanded = expand_actions(macro.get(key, []), entries)
            Action.validate_parallel_actions([Action.from_dict(a, resolver) for a in expanded], allow_parallel=key == 'actions')


def expand_macro(macro, entries, resolver=None):
    from engine import Action
    # Keep callers' original actions untouched, including separate per-call IF state.
    result = copy.deepcopy(macro)
    for key in ('actions', 'stop_actions'):
        source = getattr(macro, key)
        if any(a.get('type') == 'shared_block' for _, a in walk([v.to_dict() for v in source])):
            setattr(result, key, [Action.from_dict(a, resolver) for a in
                                 expand_actions([v.to_dict() for v in source], entries)])
    return result


def fingerprint(actions):
    # Deliberately exact: timing, enabled flags and transition targets all matter.
    return json.dumps(actions, sort_keys=True, ensure_ascii=False)
