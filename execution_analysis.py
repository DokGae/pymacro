"""Engine-side execution counters. No Qt, input driver, or event-queue dependency."""
from __future__ import annotations

import copy
import hashlib
import json
import threading
import time
from action_controls import if_scope_label


def macro_signature(macro):
    # Manual once/repeat execution changes cycle_count on a runtime copy, not its actions.
    definition = {'actions': [action.to_dict() for action in macro.actions],
                  'stop_actions': [action.to_dict() for action in macro.stop_actions]}
    def normalize(value):
        if isinstance(value, dict):
            value.pop('transition_target_key', None)
            value.pop('transition_target_label', None)
            # Quick switches affect live runner copies via engine overrides.
            # Their current enabled state is captured by the measurement catalog.
            if value.get('quick_toggle_id'):
                value.pop('enabled', None)
            for child in value.values():
                normalize(child)
        elif isinstance(value, (list, tuple)):
            for child in value:
                normalize(child)
    normalize(definition)
    return hashlib.sha256(json.dumps(definition, sort_keys=True, ensure_ascii=False,
                                     default=str).encode('utf-8')).hexdigest()


def action_catalog(actions, *, enabled_override=None):
    """Use the runner's flattened IF child offsets; markers are presentation only."""
    rows = []
    counters = {False: 1, True: 1}
    if_counters = {False: 0, True: 0}

    def next_number(parallel):
        number = str(counters[parallel])
        counters[parallel] += 1
        return number

    def walk(items, prefix=(), parent=None, disabled=False, offset=0, parallel=False):
        for index, action in enumerate(items):
            section = bool(action.parallel_enabled) if not prefix else parallel
            path = prefix + (offset + index,)
            off = disabled or not (enabled_override(action) if enabled_override else action.enabled)
            label = action.name or action.description or action.type
            if action.type == 'if':
                if_counters[section] += 1
                label = if_scope_label(f'{if_counters[section]:02}', action.name)
            target = getattr(action, 'key', '') or getattr(action, 'mouse_button', '')
            if action.type == 'press' and getattr(action, 'key_source', 'direct') == 'aion2':
                from aion2_conditions import skill_label
                target = 'AION2 전용 · ' + skill_label(action.aion2_skill)
            if target and action.type in ('press', 'down', 'up', 'mouse_click', 'mouse_down', 'mouse_up'):
                label += f' [{target}]'
            rows.append(dict(path=path, parent=parent, label=label, kind=action.type,
                             number=next_number(section),
                             disabled=off, gate=parent, parallel=bool(action.parallel_enabled)))
            if action.type == 'if':
                walk(action.actions, path, path, off, parallel=section)
                child_offset = len(action.actions)
                for n, block in enumerate(action.elif_blocks or []):
                    if not isinstance(block, (list, tuple)) or len(block) < 2:
                        continue
                    cond, children = block[:2]
                    if not hasattr(cond, 'enabled'):
                        continue
                    branch = path + (f'elif{n}',)
                    branch_enabled = block[3] if len(block) > 3 and isinstance(block[3], bool) else getattr(cond, 'enabled', True)
                    branch_off = off or not branch_enabled
                    rows.append(dict(path=branch, parent=path, label=f'ELIF · {label}',
                                     number=next_number(section), kind='elif', disabled=branch_off, gate=path, parallel=False))
                    walk(children, path, branch, branch_off, child_offset, parallel=section)
                    child_offset += len(children)
                if action.else_actions or action.has_else_branch:
                    branch = path + ('else',)
                    else_off = off or not action.else_enabled
                    rows.append(dict(path=branch, parent=path, label=f'IF NOT · {label}', kind='else',
                                     number='↳', disabled=else_off, gate=path, parallel=False))
                    walk(action.else_actions, path, branch, else_off, child_offset, parallel=section)
                child_offset += len(action.else_actions)
                if action.transition_enabled or action.transition_actions:
                    branch = path + ('transition',)
                    transition_off = off or not action.transition_enabled
                    target = action.transition_target_label or '전체 IF 결과'
                    rows.append(dict(path=branch, parent=path, label=f'참→거짓 · {label} · {target}', kind='transition', target=target,
                                     number='↳', disabled=transition_off, gate=path, parallel=False))
                    walk(action.transition_actions, path, branch, transition_off, child_offset, parallel=section)
            elif action.type == 'group':
                walk(action.actions, path, path, off, parallel=section)

    walk(actions)
    return rows


def empty_counts():
    return dict(reached=0, true=0, false=0, inputs=0, jumps=0, errors=0,
                unavailable=0, skipped=0, completed=0, last='', destination='', condition_detail=None,
                transition_state='waiting', transition_target='', transition_reason='')


class ExecutionRecorder:
    """One manually controlled measurement; storage depends on actions, not executions."""
    def __init__(self):
        self._lock = threading.RLock()
        self.enabled = False
        self.generation = 0
        self._measurement = None
        self._definitions = {}

    def start(self):
        with self._lock:
            self.generation += 1
            self._definitions.clear()
            self._measurement = dict(id=self.generation, started=time.monotonic(), ended=None,
                                     state='running', reason='', macros={}, version=0)
            self.enabled = True
            return self.generation

    def stop(self, reason='측정 멈춤'):
        with self._lock:
            self.enabled = False
            if self._measurement is not None and self._measurement['ended'] is None:
                self._measurement.update(ended=time.monotonic(), state='stopped', reason=reason)
                self._measurement['version'] += 1

    def clear(self):
        with self._lock:
            self.enabled = False
            self._measurement = None
            self._definitions.clear()

    def begin(self):
        # All repeated executions and parallel workers join the current measurement.
        with self._lock:
            return self.generation if self.enabled else None

    def register(self, measurement_id, key, name, catalog, *, slot=None):
        with self._lock:
            measurement = self._measurement
            if not self.enabled or measurement_id != self.generation or measurement is None:
                return False
            if slot is not None:
                previous = self._definitions.get(slot)
                if previous is not None and previous != key:
                    self.stop('설정이 변경되어 측정을 멈췄습니다. 다시 시작하세요.')
                    return False
                self._definitions[slot] = key
            if key not in measurement['macros']:
                measurement['macros'][key] = dict(name=name, rows=catalog,
                    counts={row['path']: empty_counts() for row in catalog})
                measurement['version'] += 1
            return True

    def record(self, measurement_id, macro_key, path, stage, **extra):
        with self._lock:
            measurement = self._measurement
            if not self.enabled or measurement_id != self.generation or measurement is None:
                return
            macro = measurement['macros'].get(macro_key)
            path = tuple(path)
            if macro is None or path not in macro['counts']:
                return
            counts = macro['counts'][path]
            status = extra.get('status', stage)
            if stage == 'condition' or 'condition_detail' in extra:
                evidence = extra.get('condition_detail')
                counts['condition_detail'] = (evidence if isinstance(evidence, dict) and evidence.get('state')
                    and extra.get('evidence_generation') == self.generation else None)
            if stage == 'action_start':
                counts['reached'] += 1
            elif stage == 'transition_state':
                counts['transition_state'] = extra['transition_state']
                counts['transition_target'] = extra.get('target', '')
                counts['transition_reason'] = extra.get('reason', '')
            elif stage == 'condition':
                state = (counts['condition_detail'] or {}).get('state')
                if state == 'unavailable':
                    counts['unavailable'] += 1
                    if extra['value']:
                        counts['true'] += 1
                elif state == 'error':
                    counts['errors'] += 1
                elif state != 'disabled':
                    counts['true' if extra['value'] else 'false'] += 1
                if extra.get('elif_branch'):
                    counts['reached'] += 1
                status = ('검사 불가' if state == 'unavailable' else '조건 비활성' if state == 'disabled'
                          else '조건 참' if extra['value'] else '조건 거짓')
            elif stage == 'branch_enter':
                counts['reached'] += 1
            elif stage == 'input':
                counts['inputs'] += 1
            elif stage == 'jump':
                counts['jumps'] += 1
                counts['destination'] = str(extra.get('label', ''))
            elif stage == 'action_end':
                if status in ('disabled', 'skip_once'):
                    counts['skipped'] += 1
                elif status == 'external_unavailable':
                    counts['unavailable'] += 1
                elif status in ('error', 'sound_failed'):
                    counts['errors'] += 1
                else:
                    counts['completed'] += 1
            counts['last'] = status
            measurement['version'] += 1

    def snapshot(self):
        with self._lock:
            return copy.deepcopy(self._measurement)


def row_explanation(row, macro, by_path=None):
    """Explain only facts proved by counters; never invent a cause for zero reach."""
    counts = macro['counts'][row['path']]
    if row['disabled']:
        return '비활성 (부모 포함)'
    if row['kind'] == 'transition':
        from if_transition import TRANSITION_STATES
        state = TRANSITION_STATES.get(counts['transition_state'], counts['transition_state'])
        return state + (f" · {counts['transition_reason']}" if counts['transition_reason'] else '')
    if (counts['condition_detail'] or {}).get('state') == 'disabled':
        return '조건 비활성'
    if counts['skipped'] and not counts['reached']:
        return '1회 실행 제한으로 건너뜀'
    if counts['errors']:
        return f"오류 {counts['errors']:,}회"
    if counts['unavailable']:
        return f"검사 불가 {counts['unavailable']:,}회"
    if not counts['reached'] and (counts['inputs'] or counts['true'] or counts['false'] or counts['completed']):
        return '측정 시작 전부터 실행 중이던 항목'
    if counts['reached']:
        if row['kind'] in ('if', 'elif') and counts['true'] == 0 and counts['false']:
            return '검사했지만 한 번도 참이 아님'
        if counts['jumps']:
            return f"라벨로 복귀/이동 {counts['jumps']:,}회"
        return '실행됨'
    if by_path is None:
        by_path = {r['path']: r for r in macro['rows']}
    parent = by_path.get(row['parent'])
    while parent:
        pc = macro['counts'][parent['path']]
        if parent['kind'] in ('if', 'elif') and row['parent'] == parent['path'] and pc['false'] and not pc['true']:
            # Direct true-branch children only; markers have separate branch rules.
            if row['kind'] not in ('elif', 'else', 'transition'):
                return f"부모 조건 참 0회: {parent['label']}"
        if pc['reached'] == 0:
            return f"부모 미도달: {parent['label']}"
        parent = by_path.get(parent['parent'])
    return '미도달 · 상위 분기와 앞선 액션 확인'


def selection_evidence(row, macro):
    """A short explanation and the proven related rows, independent of Qt."""
    rows = {r['path']: r for r in macro['rows']}
    selected = row['path']
    ancestors = set()
    parent = row['parent']
    while parent is not None:
        ancestors.add(parent)
        parent = rows[parent]['parent']
    descendants = set()
    for candidate in macro['rows']:
        parent = candidate['parent']
        while parent is not None:
            if parent == selected:
                descendants.add(candidate['path'])
                break
            parent = rows[parent]['parent']
    outputs = {p for p in descendants if macro['counts'][p]['reached'] or macro['counts'][p]['inputs']}
    related = {selected} | ancestors | outputs
    # Keep the intermediate branch path to each executed descendant highlighted too.
    for path in outputs:
        parent = rows[path]['parent']
        while parent is not None:
            related.add(parent)
            parent = rows[parent]['parent']
    c = macro['counts'][selected]
    if row['disabled']:
        text = '이 항목 또는 부모가 비활성이라 실행 대상에서 제외됩니다.'
    elif row['kind'] == 'transition':
        target = c['transition_target'] or row.get('target', '전체 IF 결과')
        text = f"감지 대상: {target}\n상태: {row_explanation(row, macro, rows)}"
    elif (c['condition_detail'] or {}).get('state') == 'disabled':
        text = '이 IF의 조건이 비활성이라 검사하지 않았습니다.'
    elif c['skipped'] and not c['reached']:
        text = '1회 실행 제한으로 이번 실행에서는 건너뛰었습니다.'
    elif not c['reached'] and (c['inputs'] or c['true'] or c['false'] or c['completed']):
        text = (f"측정 시작 전부터 실행 중이던 항목입니다. 측정 구간 내 입력 전송 {c['inputs']:,}회 · "
                f"조건 참 {c['true']:,}회 / 거짓 {c['false']:,}회.")
    elif not c['reached']:
        text = '이 항목에는 한 번도 도달하지 않았습니다. ' + row_explanation(row, macro, rows) + '.'
    elif row['kind'] in ('if', 'elif'):
        tested = c['true'] + c['false']
        text = f"{c['reached']:,}회 도달 · 조건 판단 {tested:,}회 중 참 {c['true']:,}회 / 거짓 {c['false']:,}회."
        if c['false'] and not c['true']:
            text += ' 참 분기에는 한 번도 진입하지 않았습니다.'
        elif not tested:
            text += (' 검사 불가 항목이 있어 참·거짓 횟수에서 제외했습니다.' if c['unavailable']
                     else ' 판단 결과가 아직 없으므로 최근 결과를 확인하세요.')
        inputs = sum(macro['counts'][p]['inputs'] for p in descendants)
        text += f' 하위 액션의 입력 전송은 총 {inputs:,}회입니다.'
    else:
        text = f"측정 구간 동안 {c['reached']:,}회 도달했습니다."
        if row['kind'] in ('press', 'down', 'up', 'mouse_click', 'mouse_down', 'mouse_up', 'mouse_wheel'):
            text += f" 입력 전송 성공 {c['inputs']:,}회."
    if c['jumps']:
        text += f" 라벨 {c['destination']}로 {c['jumps']:,}회 이동했습니다."
    if c['errors']:
        text += f" 오류 {c['errors']:,}회."
    if c['unavailable']:
        text += f" 검사 불가 {c['unavailable']:,}회."
    return text, related, outputs
