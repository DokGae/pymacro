"""Session-only IF overrides and entry paths; never serialized into profiles."""
import json
import threading
from collections import deque


def signature(action):
    data = action.to_dict()
    for key in ('actions', 'else_actions', 'elif_blocks', 'transition_actions',
                'transition_target_key', 'transition_target_label'):
        data.pop(key, None)
    return json.dumps(data, sort_keys=True, ensure_ascii=False)


class IfTestState:
    def __init__(self):
        self.lock = threading.RLock()
        self.overrides = {}
        self.progress = {}
        self.events = {}

    def set(self, index, stop, path, action, mode):
        if mode not in ('actual', 'once', 'always'):
            raise ValueError('Unknown IF test mode')
        key = (index, bool(stop), tuple(path))
        with self.lock:
            if mode == 'actual':
                self.overrides.pop(key, None)
            else:
                self.overrides[key] = (signature(action), mode)

    def mode(self, index, stop, path, action=None, *, consume=False):
        key = (index, bool(stop), tuple(path))
        with self.lock:
            entry = self.overrides.get(key)
            if entry is None:
                return 'actual'
            if action is not None and entry[0] != signature(action):
                return 'actual'
            if consume and entry[1] == 'once':
                self.overrides.pop(key, None)
            return entry[1]

    def clear(self, index=None):
        with self.lock:
            if index is None:
                self.overrides.clear()
                self.progress.clear()
                self.events.clear()
            else:
                self.overrides = {k: v for k, v in self.overrides.items() if k[0] != index}
                self.progress.pop(index, None)
                self.events.pop(index, None)

    def finish(self, index):
        with self.lock:
            self.overrides = {k: v for k, v in self.overrides.items() if k[0] != index}
            self.progress.pop(index, None)
            if index in self.events:
                self.events[index].append('실행 종료 · 강제 판정 해제')

    def reconcile(self, profile):
        """Keep pending tests only when their exact action still exists."""
        with self.lock:
            for key, (expected, _) in list(self.overrides.items()):
                index, stop, path = key
                try:
                    macro = profile.macros[index]
                    actions, position, _ = locate(macro.stop_actions if stop else macro.actions, path)
                    matches = signature(actions[position]) == expected
                except (IndexError, ValueError):
                    matches = False
                if not matches:
                    self.overrides.pop(key, None)

    def record(self, index, stop, path, stage, label, status=''):
        with self.lock:
            self.progress[index] = (bool(stop), tuple(path), stage, label)
            if stage == 'action_start':
                self.events.setdefault(index, deque(maxlen=100)).append('▶ ' + label)
            elif status in ('error', 'disabled', 'skip_once', 'external_unavailable'):
                reason = {'error': '오류', 'disabled': '사용 꺼짐', 'skip_once': '첫 사이클 이후 건너뜀',
                          'external_unavailable': '외부 상태 확인 불가'}[status]
                self.events.setdefault(index, deque(maxlen=100)).append(label + ' · ' + reason)

    def note(self, index, message):
        with self.lock:
            self.events.setdefault(index, deque(maxlen=100)).append(message)

    def history(self, index):
        with self.lock:
            return list(self.events.get(index, ()))

    def current(self, index):
        with self.lock:
            return self.progress.get(index)


def child_lists(action):
    """Branches with the same offsets as MacroRunner's execution paths."""
    from engine import _iter_elif_blocks
    offset = 0
    yield offset, action.actions
    offset += len(action.actions)
    if action.type == 'if':
        for _, children, _ in _iter_elif_blocks(action.elif_blocks):
            yield offset, children
            offset += len(children)
        yield offset, action.else_actions
        offset += len(action.else_actions)
        yield offset, action.transition_actions


def locate(actions, path):
    """Return (containing list, local index, offset) for a runner path."""
    if not path or any(type(i) is not int or i < 0 for i in path):
        raise ValueError('실행할 IF 위치가 올바르지 않습니다.')
    offset = 0
    for depth, position in enumerate(path):
        local = position - offset
        if not 0 <= local < len(actions):
            raise ValueError('액션 위치가 변경되었습니다. 설정창을 다시 열어 주세요.')
        if depth == len(path) - 1:
            return actions, local, offset
        action = actions[local]
        next_position = path[depth + 1]
        for offset, children in child_lists(action):
            if offset <= next_position < offset + len(children):
                actions = children
                break
        else:
            raise ValueError('실행할 하위 IF를 찾을 수 없습니다.')


def entry_index(runner, prefix, offset=0):
    entry = getattr(runner, '_if_test_entry', None)
    if entry and len(entry) > len(prefix) and entry[:len(prefix)] == tuple(prefix):
        return entry[len(prefix)] - offset
    return None


def run_from_path(runner, actions, entry, labels, *, path=None):
    """Consume the entry once; retain ordinary group, repeat and jump rules."""
    locate(actions, entry)
    runner._if_test_entry = tuple(entry)
    try:
        return runner._run_actions(actions, labels, root=True, path=path)
    finally:
        runner._if_test_entry = None
