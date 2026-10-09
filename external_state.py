"""Generic local TCP state receiver. One connection is shared by all IF checks."""
import atexit
import json
import math
import socket
import threading
import time

PROTOCOL = 'external-state-v1'
DEFAULT_PORT = 47653
MAX_FRAME = 1_000_000
STALE_SECONDS = 3.0


def parse_value(text):
    text = str(text).strip()
    aliases = {'참': True, '거짓': False, 'true': True, 'false': False}
    if text.lower() in aliases: return aliases[text.lower()]
    try:
        value = json.loads(text)
    except ValueError:
        return text
    if not isinstance(value, (str, bool, int, float)) or isinstance(value, float) and not math.isfinite(value):
        raise ValueError('비교값은 참/거짓, 숫자 또는 문자열이어야 합니다.')
    return value


def validate_message(data):
    if not isinstance(data, dict) or data.get('protocol') != PROTOCOL:
        raise ValueError('지원하지 않는 TCP 상태 형식')
    for key in ('source', 'session'):
        if not isinstance(data.get(key), str) or not data[key] or len(data[key]) > 200:
            raise ValueError('프로그램 식별 정보 오류')
    if type(data.get('sequence')) is not int or data['sequence'] < 0:
        raise ValueError('상태 순서 오류')
    values = data.get('values')
    if not isinstance(values, dict) or len(values) > 20000:
        raise ValueError('상태 항목 오류')
    for key, value in values.items():
        if not isinstance(key, str) or not key or len(key) > 300:
            raise ValueError('상태 항목 이름 오류')
        if not isinstance(value, (str, bool, int, float)) or isinstance(value, float) and not math.isfinite(value):
            raise ValueError('상태 값 오류')
    for field in ('false_prefixes', 'unavailable_prefixes'):
        prefixes = data.get(field, [])
        if not isinstance(prefixes, list) or len(prefixes) > 100 or any(
                not isinstance(p, str) or not p or len(p) > 200 for p in prefixes):
            raise ValueError('상태 범위 오류')
    items = data.get('items', {})
    unavailable_keys=data.get('unavailable_keys',[])
    if not isinstance(unavailable_keys,list) or len(unavailable_keys)>20000 or any(
            not isinstance(k,str) or not k or len(k)>300 for k in unavailable_keys):
        raise ValueError('통신 해제 항목 오류')
    if not isinstance(items, dict) or len(items) > 20000 or any(
            not isinstance(k, str) or not isinstance(v, str) or len(k) > 300 or len(v) > 300
            for k, v in items.items()):
        raise ValueError('항목 설명 오류')
    return data


class StateClient:
    def __init__(self, host='127.0.0.1', port=DEFAULT_PORT, *, stale_seconds=STALE_SECONDS, retry_seconds=1.0):
        if host not in ('127.0.0.1', 'localhost'): raise ValueError('같은 PC의 127.0.0.1 주소만 지원합니다.')
        if type(port) is not int or not 1 <= port <= 65535: raise ValueError('TCP 포트는 1~65535입니다.')
        self.host = '127.0.0.1'; self.port = port
        self.stale_seconds = stale_seconds; self.retry_seconds = retry_seconds
        self._lock = threading.Lock(); self._stop = threading.Event()
        self._data = None; self._received_at = 0; self._status = '연결 대기'
        self._thread = None; self._socket = None

    def start(self):
        if self._thread and self._thread.is_alive(): return
        self._stop.clear()
        self._thread = threading.Thread(target=self._run, name=f'external-state-{self.port}', daemon=True)
        self._thread.start()

    def close(self):
        self._stop.set()
        with self._lock: peer = self._socket
        if peer is not None:
            try: peer.shutdown(socket.SHUT_RDWR)
            except OSError: pass
        if self._thread: self._thread.join(2)
        self._invalidate('연결 중지')

    def _invalidate(self, status):
        with self._lock:
            self._data = None; self._received_at = 0; self._status = status

    def snapshot(self, source):
        with self._lock:
            data = self._data
            if data is None: return None, self._status
            if time.monotonic() - self._received_at > self.stale_seconds:
                return None, '상태 수신 시간 초과 · 재연결 대기'
            if data['source'] != source:
                return None, f"다른 프로그램 연결됨: {data['source']}"
            return data, '연결됨'

    def lookup(self, source, key):
        data, status = self.snapshot(source)
        if data is None: return False, None, status
        if key in data.get('unavailable_keys',[]):
            return False,None,'통신 전송 해제 또는 효과 감지 대기 중입니다.'
        if key in data['values']: return True, data['values'][key], status
        if any(key.startswith(p) for p in data.get('unavailable_prefixes', [])):
            return False, None, '감지 대기 · 이 항목은 아직 확인되지 않았습니다.'
        if any(key.startswith(p) for p in data.get('false_prefixes', [])):
            return True, False, status
        return False, None, '아직 수신하지 않은 항목'

    def _run(self):
        while not self._stop.is_set():
            peer = None
            try:
                peer = socket.create_connection((self.host, self.port), timeout=.5)
                peer.settimeout(min(self.stale_seconds, .5))
                with self._lock: self._socket = peer
                self._invalidate('TCP 연결됨 · 첫 상태 수신 대기')
                buffer = b''; last_data = time.monotonic(); previous = None
                while not self._stop.is_set():
                    try: chunk = peer.recv(65536)
                    except socket.timeout:
                        if time.monotonic() - last_data >= self.stale_seconds:
                            raise OSError('상태 수신 시간 초과')
                        continue
                    if not chunk: raise OSError('상대 프로그램 종료')
                    buffer += chunk
                    while b'\n' in buffer:
                        line, buffer = buffer.split(b'\n', 1)
                        if not line or len(line) > MAX_FRAME: raise ValueError('TCP 메시지 크기 오류')
                        data = validate_message(json.loads(line.decode('utf-8')))
                        identity = (data['source'], data['session'])
                        if previous and (identity != previous[0] or data['sequence'] <= previous[1]):
                            raise ValueError('TCP 상태 순서 또는 프로그램 식별 변경')
                        previous = (identity, data['sequence'])
                        last_data = time.monotonic()
                        with self._lock:
                            self._data = data; self._received_at = last_data; self._status = '연결됨'
                    if len(buffer) > MAX_FRAME: raise ValueError('TCP 메시지 크기 초과')
            except (OSError, ValueError, UnicodeError) as exc:
                self._invalidate(f'연결 대기 · {exc}')
            finally:
                if peer is not None: peer.close()
                with self._lock: self._socket = None
            self._stop.wait(self.retry_seconds)


class StateHub:
    def __init__(self):
        self._lock = threading.Lock(); self._clients = {}

    def client(self, host, port):
        key = ('127.0.0.1' if host == 'localhost' else host, port)
        with self._lock:
            if key not in self._clients:
                if len(self._clients) >= 16: raise ValueError('동시 TCP 연결은 16개까지 지원합니다.')
                client = StateClient(*key); self._clients[key] = client; client.start()
            return self._clients[key]

    def evaluate(self, cond):
        try:
            client = self.client(cond.external_host, cond.external_port)
            data, connection_status = client.snapshot(cond.external_source)
            available, actual, status = client.lookup(cond.external_source, cond.external_key)
            detail = dict(source=cond.external_source, key=cond.external_key, actual=actual,
                          operator=cond.external_operator, status=status, unavailable=not available,
                          connected=data is not None, connection_status=connection_status,
                          host=cond.external_host, port=cond.external_port)
            if not available: return False, detail
            op = cond.external_operator
            if op in ('true', 'false'):
                result = type(actual) is bool and actual is (op == 'true')
            else:
                expected = parse_value(cond.external_value)
                detail['expected'] = expected
                numeric = type(actual) in (int, float) and type(expected) in (int, float)
                equal = actual == expected and (numeric or type(actual) is type(expected))
                if op == 'eq': result = equal
                elif op == 'ne': result = not equal
                elif numeric:
                    result = {'gt': actual > expected, 'ge': actual >= expected,
                              'lt': actual < expected, 'le': actual <= expected}.get(op, False)
                else: result = False
            return result, detail
        except (ValueError, TypeError) as exc:
            return False, dict(unavailable=True, connected=False, connection_status=str(exc), status=str(exc))

    def connect_profile(self, profile):
        """Warm saved endpoints on profile load, before any macro is run."""
        def visit(node):
            if isinstance(node, dict):
                for value in node.values(): visit(value)
            elif isinstance(node, (list, tuple)):
                for value in node: visit(value)
            elif hasattr(node, '__dict__'):
                if getattr(node, 'type', None) == 'external':
                    try: self.client(node.external_host, node.external_port)
                    except ValueError: pass
                for field in ('macros','actions','stop_actions','else_actions','elif_blocks',
                              'condition','conditions','on_true','on_false'):
                    value = getattr(node, field, None)
                    if value is not None: visit(value)
        visit(profile)

    def close(self):
        with self._lock: clients = list(self._clients.values()); self._clients.clear()
        for client in clients: client.close()


state_hub = StateHub()
atexit.register(state_hub.close)


def external_result(cond, cache=None):
    key = ('external', id(cond))
    if cache is not None and key in cache: return cache[key]
    result = state_hub.evaluate(cond)
    if cache is not None: cache[key] = result
    return result


def external_conditions_ready(cond, cache=None):
    if not getattr(cond, 'enabled', True): return True
    if cond.type == 'external' and external_result(cond, cache)[1].get('unavailable'):
        return False
    children = list(cond.conditions or []) if cond.type in ('all','any') else []
    children += list(cond.on_true or []) + list(cond.on_false or [])
    return all(external_conditions_ready(child, cache) for child in children)
