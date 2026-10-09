"""Local, newline-delimited JSON snapshots for cooperating programs."""
import json
import select
import socket
import threading
import uuid

PROTOCOL = 'external-state-v1'
DEFAULT_PORT = 47653
MAX_FRAME = 1_000_000


def hp_settings(settings):
    name=settings.get('tcp_hp_name','내HP').strip()
    if not name or len(name)>120 or any(ord(c)<32 for c in name):
        raise ValueError('HP 내용 이름은 1~120자 한 줄로 입력하세요.')
    if name in ('게임연결','내캐릭터','대상이름','대상감지'):
        raise ValueError('HP 내용 이름이 기본 상태 이름과 겹칩니다.')
    return dict(tcp_hp_enabled=bool(settings.get('tcp_hp_enabled',True)),tcp_hp_name=name)


def monitor_snapshot(states, catalog, connected=True, observed_keys=None, settings=None):
    values = {'게임연결': bool(connected)}
    false_prefixes = []
    unavailable_prefixes = []
    items = {}
    unavailable_keys=[]
    role_states={}
    for prefix, key in (('내효과.', states.owner_key), ('대상효과.', states.attack_target_key)):
        actor = states.actors.get(key) if connected else None
        known = actor is not None and (actor.effects_at is not None or bool(actor.effects))
        if observed_keys is not None and key not in observed_keys: known = False
        role_states['own' if prefix=='내효과.' else 'target']=(actor,known)
        unavailable_prefixes.append(prefix)
    for code,config in catalog.preview.items():
        if code.startswith('attack:'):continue
        for roles,name,on,off in catalog.tcp_channels(code,config):
            items[name]=catalog.name(code)
            selected=[role_states[role] for role in roles]
            active=any(known and any(str(effect['code'])==code for effect in actor.effects.values()) for actor,known in selected)
            if not config.get('tcp_enabled',False) or not active and not all(known for _,known in selected):
                unavailable_keys.append(name)
            else:
                values[name]=catalog.tcp_value(on if active else off)
        for prefix in ('내효과.','대상효과.'):
            if prefix+code not in values:unavailable_keys.append(prefix+code)
    owner = states.actors.get(states.owner_key) if connected else None
    target = states.actors.get(states.attack_target_key) if connected else None
    values.update(내캐릭터=owner.nickname if owner else '', 대상이름=target.nickname if target else '',
                  대상감지=target is not None)
    if settings is not None:
        config=hp_settings(settings);name=config['tcp_hp_name']
        collision=name in items or name in values or name in unavailable_keys
        items[name]='내 HP (%)'
        if collision or not config['tcp_hp_enabled']:
            values.pop(name,None);unavailable_keys.append(name)
        else:
            values[name]=round(max(0,min(100,owner.hp/owner.max_hp*100)),2) if owner and owner.hp is not None and owner.max_hp is not None and owner.max_hp>0 else False
    return dict(values=values, items=items, false_prefixes=false_prefixes,
                unavailable_prefixes=unavailable_prefixes,unavailable_keys=sorted(set(unavailable_keys)))


class StateServer:
    """Latest snapshots only; socket I/O never blocks the GUI thread."""
    def __init__(self, port=DEFAULT_PORT, source='leesangjin-monitor'):
        if not isinstance(source,str) or not source.strip() or len(source)>200 or any(ord(c)<32 for c in source):
            raise ValueError('프로그램 ID는 1~200자 한 줄로 입력하세요.')
        self.source=source.strip()
        self.port = port
        self.session = uuid.uuid4().hex
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread = None
        self._frame = b''
        self._revision = 0
        self._status = 'TCP 연결 대기'
        self.bound_port = None

    @property
    def status(self):
        with self._lock: return self._status

    def _set_status(self, value):
        with self._lock: self._status = value

    def publish(self, snapshot):
        with self._lock:
            revision = self._revision + 1
            message = dict(snapshot, protocol=PROTOCOL, source=self.source,
                           name='작은 모니터', session=self.session, sequence=revision)
            frame = (json.dumps(message, ensure_ascii=False, separators=(',', ':'), allow_nan=False) + '\n').encode('utf-8')
            if len(frame) > MAX_FRAME: raise ValueError('TCP 상태 데이터가 너무 큽니다.')
            self._frame = frame; self._revision = revision

    def start(self):
        if self._thread and self._thread.is_alive(): return
        self._stop.clear()
        self._thread = threading.Thread(target=self._run, name='monitor-state-tcp', daemon=True)
        self._thread.start()

    def stop(self):
        self._stop.set()
        if self._thread: self._thread.join(2)
        self._set_status('TCP 중지')

    def _run(self):
        while not self._stop.is_set():
            listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            clients = {}
            try:
                # Windows must not allow a second server to steal the same port.
                if hasattr(socket, 'SO_EXCLUSIVEADDRUSE'):
                    listener.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
                else:
                    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                listener.bind(('127.0.0.1', self.port)); listener.listen(8); listener.setblocking(False)
                self.bound_port = listener.getsockname()[1]
                while not self._stop.is_set():
                    with self._lock: frame, revision = self._frame, self._revision
                    for client, state in list(clients.items()):
                        if state[0] != revision:
                            if state[1]:
                                # A slow reader must not accumulate stale snapshots.
                                client.close(); clients.pop(client); continue
                            state[:] = [revision, frame]
                    readable, writable, _ = select.select([listener, *clients],
                        [c for c, state in clients.items() if state[1]], [], .05)
                    if listener in readable:
                        client, _ = listener.accept(); client.setblocking(False)
                        if len(clients) < 16: clients[client] = [-1, b'']
                        else: client.close()
                    for client in readable:
                        if client is listener or client not in clients: continue
                        try:
                            # This protocol is one-way; any input or EOF closes a peer.
                            client.recv(1)
                        except BlockingIOError: continue
                        except OSError: pass
                        client.close(); clients.pop(client, None)
                    for client in writable:
                        if client not in clients: continue
                        try:
                            sent = client.send(clients[client][1])
                            if not sent: raise OSError('closed')
                            clients[client][1] = clients[client][1][sent:]
                        except BlockingIOError: pass
                        except OSError:
                            client.close(); clients.pop(client, None)
                    self._set_status(f'TCP 연결 정상 · 127.0.0.1:{self.bound_port} · ' +
                                     (f'외부 프로그램 연결 {len(clients)}개' if clients else '외부 프로그램 접속 대기'))
            except OSError as exc:
                if getattr(exc,'winerror',None)==10048 or exc.errno in (98,10048):
                    self._set_status(f'TCP 연결 실패 · 포트 {self.port}를 다른 프로그램이 사용 중입니다. '
                                     '모니터를 중복 실행했다면 하나를 종료하세요. 여러 개 사용하려면 서로 다른 포트를 설정하세요.')
                elif getattr(exc,'winerror',None)==10013:
                    self._set_status(f'TCP 연결 실패 · 포트 {self.port}를 다른 프로그램이 사용 중이거나 Windows에서 사용을 제한했습니다. '
                                     '모니터 중복 실행을 확인하거나 다른 포트를 설정하세요.')
                else:self._set_status(f'TCP 연결 실패 (포트 {self.port}): {exc}')
            finally:
                for client in clients: client.close()
                listener.close(); self.bound_port = None
            self._stop.wait(1)
