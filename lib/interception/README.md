# Interception 매뉴얼 (로컬 번들)

이 폴더에는 Interception 드라이버용 파이썬 바인딩을 로컬로 들고 있습니다. 키/마우스 입력을 커널 레벨에서 가로채거나 전송할 수 있습니다.

## 준비물
- **드라이버 설치(필수)**: 관리자 PowerShell/명령 프롬프트에서 `D:\Programing\Python\자료저장\마우스키보드\Interception\command line installer\install-interception.exe` 를 실행해 설치합니다. 설치/제거 모두 관리자 권한이 필요하며, 설치 후 재부팅이 필요할 수 있습니다.
- **DLL 불필요**: 여기서는 `Python-Interception-Driver`의 순수 파이썬 바인딩만 사용합니다. 별도 `Interception.dll` 복사 없이 드라이버만 설치되어 있으면 됩니다.

## 주요 객체
- `Interception`: 드라이버와 통신하는 컨텍스트. 장치 리스트를 만들고 이벤트를 기다립니다.
- `Device`: `wait_receive()`로 얻는 장치 핸들. `device.stroke`에 최근 이벤트가 들어 있으며, `device.send()`로 원본/수정 이벤트를 다시 내보냅니다.
- `KeyFilter`, `MouseFilter`: 어떤 이벤트를 받을지 필터. 예) `KeyFilter.All`, `KeyFilter.Down | KeyFilter.Up`.
- `Vk`, `MapVk`, `map_virtual_key`: 가상키 ↔ 스캔코드 변환용.
- `KeyState`: 키 상태 (`Down`, `Up`).

## 기본 흐름 (키보드)
```python
from lib.interception import Interception, KeyFilter, KeyState, MapVk, Vk, map_virtual_key

inter = Interception()
inter.set_keyboard_filter(KeyFilter.All)

z_sc = map_virtual_key(Vk.Z, MapVk.VkToSc)

while True:
    device = inter.wait_receive()      # 장치 이벤트 대기
    if not device:
        continue

    stroke = device.stroke             # KeyStroke 구조체
    device.send()                      # 원본 이벤트를 시스템에 전달

    is_down = stroke.state == KeyState.Down
    if stroke.code == z_sc and is_down:
        # 원하는 동작 수행
        ...
```

## 키 전송 예시
```python
from lib.interception import KeyState, MapVk, Vk, map_virtual_key

def send_key(device, vk, *, info=0):
    sc = map_virtual_key(vk, MapVk.VkToSc)
    ks = device.stroke.__class__()  # KeyStroke 생성
    ks.code = sc
    ks.state = KeyState.Down
    ks.info = info
    device.send(ks)
    ks.state = KeyState.Up
    device.send(ks)
```

## 주의사항
- 관리자 권한이 필요합니다. 드라이버가 미설치되었거나 권한이 없으면 장치를 열지 못합니다.
- 일부 게임/안티치트/보안 도구가 차단할 수 있습니다.
- 필터를 설정했으면, `device.send()`로 원본 이벤트를 다시 내보내야 입력이 정상 전달됩니다.

## 키보드 헬퍼 (`lib/keyboard.py`)
- `key("r")` 또는 `key(Vk.R)`: 키 눌렀다 떼기
- `key("r", "down")` / `key("r", "up")`: 다운/업만 전송
- 별도 디바이스를 지정하지 않으면 첫 번째 키보드 장치로 전송합니다.
- 관리자 권한 + 드라이버 설치가 여전히 필요합니다.
- `listen_and_press("z", "r", exit_key="esc")`: z를 누르면 r을 한 번 전송, esc로 종료하는 간단 리스너.
- `listen(trigger, callback)`: 트리거 키(Down)와 콜백을 등록. 콜백 시그니처 `callback(device, stroke)`.
- `run_listeners(exit_keys=("esc",))`: 등록된 listen 매핑을 실행하는 메인 루프. exit_keys 누르면 종료.
