# GUI 매크로 설계 메모 (다음 세션 작업 지침)

## 목표
- Interception 기반 키/마우스 매크로 엔진 + PyQt6 GUI 한 번에 구성.
- 조건: 키 상태, 픽셀 색상 매칭(범위+허용오차).
- 액션: 키 press/down/up, sleep (추후 마우스, 클릭 추가 가능).
- 글로벌 키: Home(활성화), Insert(일시정지), End/ESC(종료), PageUp(픽셀 테스트).

## 작업 순서
1) **키 헬퍼 보강**
   - `lib/keyboard.py`: `get_keystate(key, async_=True)` 추가. (MapVk + is_key_pressed 사용)
2) **픽셀 헬퍼 신규**
   - `lib/pixel.py`: `capture_region(region) -> Image`, `find_color_in_region(region, rgb, tolerance) -> (found, coord|None)`.
   - 구현은 `mss` 우선; 불가 시 `PIL.ImageGrab`.
   - 좌표계: (x, y, w, h), 다중 모니터 음수 좌표 고려.
3) **엔진(콘솔 루프)**
   - `engine.py` 또는 `macro/engine.py`:
     - 상태: `running`, `active`, `paused`.
     - 루프 틱: 10~20ms.
     - 키 토글: Home→active=True, Insert→paused toggle, End/ESC→running=False.
     - 조건→액션 실행: 조건 히트 시 액션 리스트 수행, 조건별 쿨다운(ms) 필드.
4) **PyQt6 GUI**
   - 메인 UI:
     - 상태 패널: 활성/일시정지 표시.
     - 조건 리스트: 타입(Key/Pixel), 파라미터, 허용오차, 쿨다운.
     - 액션 리스트: Press/Down/Up/Sleep.
     - 프로필 저장/로드(JSON).
     - 로그 패널: 조건 히트/액션 실행 기록.
   - 픽셀 테스트:
     - 범위 입력(또는 드래그 선택 가능하면 추가), RGB+허용오차 입력.
     - PageUp 핫키 → 현재 설정으로 `find_color_in_region` 실행 → 메시지박스 “찾음/없음” + 좌표 표시.
5) **통합**
   - GUI 스레드 + 백그라운드 엔진 스레드(조건 평가/액션 실행).
   - 스레드 안전: 큐 또는 이벤트로 상태 전달; GUI는 주기적으로 상태 폴링/신호 처리.

## 데이터 모델 (초안)
- Condition:
  - type: `"key"` | `"pixel"`
  - params:
    - key: `"z"` 등
    - region: (x, y, w, h), color: (r,g,b), tolerance: int
  - cooldown_ms: int
- Action:
  - type: `"press"` | `"down"` | `"up"` | `"sleep"`
  - key: `"r"` 등, sleep_ms: int
- MacroProfile: { conditions: [Condition], actions: [Action] }

## 키 바인딩
- Home: 활성화
- Insert: 일시정지/재개
- End/ESC: 종료
- PageUp: 픽셀 테스트 실행

## 나중 옵션(시간 되면)
- 마우스 클릭/이동 액션 추가
- 픽셀 “픽커” (스크린 캡처에서 클릭해 RGB/좌표 채우기)
- 조건/액션 재정렬(위/아래 버튼)
- 다국어 메시지 리소스 분리
