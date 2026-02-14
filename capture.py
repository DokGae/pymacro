from __future__ import annotations

import json
import queue
import threading
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Callable, Optional

import mss
import mss.tools
from PIL import Image

try:
    # lib.keyboard는 Interception 기반 키 조회를 제공한다.
    from lib.keyboard import get_keystate
except Exception:  # pragma: no cover - GUI/핫키 없는 환경 대비
    get_keystate = None  # type: ignore

# 기본 캡처 주기(초). GUI에서 덮어쓸 수 있다.
CAPTURE_INTERVAL_SECONDS = 0.01
MIN_INTERVAL_SECONDS = 0.0005

# 이미지 포맷/품질 설정
DEFAULT_FORMAT = "jpeg"  # "jpeg" 또는 "png"
DEFAULT_JPEG_QUALITY = 80
DEFAULT_PNG_COMPRESS_LEVEL = 6  # 0(빠름, 큼)~9(느림, 작음)

# 디스크 쓰기 병목을 줄이기 위한 프레임 버퍼 크기
MAX_QUEUE_SIZE = 120  # 프레임 개수

# 스크린샷 저장 폴더
SCREENSHOT_DIR = Path(__file__).parent / "screenshot"


def _ensure_dir(path: Path) -> Path:
    path.mkdir(parents=True, exist_ok=True)
    return path


@dataclass
class HotkeyConfig:
    start: Optional[str] = None
    stop: Optional[str] = None
    capture: Optional[str] = None  # 단일 캡처
    enabled: bool = False


class ScreenCaptureManager:
    """
    전체 화면을 주기적으로 캡처하는 간단한 매니저.
    - start/stop 메서드로 직접 제어
    - 필요 시 전역 핫키(폴링 기반)로 시작/정지 트리거
    """

    def __init__(
        self,
        *,
        output_dir: Path | str = SCREENSHOT_DIR,
        interval_seconds: float = CAPTURE_INTERVAL_SECONDS,
        hotkeys: Optional[HotkeyConfig] = None,
        image_format: str = DEFAULT_FORMAT,
        jpeg_quality: int = DEFAULT_JPEG_QUALITY,
        png_compress_level: int = DEFAULT_PNG_COMPRESS_LEVEL,
        max_queue_size: int = MAX_QUEUE_SIZE,
    ):
        self.output_dir = Path(output_dir)
        self.interval = max(float(interval_seconds), MIN_INTERVAL_SECONDS)
        self.hotkeys = hotkeys or HotkeyConfig()
        self.image_format = image_format.lower() if image_format else DEFAULT_FORMAT
        self.jpeg_quality = int(jpeg_quality)
        self.png_compress_level = int(png_compress_level)
        self.max_queue_size = max(1, int(max_queue_size))

        self._capture_stop = threading.Event()
        self._writer_stop = threading.Event()
        self._hotkey_stop = threading.Event()
        self._queue: queue.Queue[tuple[int, str, bytes, tuple[int, int]]] = queue.Queue(maxsize=self.max_queue_size)
        self._capture_thread: Optional[threading.Thread] = None
        self._writer_thread: Optional[threading.Thread] = None
        self._hotkey_thread: Optional[threading.Thread] = None
        self._lock = threading.Lock()
        self._seq = 0
        self._capture_listeners: list[Callable[[Path], None]] = []

    # ---------------------- 캡처 루프 ----------------------
    def _capture_loop(self):
        _ensure_dir(self.output_dir)
        next_at = time.perf_counter()
        with mss.mss() as sct:
            monitor = sct.monitors[0]  # 모든 모니터 영역
            while not self._capture_stop.is_set():
                now = time.perf_counter()
                if now < next_at:
                    time.sleep(next_at - now)
                else:
                    next_at = now

                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
                self._seq += 1
                shot = sct.grab(monitor)
                # shot.rgb와 shot.size를 버퍼에 넣고, 파일 쓰기는 별도 스레드에서 처리
                self._enqueue_frame((self._seq, timestamp, shot.rgb, shot.size))

                next_at += self.interval

    def _writer_loop(self):
        _ensure_dir(self.output_dir)
        while not (self._writer_stop.is_set() and self._queue.empty()):
            try:
                seq, ts, rgb, size = self._queue.get(timeout=0.05)
            except queue.Empty:
                continue

            ext = "png" if self.image_format == "png" else "jpg"
            filename = f"{seq:06d}_{ts}.{ext}"
            output_path = self.output_dir / filename

            if self.image_format == "png":
                mss.tools.to_png(rgb, size, output=str(output_path), level=self.png_compress_level)
            else:
                img = Image.frombytes("RGB", size, rgb)
                img.save(
                    output_path,
                    format="JPEG",
                    quality=self.jpeg_quality,
                    optimize=True,
                    subsampling=1,
                )

    def _enqueue_frame(self, frame: tuple[int, str, bytes, tuple[int, int]]):
        try:
            self._queue.put_nowait(frame)
        except queue.Full:
            try:
                _ = self._queue.get_nowait()  # 가장 오래된 프레임 제거
            except queue.Empty:
                pass
            try:
                self._queue.put_nowait(frame)
            except queue.Full:
                pass  # 버퍼가 꽉 찼으면 프레임을 드롭

    def start(self, *, interval_seconds: Optional[float] = None, reset_counter: bool = True) -> bool:
        """
        캡처를 시작. 이미 동작 중이면 False, 새로 시작하면 True.
        """
        with self._lock:
            if self.is_running:
                return False
            if reset_counter:
                self._seq = 0

            if interval_seconds is not None:
                self.interval = max(float(interval_seconds), MIN_INTERVAL_SECONDS)

            self._capture_stop.clear()
            self._writer_stop.clear()
            self._queue = queue.Queue(maxsize=self.max_queue_size)
            self._writer_thread = threading.Thread(target=self._writer_loop, daemon=True)
            self._writer_thread.start()
            self._capture_thread = threading.Thread(target=self._capture_loop, daemon=True)
            self._capture_thread.start()
            return True

    def stop(self) -> bool:
        """
        캡처를 중단. 이미 중지 상태면 False, 실제로 중단하면 True.
        """
        with self._lock:
            if not self.is_running:
                return False
            self._capture_stop.set()
            if self._capture_thread:
                self._capture_thread.join()
            self._capture_thread = None

            self._writer_stop.set()
            if self._writer_thread:
                self._writer_thread.join()
            self._writer_thread = None
            return True

    @property
    def is_running(self) -> bool:
        return bool(self._capture_thread and self._capture_thread.is_alive())

    # ---------------------- 핫키 ----------------------
    def configure_hotkeys(self, start: Optional[str], stop: Optional[str], capture: Optional[str], *, enabled: bool):
        has_keys = bool(start or stop or capture)
        effective_enabled = bool(enabled and has_keys)
        self.hotkeys = HotkeyConfig(start=start or None, stop=stop or None, capture=capture or None, enabled=effective_enabled)
        if self.hotkeys.enabled:
            self._start_hotkey_listener()
        else:
            self._stop_hotkey_listener()

    def add_capture_listener(self, callback: Callable[[Path], None]):
        if not callable(callback):
            return
        with self._lock:
            if callback not in self._capture_listeners:
                self._capture_listeners.append(callback)

    def remove_capture_listener(self, callback: Callable[[Path], None]):
        with self._lock:
            try:
                self._capture_listeners.remove(callback)
            except ValueError:
                pass

    def _notify_single_capture(self, path: Path):
        listeners: list[Callable[[Path], None]]
        with self._lock:
            listeners = list(self._capture_listeners)
        for cb in listeners:
            try:
                cb(path)
            except Exception:
                pass

    def _start_hotkey_listener(self):
        if self._hotkey_thread and self._hotkey_thread.is_alive():
            return
        self._hotkey_stop.clear()
        self._hotkey_thread = threading.Thread(target=self._hotkey_loop, daemon=True)
        self._hotkey_thread.start()

    def _stop_hotkey_listener(self):
        self._hotkey_stop.set()
        if self._hotkey_thread:
            self._hotkey_thread.join()
        self._hotkey_thread = None

    def _hotkey_loop(self):
        # 폴링 기반이므로 너무 짧게 잡지 않는다.
        poll_interval = 0.01
        # 리스너 시작 시점에 이미 눌려 있던 키로 오동작(즉시 시작/정지)하지 않도록
        # 초기 상태를 먼저 읽어 기준값으로 둔다.
        last_start = self._safe_pressed(self.hotkeys.start) if (self.hotkeys.start and get_keystate) else False
        last_stop = self._safe_pressed(self.hotkeys.stop) if (self.hotkeys.stop and get_keystate) else False
        last_capture = self._safe_pressed(self.hotkeys.capture) if (self.hotkeys.capture and get_keystate) else False
        while not self._hotkey_stop.is_set():
            if self.hotkeys.start and get_keystate:
                pressed = self._safe_pressed(self.hotkeys.start)
                if pressed and not last_start:
                    self.start(reset_counter=True)
                last_start = pressed

            if self.hotkeys.stop and get_keystate:
                pressed = self._safe_pressed(self.hotkeys.stop)
                if pressed and not last_stop:
                    self.stop()
                last_stop = pressed

            if self.hotkeys.capture and get_keystate:
                pressed = self._safe_pressed(self.hotkeys.capture)
                if pressed and not last_capture:
                    try:
                        self.capture_once()
                    except Exception:
                        pass
                last_capture = pressed

            time.sleep(poll_interval)

    @staticmethod
    def _safe_pressed(key: str) -> bool:
        try:
            return bool(get_keystate(key, async_=True)) if get_keystate else False
        except Exception:
            return False

    # ---------------------- 종료 처리 ----------------------
    def shutdown(self):
        self._stop_hotkey_listener()
        self.stop()

    # ---------------------- 단일 캡처 ----------------------
    def capture_with_name(self, *, filename: str, image_format: Optional[str] = None, metadata: Optional[dict] = None) -> Path | None:
        """
        지정한 파일명으로 전체 화면을 캡처한다.
        - image_format이 None이면 현재 설정을 따른다.
        - metadata가 있으면 같은 이름의 .json 사이드카로 저장한다.
        """
        fmt = (image_format or self.image_format or DEFAULT_FORMAT).lower()
        ext = "png" if fmt == "png" else "jpg"
        _ensure_dir(self.output_dir)
        with mss.mss() as sct:
            monitor = sct.monitors[0]
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
            self._seq += 1
            shot = sct.grab(monitor)
            name = filename
            if not name.lower().endswith(f".{ext}"):
                name = f"{name}.{ext}"
            output_path = self.output_dir / name
            # 이름이 겹치면 시퀀스/타임스탬프를 덧붙여 충돌을 피한다.
            if output_path.exists():
                output_path = self.output_dir / f"{output_path.stem}_{self._seq:06d}.{ext}"
            if fmt == "png":
                mss.tools.to_png(shot.rgb, shot.size, output=str(output_path), level=self.png_compress_level)
            else:
                img = Image.frombytes("RGB", shot.size, shot.rgb)
                img.save(
                    output_path,
                    format="JPEG",
                    quality=self.jpeg_quality,
                    optimize=True,
                    subsampling=1,
                )
        if metadata:
            try:
                meta_path = output_path.with_suffix(output_path.suffix + ".json")
                meta_path.write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")
            except Exception:
                pass
        self._notify_single_capture(output_path)
        return output_path

    def capture_once(self) -> Path | None:
        _ensure_dir(self.output_dir)
        with mss.mss() as sct:
            monitor = sct.monitors[0]
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
            self._seq += 1
            shot = sct.grab(monitor)
            ext = "png" if self.image_format == "png" else "jpg"
            filename = f"{self._seq:06d}_{timestamp}.{ext}"
            output_path = self.output_dir / filename
            if self.image_format == "png":
                mss.tools.to_png(shot.rgb, shot.size, output=str(output_path), level=self.png_compress_level)
            else:
                img = Image.frombytes("RGB", shot.size, shot.rgb)
                img.save(
                    output_path,
                    format="JPEG",
                    quality=self.jpeg_quality,
                    optimize=True,
                    subsampling=1,
                )
        self._notify_single_capture(output_path)
        return output_path


def main():
    manager = ScreenCaptureManager(interval_seconds=CAPTURE_INTERVAL_SECONDS)
    manager.start()
    print(
        "전체 화면 캡처 실행 중입니다.\n"
        f"주기: {manager.interval}초 | 저장 위치: {manager.output_dir}\n"
        "Ctrl+C 로 중지하세요."
    )
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        pass
    finally:
        manager.shutdown()
        print("캡처 종료")


if __name__ == "__main__":
    main()
