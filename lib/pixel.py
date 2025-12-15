"""
픽셀 캡처 및 색상 탐색 헬퍼.
mss 우선 사용, 없을 경우 PIL.ImageGrab로 폴백합니다.
"""

from __future__ import annotations

import threading
from typing import Tuple

try:
    import mss
except ImportError:
    mss = None  # type: ignore

try:
    from PIL import Image, ImageGrab
except ImportError:  # pragma: no cover - Pillow 미설치 시
    Image = None  # type: ignore
    ImageGrab = None  # type: ignore

try:
    import numpy as np
except ImportError:  # pragma: no cover - numpy 미설치 시
    np = None  # type: ignore

Region = Tuple[int, int, int, int]  # (x, y, w, h)
RGB = Tuple[int, int, int]


class PixelBackendError(RuntimeError):
    """사용 가능한 캡처 백엔드가 없을 때 발생."""


def _require_backend():
    if np is None:
        raise PixelBackendError("numpy가 필요합니다.")
    if mss is None and (Image is None or ImageGrab is None):
        raise PixelBackendError("mss 또는 Pillow(ImageGrab)가 필요합니다.")
    if mss is not None and Image is None:
        raise PixelBackendError("mss 사용 시 Pillow가 필요합니다.")


_thread_local_mss = threading.local()


def _get_mss():
    """
    스레드마다 별도 mss 인스턴스를 보관한다.
    mss는 내부에 thread-local 핸들을 들고 있어 타 스레드에서 재사용하면 AttributeError가 발생할 수 있다.
    """
    if mss is None:
        return None
    sct = getattr(_thread_local_mss, "instance", None)
    if sct is None:
        sct = mss.mss()
        _thread_local_mss.instance = sct
    return sct


def capture_region(region: Region):
    """
    지정된 영역을 캡처하여 PIL Image를 반환합니다.
    region: (x, y, w, h), 다중 모니터 음수 좌표 허용.
    """
    _require_backend()
    x, y, w, h = region
    if w <= 0 or h <= 0:
        raise ValueError("width/height must be positive")

    if mss is not None:
        sct = _get_mss()
        shot = sct.grab({"left": int(x), "top": int(y), "width": int(w), "height": int(h)})  # type: ignore[union-attr]
        # mss가 반환하는 BGRA를 RGB로 변환
        return Image.frombytes("RGB", shot.size, shot.rgb)  # type: ignore[arg-type]

    # Pillow 폴백
    bbox = (int(x), int(y), int(x + w), int(y + h))
    return ImageGrab.grab(bbox=bbox)  # type: ignore[union-attr]


def capture_region_np(region: Region):
    """
    지정된 영역을 numpy 배열(H,W,3, uint8)로 캡처합니다.
    region: (x, y, w, h), 다중 모니터 음수 좌표 허용.
    """
    _require_backend()
    x, y, w, h = region
    if w <= 0 or h <= 0:
        raise ValueError("width/height must be positive")

    if mss is not None:
        sct = _get_mss()
        shot = sct.grab({"left": int(x), "top": int(y), "width": int(w), "height": int(h)})  # type: ignore[union-attr]
        return np.frombuffer(shot.rgb, dtype=np.uint8).reshape((h, w, 3))

    # Pillow 폴백
    bbox = (int(x), int(y), int(x + w), int(y + h))
    img = ImageGrab.grab(bbox=bbox).convert("RGB")  # type: ignore[union-attr]
    return np.asarray(img, dtype=np.uint8)


def _within_tolerance(src: Tuple[int, int, int], target: RGB, tolerance: int) -> bool:
    return all(abs(s - t) <= tolerance for s, t in zip(src, target))


def find_color_in_region(region: Region, rgb: RGB, tolerance: int = 0):
    """
    영역에서 지정 색상이 존재하는지 검색합니다.
    반환: (found: bool, 좌표: (x, y) | None)
    """
    arr = capture_region_np(region)
    x, y, w, h = region
    target = np.array(rgb, dtype=np.int16)
    diff = np.abs(arr.astype(np.int16) - target).max(axis=2)
    mask = diff <= int(tolerance)
    if mask.any():
        py, px = np.argwhere(mask)[0]
        return True, (x + int(px), y + int(py))
    return False, None
