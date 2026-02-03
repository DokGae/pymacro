"""
픽셀 캡처 및 색상 탐색 헬퍼.
mss 우선 사용, 없을 경우 PIL.ImageGrab로 폴백합니다.
"""

from __future__ import annotations

import threading
from dataclasses import dataclass, field
from typing import List, Optional, Tuple

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


# ----------------------- Pixel pattern -----------------------

@dataclass
class PixelPatternPoint:
    dx: int
    dy: int
    color: RGB
    tolerance: Optional[int] = None

    def to_dict(self) -> dict:
        return {
            "dx": int(self.dx),
            "dy": int(self.dy),
            "color": list(self.color),
            "tolerance": int(self.tolerance) if self.tolerance is not None else None,
        }

    @staticmethod
    def from_dict(data: dict) -> "PixelPatternPoint":
        return PixelPatternPoint(
            dx=int(data.get("dx", 0)),
            dy=int(data.get("dy", 0)),
            color=tuple(int(c) for c in data.get("color", (0, 0, 0)))[:3],  # type: ignore[arg-type]
            tolerance=int(data["tolerance"]) if data.get("tolerance") is not None else None,
        )


@dataclass
class PixelPattern:
    name: str
    points: List[PixelPatternPoint] = field(default_factory=list)
    tolerance: int = 0
    description: Optional[str] = None

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "tolerance": int(self.tolerance),
            "description": self.description,
            "points": [p.to_dict() for p in self.points],
        }

    @staticmethod
    def from_dict(data: dict) -> "PixelPattern":
        pts_raw = data.get("points", []) or []
        points = []
        for p in pts_raw:
            if isinstance(p, dict):
                points.append(PixelPatternPoint.from_dict(p))
        return PixelPattern(
            name=str(data.get("name") or "pattern"),
            points=points,
            tolerance=int(data.get("tolerance", 0)),
            description=data.get("description"),
        )

    def normalized(self) -> "PixelPattern":
        """Anchor pattern so that min dx/dy start at 0, returning new instance."""
        if not self.points:
            return PixelPattern(name=self.name, points=[], tolerance=self.tolerance, description=self.description)
        min_dx = min(p.dx for p in self.points)
        min_dy = min(p.dy for p in self.points)
        if min_dx == 0 and min_dy == 0:
            return self
        shifted = [
            PixelPatternPoint(dx=p.dx - min_dx, dy=p.dy - min_dy, color=p.color, tolerance=p.tolerance) for p in self.points
        ]
        return PixelPattern(name=self.name, points=shifted, tolerance=self.tolerance, description=self.description)


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


def find_pattern_in_region(
    region: Region,
    pattern: PixelPattern,
    tolerance: int = 0,
):
    """
    영역 내에 픽셀 패턴이 존재하는지 검색합니다.
    패턴은 기준점(0,0) 기준 상대좌표 목록으로 저장되어 있다고 가정합니다.
    tolerance: 조건에서 넘어온 공통 허용오차. 패턴/포인트에 저장된 tolerance 값은 무시합니다.
    반환: (found: bool, 좌표: (x, y) | None) - 좌표는 영역 내 패턴의 좌측 상단(정규화 기준).
    """
    _require_backend()
    if not pattern.points:
        return False, None

    arr = capture_region_np(region)
    x0, y0, w, h = region

    # 정규화된 패턴 사용
    norm_pat = pattern.normalized()
    max_dx = max(p.dx for p in norm_pat.points)
    max_dy = max(p.dy for p in norm_pat.points)
    # 패턴이 영역보다 크면 실패
    if w - max_dx <= 0 or h - max_dy <= 0:
        return False, None

    work_w = w - max_dx
    work_h = h - max_dy
    mask_all = np.ones((work_h, work_w), dtype=bool)

    for pt in norm_pat.points:
        pt_tol = int(tolerance if tolerance is not None else 0)
        sub = arr[pt.dy : pt.dy + work_h, pt.dx : pt.dx + work_w]
        diff = np.abs(sub.astype(np.int16) - np.array(pt.color, dtype=np.int16)).max(axis=2)
        mask_all &= diff <= pt_tol
        if not mask_all.any():
            return False, None

    if mask_all.any():
        py, px = np.argwhere(mask_all)[0]
        return True, (x0 + int(px), y0 + int(py))
    return False, None
