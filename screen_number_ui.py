"""Independent desktop ROI number reader. No game-process access."""
import ctypes
from ctypes import wintypes
import json
import re
import sys
import threading
import time
from pathlib import Path

from PyQt6.QtCore import Qt, QRect, QThread, pyqtSignal, QTimer
from PyQt6.QtGui import QColor, QImage, QPainter, QPen, QPixmap
from PyQt6.QtWidgets import (QApplication, QWidget, QMainWindow, QVBoxLayout,
    QHBoxLayout, QLabel, QPushButton, QComboBox, QSpinBox, QDoubleSpinBox,
    QCheckBox, QMessageBox)

ROOT = Path(__file__).resolve().parent


def number_from_text(text):
    # Do not silently turn OCR letters such as O/I into digits.
    values = re.findall(r"(?<![\d.])\d+(?:\.\d+)?(?![\d.])", text.replace('，', ',').replace('．', '.'))
    return values[0] if len(values) == 1 else ''


def physical_monitor(name):
    """Match Qt display name to physical Windows monitor pixels, including mixed DPI."""
    class Info(ctypes.Structure):
        _fields_ = [('size', wintypes.DWORD), ('monitor', wintypes.RECT),
                    ('work', wintypes.RECT), ('flags', wintypes.DWORD),
                    ('device', wintypes.WCHAR * 32)]
    class DisplayDevice(ctypes.Structure):
        _fields_ = [('size', wintypes.DWORD), ('name', wintypes.WCHAR * 32),
                    ('description', wintypes.WCHAR * 128), ('flags', wintypes.DWORD),
                    ('id', wintypes.WCHAR * 128), ('key', wintypes.WCHAR * 128)]
    user = ctypes.WinDLL('user32', use_last_error=True)
    callback_type = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HANDLE,
                                     wintypes.HDC, ctypes.POINTER(wintypes.RECT), wintypes.LPARAM)
    user.GetMonitorInfoW.argtypes = [wintypes.HANDLE, ctypes.POINTER(Info)]
    user.EnumDisplayMonitors.argtypes = [wintypes.HDC, ctypes.c_void_p, callback_type, wintypes.LPARAM]
    user.EnumDisplayDevicesW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, ctypes.POINTER(DisplayDevice), wintypes.DWORD]
    matches = []; observed = []; all_regions = []
    @callback_type
    def visit(handle, dc, rect, data):
        info = Info(); info.size = ctypes.sizeof(info)
        if user.GetMonitorInfoW(handle, ctypes.byref(info)):
            observed.append(info.device)
            display = DisplayDevice(); display.size = ctypes.sizeof(display)
            friendly = ''
            if user.EnumDisplayDevicesW(info.device, 0, ctypes.byref(display), 0):
                friendly = display.description
            r = info.monitor
            region = dict(left=r.left, top=r.top, width=r.right-r.left, height=r.bottom-r.top)
            all_regions.append(region)
            if info.device == name or friendly == name:
                matches.append(region)
        return True
    enumerated = user.EnumDisplayMonitors(None, None, visit, 0)
    if enumerated and len(all_regions) == 1:
        return all_regions[0]
    if not enumerated or len(matches) != 1:
        raise RuntimeError(f'모니터 좌표 확인 실패: {name!r}, Windows={observed!r}')
    return matches[0]


def image_from_bgr(frame):
    rgb = frame[:, :, ::-1].copy()
    h, w = rgb.shape[:2]
    return QImage(rgb.data, w, h, rgb.strides[0], QImage.Format.Format_RGB888).copy()


def prepare_frame(raw, mode):
    import cv2
    gray = cv2.cvtColor(raw, cv2.COLOR_BGR2GRAY)
    if mode == 0:
        # OCR models expect dark text on a light background.
        return 255-raw if float(gray.mean()) < 127 else raw
    _, gray = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY | cv2.THRESH_OTSU)
    if mode == 2:
        gray = 255-gray
    return cv2.cvtColor(gray, cv2.COLOR_GRAY2BGR)


class Selector(QWidget):
    selected = pyqtSignal(dict)
    def __init__(self, screen, monitor):
        super().__init__()
        import mss
        import numpy as np
        self.monitor = monitor
        with mss.mss() as capture:
            self.picture = QPixmap.fromImage(image_from_bgr(np.array(capture.grab(monitor))[:, :, :3]))
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint | Qt.WindowType.Tool)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setGeometry(screen.geometry())
        self.setCursor(Qt.CursorShape.CrossCursor)
        self.origin = None
        self.selection = QRect()

    def paintEvent(self, event):
        p = QPainter(self)
        p.drawPixmap(self.rect(), self.picture)
        p.fillRect(self.rect(), QColor(0, 0, 0, 105))
        if not self.selection.isNull():
            p.save(); p.setClipRect(self.selection)
            p.drawPixmap(self.rect(), self.picture); p.restore()
            p.setPen(QPen(QColor('#36e5bc'), 2)); p.drawRect(self.selection)
        p.setPen(QColor('white'))
        p.drawText(24, 36, '숫자 한 줄을 여백이 적게 드래그하세요 · Esc 취소')

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.origin = event.position().toPoint()

    def mouseMoveEvent(self, event):
        if self.origin is not None:
            self.selection = QRect(self.origin, event.position().toPoint()).normalized().intersected(self.rect())
            self.update()

    def mouseReleaseEvent(self, event):
        if self.origin is None or event.button() != Qt.MouseButton.LeftButton:
            return
        r = QRect(self.origin, event.position().toPoint()).normalized().intersected(self.rect())
        if r.width() >= 4 and r.height() >= 4:
            m = self.monitor
            x1 = round(r.x() * m['width'] / self.width())
            y1 = round(r.y() * m['height'] / self.height())
            x2 = round((r.x()+r.width()) * m['width'] / self.width())
            y2 = round((r.y()+r.height()) * m['height'] / self.height())
            self.selected.emit(dict(left=m['left']+x1, top=m['top']+y1, width=x2-x1, height=y2-y1))
        self.close()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self.close()


class Reader(QThread):
    result = pyqtSignal(dict)
    status = pyqtSignal(str)
    def __init__(self, region, hz, mode, threshold):
        super().__init__()
        self.region, self.hz, self.mode, self.threshold = region.copy(), hz, mode, threshold
        self.stop_event = threading.Event()

    def run(self):
        try:
            self.status.emit('인식 모델 준비 중…')
            import cv2
            import mss
            import numpy as np
            import rapidocr_onnxruntime
            from rapidocr_onnxruntime.ch_ppocr_rec import TextRecognizer
            from rapidocr_onnxruntime.utils import read_yaml
            cv2.setNumThreads(1)
            package = Path(rapidocr_onnxruntime.__file__).parent
            cfg = read_yaml(package / 'config.yaml')['Rec']
            cfg.update(model_path=str(package / cfg['model_path']),
                       intra_op_num_threads=1, inter_op_num_threads=1)
            recognize = TextRecognizer(cfg)
            self.status.emit('읽는 중 · 게임의 숫자가 선택 영역에 보이도록 유지하세요')
            with mss.mss() as capture:
                while not self.stop_event.is_set():
                    started = time.perf_counter()
                    raw = np.array(capture.grab(self.region))[:, :, :3].copy()
                    frame = prepare_frame(raw, self.mode)
                    # Read the selected mode directly. Cross-checking different
                    # renderings rejected valid game digits too often.
                    rows, _ = recognize(frame)
                    text, confidence = rows[0] if rows else ('', 0.0)
                    from ocr_accuracy import strict_number
                    value = strict_number(text) if confidence >= self.threshold else ''
                    verification = '인식됨' if value else '신뢰도 부족 또는 숫자 아님'
                    elapsed = time.perf_counter()-started
                    self.result.emit(dict(value=value, text=text, confidence=float(confidence),
                                          ms=elapsed*1000, verification=verification, image=image_from_bgr(frame)))
                    self.stop_event.wait(max(0, 1/self.hz-elapsed))
        except Exception as exc:
            self.status.emit(f'오류: {exc}')


class Window(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle('화면 숫자 읽기 · 독립 테스트')
        self.resize(640, 520)
        self.worker = None; self.region = None; self.selector = None
        self.count = 0; self.measure_at = time.perf_counter()
        body = QWidget(); self.setCentralWidget(body); layout = QVBoxLayout(body)
        self.top = QCheckBox('항상 위에 표시')
        self.top.setStyleSheet('font-size: 15px; font-weight: bold; padding: 8px;')
        self.top.toggled.connect(self.set_top)
        layout.addWidget(self.top)
        hint = QLabel('① 화면 선택 → ② 영역 지정 → ③ 읽기 시작\n숫자 한 줄만 지정하세요. 창에 가려지면 가려진 화면을 읽습니다.')
        layout.addWidget(hint)
        row = QHBoxLayout(); layout.addLayout(row)
        self.displays = QComboBox()
        for screen in QApplication.screens():
            self.displays.addItem(screen.name(), screen)
        row.addWidget(self.displays)
        self.pick = QPushButton('영역 지정'); self.pick.clicked.connect(self.select_region); row.addWidget(self.pick)
        self.region_label = QLabel('지정 영역 없음'); layout.addWidget(self.region_label)
        options = QHBoxLayout(); layout.addLayout(options)
        options.addWidget(QLabel('초당 읽기'))
        self.hz = QSpinBox(); self.hz.setRange(1, 30); self.hz.setValue(10); options.addWidget(self.hz)
        self.mode = QComboBox(); self.mode.addItems(['자동 명암', '흑백 이진화', '흑백 반전']); options.addWidget(self.mode)
        options.addWidget(QLabel('최소 신뢰도'))
        self.threshold = QDoubleSpinBox(); self.threshold.setRange(.0, 1.0); self.threshold.setSingleStep(.05); self.threshold.setValue(.7); options.addWidget(self.threshold)
        buttons = QHBoxLayout(); layout.addLayout(buttons)
        self.start = QPushButton('읽기 시작'); self.start.clicked.connect(self.begin); buttons.addWidget(self.start)
        self.stop = QPushButton('중지'); self.stop.setEnabled(False); self.stop.clicked.connect(self.end); buttons.addWidget(self.stop)
        self.value = QLabel('—'); self.value.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.value.setStyleSheet('font-size: 52px; font-weight: bold; color: #36c7a6;'); layout.addWidget(self.value)
        self.raw = QLabel('인식 원문: —'); self.raw.setTextFormat(Qt.TextFormat.PlainText); layout.addWidget(self.raw)
        self.preview = QLabel('영역 미리보기'); self.preview.setAlignment(Qt.AlignmentFlag.AlignCenter); self.preview.setMinimumHeight(95); layout.addWidget(self.preview)
        self.metrics = QLabel('처리 시간: — / 실제 갱신: —'); layout.addWidget(self.metrics)
        self.resources = QLabel(''); layout.addWidget(self.resources)
        self.message = QLabel('준비'); self.message.setWordWrap(True); layout.addWidget(self.message)
        import psutil
        self.process = psutil.Process(); self.process.cpu_percent()
        self.cpu_count = psutil.cpu_count() or 1
        self.timer = QTimer(self); self.timer.timeout.connect(self.resources_tick); self.timer.start(1000)
        self.restore()
        self.top.setChecked(True)

    def set_top(self, checked):
        self.setWindowFlag(Qt.WindowType.WindowStaysOnTopHint, checked); self.show()

    def restore(self):
        try:
            data = json.loads((ROOT/'ocr-settings.json').read_text(encoding='utf-8'))
            r = data['region']
            if (isinstance(r, dict) and all(type(r.get(k)) is int for k in ('left', 'top', 'width', 'height'))
                    and 4 <= r['width'] <= 1600 and 4 <= r['height'] <= 600):
                self.region = r
            self.hz.setValue(int(data.get('hz', 10)))
            self.mode.setCurrentIndex(max(0, min(2, int(data.get('mode', 0)))))
            self.threshold.setValue(float(data.get('threshold', .7)))
            self.update_region()
        except (OSError, ValueError, KeyError, TypeError):
            pass

    def update_region(self):
        if self.region:
            r = self.region
            self.region_label.setText(f"X {r['left']} / Y {r['top']} / {r['width']} × {r['height']} px")

    def select_region(self):
        self.hide()
        QTimer.singleShot(250, self.open_selector)

    def open_selector(self):
        try:
            screen = self.displays.currentData()
            self.selector = Selector(screen, physical_monitor(screen.name()))
            self.selector.selected.connect(self.selected)
            self.selector.destroyed.connect(self.show)
            self.selector.show(); self.selector.activateWindow()
        except Exception as exc:
            self.show(); QMessageBox.warning(self, '영역 지정', str(exc))

    def selected(self, region):
        if region['width'] > 1600 or region['height'] > 600:
            self.message.setText('영역이 너무 큽니다. 숫자 한 줄을 작게 선택하세요.'); return
        self.region = region; self.update_region()

    def begin(self):
        if not self.region:
            self.message.setText('먼저 영역을 지정하세요.'); return
        self.worker = Reader(self.region, self.hz.value(), self.mode.currentIndex(), self.threshold.value())
        self.worker.result.connect(self.received)
        self.worker.status.connect(self.message.setText)
        self.worker.finished.connect(self.finished)
        self.count = 0; self.measure_at = time.perf_counter(); self.value.setText('—')
        for control in (self.pick, self.displays, self.start, self.hz, self.mode, self.threshold):
            control.setEnabled(False)
        self.stop.setEnabled(True)
        self.worker.start()

    def end(self):
        if self.worker:
            self.worker.stop_event.set(); self.stop.setEnabled(False)
            self.message.setText('중지 중…')

    def finished(self):
        failed = self.message.text().startswith('오류:')
        self.worker.deleteLater(); self.worker = None
        for control in (self.pick, self.displays, self.start, self.hz, self.mode, self.threshold):
            control.setEnabled(True)
        self.stop.setEnabled(False)
        self.value.setText('—')
        if not failed:
            self.message.setText('중지됨')

    def received(self, result):
        self.value.setText(result['value'] or '—')
        self.raw.setText(f"인식 원문: {result['text']!r} / 신뢰도 {result['confidence']:.0%} / {result.get('verification','')}")
        pix = QPixmap.fromImage(result['image'])
        self.preview.setPixmap(pix.scaled(580, 100, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.FastTransformation))
        self.count += 1
        elapsed = time.perf_counter()-self.measure_at
        self.metrics.setText(f"캡처+인식 {result['ms']:.1f} ms / 실제 갱신 {self.count/max(elapsed,.001):.1f}회/초")
        if elapsed > 3:
            self.count = 0; self.measure_at = time.perf_counter()

    def resources_tick(self):
        cpu = self.process.cpu_percent()/self.cpu_count
        self.resources.setText(f'이 도구 CPU {cpu:.2f}% (전체 CPU 기준) / 메모리 {self.process.memory_info().rss/1048576:.0f} MB')

    def closeEvent(self, event):
        if self.worker and self.worker.isRunning():
            self.end(); event.ignore()
            self.message.setText('중지 후 창을 다시 닫아주세요.'); return
        try:
            (ROOT/'ocr-settings.json').write_text(json.dumps(dict(region=self.region, hz=self.hz.value(),
                mode=self.mode.currentIndex(), threshold=self.threshold.value()), indent=2), encoding='utf-8')
        except OSError:
            pass
        event.accept()


if __name__ == '__main__':
    app = QApplication(sys.argv)
    app.setStyle('Fusion')
    window = Window(); window.show()
    sys.exit(app.exec())
