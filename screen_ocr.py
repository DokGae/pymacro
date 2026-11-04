"""Shared local OCR source. One worker, no TCP, stale values unavailable."""
import atexit
import json
import threading
import time
from pathlib import Path
from PyQt6 import QtCore

SOURCE = 'screen-ocr'
def registered_name():
    try:
        cfg = json.loads((Path(__file__).parent/'ocr-settings.json').read_text(encoding='utf-8'))
        return str(cfg.get('name','대상거리')).strip() or '대상거리'
    except (OSError,ValueError):
        return '대상거리'

class OCRSource:
    def __init__(self):
        self.lock = threading.RLock()
        self.worker = None
        self.latest = None
        self.stamp = 0
        self.message = 'OCR 영역을 지정하세요'
        self.enabled = True
        self.session = str(time.time_ns())

    def start(self, region=None, hz=10, mode=0, threshold=.7):
        with self.lock:
            if not self.enabled or self.worker is not None:
                return
            if region is None:
                try:
                    cfg = json.loads((Path(__file__).parent/'ocr-settings.json').read_text(encoding='utf-8'))
                    region = cfg['region']; hz = cfg.get('hz',10)
                    mode = cfg.get('mode',0); threshold = cfg.get('threshold',.7)
                except (OSError, ValueError, KeyError):
                    return
            if not isinstance(region,dict) or any(type(region.get(k)) is not int for k in ('left','top','width','height')):
                return
            if not 4 <= region['width'] <= 1600 or not 4 <= region['height'] <= 600:
                return
            from screen_number_ui import Reader
            self.latest = None; self.stamp = 0
            self.worker = Reader(region, max(1,min(30,int(hz))), int(mode), float(threshold))
            self.worker.result.connect(self.receive, QtCore.Qt.ConnectionType.DirectConnection)
            self.worker.status.connect(self.status, QtCore.Qt.ConnectionType.DirectConnection)
            self.worker.start()

    def receive(self, result):
        with self.lock:
            self.latest = result; self.stamp = time.monotonic()

    def status(self, text):
        with self.lock:
            self.message = text

    def stop(self):
        with self.lock:
            worker = self.worker
            self.latest = None; self.stamp = 0; self.enabled = False
        if worker:
            worker.stop_event.set(); worker.wait()
        with self.lock:
            self.worker = None
            self.message = 'OCR 중지됨'

    def snapshot(self, source):
        self.start()
        with self.lock:
            result = self.latest
            valid = result is not None and time.monotonic()-self.stamp <= .5 and bool(result['value'])
            key = registered_name()
            values = {key:float(result['value'])} if valid else {}
            data = dict(session=self.session, values=values, items={key:'화면 숫자 · '+key})
            return data, '화면 숫자 읽는 중' if valid else self.message+' · 현재 숫자 읽기 불가'

    def lookup(self, source, key):
        data, status = self.snapshot(source)
        return key in data['values'], data['values'].get(key), status

    def transport_connected(self):
        return self.worker is not None and self.worker.isRunning()

ocr_source = OCRSource()
atexit.register(ocr_source.stop)
_window = None

def show_manager(parent=None):
    global _window
    if _window is None:
        from screen_number_ui import Window, ROOT
        class Manager(Window):
            def __init__(self):
                super().__init__()
                self.setWindowTitle('화면숫자(OCR) 설정')
                from PyQt6.QtWidgets import QLineEdit, QLabel
                self.item_name = QLineEdit(registered_name())
                self.item_name.setPlaceholderText('조건에서 사용할 이름 · 예: 대상거리')
                self.centralWidget().layout().insertWidget(1,QLabel('등록할 화면 숫자 이름'))
                self.centralWidget().layout().insertWidget(2,self.item_name)
                self.start.setText('저장하고 인식 테스트')
                from ocr_region_picker import attach_coordinates
                attach_coordinates(self)
                self.top.setChecked(False)
                from PyQt6.QtWidgets import QPushButton
                convert = QPushButton('기존 프로필의 대상거리 조건을 OCR 사본으로 변환')
                convert.clicked.connect(self.convert_profile)
                self.centralWidget().layout().addWidget(convert)
                from PyQt6.QtWidgets import QLabel
                self.conversion_status = QLabel('비교값·활성 여부는 유지하고 대상높이거리는 제외합니다.')
                self.conversion_status.setWordWrap(True)
                self.centralWidget().layout().addWidget(self.conversion_status)
                self.poll = QtCore.QTimer(self)
                self.poll.timeout.connect(self.update_shared)
                self.poll.start(100)
                self._last_stamp = 0
            def select_region(self):
                from ocr_region_picker import open_picker
                open_picker(self)

            def convert_profile(self):
                from PyQt6.QtWidgets import QFileDialog
                dialog = QFileDialog(self,'OCR로 변환할 프로필 선택',str(ROOT/'setting'),'JSON (*.json)')
                dialog.setFileMode(QFileDialog.FileMode.ExistingFile)
                dialog.setModal(False)
                def selected(path):
                    try:
                        original = Path(path)
                        data = json.loads(original.read_text(encoding='utf-8-sig'))
                        count = 0
                        def visit(node):
                            nonlocal count
                            if isinstance(node,dict):
                                if node.get('type') == 'external' and node.get('external_key') == '대상거리':
                                    node['external_source'] = SOURCE
                                    count += 1
                                for value in node.values(): visit(value)
                            elif isinstance(node,list):
                                for value in node: visit(value)
                        visit(data)
                        output = original.with_name(original.stem+'-OCR-'+str(time.time_ns())+'.json')
                        with output.open('x',encoding='utf-8') as stream:
                            json.dump(data,stream,ensure_ascii=False,indent=2)
                        self.conversion_status.setText(f'{count}개 변환: {output.name} · 매크로에서 이 사본을 불러오세요.')
                    except (OSError,ValueError) as exc:
                        self.conversion_status.setText(f'변환 실패: {exc}')
                dialog.fileSelected.connect(selected)
                self._convert_dialog = dialog
                dialog.show()

            def begin(self):
                if not self.region:
                    self.message.setText('먼저 영역을 지정하세요.'); return
                ocr_source.stop(); ocr_source.enabled = True
                (ROOT/'ocr-settings.json').write_text(json.dumps(dict(name=self.item_name.text().strip() or '대상거리',region=self.region,hz=self.hz.value(),mode=self.mode.currentIndex(),threshold=self.threshold.value())),encoding='utf-8')
                ocr_source.start(self.region,self.hz.value(),self.mode.currentIndex(),self.threshold.value())
            def end(self):
                ocr_source.stop()
            def update_shared(self):
                active = ocr_source.transport_connected()
                self.stop.setEnabled(active)
                for control in (self.pick,self.displays,self.hz,self.mode,self.threshold,self.item_name):
                    control.setEnabled(not active)
                with ocr_source.lock:
                    result, stamp, message = ocr_source.latest, ocr_source.stamp, ocr_source.message
                if result is not None and stamp != self._last_stamp:
                    self._last_stamp = stamp; self.received(result)
                if not stamp or time.monotonic()-stamp > .5:
                    self.value.setText('—')
                self.message.setText(message)
            def closeEvent(self,event):
                self.hide(); event.ignore()
        _window = Manager()
    _window.show(); _window.raise_(); _window.activateWindow()
