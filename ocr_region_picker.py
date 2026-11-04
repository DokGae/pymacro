"""Use the macro image picker for physical desktop OCR bounds."""
from pathlib import Path
import tempfile
from PyQt6 import QtCore, QtWidgets

def attach_coordinates(owner):
    layout=owner.centralWidget().layout()
    row=QtWidgets.QHBoxLayout()
    owner.ocr_corners=[]
    for label in ('시작 X','시작 Y','끝 X','끝 Y'):
        row.addWidget(QtWidgets.QLabel(label))
        field=QtWidgets.QSpinBox();field.setRange(-100000,100000)
        owner.ocr_corners.append(field);row.addWidget(field)
    apply=QtWidgets.QPushButton('좌표 적용')
    row.addWidget(apply)
    layout.insertWidget(4,QtWidgets.QLabel('모니터 픽셀 좌표 · 끝 좌표 포함'))
    layout.insertLayout(5,row)
    def sync():
        if owner.region:
            r=owner.region
            for field,value in zip(owner.ocr_corners,(r['left'],r['top'],r['left']+r['width']-1,r['top']+r['height']-1)):
                field.setValue(value)
    def selected(region):
        owner.selected(region);sync()
    owner._ocr_pick_selected=selected
    owner._ocr_sync_coordinates=sync
    def apply_coords():
        from screen_ocr import ocr_source
        if ocr_source.transport_connected():
            owner.message.setText('인식을 중지한 뒤 좌표를 변경하세요.');return
        a,b,c,d=[field.value() for field in owner.ocr_corners]
        r=dict(left=min(a,c),top=min(b,d),width=abs(c-a)+1,height=abs(d-b)+1)
        if not 4<=r['width']<=1600 or not 4<=r['height']<=600:
            owner.message.setText('범위 크기는 가로 4~1600, 세로 4~600픽셀이어야 합니다.');return
        selected(r)
        owner.message.setText('좌표 적용됨 · 저장하고 인식 테스트를 누르세요.')
    apply.clicked.connect(apply_coords)
    owner.pick.setText('이미지 뷰어에서 범위 지정')
    sync()

def open_picker(owner):
    owner.hide()
    def capture():
        try:
            import mss
            import mss.tools
            from main import ImageViewerDialog
            cache=tempfile.TemporaryDirectory(prefix='macro-ocr-picker-')
            path=Path(cache.name)/'전체모니터.png'
            with mss.mss() as screen:
                bounds=dict(screen.monitors[0]);shot=screen.grab(bounds)
                mss.tools.to_png(shot.rgb,shot.size,output=str(path))
            class OCRViewer(ImageViewerDialog):
                def _on_region_selected(self,region):
                    self.region_select_btn.setEnabled(True)
                    if region:
                        x,y,w,h=map(int,region)
                        x,y=self._recognition_position(x,y)
                        owner._ocr_pick_selected(dict(left=x,top=y,width=w,height=h))
                        owner.show()
                        self.status_label.setText(f'OCR 범위 적용: ({x}, {y}) → ({x+w-1}, {y+h-1}) · {w}×{h}')
                def closeEvent(self,event):
                    super().closeEvent(event)
                    owner.show()
            viewer=OCRViewer(start_dir=Path(cache.name))
            viewer._ocr_temp=cache
            viewer.canvas.set_image(path)
            viewer._capture_metadata={'screen_origin':[bounds['left'],bounds['top']]}
            viewer.setWindowTitle('OCR 범위 지정 · 전체 모니터 · 범위 선택 버튼으로 시작점/끝점 선택')
            viewer._resize_to_available()
            viewer.show();viewer.raise_();viewer.activateWindow()
            owner._ocr_viewer=viewer
        except Exception as exc:
            owner.show();owner.message.setText(f'이미지 뷰어 열기 실패: {exc}')
    QtCore.QTimer.singleShot(250,capture)
