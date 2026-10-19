"""Nonmodal pack editor sharing the existing image viewer."""
import copy
import hashlib
import uuid
from PyQt6 import QtCore, QtGui, QtWidgets
from lib.pattern_packs import load_packs, save_packs


class PackManager(QtWidgets.QDialog):
    def __init__(self, owner):
        # A native owned dialog is hidden with its owner on Windows minimize.
        # Keep only a Python reference so the editor remains above the viewer.
        super().__init__(None)
        self.owner = owner
        self.packs = load_packs()
        self.viewer = None
        self.image_id = None
        self.history = []
        self.setWindowTitle('픽셀 팩 관리')
        self.setModal(False)
        self.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, True)
        self.resize(520, 520)
        layout = QtWidgets.QVBoxLayout(self)
        self.pack_combo = QtWidgets.QComboBox()
        layout.addWidget(self.pack_combo)
        row = QtWidgets.QHBoxLayout()
        layout.addLayout(row)
        for title, callback in [('새 팩', self.add_pack), ('팩 이름 변경', self.rename_pack), ('이미지 뷰어', self.open_viewer)]:
            button = QtWidgets.QPushButton(title)
            button.clicked.connect(callback)
            row.addWidget(button)
        self.items = QtWidgets.QListWidget()
        layout.addWidget(self.items)
        row = QtWidgets.QHBoxLayout()
        layout.addLayout(row)
        for title, callback in [('항목 추가', self.add_item), ('1~N 일괄 추가', self.add_range), ('이름 변경', self.rename_item), ('항목 초기화', self.reset_item), ('항목 삭제', self.delete_item)]:
            button = QtWidgets.QPushButton(title)
            button.clicked.connect(callback)
            row.addWidget(button)
        self.preview = QtWidgets.QLabel('항목을 선택하세요.')
        self.preview.setMinimumHeight(100)
        self.preview.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(self.preview)
        self.record = QtWidgets.QCheckBox('F1로 등록 (같은 픽셀에서 다시 누르면 해제)')
        self.record.setChecked(True)
        layout.addWidget(self.record)
        self.status = QtWidgets.QLabel()
        self.status.setWordWrap(True)
        layout.addWidget(self.status)
        self.pack_combo.currentIndexChanged.connect(self.populate_items)
        self.items.currentRowChanged.connect(self.refresh)
        self.record.toggled.connect(self.refresh)
        self.undo_shortcut = QtGui.QShortcut(QtGui.QKeySequence('Ctrl+Z'), self)
        self.undo_shortcut.activated.connect(self.undo)
        self.populate_packs()
        QtWidgets.QApplication.instance().installEventFilter(self)

    def persist(self):
        try:
            save_packs(self.packs)
            self.status.setText('자동 저장됨')
        except Exception as exc:
            self.status.setText(f'저장 실패: {exc}')
            QtWidgets.QMessageBox.warning(self, '팩 저장 실패', str(exc))

    def populate_packs(self, selected=None):
        self.pack_combo.blockSignals(True)
        self.pack_combo.clear()
        for key, pack in self.packs.items():
            self.pack_combo.addItem(pack['name'], key)
        if selected:
            self.pack_combo.setCurrentIndex(self.pack_combo.findData(selected))
        self.pack_combo.blockSignals(False)
        self.populate_items()

    def pack(self):
        return self.packs.get(self.pack_combo.currentData())

    def item(self):
        row = self.items.currentItem()
        pack = self.pack()
        return pack['items'].get(row.data(QtCore.Qt.ItemDataRole.UserRole)) if row and pack else None

    def populate_items(self, *_):
        self.items.clear()
        pack = self.pack()
        if pack:
            for key, item in pack['items'].items():
                row = QtWidgets.QListWidgetItem(f"{item['name']} · {len(item['points'])}점")
                row.setData(QtCore.Qt.ItemDataRole.UserRole, key)
                self.items.addItem(row)
            self.items.setCurrentRow(0)
        self.refresh()

    def add_pack(self):
        name, ok = QtWidgets.QInputDialog.getText(self, '새 팩', '팩 이름')
        if ok and name.strip():
            key = uuid.uuid4().hex
            self.packs[key] = {'name': name.strip(), 'items': {}}
            self.persist()
            self.populate_packs(key)

    def rename_pack(self):
        if not self.pack():
            return
        name, ok = QtWidgets.QInputDialog.getText(self, '팩 이름 변경', '이름', text=self.pack()['name'])
        if ok and name.strip():
            self.pack()['name'] = name.strip()
            self.persist()
            self.populate_packs(self.pack_combo.currentData())

    def insert_items(self, names):
        if self.pack() is None:
            self.status.setText('먼저 팩을 만드세요.')
            return
        existing = {v['name'] for v in self.pack()['items'].values()}
        for name in names:
            if name not in existing:
                self.pack()['items'][uuid.uuid4().hex] = {'name': name, 'points': []}
                existing.add(name)
        self.persist()
        self.populate_items()

    def add_item(self):
        name, ok = QtWidgets.QInputDialog.getText(self, '항목 추가', '항목 이름')
        if ok and name.strip():
            self.insert_items([name.strip()])
            self.items.setCurrentRow(self.items.count() - 1)

    def add_range(self):
        count, ok = QtWidgets.QInputDialog.getInt(self, '숫자 항목 추가', '1부터 몇 번까지?', 20, 1, 1000)
        if ok:
            self.insert_items([str(i) for i in range(1, count + 1)])

    def rename_item(self):
        item = self.item()
        if item is None:
            return
        name, ok = QtWidgets.QInputDialog.getText(self, '이름 변경', '항목 이름', text=item['name'])
        if ok and name.strip():
            item['name'] = name.strip()
            self.persist()
            self.refresh()

    def remember(self):
        self.history.append(copy.deepcopy(self.packs))
        self.history = self.history[-50:]

    def undo(self):
        if self.history:
            selected = self.pack_combo.currentData()
            index = self.items.currentRow()
            self.packs = self.history.pop()
            self.persist()
            self.populate_packs(selected)
            self.items.setCurrentRow(min(index, self.items.count() - 1))

    def delete_item(self):
        if self.item() is not None:
            self.remember()
            del self.pack()['items'][self.items.currentItem().data(QtCore.Qt.ItemDataRole.UserRole)]
            self.persist()
            self.populate_items()

    def reset_item(self):
        item = self.item()
        if item is None:
            return
        self.remember()
        item['points'] = []
        item.pop('source', None)
        item.pop('thumbnail', None)
        self.persist()
        self.refresh()

    def open_viewer(self):
        self.owner._open_image_viewer_dialog()
        self.attach_viewer()
        self.raise_()

    def attach_viewer(self):
        viewer = getattr(self.owner, '_image_viewer_dialog', None)
        if viewer is not None and viewer is not self.viewer:
            self.viewer = viewer
            viewer.canvas.imageChanged.connect(self.image_changed)
            self.image_changed()

    def image_changed(self):
        image = self.viewer.canvas._image if self.viewer else None
        self.image_id = None
        if image is not None and not image.isNull():
            image = image.convertToFormat(QtGui.QImage.Format.Format_RGBA8888)
            self.image_id = hashlib.sha256(bytes(image.constBits().asstring(image.sizeInBytes())) + f'{image.width()},{image.height()}'.encode()).hexdigest()
        self.refresh()

    def eventFilter(self, obj, event):
        controller = getattr(self.owner, '_shared_controller', None)
        if controller is not None and controller.pick is not None:
            return False
        if not self.isVisible():
            return False
        if event.type() not in (QtCore.QEvent.Type.KeyPress, QtCore.QEvent.Type.ShortcutOverride):
            return False
        self.attach_viewer()
        if not self.record.isChecked() or not self.viewer:
            return False
        window = obj.window() if isinstance(obj, QtWidgets.QWidget) else None
        if window not in (self, self.viewer):
            return False
        is_f1 = event.key() == QtCore.Qt.Key.Key_F1 and event.modifiers() == QtCore.Qt.KeyboardModifier.NoModifier
        is_undo = event.key() == QtCore.Qt.Key.Key_Z and event.modifiers() == QtCore.Qt.KeyboardModifier.ControlModifier
        if not (is_f1 or is_undo):
            return False
        event.accept()
        if event.type() == QtCore.QEvent.Type.KeyPress and not event.isAutoRepeat():
            self.undo() if is_undo else self.capture_point()
        return True

    def capture_point(self):
        item = self.item()
        sample = self.viewer._last_sample if self.viewer else None
        if item is None or not sample or self.image_id is None:
            self.status.setText('항목을 선택하고 이미지 위에 커서를 놓은 뒤 F1을 누르세요.')
            return
        if item.get('source') and item['source'] != self.image_id and item['points']:
            self.status.setText('다른 이미지에서 등록한 항목입니다. 항목 초기화 후 다시 찍거나 새 항목을 추가하세요.')
            return
        x, y = map(int, sample['pos'])
        image = self.viewer.canvas._image
        if not image.rect().contains(x, y):
            return
        self.remember()
        point = next((p for p in item['points'] if p['dx'] == x and p['dy'] == y), None)
        if point:
            item['points'].remove(point)
        else:
            color = image.pixelColor(x, y)
            item['points'].append({'dx': x, 'dy': y, 'color': [color.red(), color.green(), color.blue()]})
        item['source'] = self.image_id
        if item['points']:
            xs = [p['dx'] for p in item['points']]
            ys = [p['dy'] for p in item['points']]
            crop = image.copy(min(xs), min(ys), max(xs)-min(xs)+1, max(ys)-min(ys)+1)
            data = QtCore.QByteArray()
            buffer = QtCore.QBuffer(data)
            buffer.open(QtCore.QIODevice.OpenModeFlag.WriteOnly)
            crop.save(buffer, 'PNG')
            item['thumbnail'] = bytes(data.toBase64()).decode('ascii')
        else:
            item.pop('thumbnail', None)
        self.persist()
        self.refresh()

    def refresh(self, *_):
        item = self.item()
        rects = []
        self.preview.clear()
        if item is not None:
            self.items.currentItem().setText(f"{item['name']} · {len(item['points'])}점")
            self.record.setText(f"F1 등록: {self.pack()['name']} / {item['name']} · {len(item['points'])}점")
            if item.get('thumbnail'):
                pixmap = QtGui.QPixmap()
                pixmap.loadFromData(QtCore.QByteArray.fromBase64(item['thumbnail'].encode()))
                self.preview.setPixmap(pixmap.scaled(400, 110, QtCore.Qt.AspectRatioMode.KeepAspectRatio, QtCore.Qt.TransformationMode.FastTransformation))
            else:
                self.preview.setText('미등록 · 이미지 위에서 F1로 픽셀을 찍으세요.')
            if item.get('source') == self.image_id:
                rects = [(p['dx'], p['dy'], 1, 1) for p in item['points']]
        else:
            self.record.setText('F1 등록 · 먼저 항목을 선택하세요.')
            self.preview.setText('항목을 추가하거나 선택하세요.')
        if self.viewer:
            self.viewer.canvas.set_overlays(rects)

    def done(self, result):
        if self.viewer:
            self.viewer.canvas.set_overlays([])
        super().done(result)

    def closeEvent(self, event):
        if self.viewer:
            self.viewer.canvas.set_overlays([])
        super().closeEvent(event)


def open_pack_manager(owner):
    dialog = getattr(owner, '_pack_manager', None)
    if dialog is None:
        dialog = PackManager(owner)
        owner._pack_manager = dialog
    dialog.show()
    dialog.attach_viewer()
    dialog.refresh()
    dialog.raise_()
    dialog.activateWindow()
