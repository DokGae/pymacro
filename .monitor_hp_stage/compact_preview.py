"""Opaque, flat color swatches for small always-on-top visual monitoring."""
import math
import time
from functools import lru_cache
from PyQt6.QtCore import Qt, QSize, QRect, QRectF, QPointF, QPoint, QEvent, pyqtSignal
from PyQt6.QtGui import QColor, QPainter, QFont, QPixmap, QImage, QPainterPath, QPen, QPolygonF, QRegion
from packetcore.icons import effect_icon,job_icon
from PyQt6.QtWidgets import (QWidget, QLabel, QPushButton, QVBoxLayout,
    QHBoxLayout, QFrame, QSizePolicy, QSlider, QApplication)


class ElidedLabel(QLabel):
    """Keep the full text while painting only what fits the allocated column."""
    def __init__(self, text=''):
        super().__init__(text)
        self.icon_path=None;self.icon_size=14
        self.setMinimumWidth(0)
        self.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Preferred)

    def minimumSizeHint(self):
        return QSize(0, super().minimumSizeHint().height())

    def set_icon(self,path):
        if self.icon_path!=path:self.icon_path=path;self.update()

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setFont(self.font())
        painter.setPen(self.palette().windowText().color())
        rect=self.contentsRect()
        if self.icon_path:
            pixmap=icon_pixmap(self.icon_path)
            if not pixmap.isNull():
                size=min(self.icon_size,rect.height(),rect.width())
                painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
                painter.drawPixmap(QRect(rect.left(),rect.top()+(rect.height()-size)//2,size,size),pixmap,pixmap.rect())
                rect=rect.adjusted(size+3,0,0,0)
        text = self.fontMetrics().elidedText(self.text(), Qt.TextElideMode.ElideRight, max(0,rect.width()))
        painter.drawText(rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, text)


def countdown(effect, now):
    """Use a wall-clock expiry when available; otherwise count from observation."""
    expires = effect.get('expires_at_ms', 0)
    duration = effect.get('duration_ms', 0)
    observed = effect.get('observed_at')
    if isinstance(expires, (int,float)) and expires >= 1_000_000_000_000:
        remaining = expires / 1000 - now
    elif isinstance(duration, (int,float)) and duration > 0 and isinstance(observed, (int,float)):
        remaining = duration / 1000 - (now - observed)
    else:
        return None
    return math.ceil(remaining) if 0 < remaining <= 5 else None


def preview_entries(catalog, states, now=None):
    if now is None: now = time.time()
    watched = sorted((key for key,value in catalog.preview.items() if value.get('enabled')),
                     key=lambda key: (catalog.preview[key].get('priority',0) == 0,
                         catalog.preview[key].get('priority',0),
                         (1,key) if key.startswith('attack:') else (0,int(key))))
    def active(key):
        state = states.actors.get(key)
        effects = {}
        if state:
            for effect in state.effects.values():
                effects.setdefault(str(effect['code']), []).append(effect)
        return effects
    own = active(states.owner_key); target = active(states.attack_target_key)
    if states.attack_target_key:
        position = states.attack_positions.get(states.attack_target_key)
        if position in (1,2): target['attack:back' if position == 1 else 'attack:front'] = []
        outcome = states.attack_outcomes.get(states.attack_target_key)
        if outcome in ('회피','막기'): target['attack:evade' if outcome == '회피' else 'attack:block'] = []
    def entries(keys,role):
        def latest(key):
            return max(((effect.get('observed_at',0), effect.get('observed_record',0),
                         effect.get('observed_index',0)) for effect in keys.get(key,[])),
                       default=(states.attack_target_at or 0, states.attack_target_record,0)
                       if key.startswith('attack:') else (0,0,0))
        result = [(key,catalog.name(key),catalog.preview[key].get('color') or '#64748B',key in keys,
                 min((value for effect in keys.get(key,[]) if (value := countdown(effect,now)) is not None), default=None)
                 if catalog.preview[key].get('remaining_time',False) else None,
                 effect_icon(key) if catalog.preview[key].get('display_mode','image') == 'image' else None)
                for key in watched if catalog.preview[key].get(role,True)]
        winners = {}
        for entry in result:
            key, _, color, enabled, _, icon = entry
            if enabled and icon is None:
                group = color.upper()
                if group not in winners or latest(key) >= latest(winners[group]):
                    winners[group] = key
        return [entry for entry in result if not entry[3] or entry[5] is not None
                or winners[entry[2].upper()] == entry[0]]
    return entries(own,'own'), entries(target,'target')


@lru_cache(maxsize=1200)
def icon_pixmap(path):
    return QPixmap(path)


class SwatchPanel(QWidget):
    CELL = 22
    TILE = 16
    countdown_size = 0
    countdown_weight = 700

    def __init__(self, parent=None):
        super().__init__(parent); self.entries=[]
        self.setMinimumHeight(22); self.setMouseTracking(True)

    def set_entries(self, entries):
        # Pack active effects in the catalog's priority order, without empty slots.
        entries=[entry for entry in entries if entry[3]]
        if self.entries != entries:
            self.entries=entries; self.updateGeometry(); self.update()

    def columns(self): return max(1,self.width() // self.CELL)

    def sizeHint(self):
        rows=max(1,(len(self.entries)+self.columns()-1)//self.columns())
        return QSize(90,rows*self.CELL)

    def paintEvent(self, event):
        painter=QPainter(self)
        # Fill each row from the left, then wrap to the next row.
        for index,(_,_,color,enabled,remaining,icon) in enumerate(self.entries):
            if enabled:
                x=(index % self.columns())*self.CELL+3
                y=(index // self.columns())*self.CELL+3
                background = QColor(color)
                painter.fillRect(x,y,self.TILE,self.TILE,background)
                pixmap=icon_pixmap(icon) if icon else None
                has_image=pixmap is not None and not pixmap.isNull()
                if has_image:
                    painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform,True)
                    painter.drawPixmap(QRect(x,y,self.TILE,self.TILE),pixmap,pixmap.rect())
                if remaining is not None:
                    font = QFont('Segoe UI'); font.setWeight(QFont.Weight(self.countdown_weight))
                    font.setPixelSize(self.countdown_size or max(7,round(self.TILE*0.8)))
                    painter.setFont(font)
                    luminance = 0.2126*background.redF()+0.7152*background.greenF()+0.0722*background.blueF()
                    if has_image:
                        painter.setRenderHint(QPainter.RenderHint.Antialiasing,True)
                        font.setPixelSize(self.countdown_size or max(8,round(self.TILE*1.05)))
                        path=QPainterPath()
                        path.addText(0,0,font,str(remaining))
                        center=path.boundingRect().center()
                        path.translate(x+self.TILE/2-center.x(),y+self.TILE/2-center.y())
                        outline=QPen(QColor('#000000'),max(2,min(3,self.TILE/8)))
                        outline.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
                        # Fill after the outline so the stroke never covers the white interior.
                        painter.strokePath(path,outline)
                        painter.fillPath(path,QColor('#FFFFFF'))
                    else:
                        painter.setPen(QColor('#000000' if luminance > 0.55 else '#FFFFFF'))
                        painter.drawText(QRect(x,y,self.TILE,self.TILE),Qt.AlignmentFlag.AlignCenter,str(remaining))

    def resizeEvent(self,event):
        super().resizeEvent(event); self.updateGeometry()

    def mouseMoveEvent(self,event):
        index=int(event.position().y())//self.CELL*self.columns()+int(event.position().x())//self.CELL
        if 0 <= index < len(self.entries):
            code,name,color,enabled,remaining,icon=self.entries[index]
            self.setToolTip(f'{name} · {code}\n{"효과 이미지" if icon else color} · {"발생 중" if enabled else "현재 없음"}')
        else: self.setToolTip('')


class HpBar(QWidget):
    def __init__(self,parent=None, ticks=False):
        super().__init__(parent); self.ratio=None; self.ticks=ticks; self.tick_interval=5 if ticks else 0; self.setFixedHeight(6)

    def set_tick_interval(self,percent):
        if percent not in (0,5,10,20):raise ValueError('HP 구분선 간격은 없음, 5%, 10%, 20% 중에서 선택하세요.')
        self.tick_interval=percent;self.ticks=percent>0;self.update()

    def set_hp(self,state):
        hp=state.hp if state else None; maximum=state.max_hp if state else None
        if isinstance(hp,int) and hp>=0 and isinstance(maximum,int) and maximum>0:
            self.ratio=max(0,min(1,hp/maximum))
            self.setToolTip(f'HP {hp:,} / {maximum:,} · {self.ratio:.1%}')
        elif isinstance(hp,int) and hp>=0:
            self.ratio=None
            self.setToolTip(f'현재 HP {hp:,} · 최대 HP 수신 대기')
        else:
            self.ratio=None; self.setToolTip('현재 HP·최대 HP 수신 대기')
        self.update()

    def paintEvent(self,event):
        painter=QPainter(self)
        if self.ratio is not None:
            painter.fillRect(0,0,round(self.width()*self.ratio),self.height(),QColor('#FE2B2B'))
        if self.ticks:
            for percent in range(self.tick_interval,100,self.tick_interval):
                painter.fillRect(round(self.width()*percent/100),0,1,self.height(),QColor('#697180'))


class DragHeader(QWidget):
    def __init__(self,parent): super().__init__(parent); self.offset=None

    def mousePressEvent(self,event):
        if event.button()==Qt.MouseButton.LeftButton:
            self.offset=event.globalPosition().toPoint()-self.window().pos()

    def mouseMoveEvent(self,event):
        if self.offset is not None and event.buttons() & Qt.MouseButton.LeftButton:
            self.window().move(event.globalPosition().toPoint()-self.offset)

    def mouseReleaseEvent(self,event): self.offset=None


class CornerResizeGrip(QWidget):
    def __init__(self,parent,left,top):
        super().__init__(parent);self.left=left;self.top=top;self.drag=None
        self.setFixedSize(10,10)
        self.setCursor(Qt.CursorShape.SizeFDiagCursor if left==top else Qt.CursorShape.SizeBDiagCursor)
        self.setToolTip('드래그하여 창 크기 조절')

    def mousePressEvent(self,event):
        if event.button()==Qt.MouseButton.LeftButton:
            self.drag=(event.globalPosition().toPoint(),self.parentWidget().geometry())
            event.accept()

    def mouseMoveEvent(self,event):
        if self.drag is None: return
        start,original=self.drag;delta=event.globalPosition().toPoint()-start
        window=self.parentWidget();rect=QRect(original)
        if self.left: rect.setLeft(min(original.right()-window.minimumWidth()+1,original.left()+delta.x()))
        else: rect.setRight(max(original.left()+window.minimumWidth()-1,original.right()+delta.x()))
        if self.top: rect.setTop(min(original.bottom()-window.minimumHeight()+1,original.top()+delta.y()))
        else: rect.setBottom(max(original.top()+window.minimumHeight()-1,original.bottom()+delta.y()))
        window.setGeometry(rect);event.accept()

    def mouseReleaseEvent(self,event):
        if event.button()==Qt.MouseButton.LeftButton and self.drag is not None:
            self.drag=None
            window=self.parentWidget();window.sizeCommitted.emit(window.width(),window.height())
            event.accept()

    def paintEvent(self,event):
        painter=QPainter(self);painter.setPen(QColor('#68788E'))
        # A small mark makes each corner's drag handle discoverable.
        x=2 if self.left else 7;y=2 if self.top else 7
        painter.drawLine(x,y,x+(4 if self.left else -4),y)
        painter.drawLine(x,y,x,y+(4 if self.top else -4))


class HeaderButton(QPushButton):
    def __init__(self,text,parent=None):
        super().__init__(text,parent);self.setFixedSize(18,18)

    def paintEvent(self,event):
        painter=QPainter(self);painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.underMouse() or self.isDown():
            painter.setPen(Qt.PenStyle.NoPen);painter.setBrush(QColor('#283244'))
            painter.drawRoundedRect(QRectF(self.rect()),4,4)
        font=QFont('Segoe UI Symbol');font.setPixelSize(15);font.setBold(True)
        path=QPainterPath();path.addText(0,0,font,self.text())
        center=path.boundingRect().center();path.translate(self.width()/2-center.x(),self.height()/2-center.y())
        painter.fillPath(path,QColor('#CBD5E1'))


class RecordButton(HeaderButton):
    def paintEvent(self,event):
        painter=QPainter(self);painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(Qt.PenStyle.NoPen)
        if self.underMouse() or self.isDown():
            painter.setBrush(QColor('#283244'));painter.drawRoundedRect(QRectF(self.rect()),4,4)
        painter.setBrush(QColor('#EF4444'))
        if self.text() == '■':painter.drawRect(QRectF(4,4,10,10))
        else:painter.drawEllipse(QRectF(3,3,12,12))


class SpeakerButton(QPushButton):
    def __init__(self,parent=None):
        super().__init__(parent);self.setFixedSize(18,18);self.setCheckable(True)
        self.setChecked(True);self.toggled.connect(self.update_state);self.update_state(True)

    def update_state(self,enabled):
        self.setToolTip('소리 켜짐 · 누르면 음소거' if enabled else '음소거 · 누르면 소리 켜기')
        self.setAccessibleName('소리 켜짐' if enabled else '음소거');self.update()

    def paintEvent(self,event):
        super().paintEvent(event)
        painter=QPainter(self);painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        color=QColor('#CBD5E1' if self.isChecked() else '#F87171')
        painter.setPen(Qt.PenStyle.NoPen);painter.setBrush(color)
        painter.drawPolygon(QPolygonF([QPointF(2,7),QPointF(5,7),QPointF(9,4),QPointF(9,14),QPointF(5,11),QPointF(2,11)]))
        painter.setBrush(Qt.BrushStyle.NoBrush);painter.setPen(QPen(color,1.4))
        if self.isChecked():
            painter.drawArc(QRectF(7,5,7,8),-60*16,120*16)
            painter.drawArc(QRectF(7,2,10,14),-60*16,120*16)
        else:
            painter.drawLine(QPointF(12,6),QPointF(16,12))
            painter.drawLine(QPointF(16,6),QPointF(12,12))


class ClickThroughDisplay(QWidget):
    """Separate native display surface; the control window has no body region."""
    def __init__(self,monitor):
        super().__init__(monitor,Qt.WindowType.Tool | Qt.WindowType.FramelessWindowHint |
                         Qt.WindowType.WindowStaysOnTopHint | Qt.WindowType.WindowTransparentForInput |
                         Qt.WindowType.WindowDoesNotAcceptFocus)
        self.monitor=monitor
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating)

    def paintEvent(self,event):
        image=QImage(self.monitor.size(),QImage.Format.Format_ARGB32_Premultiplied)
        image.fill(Qt.GlobalColor.transparent)
        self.monitor.render(image,QPoint(),QRegion(),QWidget.RenderFlag.DrawWindowBackground |
                            QWidget.RenderFlag.DrawChildren | QWidget.RenderFlag.IgnoreMask)
        painter=QPainter(self);painter.drawImage(0,0,image)


class CompactPreview(QWidget):
    manageRequested=pyqtSignal()
    exitRequested=pyqtSignal()
    sizeCommitted=pyqtSignal(int,int)
    backgroundOpacityChanged=pyqtSignal(int)
    soundEnabledChanged=pyqtSignal(bool)
    recordingRequested=pyqtSignal()

    def closeEvent(self,event):
        self.exitRequested.emit();event.accept()

    def __init__(self):
        super().__init__(None,Qt.WindowType.Window | Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.background_opacity=100
        self.sample_effect=None
        self.setWindowTitle('AION2 · 작은 모니터'); self.setObjectName('compact')
        self.setMinimumSize(220,110);self.resize(260,128)
        self.resize_grips=[CornerResizeGrip(self,left,top) for left,top in ((True,True),(False,True),(True,False),(False,False))]
        font=QFont('Malgun Gothic');font.setPixelSize(11)
        self.setFont(font)
        self.setStyleSheet('''
            QWidget#compact {background:transparent;border:0;}
            QLabel {color:#D6DDE8;font-family:"Malgun Gothic";font-size:11px;font-weight:600;background:transparent;border:0;}
            QLabel#title {color:#CBD5E1;font-size:11px;font-weight:700;}
            QLabel#group {color:#F1F5F9;font-weight:700;}
            QPushButton {color:#94A3B8;background:transparent;border:0;border-radius:4px;font-size:12px;}
            QPushButton:hover {background:#283244;color:#FFFFFF;}
            QFrame#groupbox {background:transparent;border:0;}
            QSlider {background:transparent;}
            QSlider::groove:horizontal {height:3px;background:#64748B;border-radius:1px;}
            QSlider::handle:horizontal {width:9px;margin:-4px 0;background:#CBD5E1;border-radius:4px;}
        ''')
        layout=QVBoxLayout(self);layout.setContentsMargins(8,6,8,3);layout.setSpacing(5)
        header=DragHeader(self);self.header=header;bar=QHBoxLayout(header);bar.setContentsMargins(0,0,0,0);bar.setSpacing(4)
        self.opacity_slider=QSlider(Qt.Orientation.Horizontal);self.opacity_slider.setRange(0,100)
        self.opacity_slider.setValue(100);self.opacity_slider.setFixedWidth(48)
        self.opacity_slider.setAccessibleName('배경 불투명도');self.opacity_slider.valueChanged.connect(self.change_background_opacity)
        self.opacity_slider.setToolTip('배경 불투명도 100% · 왼쪽으로 이동하면 배경만 투명해집니다')
        bar.addWidget(self.opacity_slider)
        self.sound_button=SpeakerButton();self.sound_button.toggled.connect(self.soundEnabledChanged)
        bar.addWidget(self.sound_button)
        self.record_button=RecordButton('●')
        self.record_button.clicked.connect(self.recordingRequested);bar.addWidget(self.record_button)
        self.set_recording(False);bar.addStretch()
        self.sample_stop_button=HeaderButton('↩')
        self.sample_stop_button.setToolTip('미리 표시 해제 · 실제 감지 화면으로 돌아가기')
        self.sample_stop_button.setAccessibleName('미리 표시 해제')
        self.sample_stop_button.clicked.connect(self.stop_sample)
        self.sample_stop_button.hide();bar.addWidget(self.sample_stop_button)
        settings=HeaderButton('⚙');settings.setToolTip('설정')
        settings.setStyleSheet('font-family: Segoe UI Symbol; font-size:15px;');settings.setAccessibleName('설정')
        settings.clicked.connect(self.manageRequested);bar.addWidget(settings)
        self.minimize_button=HeaderButton('−')
        self.minimize_button.setToolTip('최소화');self.minimize_button.setAccessibleName('최소화')
        self.minimize_button.clicked.connect(self.showMinimized);bar.addWidget(self.minimize_button)
        close=HeaderButton('×');close.setToolTip('미리보기 닫기');close.clicked.connect(self.close);bar.addWidget(close)
        layout.addWidget(header)
        groups=QHBoxLayout();groups.setSpacing(6);layout.addLayout(groups,1)
        self.own_label,self.own_hp,self.own_panel=self.make_group(groups,'나')
        self.target_label,self.target_hp,self.target_panel=self.make_group(groups,'대상')
        self.target_label.icon_size=26;self.target_label.setFixedHeight(26)
        self.own_label.setFixedHeight(26)
        self.target_counts=QLabel('회피·막기: 0%')
        self.target_counts.setStyleSheet('color:#A8B5C7;font-size:10px;font-weight:600;')
        self.target_counts.setToolTip('내 직접 공격 전체 판정(회피·막기 포함) 중 회피·막기의 비율. 대상 변경 또는 감지 초기화 시 초기화됩니다.')
        self.target_label.parentWidget().layout().addWidget(self.target_counts)
        footer=QHBoxLayout();footer.setContentsMargins(0,0,0,0)
        footer.addStretch()
        self.combat_time=QLabel('전투 00:00');self.combat_time.setFixedWidth(96)
        self.combat_time.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        self.combat_time.setStyleSheet('color:#B6F0E6;font-size:11px;font-weight:700;')
        footer.addWidget(self.combat_time);layout.addLayout(footer)
        self.clickthrough_display=None
        # Native Windows surfaces provide cross-process click-through, including games.
        if QApplication.platformName()=='windows':self.clickthrough_display=ClickThroughDisplay(self)
        self.position_grips()

    def interaction_region(self):
        region=QRegion(self.header.geometry())
        for grip in self.resize_grips:region=region.united(QRegion(grip.geometry()))
        return region

    def sync_clickthrough_display(self):
        display=getattr(self,'clickthrough_display',None)
        if display is None:return
        controls=self.interaction_region()
        self.setMask(controls)
        display.setGeometry(QRect(self.mapToGlobal(QPoint(0,0)),self.size()))
        display.setMask(QRegion(self.rect()).subtracted(controls))
        if self.isVisible() and not self.isMinimized():
            display.show();display.update()
        else:display.hide()

    def showEvent(self,event):
        super().showEvent(event);self.layout().activate();self.sync_clickthrough_display()

    def hideEvent(self,event):
        display=getattr(self,'clickthrough_display',None)
        if display is not None:display.hide()
        super().hideEvent(event)

    def moveEvent(self,event):
        super().moveEvent(event);self.sync_clickthrough_display()

    def changeEvent(self,event):
        super().changeEvent(event)
        if event.type()==QEvent.Type.WindowStateChange:self.sync_clickthrough_display()

    def change_background_opacity(self,value):
        self.background_opacity=value
        self.opacity_slider.setToolTip(f'배경 불투명도 {value}% · 왼쪽으로 이동하면 배경만 투명해집니다')
        self.update();self.sync_clickthrough_display();self.backgroundOpacityChanged.emit(value)

    def set_recording(self,active):
        self.record_button.setText('■' if active else '●')
        label='로그 수집 중지·저장' if active else '로그 수집 시작'
        self.record_button.setToolTip(label);self.record_button.setAccessibleName(label)

    def set_sound_enabled(self,enabled):
        self.sound_button.blockSignals(True);self.sound_button.setChecked(enabled);self.sound_button.blockSignals(False)
        self.sound_button.update_state(enabled)

    def set_background_opacity(self,value):
        self.opacity_slider.blockSignals(True);self.opacity_slider.setValue(value);self.opacity_slider.blockSignals(False)
        self.background_opacity=value
        self.opacity_slider.setToolTip(f'배경 불투명도 {value}% · 왼쪽으로 이동하면 배경만 투명해집니다')
        self.update();self.sync_clickthrough_display()

    def paintEvent(self,event):
        painter=QPainter(self);painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        # Paint backgrounds once on the translucent window, independently of children.
        painter.setCompositionMode(QPainter.CompositionMode.CompositionMode_Source)
        alpha=round(self.background_opacity*255/100)
        def rounded(rect,fill,border,radius):
            color=QColor(fill);color.setAlpha(alpha);painter.setBrush(color)
            line=QColor(border);line.setAlpha(alpha);painter.setPen(QPen(line,1))
            painter.drawRoundedRect(QRectF(rect).adjusted(.5,.5,-.5,-.5),radius,radius)
        rounded(self.rect(),'#10141C','#303A4A',8)
        for frame in self.findChildren(QFrame):
            if frame.objectName()=='groupbox':
                rect=QRect(frame.mapTo(self,frame.rect().topLeft()),frame.size())
                rounded(rect,'#171C25','#283244',5)
        for hp in (self.own_hp,self.target_hp):
            color=QColor('#000000');color.setAlpha(alpha)
            painter.fillRect(QRect(hp.mapTo(self,hp.rect().topLeft()),hp.size()),color)

    def position_grips(self):
        for grip in self.resize_grips:
            grip.move(0 if grip.left else self.width()-grip.width(),0 if grip.top else self.height()-grip.height())
            grip.raise_()

    def resizeEvent(self,event):
        super().resizeEvent(event)
        if hasattr(self,'resize_grips'): self.position_grips()
        if hasattr(self,'header'):
            self.layout().activate();self.sync_clickthrough_display()

    def make_group(self,layout,title):
        frame=QFrame();frame.setObjectName('groupbox')
        frame.setMinimumWidth(0);frame.setSizePolicy(QSizePolicy.Policy.Ignored,QSizePolicy.Policy.Expanding)
        inner=QVBoxLayout(frame)
        inner.setContentsMargins(6,5,6,5);inner.setSpacing(3)
        label=ElidedLabel(title);label.setObjectName('group');inner.addWidget(label)
        hp=HpBar(ticks=title=='나');inner.addWidget(hp)
        panel=SwatchPanel();inner.addWidget(panel,1);layout.addWidget(frame,1)
        return label,hp,panel

    def stop_sample(self):
        self.sample_effect=None;self.sample_stop_button.hide()
        if hasattr(self,'last_refresh'):self.refresh(*self.last_refresh)

    def refresh(self,catalog,states,now=None):
        import time
        if now is None: now=time.time()
        self.last_refresh=(catalog,states,now)
        own,target=preview_entries(catalog,states,now)
        if self.sample_effect is not None:
            sample=self.sample_effect;config=sample['config'];code=sample['code']
            entry=(code,sample['name'],config.get('color') or '#64748B',True,None,
                   effect_icon(code) if config.get('display_mode','image')=='image' else None)
            own=[entry] if config.get('own',True) else []
            target=[entry] if config.get('target',True) else []
        self.own_panel.set_entries(own);self.target_panel.set_entries(target)
        own_state=states.actors.get(states.owner_key)
        self.own_hp.set_hp(own_state)
        self.own_label.setText('나' + (' · '+own_state.nickname if own_state and own_state.nickname else ' · 감지 대기'))
        self.own_label.setToolTip(self.own_label.text())
        key=states.attack_target_key
        target_state=states.actors.get(key)
        self.target_hp.set_hp(target_state)
        name=target_state.nickname if target_state and target_state.nickname else '이름 미확인'
        job=target_state.job_name if target_state and target_state.mob_code is None else ''
        self.target_label.set_icon(job_icon(job))
        self.target_label.setText(name if key else '대상 · 감지 대기')
        self.target_label.setToolTip(f'{name}'+(f' · {job}' if job else '')+f' · ID {key[1]}' if key else '')
        if self.sample_effect is not None:
            self.own_label.setText('나 · 미리 표시');self.own_label.setToolTip(self.sample_effect['name'])
            self.target_label.set_icon(None)
            self.target_label.setText('대상 · 미리 표시');self.target_label.setToolTip(self.sample_effect['name'])
        counts=states.attack_counts if key else {}
        total=counts.get('전체',0)
        avoided=counts.get('회피',0)+counts.get('막기',0)
        rate=100*avoided/total if total else 0
        # Keep a nonzero rate visible even when it would round to zero.
        percentage=f'{rate:.0f}' if rate>=1 or not avoided else '<1'
        self.target_counts.setText(f'회피·막기: {percentage}%')
        color='#F87171' if avoided else '#A8B5C7'
        self.target_counts.setStyleSheet(f'color:{color};font-size:10px;font-weight:600;')
        self.target_counts.setToolTip(f"내 직접 공격 총 {total}회 · 회피 {counts.get('회피',0)}회 · 막기 {counts.get('막기',0)}회\n회피·막기도 전체 판정에 포함합니다. 대상 변경 또는 감지 초기화 시 초기화됩니다.")
        clock=states.combat_clocks.get(key)
        elapsed=clock.text(now,target_state) if clock and target_state else '00:00'
        self.combat_time.setText('전투 '+elapsed)
        self.combat_time.setToolTip('공격 대상의 첫 데미지부터 계산한 전투시간')
        display=getattr(self,'clickthrough_display',None)
        if display is not None:display.update()
