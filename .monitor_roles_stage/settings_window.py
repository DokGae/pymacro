import json
from PyQt6.QtCore import Qt,QTimer
from PyQt6.QtWidgets import (QDialog,QHBoxLayout,QVBoxLayout,QListWidget,QStackedWidget,
    QWidget,QLabel,QSpinBox,QFormLayout,QPushButton,QMessageBox,QCheckBox,QComboBox,
    QButtonGroup,QScrollArea,QSlider,QLineEdit)
from effect_manager import EffectManager
from preset_panel import PresetPanel
from packetcore.analysis import save_json
from status_label import StatusLabel

LOG_ANALYSIS_ITEMS = (
    ('log_effects', '효과', '버프·디버프의 적용, 갱신, 해제를 기록합니다.'),
)


def load_ui(path):
    defaults=dict(tile_size=16,countdown_font_size=0,countdown_font_weight=700,show_combat_time=True,show_attack_rate=True,target_idle_seconds=10,window_width=260,window_height=128,settings_width=1080,settings_height=700,speech_enabled=True,speech_voice='',speech_volume=80,speech_rate=0,background_opacity=100)
    defaults.update(log_effects=True,log_own=True,log_target=True)
    defaults.update(own_hp_tick_interval=5,target_hp_tick_interval=0)
    defaults.update(tcp_port=47653,tcp_source='leesangjin-monitor',tcp_hp_enabled=True,tcp_hp_name='내HP')
    if not path.exists(): return defaults
    data=json.loads(path.read_text(encoding='utf-8'))
    defaults.update(data)
    for key in ('own_hp_tick_interval','target_hp_tick_interval'):
        if type(defaults[key]) is not int or defaults[key] not in (0,5,10,20,50):
            defaults[key]=5 if key.startswith('own_') else 0
    defaults['target_idle_seconds']=max(1,min(300,int(data.get('target_idle_seconds',10))))
    defaults['tile_size']=max(8,min(32,int(data.get('tile_size',16))))
    defaults['countdown_font_size']=max(0,min(48,int(data.get('countdown_font_size',0))))
    if defaults['countdown_font_weight'] not in (400,500,600,700,800,900):
        defaults['countdown_font_weight']=700
    defaults['window_width']=max(220,int(data.get('window_width',260)))
    defaults['window_height']=max(110,int(data.get('window_height',128)))
    for key,minimum,maximum in (('settings_width',800,10000),('settings_height',650,10000),('speech_volume',0,100),('speech_rate',-10,10),('background_opacity',0,100)):
        defaults[key]=max(minimum,min(maximum,int(defaults[key])))
    defaults['speech_enabled']=bool(defaults['speech_enabled'])
    defaults['tcp_port']=max(1024,min(65535,int(data.get('tcp_port',47653))))
    source=defaults.get('tcp_source')
    if not isinstance(source,str) or not source.strip() or len(source)>200 or any(ord(c)<32 for c in source):
        defaults['tcp_source']='leesangjin-monitor'
    if not isinstance(defaults['speech_voice'],str): defaults['speech_voice']=''
    from tcp_state_server import hp_settings
    try:defaults.update(hp_settings(defaults))
    except (ValueError,AttributeError):defaults.update(tcp_hp_enabled=True,tcp_hp_name='내HP')
    return defaults


class SettingsSection(QWidget):
    def __init__(self,title,description,entries,parent=None):
        super().__init__(parent);self.entries=entries
        layout=QVBoxLayout(self);layout.setContentsMargins(16,10,16,10);layout.setSpacing(14)
        heading=QLabel(title);heading.setStyleSheet('font-size:23px;font-weight:700;');layout.addWidget(heading)
        note=QLabel(description);note.setWordWrap(True);layout.addWidget(note)
        tabs=QHBoxLayout();tabs.setSpacing(8);layout.addLayout(tabs)
        self.buttons=QButtonGroup(self);self.stack=QStackedWidget();self.indices=[]
        for index,(label,widget,callback) in enumerate(entries):
            button=QPushButton(label);button.setCheckable(True);tabs.addWidget(button);self.buttons.addButton(button,index)
            page=self.stack.indexOf(widget)
            if page<0:page=self.stack.addWidget(widget)
            self.indices.append(page)
        tabs.addStretch();layout.addWidget(self.stack,1)
        self.buttons.idClicked.connect(self.select);self.select(0)

    def select(self,index):
        self.buttons.button(index).setChecked(True);self.stack.setCurrentIndex(self.indices[index])
        callback=self.entries[index][2]
        if callback:callback()


class SettingsWindow(QDialog):
    def __init__(self,controller):
        super().__init__();self.controller=controller
        self.setWindowTitle('작은 모니터 · 설정');self.resize(controller.ui['settings_width'],controller.ui['settings_height'])
        self.resize_timer=QTimer(self);self.resize_timer.setSingleShot(True);self.resize_timer.timeout.connect(self.save_size)
        self.setStyleSheet("""QDialog,QWidget {background:#F5F7F2;color:#263527;font-family:"Malgun Gothic";font-size:12px;}
            QListWidget {background:#EAF0E3;border:0;padding:10px;} QListWidget::item {padding:16px;border-radius:6px;}
            QListWidget::item:selected {background:#D8E3CD;color:#34482E;}
            QLineEdit,QSpinBox,QComboBox,QTableView {background:white;border:1px solid #CDD7C5;border-radius:4px;padding:4px;}
            QPushButton {background:#EAF0E5;border:1px solid #CDD7C5;border-radius:5px;padding:8px 12px;}
            QPushButton:hover {background:#DDE7D5;} QPushButton:checked {background:#536849;color:white;border-color:#536849;}
            QScrollArea {border:0;}""")
        root=QVBoxLayout(self);root.setContentsMargins(12,12,12,12)
        top=QLabel('작은 모니터  /  환경설정');top.setStyleSheet('font-size:15px;font-weight:700;padding:6px;');root.addWidget(top)
        body=QHBoxLayout();root.addLayout(body,1)
        self.nav=QListWidget();self.nav.addItems(['효과 관리','모니터 표시','소리·음성','로그분석','외부 연결']);self.nav.setFixedWidth(165);body.addWidget(self.nav)
        self.pages=QStackedWidget();body.addWidget(self.pages,1)
        observed={e['code'] for state in controller.states.actors.values() for e in state.effects.values()}
        self.effects=EffectManager(controller.catalog,observed,self);self.effects.setWindowFlags(Qt.WindowType.Widget)
        self.effects.changed.connect(controller.refresh);self.effects.speechPreview.connect(self.preview_speech)
        self.effects.monitorPreview.connect(controller.set_monitor_preview)
        self.effects.tcpPreview.connect(controller.set_tcp_preview)
        for button in self.effects.findChildren(QPushButton):
            if button.text()=='닫기':button.hide()
        self.preset_panel=PresetPanel(controller,self.effects,self)
        self.preset_panel.layout().removeWidget(self.effects)
        self.preset_panel.layout().addStretch()
        self.effect_section=SettingsSection('효과 관리','변경한 셀은 노란색으로 표시됩니다. 여러 효과를 수정한 뒤 전체 변경 저장을 누르세요.',[
            ('효과 선택',self.effects,lambda:self.effects.select_settings_section('select')),
            ('표시·정렬',self.effects,lambda:self.effects.select_settings_section('display')),
            ('음성 알림',self.effects,lambda:self.effects.select_settings_section('speech')),
            ('프리셋·공유',self.preset_panel,None),
            ('통신 전송',self.effects,lambda:self.effects.select_settings_section('tcp'))])
        self.pages.addWidget(self.effect_section)

        size_page,size_layout=self.form_page('크기·글씨','버프 아이콘과 남은시간 글씨를 조절합니다. 변경한 값은 모니터에서 바로 확인할 수 있습니다.')
        form=QFormLayout();size_layout.addLayout(form)
        self.size=QSpinBox();self.size.setRange(8,32);self.size.setSuffix(' px');self.size.setValue(controller.ui['tile_size']);form.addRow('버프·효과 네모 크기',self.size)
        self.countdown_size=QSpinBox();self.countdown_size.setRange(0,48);self.countdown_size.setSuffix(' px');self.countdown_size.setSpecialValueText('자동 (효과 크기에 맞춤)');self.countdown_size.setValue(controller.ui['countdown_font_size']);form.addRow('남은시간 글씨 크기',self.countdown_size)
        self.countdown_weight=QComboBox()
        for label,weight in (('보통',400),('중간',500),('약간 굵게',600),('굵게',700),('더 굵게',800),('가장 굵게',900)):self.countdown_weight.addItem(label,weight)
        self.countdown_weight.setCurrentIndex(self.countdown_weight.findData(controller.ui['countdown_font_weight']));form.addRow('남은시간 글씨 두께',self.countdown_weight)
        self.size.valueChanged.connect(self.preview_size);self.countdown_size.valueChanged.connect(self.preview_countdown_font);self.countdown_weight.currentIndexChanged.connect(self.preview_countdown_font)
        size_layout.addStretch()
        target_page,target_layout=self.form_page('대상·전투','공격 중인 대상의 표시와 감지 대기 시간을 설정합니다.')
        form=QFormLayout();target_layout.addLayout(form)
        self.target_idle=QSpinBox();self.target_idle.setRange(1,300);self.target_idle.setSuffix(' 초');self.target_idle.setValue(controller.ui['target_idle_seconds']);form.addRow('공격 대상 감지 대기로 전환',self.target_idle)
        self.show_attack_rate=QCheckBox('대상창 아래 회피·막기 비율 표시');self.show_attack_rate.setChecked(controller.ui['show_attack_rate']);form.addRow(self.show_attack_rate);self.show_attack_rate.toggled.connect(self.preview_attack_rate)
        target_layout.addWidget(QLabel('내 마지막 공격 이후 지정한 시간 동안 공격하지 않으면 감지 대기로 돌아갑니다.\n플레이어 직업이 확인되면 대상 이름 옆에 직업 아이콘을 표시합니다.'));target_layout.addStretch()
        background_page,background_layout=self.form_page('배경·조작','투명도를 바꿔도 글씨·버프·HP 막대는 선명하게 유지됩니다.')
        form=QFormLayout();background_layout.addLayout(form)
        self.background_slider=QSlider(Qt.Orientation.Horizontal);self.background_slider.setRange(0,100);self.background_slider.setValue(controller.ui['background_opacity']);form.addRow('배경 불투명도',self.background_slider)
        self.background_slider.valueChanged.connect(self.preview_background)
        controller.preview.backgroundOpacityChanged.connect(self.sync_background_slider)
        background_layout.addWidget(QLabel('왼쪽: 배경 투명 / 오른쪽: 배경 불투명\n투명도는 자동 저장됩니다.\n\n창 이동: 위쪽 빈 영역을 드래그\n창 크기: 네 모서리를 드래그\n버프·HP·전투시간 영역은 게임으로 클릭 통과\n위쪽 버튼과 슬라이더는 계속 조작 가능'));background_layout.addStretch()
        log_page,log_layout=self.form_page('로그분석','분석할 항목과 수집 대상을 선택하세요. 상단 스피커 오른쪽 ● 버튼으로 시작하고 ■ 버튼으로 중지·저장합니다.')
        self.log_checks={}
        log_layout.addWidget(QLabel('분석 항목'))
        for key,label,description in LOG_ANALYSIS_ITEMS:
            check=QCheckBox(label);check.setToolTip(description);check.setChecked(controller.ui.get(key,True));self.log_checks[key]=check;log_layout.addWidget(check)
        log_layout.addWidget(QLabel('수집 대상'))
        for key,label in (('log_own','나'),('log_target','대상 (현재 공격 대상)')):
            check=QCheckBox(label);check.setChecked(controller.ui.get(key,True));self.log_checks[key]=check;log_layout.addWidget(check)
        log_note=QLabel('화면 표시 여부와 관계없이 모든 효과의 적용·갱신·해제를 기록합니다.\n수집 대상 설정은 다음 수집 시작부터 적용됩니다.\n프로그램 폴더의 log에 ID·직업별 텍스트 파일을 저장합니다.\n시전자·이름·직업은 패킷에서 확인된 정보만 기록합니다.');log_note.setWordWrap(True);log_layout.addWidget(log_note)
        folder=QPushButton('저장된 로그 열기');folder.clicked.connect(controller.open_log_folder);log_layout.addWidget(folder);log_layout.addStretch()
        tcp_page,tcp_layout=self.form_page('외부 프로그램 연결','TCP 소켓 상태 통신을 지원하는 프로그램과 같은 PC에서 자동 연결합니다.')
        tcp_layout.addWidget(QLabel('연결 주소: 127.0.0.1\n실제 감지한 효과만 전송합니다. 미리 표시는 전송하지 않습니다.'))
        tcp_form=QFormLayout();tcp_layout.addLayout(tcp_form)
        self.tcp_port=QSpinBox();self.tcp_port.setRange(1024,65535);self.tcp_port.setValue(controller.state_server.port)
        tcp_form.addRow('TCP 포트',self.tcp_port)
        self.tcp_source=QLineEdit(controller.state_server.source);self.tcp_source.setMaxLength(200);tcp_form.addRow('프로그램 ID (고정 이름)',self.tcp_source)
        tcp_apply=QPushButton('연결 설정 저장 · 다시 연결');tcp_apply.clicked.connect(self.save_tcp_port);tcp_layout.addWidget(tcp_apply)
        self.tcp_status=StatusLabel(controller.state_server.status);self.tcp_status.setWordWrap(True);tcp_layout.addWidget(self.tcp_status)
        tcp_note=QLabel('매크로 IF → 외부 프로그램 상태에서 같은 프로그램 ID와 포트를 입력하세요.\n내용 예: 내효과.123 / 대상효과.123 · 판정: 켜짐(참) / 꺼짐(거짓)\n효과의 화면 표시 여부와 관계없이 전송합니다. 감지 전이나 연결 끊김은 꺼짐으로 판단하지 않습니다.\n프로그램을 다시 켜면 자동 연결되며 현재 상태를 다시 보냅니다.')
        tcp_note.setWordWrap(True);tcp_layout.addWidget(tcp_note);tcp_layout.addStretch()
        hp_display_page,hp_display_layout=self.form_page('HP','HP 막대의 구분선 간격을 나와 대상 각각 설정합니다. 변경한 값은 모니터에 바로 반영됩니다.')
        hp_display_form=QFormLayout();hp_display_layout.addLayout(hp_display_form)
        self.hp_tick_combos={}
        for key,label,default in (('own_hp_tick_interval','내 HP 구분선 간격',5),('target_hp_tick_interval','대상 HP 구분선 간격',0)):
            combo=QComboBox()
            for text,value in (('없음',0),('5%',5),('10%',10),('20%',20),('50%',50)):combo.addItem(text,value)
            combo.setCurrentIndex(max(0,combo.findData(controller.ui.get(key,default))))
            self.hp_tick_combos[key]=combo;hp_display_form.addRow(label,combo)
            combo.currentIndexChanged.connect(self.preview_hp_ticks)
        hp_display_layout.addWidget(QLabel('5%: 20칸 · 10%: 10칸 · 20%: 5칸 · 50%: 2칸\n설정 저장을 누르면 다음 실행에도 유지됩니다.'));hp_display_layout.addStretch()
        self.monitor_section=SettingsSection('모니터 표시','크기, 글씨, 대상 표시와 배경을 조절합니다.',[
            ('크기·글씨',size_page,None),('대상·전투',target_page,None),('HP',hp_display_page,None),('배경·조작',background_page,None)])
        self.pages.addWidget(self.monitor_section)

        voice_page,voice_layout=self.form_page('목소리·음량','설치된 Windows 음성을 사용합니다. 미리 듣기로 목소리를 확인하세요.')
        form=QFormLayout();voice_layout.addLayout(form)
        self.speech_enabled=QCheckBox('게임 중 음성 알림 사용');self.speech_enabled.setChecked(controller.ui['speech_enabled']);form.addRow(self.speech_enabled)
        self.voice=QComboBox();self.voice.addItem('Windows 기본 목소리 (한국어 우선)','');form.addRow('음성 목소리',self.voice)
        self.volume=QSpinBox();self.volume.setRange(0,100);self.volume.setSuffix(' %');self.volume.setValue(controller.ui['speech_volume']);form.addRow('음성 음량',self.volume)
        self.rate=QSpinBox();self.rate.setRange(-10,10);self.rate.setValue(controller.ui['speech_rate']);form.addRow('읽는 속도 (-10 느림 / 10 빠름)',self.rate)
        voice_test=QPushButton('목소리 미리 듣기');voice_test.clicked.connect(lambda:self.preview_speech('음성 안내 테스트입니다.'));voice_layout.addWidget(voice_test);voice_layout.addStretch()
        condition_page,condition_layout=self.form_page('효과별 알림','효과마다 알림할 대상, 시점과 읽을 문구를 정할 수 있습니다.')
        condition_layout.addWidget(QLabel('① 효과를 선택합니다.\n② 음성 알림을 켜고 나만·대상만·둘 다를 고릅니다.\n③ 적용될 때 또는 종료 몇 초 전을 정합니다.\n④ 문구를 입력합니다. 여러 효과를 수정한 뒤 전체 변경 저장을 누릅니다.'))
        condition_button=QPushButton('효과별 음성 알림 설정으로 이동');condition_button.clicked.connect(lambda:self.navigate(0,2));condition_layout.addWidget(condition_button);condition_layout.addStretch()
        self.audio_section=SettingsSection('소리·음성','전체 음성 설정과 효과별 알림 조건을 관리합니다.',[('목소리·음량',voice_page,None),('효과별 알림',condition_page,None)])
        self.pages.addWidget(self.audio_section)
        self.log_section=SettingsSection('로그분석','분석할 항목과 수집 대상을 설정하고 저장된 로그를 열 수 있습니다.',[('분석 설정',log_page,None)])
        self.pages.addWidget(self.log_section)
        hp_page,hp_layout=self.form_page('내 HP 전송','현재 HP를 최대 HP 기준 0~100% 숫자로 계속 전송합니다.')
        self.hp_enabled=QCheckBox('내 HP를 통신으로 전송');self.hp_enabled.setChecked(controller.ui.get('tcp_hp_enabled',True));hp_layout.addWidget(self.hp_enabled)
        self.hp_name=QLineEdit(controller.ui.get('tcp_hp_name','내HP'));self.hp_name.setMaxLength(120)
        hp_form=QFormLayout();hp_form.addRow('내용 이름',self.hp_name);hp_layout.addLayout(hp_form)
        hp_save=QPushButton('HP 설정 저장');hp_save.clicked.connect(self.save_hp);hp_layout.addWidget(hp_save)
        self.hp_status=StatusLabel('HP 감지 대기');hp_layout.addWidget(self.hp_status)
        hp_note=QLabel('예: 현재 HP 250 / 최대 HP 1000 → 25 전송\n최대 HP 또는 현재 HP를 모르거나 게임 연결이 끊기면 false를 전송합니다.\n매크로 IF → 외부 프로그램 상태에서 같은 내용 이름을 선택하고, 이하 / 이상과 기준값(예: 30)을 입력하세요.\nfalse는 숫자가 아니므로 이하 / 이상 조건을 만족하지 않습니다. 내용 이름은 효과의 통신 내용 이름과 다르게 입력하세요.')
        hp_note.setWordWrap(True);hp_layout.addWidget(hp_note);hp_layout.addStretch()
        self.external_section=SettingsSection('외부 연결','외부 프로그램과 통신할 프로그램 ID와 TCP 포트를 설정합니다.',[('연결 설정',tcp_page,None),('HP',hp_page,None)])
        self.pages.addWidget(self.external_section)
        self.sections=[self.effect_section,self.monitor_section,self.audio_section,self.log_section,self.external_section]
        controller.speech.voicesChanged.connect(self.update_voices);self.update_voices(controller.speech.voices)
        self.nav.currentRowChanged.connect(self.pages.setCurrentIndex);self.nav.setCurrentRow(0)
        self.status=StatusLabel(controller.status);self.status.set_status(controller.status,controller.status_level);root.addWidget(self.status)
        footer=QHBoxLayout();root.addLayout(footer)
        hint=QLabel('노란 셀: 저장 전 변경  ·  저장하면 모니터에 적용됩니다.');footer.addWidget(hint);footer.addStretch()
        save=QPushButton('전체 설정 저장');save.clicked.connect(self.save_ui);footer.addWidget(save)
        close=QPushButton('닫기');close.clicked.connect(self.close);footer.addWidget(close)

    def form_page(self,title,description):
        scroll=QScrollArea();scroll.setWidgetResizable(True)
        widget=QWidget();layout=QVBoxLayout(widget);layout.setContentsMargins(8,12,8,12);layout.setSpacing(18)
        heading=QLabel(title);heading.setStyleSheet('font-size:16px;font-weight:700;');layout.addWidget(heading)
        note=QLabel(description);note.setWordWrap(True);layout.addWidget(note)
        scroll.setWidget(widget);return scroll,layout

    def save_tcp_port(self):
        from tcp_state_server import StateServer
        port=self.tcp_port.value()
        try:
            replacement=StateServer(port,self.tcp_source.text().strip())
            settings=dict(self.controller.ui,tcp_port=port,tcp_source=replacement.source)
            save_json(self.controller.ui_path,settings)
            self.controller.ui=settings
            self.apply_tcp_server(replacement)
            self.tcp_status.setText('포트와 프로그램 ID를 저장했습니다. 매크로에서도 같은 값을 사용하세요.')
        except (OSError,ValueError) as exc:self.tcp_status.setText('연결 설정 저장 실패: '+str(exc))

    def hp_values(self):
        from tcp_state_server import hp_settings
        config=hp_settings(dict(tcp_hp_enabled=self.hp_enabled.isChecked(),tcp_hp_name=self.hp_name.text()))
        name=config['tcp_hp_name']
        if any(channel[1]==name for code,item in self.controller.catalog.preview.items() for channel in self.controller.catalog.tcp_channels(code,item)) or name.startswith(('내효과.','대상효과.')):
            raise ValueError('HP 내용 이름이 효과 통신 이름과 겹칩니다. 다른 이름을 입력하세요.')
        return config

    def save_hp(self):
        try:
            settings=dict(self.controller.ui,**self.hp_values())
            save_json(self.controller.ui_path,settings);self.controller.ui=settings
            self.controller.refresh();self.status.setText('HP 통신 설정을 저장했습니다.')
        except (OSError,ValueError) as exc:self.hp_status.setText('HP 설정 저장 실패: '+str(exc))

    def apply_tcp_server(self,replacement):
        current=self.controller.state_server
        if (current.port,current.source)==(replacement.port,replacement.source):return
        running=bool(current._thread and current._thread.is_alive())
        current.stop();self.controller.state_server=replacement
        self.controller.refresh()
        if running:replacement.start()

    def navigate(self,category,tab):
        self.nav.setCurrentRow(category);self.sections[category].select(tab)

    def preview_background(self,value):
        self.controller.preview.opacity_slider.setValue(value)

    def sync_background_slider(self,value):
        self.background_slider.blockSignals(True);self.background_slider.setValue(value);self.background_slider.blockSignals(False)

    def preview_size(self,value):
        self.controller.ui['tile_size']=value;self.controller.apply_ui()

    def preview_hp_ticks(self,_):
        self.controller.ui.update({key:combo.currentData() for key,combo in self.hp_tick_combos.items()})
        self.controller.apply_ui()

    def preview_attack_rate(self,value):
        self.controller.ui['show_attack_rate']=value;self.controller.apply_ui()

    def preview_countdown_font(self,_):
        self.controller.ui.update(countdown_font_size=self.countdown_size.value(),
                                  countdown_font_weight=self.countdown_weight.currentData())
        self.controller.apply_ui()

    def save_ui(self):
        if not self.effects.save_all():return
        try:
            from tcp_state_server import StateServer
            replacement=StateServer(self.tcp_port.value(),self.tcp_source.text().strip())
            settings = dict(self.controller.ui, target_idle_seconds=self.target_idle.value(),
                            tcp_port=replacement.port,tcp_source=replacement.source,
                            countdown_font_size=self.countdown_size.value(),
                            countdown_font_weight=self.countdown_weight.currentData(),
                            show_attack_rate=self.show_attack_rate.isChecked(), **self.voice_settings())
            settings.update({key:check.isChecked() for key,check in self.log_checks.items()})
            settings.update(self.hp_values())
            settings.update({key:combo.currentData() for key,combo in self.hp_tick_combos.items()})
            saved=load_ui(self.controller.ui_path)
            settings.update(settings_width=saved['settings_width'],settings_height=saved['settings_height'])
            save_json(self.controller.ui_path,settings)
            self.controller.ui=settings
            self.apply_tcp_server(replacement)
            self.controller.preview.set_sound_enabled(settings['speech_enabled'])
            if not settings['speech_enabled']: self.controller.speech.stop()
            self.controller.refresh()
            self.status.setText('UI 설정을 저장했습니다.')
        except (OSError,ValueError) as exc:
            self.status.set_status('저장 실패: '+str(exc),'error')
            QMessageBox.warning(self,'저장 실패',str(exc))

    def closeEvent(self,event):
        if self.effects.has_pending_changes():
            dialog=QMessageBox(self);dialog.setWindowTitle('저장 전 변경');dialog.setText('아직 저장하지 않은 효과 변경이 있습니다.')
            save=dialog.addButton('모두 저장',QMessageBox.ButtonRole.AcceptRole)
            discard=dialog.addButton('변경 취소 후 닫기',QMessageBox.ButtonRole.DestructiveRole)
            dialog.addButton('계속 편집',QMessageBox.ButtonRole.RejectRole);dialog.exec()
            if dialog.clickedButton()==save:
                if not self.effects.save_all():event.ignore();return
            elif dialog.clickedButton()==discard:self.effects.discard_changes()
            else:event.ignore();return
        if self.controller.opacity_timer.isActive():
            self.controller.opacity_timer.stop();self.controller.save_background_opacity()
        self.resize_timer.stop();self.save_size()
        self.controller.ui=load_ui(self.controller.ui_path)
        for key,combo in self.hp_tick_combos.items():
            combo.blockSignals(True);combo.setCurrentIndex(combo.findData(self.controller.ui[key]));combo.blockSignals(False)
        self.hp_enabled.setChecked(self.controller.ui.get('tcp_hp_enabled',True))
        self.hp_name.setText(self.controller.ui.get('tcp_hp_name','내HP'))
        for key,check in self.log_checks.items():check.setChecked(self.controller.ui[key])
        self.size.setValue(self.controller.ui['tile_size'])
        self.target_idle.setValue(self.controller.ui['target_idle_seconds'])
        self.show_attack_rate.setChecked(self.controller.ui['show_attack_rate'])
        self.countdown_size.blockSignals(True);self.countdown_weight.blockSignals(True)
        self.countdown_size.setValue(self.controller.ui['countdown_font_size'])
        self.countdown_weight.setCurrentIndex(self.countdown_weight.findData(self.controller.ui['countdown_font_weight']))
        self.countdown_size.blockSignals(False);self.countdown_weight.blockSignals(False)
        self.speech_enabled.setChecked(self.controller.ui['speech_enabled'])
        self.volume.setValue(self.controller.ui['speech_volume']);self.rate.setValue(self.controller.ui['speech_rate'])
        self.voice.setCurrentIndex(max(0,self.voice.findData(self.controller.ui['speech_voice'])))
        self.update_voices(self.controller.speech.voices)
        self.controller.apply_ui();event.accept()

    def voice_settings(self):
        return dict(speech_enabled=self.speech_enabled.isChecked(),speech_voice=self.voice.currentData() or '',
                    speech_volume=self.volume.value(),speech_rate=self.rate.value())

    def preview_speech(self,text):
        self.controller.speech.speak(text,self.voice_settings())

    def update_voices(self,voices):
        selected=self.voice.currentData() or self.controller.ui['speech_voice']
        self.voice.clear();self.voice.addItem('Windows 기본 목소리 (한국어 우선)','')
        for voice in voices: self.voice.addItem(voice['name'],voice['id'])
        if selected and self.voice.findData(selected)<0:
            self.voice.addItem('저장된 목소리 (설치 확인 필요)',selected)
        self.voice.setCurrentIndex(max(0,self.voice.findData(selected)))

    def showEvent(self,event):
        super().showEvent(event)
        self.controller.speech.start()

    def resizeEvent(self,event):
        super().resizeEvent(event)
        if hasattr(self,'resize_timer') and self.isVisible(): self.resize_timer.start(400)

    def save_size(self):
        if self.isMaximized() or self.isMinimized(): return
        try:
            saved=load_ui(self.controller.ui_path)
            saved.update(settings_width=self.width(),settings_height=self.height())
            save_json(self.controller.ui_path,saved)
            self.controller.ui.update(settings_width=self.width(),settings_height=self.height())
        except (ValueError,OSError) as exc: self.controller.capture_status('설정창 크기 저장 실패: '+str(exc))
