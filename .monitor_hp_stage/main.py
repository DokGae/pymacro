import os
import sys
import time
import sqlite3
from pathlib import Path
from PyQt6.QtCore import QObject,QTimer
from PyQt6.QtWidgets import QApplication,QMessageBox
from compact_preview import CompactPreview
from presets import PresetStore
from packetcore.state import StateStore
from packetcore.combat import direct_attack_target
from packetcore.owner_history import load_identity_cache,remember_owner
from live_capture import LiveCapture
from speech_alerts import WindowsSpeech,EffectAlerts
from settings_window import SettingsWindow,load_ui
from packetcore.analysis import save_json
from effect_log import EffectLog
from tcp_state_server import StateServer,monitor_snapshot
from status_label import message_level
from PyQt6.QtCore import QUrl
from PyQt6.QtGui import QDesktopServices


class UserMonitor(QObject):
    def __init__(self,data_dir=None):
        super().__init__()
        # Closing settings must not terminate the persistent monitor.
        QApplication.instance().setQuitOnLastWindowClosed(False)
        self.data_dir=Path(data_dir) if data_dir else Path(os.environ.get('LOCALAPPDATA',Path.home()/'AppData/Local'))/'LeeSangJinMonitor'
        self.data_dir.mkdir(parents=True,exist_ok=True)
        self.ui_path=self.data_dir/'ui_settings.json'
        self.presets=PresetStore(self.data_dir)
        self.active_preset_id='default';self.catalog=self.presets.catalog('default')
        self.states=StateStore(load_identity_cache(self.data_dir/'owner_identity.json',time.time()))
        self.speech=WindowsSpeech(self);self.alerts=EffectAlerts()
        self.speech.failed.connect(lambda message:self.capture_status(message,'error'))
        self.ui=load_ui(self.ui_path);self.status='게임 접속 대기';self.settings=None
        self.status_level='success'
        self.game_connected=False
        self.tcp_observed_actors=set()
        self.tcp_preview=None
        self.state_server=StateServer(self.ui.get('tcp_port',47653),self.ui.get('tcp_source','leesangjin-monitor'))
        self.preview=CompactPreview();self.preview.manageRequested.connect(self.open_settings)
        self.preview.exitRequested.connect(QApplication.instance().quit)
        self.preview.resize(self.ui['window_width'],self.ui['window_height'])
        self.preview.sizeCommitted.connect(self.save_window_size)
        self.opacity_timer=QTimer(self);self.opacity_timer.setSingleShot(True)
        self.opacity_timer.timeout.connect(self.save_background_opacity)
        self.preview.backgroundOpacityChanged.connect(self.background_opacity_changed)
        self.preview.soundEnabledChanged.connect(self.set_sound_enabled)
        self.effect_log=EffectLog()
        self.preview.recordingRequested.connect(self.toggle_recording)
        self.worker=LiveCapture();self.worker.batch.connect(self.receive)
        self.worker.status.connect(self.capture_status);self.worker.failed.connect(self.capture_error)
        self.timer=QTimer(self);self.timer.timeout.connect(self.refresh);self.timer.start(200)
        self.apply_ui()

    def start(self):self.preview.show();self.state_server.start();self.worker.start()

    def save_window_size(self,width,height):
        try:
            # Keep unsaved UI previews out of the automatic window-size save.
            saved=load_ui(self.ui_path)
            saved.update(window_width=width,window_height=height)
            save_json(self.ui_path,saved)
            self.ui.update(window_width=width,window_height=height)
        except (ValueError,OSError) as exc:self.capture_status('창 크기 저장 실패: '+str(exc))

    def background_opacity_changed(self,value):
        self.ui['background_opacity']=value;self.opacity_timer.start(400)

    def set_sound_enabled(self,enabled):
        self.ui['speech_enabled']=enabled
        if not enabled:self.speech.stop()
        if self.settings:self.settings.speech_enabled.setChecked(enabled)
        try:
            saved=load_ui(self.ui_path);saved['speech_enabled']=enabled
            save_json(self.ui_path,saved)
        except (ValueError,OSError) as exc:self.capture_status('음소거 설정 저장 실패: '+str(exc))

    def save_background_opacity(self):
        try:
            saved=load_ui(self.ui_path);saved['background_opacity']=self.ui['background_opacity']
            save_json(self.ui_path,saved)
        except (ValueError,OSError) as exc:self.capture_status('배경 투명도 저장 실패: '+str(exc))

    def receive(self,batch):
        if batch:self.game_connected=True
        for row,result in batch:
            if not result.error and result.opcode in ('0x2A38','0x2B38','0x2C38'):
                self.tcp_observed_actors.add((row['flow'],result.values.get('actor_id')))
            key=(row['flow'],result.values.get('target_id'))
            state=self.states.actors.get(key)
            previous=dict(state.effects) if self.effect_log.active and state and result.opcode in ('0x2A38','0x2B38','0x2C38') else {}
            self.expire_target(row['stamp'])
            target=direct_attack_target(result) if row.get('direction')=='in' else None
            if (target is not None and (row['flow'],result.values.get('actor_id'))==self.states.owner_key
                    and (row['flow'],target)!=self.states.attack_target_key):
                # Each newly selected target starts its own fresh combat session.
                self.states.combat_clocks.pop(self.states.attack_target_key,None)
                self.states.combat_clocks.pop((row['flow'],target),None)
            self.states.apply(row,result)
            if self.effect_log.active:
                try:self.effect_log.observe(row,result,self.states,self.catalog,previous)
                except (OSError, sqlite3.Error) as exc:
                    self.capture_status('로그 기록 실패: '+str(exc))
                    self.toggle_recording()
            self.check_alerts(row['stamp'])
            if result.opcode=='0x3336' and result.values.get('own_identity'):
                try:remember_owner(self.data_dir/'owner_identity.json',row['flow'],result.values,row['stamp'])
                except OSError as exc:self.capture_status('캐릭터 설정 저장 실패: '+str(exc))
        if self.effect_log.active:
            try:self.effect_log.flush()
            except (OSError,sqlite3.Error) as exc:self.capture_status('로그 기록 실패: '+str(exc));self.toggle_recording()
        self.refresh()

    def toggle_recording(self):
        try:
            if self.effect_log.active:
                path=self.effect_log.stop(self.states)
                self.capture_status('로그 저장 완료: '+str(path))
            else:
                if not self.ui.get('log_effects',True) or not (self.ui.get('log_own',True) or self.ui.get('log_target',True)):
                    QMessageBox.information(self.preview,'로그 수집','설정 → 로그분석에서 효과와 수집 대상을 선택하고 저장하세요.');return
                self.effect_log.start(self.ui)
                self.capture_status('효과 로그 수집 시작')
        except (OSError, sqlite3.Error) as exc:
            self.capture_status('로그 저장 오류: '+str(exc),'error')
            QMessageBox.warning(self.preview,'로그 저장 오류',str(exc))
        self.preview.set_recording(self.effect_log.active)

    def open_log_folder(self):
        try:self.effect_log.directory.mkdir(parents=True,exist_ok=True)
        except OSError as exc:
            self.capture_status('로그 폴더 오류: '+str(exc),'error')
            QMessageBox.warning(self.preview,'로그 폴더 오류',str(exc));return
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.effect_log.directory)))

    def capture_status(self,status,level=None):
        if status.startswith('게임 연결 감지'):self.game_connected=True
        elif status=='AION2 실행 및 접속 대기':
            self.game_connected=False;self.tcp_observed_actors.clear()
        self.status=status
        self.status_level=level or message_level(status)
        if self.settings:self.settings.status.set_status(status,self.status_level)

    def capture_error(self,message):
        self.game_connected=False
        self.tcp_observed_actors.clear()
        self.capture_status('수집 오류: '+message)
        QMessageBox.warning(self.preview,'모니터 연결 오류',message)

    def refresh(self,now=None):
        if now is None: now=time.time()
        state=self.states.actors.get(self.states.owner_key)
        self.active_preset_id=self.presets.match(state.nickname if state else '',state.server_id if state else None)
        self.catalog=self.presets.catalog(self.active_preset_id)
        if self.settings: self.settings.preset_panel.update_active()
        self.expire_target(now)
        self.preview.target_counts.setVisible(self.ui['show_attack_rate'])
        self.preview.refresh(self.catalog,self.states,now)
        snapshot=monitor_snapshot(self.states,self.catalog,self.game_connected,self.tcp_observed_actors,self.ui)
        if self.tcp_preview:
            values,until=self.tcp_preview
            if time.monotonic()<until:
                snapshot['values'].update(values)
                snapshot['items'].update({key:'미리 전송' for key in values})
                snapshot['unavailable_keys']=[key for key in snapshot['unavailable_keys'] if key not in values]
            else:self.tcp_preview=None
        self.state_server.publish(snapshot)
        if self.settings:
            name=self.ui.get('tcp_hp_name','내HP');value=snapshot['values'].get(name)
            text='HP 전송 꺼짐' if not self.ui.get('tcp_hp_enabled',True) else ('최대 HP 또는 현재 HP 감지 대기 · false 전송' if value is False else (f'현재 전송: {name} = {value}%' if value is not None else 'HP 전송 실패: 내용 이름이 효과 이름과 겹칩니다.'))
            self.settings.hp_status.setText(text)
        if self.settings:self.settings.tcp_status.setText(self.state_server.status)
        self.check_alerts(now)

    def set_monitor_preview(self,payload):
        self.preview.sample_effect=payload
        self.preview.sample_stop_button.setVisible(payload is not None)
        if payload is not None:
            self.preview.showNormal();self.preview.raise_()
        self.refresh()

    def set_tcp_preview(self,values):
        if values and self.ui.get('tcp_hp_name','내HP') in values:
            self.settings.effects.note.setText('미리 전송 실패: HP 내용 이름과 겹칩니다.');return
        self.tcp_preview=(values,time.monotonic()+5) if values else None
        self.refresh()

    def check_alerts(self,now):
        state=self.states.actors.get(self.states.owner_key)
        preset=self.presets.match(state.nickname if state else '',state.server_id if state else None)
        catalog=self.presets.catalog(preset)
        for text in self.alerts.poll(catalog,self.states,now,preset,self.ui['speech_enabled']):
            self.speech.speak(text,self.ui)

    def expire_target(self,now):
        states=self.states
        if (states.attack_target_key is not None and states.attack_target_at is not None
                and now-states.attack_target_at >= self.ui['target_idle_seconds']):
            key=states.attack_target_key
            states.attack_target_key=None;states.attack_target_at=None;states.attack_target_record=0
            states.attack_counts = {'전체': 0, '회피': 0, '막기': 0}
            states.attack_positions.pop(key,None);states.attack_outcomes.pop(key,None)
            states.combat_clocks.pop(key,None)

    def apply_ui(self):
        self.preview.own_hp.set_tick_interval(self.ui.get('own_hp_tick_interval',5))
        self.preview.target_hp.set_tick_interval(self.ui.get('target_hp_tick_interval',0))
        self.preview.set_sound_enabled(self.ui['speech_enabled'])
        self.preview.set_background_opacity(self.ui['background_opacity'])
        for panel in (self.preview.own_panel,self.preview.target_panel):
            panel.countdown_size=self.ui['countdown_font_size']
            panel.countdown_weight=self.ui['countdown_font_weight']
            panel.TILE=self.ui['tile_size'];panel.CELL=panel.TILE+6;panel.updateGeometry();panel.update()
        self.refresh()

    def open_settings(self):
        if self.settings is None:self.settings=SettingsWindow(self)
        if not self.settings.isVisible(): self.settings.preset_panel.reload(self.active_preset_id)
        observed={e['code'] for state in self.states.actors.values() for e in state.effects.values()}
        self.settings.effects.model.observed.update(observed)
        self.settings.effects.model.refresh()
        self.settings.effects.update_count()
        self.settings.show();self.settings.raise_();self.settings.activateWindow()

    def shutdown(self):
        self.state_server.stop()
        if self.effect_log.active:self.toggle_recording()
        if self.opacity_timer.isActive():
            self.opacity_timer.stop();self.save_background_opacity()
        if self.settings and self.settings.isVisible(): self.settings.close()
        self.speech.stop()
        self.timer.stop();self.worker.stop()
        self.worker.wait()


def main():
    app=QApplication(sys.argv);app.setApplicationName('이상진 제작 · 모니터')
    controller=UserMonitor();app.aboutToQuit.connect(controller.shutdown)
    if '--smoke-test' in sys.argv:
        controller.open_settings();controller.settings.close();controller.preview.close();return 0
    controller.start();return app.exec()


if __name__=='__main__':sys.exit(main())
