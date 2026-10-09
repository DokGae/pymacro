import os,sys,tempfile
from pathlib import Path
os.environ['QT_QPA_PLATFORM']='offscreen'
root=Path(r'C:\Users\goldang\Downloads\notmeter\newmonitor_packet\leesangjin_monitor');stage=Path('.monitor_roles_stage').resolve()
sys.path.insert(0,str(root))
import packetcore.catalog as catalog_module
exec(compile((stage/'catalog.py').read_text(encoding='utf-8'),str(root/'packetcore/catalog.py'),'exec'),catalog_module.__dict__)
sys.path.insert(0,str(stage))
from PyQt6.QtWidgets import QApplication,QDialogButtonBox
from PyQt6.QtCore import Qt,QTimer
from PyQt6.QtTest import QTest
from effect_manager import EffectColorDialog
from packetcore.state import ActorState,StateStore
from tcp_state_server import monitor_snapshot
from main import UserMonitor
app=QApplication([])
with tempfile.TemporaryDirectory() as t:
 u=UserMonitor(t)
 try:
  u.catalog.save_effect(123,'test','#95E342',True,display_mode='color')
  u.open_settings();e=u.settings.effects;e.search.setText('123');app.processEvents()
  row=next(i for i in range(e.proxy.rowCount()) if str(e.proxy.index(i,1).data())=='123')
  idx=e.proxy.index(row,9);e.table.setCurrentIndex(idx);app.processEvents()
  def clear_dialog():
   d=app.activeModalWidget();assert isinstance(d,EffectColorDialog)
   d.html_edit.setFocus();d.html_edit.selectAll();QTest.keyClick(d.html_edit,Qt.Key.Key_Delete)
   assert d.html_edit.text()==''
   QTest.mouseClick(d.findChild(QDialogButtonBox).button(QDialogButtonBox.StandardButton.Ok),Qt.MouseButton.LeftButton)
  QTimer.singleShot(50,clear_dialog);e.cell_clicked(idx)
  assert e.catalog.preview['123']['color']=='' and e.catalog.preview['123']['display_mode']=='image',e.catalog.preview['123']
  assert e.color.text()=='' and e.display_mode.currentData()=='image'
  e._loading=True;e.tcp_check.setChecked(True);e.tcp_mode.setCurrentIndex(e.tcp_mode.findData(True))
  for role,vals in [('own',('나.축복','적용','해제')),('target',('대상.축복','있음','없음'))]:
   for control,value in zip(e.tcp_role_controls[role],vals):control.setText(value)
  e._loading=False;assert e.stage_form()
  states=StateStore();states.owner_key=('a',1);states.attack_target_key=('a',2)
  states.actors[('a',1)]=ActorState(effects={1:dict(code=123)})
  states.actors[('a',2)]=ActorState(effects_at=100)
  snap=monitor_snapshot(states,e.catalog)
  assert snap['values']['나.축복']=='적용' and snap['values']['대상.축복']=='없음'
  states.actors[('a',1)].effects.clear();states.actors[('a',1)].effects_at=100
  states.actors[('a',2)].effects={1:dict(code=123)}
  snap=monitor_snapshot(states,e.catalog)
  assert snap['values']['나.축복']=='해제' and snap['values']['대상.축복']=='있음'
  sent=[];e.tcpPreview.connect(sent.append);e.preview_tcp(True,'own');assert sent[-1]=={'나.축복':'적용'}
  assert e.save_all()
  restored=catalog_module.BuffCatalog(u.catalog.overrides_path)
  assert restored.preview['123']['tcp_target_on']=='있음'
  assert restored.preview['123']['color']=='' and restored.preview['123']['display_mode']=='image'
  print('Actual modal clear, selected-row regression, independent messages, preview and persistence passed')
 finally:u.shutdown();u.preview.close();u.settings.close()
