"""Specialization conditions use a single received snapshot for all five flags."""
import json
from pathlib import Path
from PyQt6 import QtCore, QtWidgets

SKILLS = {row['code']: row for row in json.loads((Path(__file__).parent/'assets/aion2_specializations.json').read_text('utf-8'))}


def summary(cond):
    skill = SKILLS.get(cond.aion2_skill, {}).get('label', '미지원 스킬')
    numbers = '·'.join(str(n) for n in cond.aion2_specializations)
    match = (' 모두' if cond.aion2_specialization_match == 'all' else ' 하나라도') if len(cond.aion2_specializations)>1 else ''
    expected = '선택됨' if cond.aion2_specialization_selected else '선택 안 됨'
    return f'{skill} · {numbers}번 특화{match} {expected}'


def evaluate(client, cond):
    skill = SKILLS.get(cond.aion2_skill)
    numbers = cond.aion2_specializations
    match = cond.aion2_specialization_match
    expected = cond.aion2_specialization_selected
    detail = dict(aion2_kind='skill_specialization', unavailable=True, source=cond.external_source)
    if (not skill or not isinstance(numbers,(list,tuple)) or not numbers or
            any(type(n) is not int or not 1<=n<=5 for n in numbers) or
            len(set(numbers))!=len(numbers) or match not in ('all','any') or type(expected) is not bool):
        return False, dict(detail,status='스킬과 특화 번호(1~5)를 선택하세요.')
    data, status = client.snapshot(cond.external_source)
    if data is None:
        return False, dict(detail,status=status)
    keys = {n:f"{skill['prefix']}.{n}" for n in range(1,6)}
    unknown = set(data.get('unavailable_keys',()))
    values = data.get('values',{})
    missing = [n for n in numbers if keys[n] in unknown or type(values.get(keys[n])) is not bool]
    if missing:
        disabled = any(keys[n] not in data.get('items',{}) and keys[n] not in values and keys[n] not in unknown for n in missing)
        message = f"모니터 스킬관리에서 {skill['label']}의 ‘특화 전송’을 켜세요." if disabled else '특화 정보 수신 대기 · 게임의 특화 패킷을 아직 받지 못했습니다.'
        return False, dict(detail,status=message)
    checks = [values[keys[n]] is expected for n in numbers]
    result = all(checks) if match=='all' else any(checks)
    complete = all(keys[n] not in unknown and type(values.get(keys[n])) is bool for n in keys)
    selected = [n for n in keys if values.get(keys[n]) is True and keys[n] not in unknown]
    text = ('·'.join(map(str,selected))+'번 선택됨' if selected else '선택된 특화 없음') if complete else '일부 특화 미확인'
    return result, dict(detail,unavailable=False,actual=result,selection_text=text,
                        status=f"현재 {text} · {'조건 충족' if result else '조건 미충족'}")


class SpecializationPicker(QtWidgets.QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        layout = QtWidgets.QVBoxLayout(self);layout.setContentsMargins(0,0,0,0)
        row = QtWidgets.QHBoxLayout();self.buttons = {}
        for number in range(1,6):
            button = QtWidgets.QPushButton(str(number));button.setCheckable(True)
            button.setMinimumWidth(38);button.setToolTip(f'{number}번 특화 확인')
            button.setStyleSheet('QPushButton:checked {background: #2563eb; color: white; font-weight: bold;}')
            self.buttons[number]=button;row.addWidget(button)
        row.addStretch();layout.addLayout(row)
        self.expected=QtWidgets.QComboBox();self.expected.addItem('선택되어 있음',True);self.expected.addItem('선택되어 있지 않음',False)
        layout.addWidget(self.expected)
        self.match=QtWidgets.QComboBox();self.match.addItem('선택한 번호 모두','all');self.match.addItem('선택한 번호 중 하나라도','any')
        layout.addWidget(self.match)
        self.buttons[5].setChecked(True)
        for button in self.buttons.values():button.toggled.connect(self._sync)
        self._sync()

    def _sync(self):
        count=sum(button.isChecked() for button in self.buttons.values())
        if count==0 and self.sender() in self.buttons.values():
            with QtCore.QSignalBlocker(self.sender()):self.sender().setChecked(True)
            count=1
        self.match.setVisible(count>1)

    def fields(self):
        return dict(aion2_specializations=tuple(n for n,b in self.buttons.items() if b.isChecked()),
                    aion2_specialization_match=self.match.currentData(),
                    aion2_specialization_selected=self.expected.currentData())

    def load(self, cond):
        for n,button in self.buttons.items():
            with QtCore.QSignalBlocker(button):button.setChecked(n in cond.aion2_specializations)
        self.match.setCurrentIndex(max(0,self.match.findData(cond.aion2_specialization_match)))
        self.expected.setCurrentIndex(max(0,self.expected.findData(cond.aion2_specialization_selected)))
        self._sync()
