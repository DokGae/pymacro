"""Resolve live monitor quickslots for press; never cache a usable key."""
from PyQt6.QtCore import Qt
from PyQt6.QtGui import QKeySequence
from aion2_conditions import ALL_SKILLS, skill_label

SLOT_IDS = (0, 1, 2, 3, 4, 5, 6, 7, 20, 21, 22, 23)
SKILL_CODES = frozenset(code for code, _, _ in ALL_SKILLS)


def validate_settings(data):
    mode = data.get('key_source', 'direct')
    if mode not in ('direct', 'aion2', 'aion2_consumable'):
        raise ValueError('지원하지 않는 키 입력 방식입니다.')
    if mode == 'direct':return
    if data.get('type', 'press') != 'press':
        raise ValueError('AION2 전용 스킬 단축키는 press에서 사용하세요.')
    skill = data.get('aion2_skill', 18120000)
    if mode == 'aion2_consumable':
        from aion2_consumables import ITEMS, canonical_item
        item = data.get('aion2_item', 530116010)
        if type(item) is not int or canonical_item(item) not in ITEMS:raise ValueError('소모품을 선택하세요.')
    if mode == 'aion2' and (type(skill) is not int or skill not in SKILL_CODES):
        raise ValueError('AION2 스킬을 선택하세요.')
    host = data.get('external_host', '127.0.0.1')
    port = data.get('external_port', 47653)
    source = data.get('external_source', 'leesangjin-monitor')
    if (host not in ('127.0.0.1', 'localhost') or type(port) is not int
            or not 1 <= port <= 65535 or not isinstance(source, str)
            or not source.strip() or len(source) > 200):
        raise ValueError('AION2 외부 연결 설정을 확인하세요.')


def portable_key(text):
    """Convert Qt's single-stroke key to the existing macro backend names."""
    if not isinstance(text, str) or not text or len(text) > 120:
        raise ValueError('단축키 미설정')
    sequence = QKeySequence.fromString(text, QKeySequence.SequenceFormat.PortableText)
    if sequence.count() != 1:
        raise ValueError('단축키는 하나의 키 조합이어야 합니다.')
    stroke = sequence[0]
    key = stroke.key()
    modifiers = stroke.keyboardModifiers()
    keypad = bool(modifiers & Qt.KeyboardModifier.KeypadModifier)
    parts = [name for flag, name in ((Qt.KeyboardModifier.ControlModifier, 'ctrl'),
             (Qt.KeyboardModifier.AltModifier, 'alt'), (Qt.KeyboardModifier.ShiftModifier, 'shift'),
             (Qt.KeyboardModifier.MetaModifier, 'win')) if modifiers & flag]
    names = {Qt.Key.Key_Space:'space', Qt.Key.Key_Tab:'tab', Qt.Key.Key_Return:'enter',
             Qt.Key.Key_Escape:'esc', Qt.Key.Key_Backspace:'backspace', Qt.Key.Key_Delete:'delete',
             Qt.Key.Key_Insert:'insert', Qt.Key.Key_Home:'home', Qt.Key.Key_End:'end',
             Qt.Key.Key_PageUp:'pageup', Qt.Key.Key_PageDown:'pagedown', Qt.Key.Key_Up:'up',
             Qt.Key.Key_Down:'down', Qt.Key.Key_Left:'left', Qt.Key.Key_Right:'right',
             Qt.Key.Key_CapsLock:'capslock', Qt.Key.Key_NumLock:'numlock',
             Qt.Key.Key_ScrollLock:'scrolllock', Qt.Key.Key_Pause:'pause',
             Qt.Key.Key_QuoteLeft:'`', Qt.Key.Key_Minus:'-', Qt.Key.Key_Equal:'=',
             Qt.Key.Key_BracketLeft:'[', Qt.Key.Key_BracketRight:']', Qt.Key.Key_Backslash:'\\',
             Qt.Key.Key_Semicolon:';', Qt.Key.Key_Apostrophe:"'", Qt.Key.Key_Comma:',',
             Qt.Key.Key_Period:'.', Qt.Key.Key_Slash:'/'}
    if keypad:
        number = chr(int(key)) if Qt.Key.Key_0 <= key <= Qt.Key.Key_9 else None
        main = 'numpad' + number if number else {
            Qt.Key.Key_Plus:'numadd', Qt.Key.Key_Minus:'numsubtract',
            Qt.Key.Key_Asterisk:'nummultiply', Qt.Key.Key_Slash:'numdivide',
            Qt.Key.Key_Period:'numdecimal', Qt.Key.Key_Comma:'numdecimal'}.get(key)
    elif Qt.Key.Key_A <= key <= Qt.Key.Key_Z or Qt.Key.Key_0 <= key <= Qt.Key.Key_9:
        main = chr(int(key)).lower()
    elif Qt.Key.Key_F1 <= key <= Qt.Key.Key_F24:
        main = f'f{int(key)-int(Qt.Key.Key_F1)+1}'
    elif key in names:
        main = names[key]
    else:
        shifted = dict(zip('~!@#$%^&*()_+{}|:"<>?', '`1234567890-=[]\\;\',./'))
        main = shifted.get(chr(int(key))) if 0 <= int(key) < 128 else None
        if main and 'shift' not in parts:parts.append('shift')
    if not main:
        raise ValueError('지원하지 않는 단축키입니다. 모니터에서 키를 다시 설정하세요.')
    return '+'.join(parts + [main])


def resolve_skill_key(client, action):
    try:
        validate_settings(vars(action))
        data, status = client.snapshot(action.external_source)
        if data is None:return None, status
        if data.get('values', {}).get('게임연결') is not True:
            return None, '게임 연결 대기'
        packet = data.get('aion2_quickslots')
        if not isinstance(packet, dict) or type(packet.get('version')) is not int or packet['version'] != 1:
            return None, '모니터의 퀵슬롯 통신 정보 수신 대기'
        if packet.get('enabled') is not True or packet.get('available') is not True:
            return None, str(packet.get('reason') or '퀵슬롯 정보 미확인')
        slots = packet.get('slots')
        if not isinstance(slots, list) or len(slots) > 12:
            return None, '퀵슬롯 정보 형식 오류'
        candidates = []
        seen = set()
        for slot in slots:
            if not isinstance(slot, dict):return None, '퀵슬롯 항목 형식 오류'
            number = slot.get('quick_use')
            codes = slot.get('codes')
            if (type(number) is not int or not 1 <= number <= 12 or number in seen
                    or type(slot.get('slot_id')) is not int or slot['slot_id'] != SLOT_IDS[number - 1]
                    or not isinstance(codes, list) or len(codes) > 4
                    or any(type(code) is not int or code <= 0 for code in codes)):
                return None, '퀵슬롯 항목 형식 오류'
            seen.add(number)
            if any(code // 10000 * 10000 == action.aion2_skill for code in codes):
                candidates.append(slot)
        if not candidates:return None, '선택한 스킬이 퀵슬롯에 등록되지 않았습니다.'
        slot = min(candidates, key=lambda item:item['quick_use'])
        key = portable_key(slot.get('key'))
        return key, f"{skill_label(action.aion2_skill)} · 빠른 사용 {slot['quick_use']} · {slot['key']}"
    except (ValueError, TypeError, AttributeError) as exc:
        return None, str(exc)


def resolve_action_key(action):
    from external_state import state_hub
    try:
        client = state_hub.client(action.external_host, action.external_port)
        if action.key_source == 'aion2_consumable':
            from aion2_consumables import resolve_item_key
            return resolve_item_key(client, action)
        return resolve_skill_key(client, action)
    except (ValueError, TypeError) as exc:
        return None, str(exc)
