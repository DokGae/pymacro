"""Consumable actions and cooldown conditions from fresh monitor snapshots."""
import math

ITEMS = {
    530116001: ('생명의 비약', 30), 530116010: ('상급 생명의 비약', 30),
    530116006: ('생명의 결정', 30), 530116008: ('생명의 신약', 30),
    510116005: ('바람의 비약', 10), 510116010: ('상급 바람의 비약', 10),
    511490001: ('간파의 씨앗', 30),
    510146002: ('상급 치유 물약', 10), 530146001: ('치유 물약', 10),
}
ALIASES = {510116006: 530116010, 510116011: 530116006}


def canonical_item(code):
    return ALIASES.get(code, code)


GROUPS = {
    530116010: ('생명의 비약 (상급 우선)', 30, (530116010, 530116001)),
    530116006: ('생명의 결정', 30, (530116006,)),
    530116008: ('생명의 신약', 30, (530116008,)),
    510116010: ('바람의 비약 (상급 우선)', 10, (510116010, 510116005)),
    511490001: ('간파의 씨앗', 30, (511490001,)),
    510146002: ('치유 물약 (상급 우선)', 10, (510146002, 530146001)),
}
CHOICES = {code:(name,seconds) for code,(name,seconds,_) in GROUPS.items()}


def group_item(code):
    code=canonical_item(code)
    return next((group for group,(_,_,members) in GROUPS.items() if code in members),code)


def item_label(code):
    return CHOICES.get(group_item(code), ('미등록 소모품', 0))[0]


def read_packet(client, source):
    data, status = client.snapshot(source)
    if data is None:
        raise ValueError(status)
    if data.get('values', {}).get('게임연결') is not True:
        raise ValueError('게임 연결 대기')
    packet = data.get('aion2_consumables')
    if not isinstance(packet, dict) or type(packet.get('version')) is not int or packet['version'] != 1:
        raise ValueError('소모품 통신 정보 수신 대기')
    if packet.get('enabled') is not True or packet.get('available') is not True:
        raise ValueError(str(packet.get('reason') or '소모품 정보 미확인'))
    if type(packet.get('group_version')) is not int or packet['group_version'] != 1:
        raise ValueError('모니터의 소모품 자동 선택·공유 쿨타임 정보 수신 대기')
    slots = packet.get('slots')
    if not isinstance(slots, list) or len(slots) > 8:
        raise ValueError('소모품 슬롯 형식 오류')
    seen = set()
    for slot in slots:
        if not isinstance(slot, dict):
            raise ValueError('소모품 슬롯 형식 오류')
        n = slot.get('quick_use')
        if (type(n) is not int or not 1 <= n <= 8 or n in seen
                or type(slot.get('slot_id')) is not int or slot['slot_id'] != n+9
                or type(slot.get('code')) is not int or slot['code'] < 0):
            raise ValueError('소모품 슬롯 형식 오류')
        seen.add(n)
    return packet


def resolve_item_key(client, action):
    from aion2_actions import portable_key, validate_settings
    try:
        validate_settings(vars(action))
        packet = read_packet(client, action.external_source)
        group=group_item(action.aion2_item)
        members=GROUPS[group][2]
        candidates = [s for s in packet['slots'] if group_item(s['code']) == group]
        if not candidates:
            return None, '선택한 소모품이 퀵슬롯에 없습니다.'
        # Duplicate item registrations may have only one configured key.
        candidates.sort(key=lambda s:(members.index(canonical_item(s['code'])),s['quick_use']))
        for slot in candidates:
            if slot.get('key'):
                actual_name=ITEMS[canonical_item(slot['code'])][0]
                return portable_key(slot['key']), f"{actual_name} · 소모품 {slot['quick_use']} · {slot['key']}"
        return None, '소모품 단축키 미설정'
    except (ValueError, TypeError, AttributeError) as exc:
        return None, str(exc)


def evaluate_item_cooldown(client, cond):
    detail = dict(unavailable=True, aion2_kind='consumable_cooldown', source=cond.external_source)
    try:
        code = group_item(cond.aion2_item)
        expected = cond.aion2_cooldown_seconds
        op = cond.aion2_cooldown_operator
        if (type(code) is not int or code not in ITEMS or op not in ('ready','cooling','le','lt','ge','gt','eq','ne')
                or type(expected) not in (int,float) or not math.isfinite(expected) or expected < 0):
            raise ValueError('소모품 쿨타임 설정 오류')
        packet = read_packet(client, cond.external_source)
        items = packet.get('groups')
        if not isinstance(items, list) or len(items) > 32:
            raise ValueError('소모품 쿨타임 형식 오류')
        rows = [i for i in items if isinstance(i, dict) and type(i.get('code')) is int and i['code'] == code]
        if len(rows) != 1 or rows[0].get('observed') is not True:
            raise ValueError('소모품 슬롯 수신 대기')
        item = rows[0]
        if item.get('present') is False:
            detail.update(unavailable=False, status='소모품 퀵슬롯에 미등록 · 조건 거짓')
            return False, detail
        if item.get('present') is not True or not any(group_item(s['code']) == code for s in packet['slots']):
            raise ValueError('소모품 등록 정보 불일치')
        seconds = item.get('remaining')
        if type(seconds) not in (int,float) or not math.isfinite(seconds) or seconds < 0:
            raise ValueError('소모품 쿨타임 미확인')
        result = {'ready':seconds==0,'cooling':seconds>0,'le':seconds<=expected,'lt':seconds<expected,
                  'ge':seconds>=expected,'gt':seconds>expected,'eq':seconds==expected,'ne':seconds!=expected}[op]
        detail.update(unavailable=False, actual=seconds, expected=expected, operator=op,
                      status=f'예상 쿨타임 {seconds:g}초 · ' + ('조건 충족' if result else '조건 미충족'))
        return result, detail
    except (ValueError, TypeError, AttributeError) as exc:
        detail['status'] = str(exc)
        return False, detail
