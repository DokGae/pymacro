"""AION2 monitor conditions. Pure comparisons; never sleep or send inputs."""
import math
import json
from pathlib import Path

ALL_SKILLS=tuple((row['code'],row['label'],row['suffix']) for row in
    json.loads((Path(__file__).parent/'assets/aion2_skills.json').read_text(encoding='utf-8')))

# Display labels keep same-name skills distinct. Values are monitor channel suffixes.
CHARGE_SKILLS = (
    (11110000, '검성 · 집중 막기', '집중막기.검성.11110000'),
    (12110000, '수호성 · 보호의 방패', '보호의방패'),
    (13050000, '살성 · 섬광 베기', '섬광베기'),
    (13060000, '살성 · 기습', '기습'),
    (13080000, '살성 · 회피 자세', '회피자세'),
    (13250000, '살성 · 연막탄', '연막탄'),
    (14090000, '궁성 · 표적 화살', '표적화살'),
    (14150000, '궁성 · 환영 화살', '환영화살'),
    (17120000, '치유성 · 쾌유의 광휘', '쾌유의광휘'),
    (18120000, '호법성 · 쾌유의 주문', '쾌유의주문'),
    (18140000, '호법성 · 집중 방어', '집중방어'),
    (19350000, '권성 · 집중 막기', '집중막기.권성.19350000'),
)


def skill_label(code):
    return next((label for skill,label,_ in ALL_SKILLS if skill==code),'지원하지 않는 스킬')


def condition_summary(cond):
    if cond.aion2_kind == 'consumable_cooldown':
        from aion2_consumables import item_label
        op={'ready':'사용 가능 (= 0초)','cooling':'쿨타임 중 (> 0초)', 'le':'≤','lt':'<','ge':'≥','gt':'>','eq':'=','ne':'≠'}.get(cond.aion2_cooldown_operator,'잘못된 판정')
        value='' if cond.aion2_cooldown_operator in ('ready','cooling') else f' {cond.aion2_cooldown_seconds:g}초'
        return f'소모품 쿨타임: {item_label(cond.aion2_item)} / {op}{value}'
    if cond.aion2_kind=='cooldown':
        role='내' if cond.aion2_role=='own' else '대상'
        op={'ready':'사용 가능 (= 0초)','cooling':'쿨타임 중 (> 0초)',
            'le':'≤','lt':'<','ge':'≥','gt':'>','eq':'=','ne':'≠'}.get(cond.aion2_cooldown_operator,'잘못된 판정')
        value='' if cond.aion2_cooldown_operator in ('ready','cooling') else f' {cond.aion2_cooldown_seconds:g}초'
        return f'스킬 쿨타임 확인: {role} / {skill_label(cond.aion2_skill)} / {op}{value}'
    return f'스킬 사용 후 대기 완료: {skill_label(cond.aion2_skill)} / {cond.aion2_wait_seconds:g}초'


def evaluate_aion2(client,cond):
    if cond.aion2_kind == 'consumable_cooldown':
        from aion2_consumables import evaluate_item_cooldown
        return evaluate_item_cooldown(client,cond)
    if getattr(cond,'aion2_kind','use_wait')=='use_wait':return evaluate_use_wait(client,cond)
    if cond.aion2_kind!='cooldown':return False,dict(unavailable=True,status='지원하지 않는 AION2 조건')
    suffix=next((suffix for code,_,suffix in ALL_SKILLS if code==cond.aion2_skill),None)
    expected=cond.aion2_cooldown_seconds;op=cond.aion2_cooldown_operator
    if (suffix is None or cond.aion2_role not in ('own','target') or
        op not in ('ready','cooling','le','lt','ge','gt','eq','ne') or
        type(expected) not in (int,float) or not math.isfinite(expected) or expected<0):
        return False,dict(unavailable=True,status='스킬 쿨타임 설정 오류')
    key=f"{'내' if cond.aion2_role=='own' else '대상'}.스킬쿨.{suffix}"
    available,seconds,status=client.lookup(cond.external_source,key)
    valid=available and type(seconds) in (int,float) and math.isfinite(seconds) and seconds>=0
    detail=dict(key=key,source=cond.external_source,actual=seconds,expected=expected,operator=op,
                skill=skill_label(cond.aion2_skill),unavailable=not valid,status=status,aion2_kind='cooldown')
    if cond.aion2_role=='own' and available and seconds is False:
        detail.update(unavailable=False,status='미채용 · 퀵슬롯에 등록되지 않은 스킬')
        return False,detail
    if not valid:
        detail['status']='쿨타임 미확인 · 모니터의 스킬 관리에서 해당 내 통신·대상 통신을 켜고 감지 여부를 확인하세요. '+status
        return False,detail
    result={'ready':seconds==0,'cooling':seconds>0,'le':seconds<=expected,'lt':seconds<expected,
            'ge':seconds>=expected,'gt':seconds>expected,'eq':seconds==expected,'ne':seconds!=expected}[op]
    detail['status']=f"수신 쿨타임 {seconds:g}초 · {'조건 충족' if result else '조건 미충족'}"
    return result,detail


def evaluate_use_wait(client,cond):
    suffix=next((suffix for code,_,suffix in CHARGE_SKILLS if code==cond.aion2_skill),None)
    wait=cond.aion2_wait_seconds
    if suffix is None or type(wait) not in (int,float) or not math.isfinite(wait) or not 0<=wait<=3600:
        return False,dict(unavailable=True,status='AION2 스킬 또는 대기 시간 설정 오류')
    key='내.스킬사용경과.'+suffix
    available,elapsed,status=client.lookup(cond.external_source,key)
    valid=available and type(elapsed) in (int,float) and math.isfinite(elapsed) and (elapsed==-1 or elapsed>=0)
    detail=dict(key=key,source=cond.external_source,actual=elapsed,expected=wait,
                skill=skill_label(cond.aion2_skill),operator='ge',unavailable=not valid,status=status)
    if not valid:return False,detail
    # A monitoring baseline without any observed use must allow the first attempt.
    result=elapsed==-1 or elapsed>=wait
    detail['status']='감시 시작 후 사용 미감지 · 대기 완료' if elapsed==-1 else '대기 완료' if result else '사용 후 대기 중 · 다음 IF 계속 처리'
    return result,detail
