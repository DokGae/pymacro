"""Korean status-effect names extracted from the user's NotMeter 1.0.256."""
import json
import re
from pathlib import Path

ATTACK_EFFECTS = {
    'attack:front': '전방데미지발생', 'attack:back': '후방데미지발생',
    'attack:evade': '내 공격 회피됨', 'attack:block': '내 공격 막힘',
}


class BuffCatalog:
    def __init__(self, overrides_path=None):
        path = Path(__file__).resolve().parent / 'data' / 'buffs.ko.json'
        self.entries = json.loads(path.read_text(encoding='utf-8-sig'))
        self.entries.update({key: {'Name': name, 'Type': 'ATTACK'} for key, name in ATTACK_EFFECTS.items()})
        self.overrides_path = Path(overrides_path) if overrides_path else None
        self.overrides = {}; self.preview = {}; self.load_error = ''
        if self.overrides_path and self.overrides_path.exists():
            try:
                saved = json.loads(self.overrides_path.read_text(encoding='utf-8-sig'))
                self.overrides, self.preview = self.validate_settings(saved)
            except (ValueError, OSError, AttributeError) as exc:
                self.overrides = {}; self.preview = {}; self.load_error = str(exc)

    @classmethod
    def validate_settings(cls, saved):
        if not isinstance(saved,dict): raise ValueError('효과 설정 형식 오류')
        names = {}; preview = {}
        if saved.get('version') != 1 or not isinstance(saved.get('names'), dict):
            raise ValueError('지원하지 않는 효과 이름 설정 형식')
        if not isinstance(saved.get('preview', {}), dict): raise ValueError('효과 표시 설정 형식 오류')
        for key, name in saved['names'].items():
            code = cls.parse_code(key)
            if not isinstance(name, str) or not name.strip() or len(name) > 120: raise ValueError('효과 이름은 1~120자로 입력하세요.')
            names[str(code)] = name.strip()
        for key, value in saved.get('preview', {}).items():
            if not isinstance(value, dict): raise ValueError('효과 표시 설정 형식 오류')
            code = cls.parse_code(key)
            color = cls.parse_color(value.get('color', ''))
            enabled = value.get('enabled', False)
            own = value.get('own', True); target = value.get('target', True)
            display_mode = value.get('display_mode', 'image')
            if display_mode not in ('image','color'): raise ValueError('효과 표시 방식 오류')
            if not all(isinstance(flag,bool) for flag in (enabled,own,target)) or (enabled and display_mode == 'color' and not color):
                raise ValueError('미리보기 색상 설정 오류')
            if not isinstance(value.get('favorite',False),bool):
                raise ValueError('즐겨찾기 설정 오류')
            remaining_time = value.get('remaining_time', False)
            priority = value.get('priority', 0)
            if not isinstance(remaining_time, bool) or type(priority) is not int or not 0 <= priority <= 9999:
                raise ValueError('남은시간·우선순위 설정 오류')
            cls.validate_speech(value)
            cls.validate_tcp(value)
            preview[str(code)] = dict(value, color=color, enabled=enabled, own=own, target=target,
                remaining_time=remaining_time, priority=priority, display_mode=display_mode)
        destinations={}
        for code,value in preview.items():
            for roles,name,on,off in cls.tcp_channels(code,value):
                if name in ('게임연결','내캐릭터','대상감지','대상이름'):raise ValueError('이 통신 내용 이름은 시스템 상태에서 사용 중입니다.')
                if name in destinations:raise ValueError('통신 내용 이름이 중복됩니다. 나와 대상에 서로 다른 이름을 입력하세요.')
                destinations[name]=code
        return names, preview

    @staticmethod
    def validate_speech(value):
        if value.get('speech_scope','both') not in ('own','target','both'): raise ValueError('음성 알림 대상 설정 오류')
        for field in ('speech_enabled','speech_include_time'):
            if not isinstance(value.get(field,False),bool): raise ValueError('음성 설정 형식 오류')
        if value.get('speech_event','ending') not in ('start','ending'): raise ValueError('음성 알림 시점 오류')
        seconds=value.get('speech_seconds',3)
        if type(seconds) is not int or not 0 <= seconds <= 300: raise ValueError('음성 알림 시간은 0~300초입니다.')
        text=value.get('speech_text','')
        if not isinstance(text,str) or len(text)>240: raise ValueError('음성 문구는 240자 이하로 입력하세요.')

    @staticmethod
    def parse_code(text):
        text = str(text).strip()
        if text in ATTACK_EFFECTS: return text
        try: code = int(text, 16 if text.lower().startswith('0x') else 10)
        except ValueError as exc: raise ValueError('효과 코드는 정수로 입력하세요. 예: 10014 또는 0x271E') from exc
        if not -2147483648 <= code <= 2147483647: raise ValueError('효과 코드 범위를 벗어났습니다')
        return code

    @staticmethod
    def parse_color(text):
        value = str(text).strip().lstrip('#')
        if not value: return ''
        if not re.fullmatch('[0-9a-fA-F]{6}', value):
            raise ValueError('색상은 FE2B2B 또는 #FE2B2B처럼 6자리 HEX로 입력하세요.')
        return '#' + value.upper()

    def save_effect(self, code, name, color, enabled, own=None, target=None, remaining_time=None, priority=None, display_mode=None, speech=None, tcp=None):
        code = self.parse_code(code); color = self.parse_color(color)
        prior = dict(self.preview.get(str(code),{}))
        if tcp is not None:
            self.validate_tcp(tcp)
            prior.update({key:value for key,value in tcp.items() if key.startswith('tcp_')})
        if speech is not None:
            self.validate_speech(speech)
            prior.update({key:value for key,value in speech.items() if key.startswith('speech_')})
        display_mode = prior.get('display_mode','image') if display_mode is None else display_mode
        if display_mode not in ('image','color'): raise ValueError('효과 표시 방식 오류')
        if enabled and display_mode == 'color' and not color: raise ValueError('색상으로 표시하려면 색상을 먼저 지정해주세요.')
        names = dict(self.overrides); name = name.strip()
        if len(name) > 120: raise ValueError('이름은 120자 이하로 입력하세요')
        if name: names[str(code)] = name
        preview = dict(self.preview)
        own = prior.get('own',True) if own is None else bool(own)
        target = prior.get('target',True) if target is None else bool(target)
        remaining_time = prior.get('remaining_time',False) if remaining_time is None else bool(remaining_time)
        priority = prior.get('priority',0) if priority is None else priority
        if type(priority) is not int or not 0 <= priority <= 9999:
            raise ValueError('우선순위는 0~9999로 입력하세요. 0은 지정 없음입니다.')
        if color or enabled or not own or not target or remaining_time or priority or prior.get('favorite',False) or display_mode != 'image' or any(key.startswith(('speech_','tcp_')) for key in prior):
            preview[str(code)] = dict(prior, color=color, enabled=bool(enabled), own=own, target=target,
                remaining_time=remaining_time, priority=priority, display_mode=display_mode)
        else: preview.pop(str(code), None)
        if tcp is not None:self.validate_settings(dict(version=1,names=names,preview=preview))
        self._save(names, preview)

    @staticmethod
    def tcp_value(text):
        import math
        text=text.strip()
        aliases={'참':True,'거짓':False,'true':True,'false':False}
        if text.lower() in aliases:return aliases[text.lower()]
        try:value=json.loads(text)
        except ValueError:return text
        if not isinstance(value,(str,bool,int,float)) or isinstance(value,float) and not math.isfinite(value):
            raise ValueError('통신 값은 참/거짓, 숫자 또는 문자열이어야 합니다.')
        return value

    @classmethod
    def validate_tcp(cls,value):
        if not isinstance(value.get('tcp_enabled',False),bool):raise ValueError('통신 전송 설정 오류')
        if value.get('tcp_scope','both') not in ('own','target','both'):raise ValueError('통신 전송 대상 오류')
        if not isinstance(value.get('tcp_separate',False),bool):raise ValueError('통신 구분 설정 오류')
        fields=[('tcp_name',''),('tcp_on','true'),('tcp_off','false')]
        if value.get('tcp_separate',False):
            fields=[('tcp_'+role+'_'+field,default) for role in ('own','target') for field,default in (('name',''),('on','true'),('off','false'))]
        for field,default in fields:
            text=value.get(field,default)
            if not isinstance(text,str) or len(text)>120 or any(ord(c)<32 for c in text):raise ValueError('통신 내용은 120자 이하 한 줄로 입력하세요.')
            if not field.endswith('_name'):
                if not text.strip():raise ValueError('버프 켜짐/꺼짐의 통신 값을 입력하세요.')
                cls.tcp_value(text.strip())

    @classmethod
    def tcp_channels(cls,code,config):
        roles=('own','target') if config.get('tcp_scope','both')=='both' else (config.get('tcp_scope','both'),)
        if config.get('tcp_separate',False):
            return [((role,),config.get('tcp_'+role+'_name','').strip() or ('내효과.' if role=='own' else '대상효과.')+str(code),
                     config.get('tcp_'+role+'_on','true'),config.get('tcp_'+role+'_off','false')) for role in roles]
        alias=config.get('tcp_name','').strip()
        if alias:return [(roles,alias,config.get('tcp_on','true'),config.get('tcp_off','false'))]
        return [((role,),('내효과.' if role=='own' else '대상효과.')+str(code),config.get('tcp_on','true'),config.get('tcp_off','false')) for role in roles]

    def set_preview(self, code, color, enabled, own=None, target=None, remaining_time=None, priority=None, display_mode=None):
        self.save_effect(code, '', color, enabled, own, target, remaining_time, priority, display_mode)

    def set_favorite(self, code, favorite):
        code = str(self.parse_code(code))
        preview = dict(self.preview)
        preview[code] = dict(preview.get(code,{}),favorite=bool(favorite))
        self._save(dict(self.overrides),preview)

    def save_name(self, code, name):
        code = self.parse_code(code); name = name.strip()
        if not name: raise ValueError('표시할 이름을 입력하세요')
        if len(name) > 120: raise ValueError('이름은 120자 이하로 입력하세요')
        self._save(dict(self.overrides, **{str(code): name}))

    def remove_name(self, code):
        code = self.parse_code(code); names = dict(self.overrides)
        names.pop(str(code), None); self._save(names)

    def _save(self, names, preview=None):
        if self.load_error: raise ValueError('기존 효과 이름 설정을 읽지 못했습니다: ' + self.load_error)
        if not self.overrides_path: raise ValueError('효과 이름 저장 경로가 없습니다')
        from .analysis import save_json
        preview = self.preview if preview is None else preview
        save_json(self.overrides_path, {'version': 1, 'names': names, 'preview': preview})
        self.overrides = names
        self.preview = preview

    def get(self, code):
        metadata = dict(self.entries.get(str(code), {}))
        if str(code) in self.overrides:
            metadata['Name'] = self.overrides[str(code)]; metadata['CustomName'] = True
        return metadata

    def name(self, code):
        return self.get(code).get('Name') or str(code)
