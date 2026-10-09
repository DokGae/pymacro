"""In-memory effect edits; persistent catalogs change only on explicit save."""
import copy
from packetcore.catalog import BuffCatalog

DEFAULTS=dict(color='',enabled=False,own=True,target=True,remaining_time=False,priority=0,
              favorite=False,display_mode='image',speech_enabled=False,speech_event='ending',
              speech_seconds=3,speech_text='',speech_include_time=False,
              tcp_enabled=False,tcp_scope='both',tcp_name='',tcp_on='true',tcp_off='false')


def normalized(value):
    result=dict(DEFAULTS,**value)
    result.setdefault('speech_scope','both' if result['own'] and result['target'] else ('own' if result['own'] else 'target'))
    return result


class DraftCatalog(BuffCatalog):
    def __init__(self,original):
        self.__dict__.update(original.__dict__)
        self.original=original;self.overrides=copy.deepcopy(original.overrides);self.preview=copy.deepcopy(original.preview)

    def _save(self,names,preview=None):
        if self.load_error:raise ValueError('기존 효과 설정을 읽지 못했습니다: '+self.load_error)
        preview=self.preview if preview is None else preview
        names,preview=self.validate_settings(dict(version=1,names=names,preview=preview))
        for code in set(preview)|set(self.original.preview):
            if normalized(preview.get(code,{}))==normalized(self.original.preview.get(code,{})):
                if code in self.original.preview:preview[code]=copy.deepcopy(self.original.preview[code])
                else:preview.pop(code,None)
        self.overrides=names;self.preview=preview

    def dirty_codes(self):
        return {code for code in set(self.preview)|set(self.overrides)|set(self.original.preview)|set(self.original.overrides)
                if self.overrides.get(code)!=self.original.overrides.get(code)
                or normalized(self.preview.get(code,{}))!=normalized(self.original.preview.get(code,{}))}

    def dirty_columns(self,code):
        code=str(code);now=normalized(self.preview.get(code,{}));before=normalized(self.original.preview.get(code,{}))
        fields={0:'favorite',6:'enabled',7:'own',8:'target',9:'color',10:'remaining_time',11:'priority',12:'display_mode',14:'tcp_enabled'}
        columns={column for column,field in fields.items() if now[field]!=before[field]}
        if self.overrides.get(code)!=self.original.overrides.get(code):columns.update((2,4))
        if any(now.get(field)!=before.get(field) for field in set(now)|set(before) if field.startswith('speech_')):columns.add(13)
        if any(now.get(field)!=before.get(field) for field in set(now)|set(before) if field.startswith('tcp_')):columns.update((2,14))
        return columns

    def commit(self):
        if self.dirty_codes():self.original._save(copy.deepcopy(self.overrides),copy.deepcopy(self.preview))

    def discard(self):
        self.overrides=copy.deepcopy(self.original.overrides);self.preview=copy.deepcopy(self.original.preview)
