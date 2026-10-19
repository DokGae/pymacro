"""Image-independent pixel packs, persisted atomically with stable references."""
import json
import os
import tempfile
from pathlib import Path

from lib.pixel import PixelPattern

PACK_FILE = Path(__file__).resolve().parent.parent / 'pattern_packs.json'
PREFIX = 'pack:'


def load_packs(path=None):
    path = Path(path or PACK_FILE)
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding='utf-8'))
    if data.get('version') != 1 or not isinstance(data.get('packs'), dict):
        raise ValueError('픽셀 팩 파일 형식을 확인하세요.')
    return data['packs']


def save_packs(packs, path=None):
    path = Path(path or PACK_FILE)
    fd, tmp = tempfile.mkstemp(dir=path.parent, suffix='.tmp')
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as stream:
            json.dump({'version': 1, 'packs': packs}, stream, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


class PackReference:
    def __init__(self, reference):
        self.reference = reference

    def patterns(self):
        if not self.reference.startswith(PREFIX):
            raise ValueError('기존 픽셀 패턴은 지원하지 않습니다. 팩이나 항목을 다시 선택하세요.')
        pack_id, _, item_id = self.reference[len(PREFIX):].partition('/')
        pack = load_packs().get(pack_id)
        if pack is None:
            raise ValueError('선택한 픽셀 팩이 없습니다.')
        if item_id:
            item = pack['items'].get(item_id)
            if item is None:
                raise ValueError('선택한 팩 항목이 없습니다.')
            items = [item]
        else:
            items = pack['items'].values()
        patterns = [PixelPattern.from_dict(item).normalized() for item in items if item.get('points')]
        if not patterns:
            raise ValueError('팩에 등록된 픽셀이 없습니다.')
        return patterns


def resolve_pattern(patterns, name):
    return PackReference(name) if name else None


def pattern_label(name):
    if name and name.startswith(PREFIX):
        pack_id, _, item_id = name[len(PREFIX):].partition('/')
        pack = load_packs().get(pack_id)
        if pack is None:
            return '삭제된 팩'
        target = pack['items'].get(item_id, {}).get('name', '삭제된 항목') if item_id else '전체'
        return f"{pack['name']} / {target}"
    return name


def pack_choices():
    for key, pack in load_packs().items():
        yield f"{pack['name']} / 전체", PREFIX + key
        for item_id, item in pack['items'].items():
            yield f"{pack['name']} / {item['name']}", PREFIX + key + '/' + item_id
