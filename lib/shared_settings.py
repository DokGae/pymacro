"""Profile-local reusable conditions and precise dependency indexing."""
import copy
import json
import re
import uuid


class SharedSettingError(ValueError):
    pass


def has_shared(condition):
    if not getattr(condition, 'enabled', True):
        return False
    return bool(getattr(condition, 'shared_ref', None)) or any(
        has_shared(child) for key in ('conditions', 'on_true', 'on_false')
        for child in getattr(condition, key, [])
    )


def at_path(root, path):
    for key in path:
        root = root[key]
    return root


def walk_conditions(data, path=(), labels=()):
    if isinstance(data, dict):
        labels = labels + ((str(data['name']),) if data.get('name') else ())
        if 'type' in data and 'pixel_exists' in data and 'sleep_ms' not in data:
            yield path, labels, data
            if data.get('shared_ref'):
                # Local branches remain local; stored condition children are a snapshot.
                for key in ('on_true', 'on_false'):
                    yield from walk_conditions(data.get(key, []), path + (key,), labels)
                return
        for key, value in data.items():
            yield from walk_conditions(value, path + (key,), labels)
    elif isinstance(data, list):
        for index, value in enumerate(data):
            yield from walk_conditions(value, path + (index,), labels)


def definition(condition):
    result = copy.deepcopy(condition)
    for key in ('shared_ref', 'name', 'enabled', 'on_true', 'on_false'):
        result.pop(key, None)
    if result.get('type') == 'pixel':
        result['pixel_exists'] = True
    return result


def fingerprint(condition):
    return json.dumps(definition(condition), sort_keys=True, ensure_ascii=False)


def register(entries, name, condition):
    key = uuid.uuid4().hex
    entries[key] = {'name': name.strip(), 'condition': definition(condition)}
    return key


def expand_condition(data, entries, stack=()):
    result = copy.deepcopy(data)
    if result.get('enabled') is False:
        return result
    reference = result.get('shared_ref')
    if reference:
        if reference in stack:
            raise SharedSettingError('공용 조건이 서로를 참조합니다.')
        entry = entries.get(reference)
        if not entry or not isinstance(entry.get('condition'), dict):
            raise SharedSettingError('연결된 공용 설정이 없습니다. 다시 선택하세요.')
        expanded = expand_condition(entry['condition'], entries, stack + (reference,))
        for key in ('name', 'enabled', 'on_true', 'on_false'):
            if key in result:
                expanded[key] = copy.deepcopy(result[key])
        if expanded.get('type') == 'pixel':
            expanded['pixel_exists'] = result.get('pixel_exists', True)
        expanded.pop('shared_ref', None)
        result = expanded
    for key in ('conditions', 'on_true', 'on_false'):
        if key in result:
            result[key] = [expand_condition(child, entries, stack) for child in result[key]]
    return result


def dependencies(condition, entries, stack=()):
    reference = condition.get('shared_ref')
    if reference:
        yield reference
        if reference in stack or reference not in entries:
            return
        yield from dependencies(entries[reference]['condition'], entries, stack + (reference,))
        keys = ('on_true', 'on_false')
    else:
        keys = ('conditions', 'on_true', 'on_false')
    for key in keys:
        for child in condition.get(key, []):
            yield from dependencies(child, entries, stack)


def condition_usages(macros, entries):
    usages = {}
    direct = []
    for index, macro in enumerate(macros):
        for path, labels, condition in walk_conditions(macro):
            location = {'macro': index, 'path': path, 'label': ' → '.join(labels) or str(path), 'condition': condition}
            if condition.get('shared_ref'):
                # Each local use counts once, including dependencies of a shared group.
                linked = dict(condition, on_true=[], on_false=[])
                for reference in set(dependencies(linked, entries)):
                    usages.setdefault(reference, []).append(location)
            elif condition.get('type') == 'pixel':
                direct.append(location)
    return usages, direct


def duplicate_groups(macro):
    groups = {}
    for path, labels, condition in walk_conditions(macro):
        if condition.get('type') != 'pixel' or condition.get('shared_ref'):
            continue
        groups.setdefault(fingerprint(condition), []).append((path, labels, condition))
    return [group for group in groups.values() if len(group) > 1]


# References are interpreted in the same typed field as VariableResolver.
REF = re.compile(r'\$\{(?P<braced>[^}]+)\}|[/@$](?P<plain>[^\s,+{}]+)')
FIELDS = {'region': 'region', 'region_raw': 'region', 'pixel_region': 'region',
          'pixel_region_raw': 'region', 'mouse_pos_raw': 'region', 'color': 'color',
          'color_raw': 'color', 'key': 'key', 'sleep_raw': 'sleep', 'repeat_raw': 'var',
          'group_repeat_raw': 'var', 'var_value_raw': 'var', 'timer_value_raw': 'var'}


def variable_usages(macros, entries):
    usages = {}
    def visit(value, index, path, labels, stack=()):
        if isinstance(value, dict):
            labels = labels + ((str(value['name']),) if value.get('name') else ())
            ref = value.get('shared_ref')
            if ref and ref in entries and ref not in stack:
                visit(entries[ref]['condition'], index, path, labels, stack + (ref,))
                for key in ('on_true', 'on_false'):
                    visit(value.get(key, []), index, path + (key,), labels, stack)
                return
            seen = set()
            for key, val in value.items():
                category = FIELDS.get(key)
                if category and isinstance(val, str):
                    for match in REF.finditer(val):
                        name = match.group('braced') or match.group('plain')
                        if (category, name) not in seen:
                            usages.setdefault((category, name), []).append({'macro': index, 'path': path + (key,), 'label': ' → '.join(labels) + ' / ' + key})
                            seen.add((category, name))
                if key == 'var_name' and val:
                    usages.setdefault(('var', val), []).append({'macro': index, 'path': path + (key,), 'label': ' → '.join(labels) + ' / 실행 변수'})
                visit(val, index, path + (key,), labels, stack)
        elif isinstance(value, list):
            for i, child in enumerate(value):
                visit(child, index, path + (i,), labels, stack)
    for index, macro in enumerate(macros):
        visit(macro, index, (), ())
    return usages


def materialize_macros(macros, entries):
    """Portable copy without dangling references to another profile."""
    def visit(value):
        if isinstance(value, dict):
            if value.get('shared_ref'):
                value = expand_condition(value, entries)
            return {key: visit(child) for key, child in value.items()}
        if isinstance(value, list):
            return [visit(child) for child in value]
        return copy.deepcopy(value)
    return visit(macros)


def rename_value(data, category, old, new):
    """Rewrite only typed reference fields, never literal labels or names."""
    from engine import VariableResolver
    if isinstance(data, dict):
        for key, value in list(data.items()):
            if key == 'var_name' and category == 'var' and value == old:
                data[key] = new
            elif FIELDS.get(key) == category and isinstance(value, str):
                def replace(match):
                    name = match.group('name') or match.group('name2') or match.group('name3')
                    return '${' + new + '}' if name == old else match.group(0)
                data[key] = VariableResolver._pattern.sub(replace, value)
            else:
                rename_value(value, category, old, new)
    elif isinstance(data, list):
        for child in data:
            rename_value(child, category, old, new)


def import_settings(macros, source, destination):
    """Bring a copied macro's shared dependencies into a destination profile."""
    result = copy.deepcopy(macros)
    mapping = {}
    def ensure(reference, stack=()):
        if reference in mapping:
            return mapping[reference]
        if reference in stack or reference not in source:
            raise SharedSettingError('복사한 매크로의 공용 설정 연결을 확인하세요.')
        original = source[reference]
        if reference in destination and destination[reference] == original:
            mapping[reference] = reference
            return reference
        key = reference if reference not in destination else uuid.uuid4().hex
        entry = copy.deepcopy(original)
        def rewrite(value):
            if isinstance(value, dict):
                if value.get('shared_ref'):
                    value['shared_ref'] = ensure(value['shared_ref'], stack + (reference,))
                for child in value.values():
                    rewrite(child)
            elif isinstance(value, list):
                for child in value:
                    rewrite(child)
        rewrite(entry)
        destination[key] = entry
        mapping[reference] = key
        return key
    def walk(value):
        if isinstance(value, dict):
            if value.get('shared_ref'):
                value['shared_ref'] = ensure(value['shared_ref'])
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)
    walk(result)
    return result


def import_values(macros, entries, source, destination):
    """Copy typed value dependencies and rename conflicts without changing existing users."""
    from engine import VariableResolver
    needed = set(variable_usages(macros, entries))
    lookup = {(kind, item['name']): item for kind, items in source.items() for item in items}
    pending = list(needed)
    while pending:
        kind, name = pending.pop()
        item = lookup.get((kind, name))
        if not item:
            continue
        for match in VariableResolver._pattern.finditer(item['value']):
            child = match.group('name') or match.group('name2') or match.group('name3')
            dependency = (kind, child) if (kind, child) in lookup else ('var', child)
            if dependency not in needed:
                needed.add(dependency)
                pending.append(dependency)
    mapping = {}
    for kind, name in sorted(needed):
        item = lookup.get((kind, name))
        if item is None:
            continue
        current = {x['name']: x for x in destination.setdefault(kind, [])}
        candidate = name
        index = 1
        while candidate in current and current[candidate]['value'] != item['value']:
            candidate = f'{name}_복사{index}'
            index += 1
        mapping[(kind, name)] = candidate
    for (kind, name), candidate in mapping.items():
        if candidate != name:
            rename_value(macros, kind, name, candidate)
            rename_value(entries, kind, name, candidate)
    for (kind, name), candidate in mapping.items():
        item = copy.deepcopy(lookup[(kind, name)])
        def replace(match):
            old = match.group('name') or match.group('name2') or match.group('name3')
            new = mapping.get((kind, old), mapping.get(('var', old), old))
            return '${' + new + '}'
        item['name'] = candidate
        item['value'] = VariableResolver._pattern.sub(replace, item['value'])
        if not any(x['name'] == candidate for x in destination[kind]):
            destination[kind].append(item)
