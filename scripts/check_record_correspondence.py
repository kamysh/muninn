#!/usr/bin/env python3
"""Check modeled record categories against the concrete Rust/SQL effects.

The formal side is the owned-state Body constructor list; the Rust side is the
literal write statements in the core crate. Every constructor needs an explicit
manifest entry (mapped, derived, unmapped, local or system), and every physical
table the Rust writes must be accounted for. Unfamiliar source forms fail the
check instead of silently passing.
"""
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'spec/RECORD-CORRESPONDENCE.json'

STATUSES = {'mapped', 'derived', 'unmapped', 'local', 'system'}
STATEMENT = re.compile(
    r'\b(?:INSERT\s+INTO|DELETE\s+FROM)\b'
    r'|\bUPDATE\s+(?!(?:SET|DO)\b)(?=(?:public\.|\{[a-z_]+\}\.)?[a-z_{])')


def formal_constructors(source):
    match = re.search(r'^data Body : Set where\s*\n(.*?)(?=\n\S)', source, re.M | re.S)
    if not match:
        raise ValueError('expected one formal Body declaration')
    result = []
    for line in match.group(1).splitlines():
        if not line.strip():
            continue
        fields = re.fullmatch(r'\s*([A-Za-z0-9_ ]+)\s*:.*', line)
        if not fields:
            raise ValueError('unsupported formal Body declaration: ' + line)
        result.extend(fields.group(1).split())
    if len(result) != len(set(result)):
        raise ValueError('duplicate formal Body constructor')
    return result


def rust_sites():
    """Every persistent write-statement line in the workspace crates."""
    found = {}
    for path in sorted((ROOT / 'crates').rglob('*.rs')):
        rel = str(path.relative_to(ROOT))
        if 'tests' in rel or '_test' in rel:
            continue
        for number, line in enumerate(path.read_text().splitlines(), 1):
            stripped = line.strip()
            if stripped.startswith('//') or 'ON CONFLICT' in line or 'DO UPDATE' in line:
                continue
            if STATEMENT.search(line):
                found[(rel, number)] = line
    return found


def rust_tables():
    tables = {}
    for path in sorted((ROOT / 'crates/core/src').rglob('*.rs')):
        source = path.read_text()
        for number, line in enumerate(source.splitlines(), 1):
            match = STATEMENT.search(line)
            if not match or line.strip().startswith('//'):
                continue
            table = match.group(1).lower()
            if table == 'set':
                # captured from a DO UPDATE SET continuation, not a table
                continue
            if table not in {'pg_advisory_lock', 'pg_advisory_xact_lock'}:
                tables.setdefault(table, []).append(f'{path.relative_to(ROOT)}:{number}')
    return tables


def _verify(constructors, manifest, found):
    if manifest.get('schema') != 1:
        raise ValueError('unsupported manifest schema')
    formal = manifest['formal']
    physical = manifest['physical']
    if set(physical.values()) > set(formal):
        raise ValueError('physical mapping names unknown formal categories')

    missing = [c for c in constructors if c not in formal]
    if missing:
        raise ValueError('formal constructors without manifest entries: ' + ', '.join(missing))
    for name, entry in formal.items():
        if entry.get('status') not in STATUSES:
            raise ValueError(f'unsupported status for {name}: {entry.get("status")}')
        if entry['status'] == 'mapped' and not entry.get('realization'):
            raise ValueError(f'mapped category {name} lacks a realization')
        if entry['status'] in ('unmapped', 'local') and entry.get('sites'):
            raise ValueError(f'{entry["status"]} category {name} lists Rust sites')

    declared = {(entry['file'], entry['line']): entry for entry in manifest.get('sites', [])}
    if len(declared) != len(manifest.get('sites', [])):
        raise ValueError('duplicate manifest site')
    missing = sorted(set(found) - set(declared))
    if missing:
        raise ValueError('undeclared persistent write statements: ' +
                         ', '.join(f'{f}:{n}' for f, n in missing))
    for key, entry in declared.items():
        if key not in found:
            raise ValueError(f'manifested site {key[0]}:{key[1]} no longer has a write statement')
        line = found[key]
        if entry.get('template'):
            if ('{%s}.' % entry['template']) not in line and '{%s}' % entry['template'] not in line:
                raise ValueError(f'site {key[0]}:{key[1]} no longer uses the declared template')
        elif entry['table'] and entry['table'] not in line and 'public.' + entry['table'] not in line:
            raise ValueError(f'site {key[0]}:{key[1]} no longer references the declared table')
    site_tables = {entry['table'] for entry in declared.values() if entry.get('table')}
    unmodeled = sorted(site_tables - set(physical))
    if unmodeled:
        raise ValueError('write-site tables missing from the physical map: ' + ', '.join(unmodeled))
    unmapped = sorted(name for name, entry in formal.items() if entry['status'] == 'unmapped')

    print(f'{len(constructors)} formal record categories manifestly accounted for; '
          f'{len(declared)} Rust write sites declared and matched.')
    if unmapped:
        print('Unmodeled record categories (explicit repair work, #52): ' + ', '.join(unmapped))
    print('Correspondence check passed; the manifest records the honest gaps.')


def main():
    manifest = json.loads(MANIFEST.read_text(), object_pairs_hook=unique_keys)
    constructors = formal_constructors((ROOT / 'spec/Muninn/OwnedState.agda').read_text())
    _verify(constructors, manifest, rust_sites())


def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate manifest key ' + repr(key))
        result[key] = value
    return result


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, json.JSONDecodeError) as error:
        print(f'Record correspondence check: {error}', file=sys.stderr)
        sys.exit(1)
