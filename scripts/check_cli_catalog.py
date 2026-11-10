#!/usr/bin/env python3
"""Check current CLI/TUI declarations against the closed formal catalog.

The mapping is an inventory, not a proof of Rust branch semantics. Unfamiliar
source forms fail the check instead of silently omitting declarations.
"""
from collections import Counter
import json
from pathlib import Path
import re
import sys

import check_mcp_catalog as rust

ROOT = Path(__file__).resolve().parents[1]


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate manifest key {key!r}')
        result[key] = value
    return result


def constructors(source, name):
    pattern = r'^data ' + re.escape(name) + r' : Set where\s*\n(.*?)(?=\n\S)'
    found = re.findall(pattern, source, re.M | re.S)
    if len(found) != 1:
        raise ValueError(f'expected one formal {name} declaration')
    result = []
    for line in found[0].splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r'\s*([A-Za-z0-9_ ]+)\s*:\s*' + name + r'\s*', line)
        if not match:
            raise ValueError(f'unsupported formal {name} declaration')
        result.extend(match.group(1).split())
    if len(result) != len(set(result)):
        raise ValueError(f'duplicate formal {name} constructor')
    return result


def variants(source, name):
    ts = rust.tokens(source)
    starts = [i for i in range(len(ts)-2) if ts[i:i+2] == ['enum', name] and ts[i+2] == '{']
    if len(starts) != 1:
        raise ValueError(f'expected one Rust enum {name}')
    start = starts[0] + 2
    stop = rust.end(ts, start)
    result, i = [], start + 1
    while i < stop:
        if ts[i] == ',':
            i += 1
            continue
        if ts[i] == '#' and i + 1 < stop and ts[i+1] == '[':
            i = rust.end(ts, i + 1) + 1
            continue
        name_token = ts[i]
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name_token):
            raise ValueError(f'unsupported variant in {name}: {name_token}')
        result.append(name_token)
        i += 1
        if i < stop and ts[i] in ('(', '{'):
            i = rust.end(ts, i) + 1
        if i < stop and ts[i] != ',':
            raise ValueError(f'unsupported syntax after {name}.{name_token}')
    if len(result) != len(set(result)):
        raise ValueError(f'duplicate variant in {name}')
    return result


def enum_fields(source, name, detailed=False):
    ts = rust.tokens(source)
    starts = [i for i in range(len(ts)-2) if ts[i:i+2] == ['enum', name] and ts[i+2] == '{']
    if len(starts) != 1:
        raise ValueError(f'expected one Rust enum {name}')
    stop, i, result = rust.end(ts, starts[0] + 2), starts[0] + 3, {}
    while i < stop:
        if ts[i] == ',':
            i += 1
            continue
        variant = ts[i]
        i += 1
        fields, details, attrs = [], {}, []
        if i < stop and ts[i] == '{':
            last = rust.end(ts, i)
            j = i + 1
            while j < last:
                if ts[j] == ',':
                    j += 1
                    continue
                if ts[j] == '#' and j + 1 < last and ts[j+1] == '[':
                    attr_end = rust.end(ts, j + 1)
                    attrs.append(''.join(ts[j:attr_end + 1]))
                    j = attr_end + 1
                    continue
                if j + 1 >= last or ts[j+1] != ':':
                    raise ValueError(f'unsupported field in {name}.{variant}')
                field = ts[j]
                fields.append(field)
                j += 2
                type_start = j
                angle = 0
                while j < last:
                    if ts[j] == '<':
                        angle += 1
                    elif ts[j] == '>':
                        angle -= 1
                    elif ts[j] == ',' and angle == 0:
                        break
                    elif ts[j] in rust.PAIR:
                        j = rust.end(ts, j) + 1
                        continue
                    j += 1
                if angle != 0:
                    raise ValueError(f'unbalanced field type in {name}.{variant}')
                details[field] = {'attributes': attrs, 'type': ''.join(ts[type_start:j])}
                attrs = []
            i = last + 1
        elif i < stop and ts[i] == '(':
            raise ValueError(f'unsupported positional arguments in {name}.{variant}')
        if variant in result or len(fields) != len(set(fields)):
            raise ValueError(f'duplicate {name}.{variant} or its fields')
        result[variant] = details if detailed else fields
    return result


def scope_fields(source):
    ts = rust.tokens(source)
    starts = [i for i in range(len(ts)-2) if ts[i:i+3] == ['struct', 'ScopeArgs', '{']]
    if len(starts) != 1:
        raise ValueError('expected one global scope declaration')
    start = starts[0] + 2
    stop = rust.end(ts, start)
    header = ts[max(0, starts[0]-30):starts[0]]
    if not contains(header, ['group', '(', 'multiple', '=', 'false', ')']):
        raise ValueError('global scope group behavior changed')
    synthetic = 'enum ScopeEnvelope { Scope { ' + ' '.join(ts[start+1:stop]) + ' } }'
    return enum_fields(synthetic, 'ScopeEnvelope', detailed=True)['Scope']


def dispatch_variants(source, function, enum):
    ts = rust.tokens(source)
    starts = [i for i in range(len(ts)-1) if ts[i:i+2] == ['fn', function]]
    if len(starts) != 1:
        raise ValueError(f'expected one {function} function')
    start = next((i for i in range(starts[0]+2, len(ts)) if ts[i] == '{'), None)
    if start is None:
        raise ValueError(f'missing {function} body')
    stop = rust.end(ts, start)
    return sorted({ts[i+3] for i in range(start, stop-3)
                   if ts[i:i+3] == [enum, ':', ':'] and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', ts[i+3])})


def contains(tokens, sequence):
    return any(tokens[i:i+len(sequence)] == sequence for i in range(len(tokens)-len(sequence)+1))


def function_tokens(source, function):
    ts = rust.tokens(source)
    starts = [i for i in range(len(ts)-1) if ts[i:i+2] == ['fn', function]]
    if len(starts) != 1:
        raise ValueError(f'expected one {function} function')
    start = next((i for i in range(starts[0]+2, len(ts)) if ts[i] == '{'), None)
    if start is None:
        raise ValueError(f'missing {function} body')
    return ts[start:rust.end(ts, start)+1]


def check_controls(source, routes):
    expected = {'startup': 'control:startup', 'help': 'control:help',
                'version': 'control:version', 'foregroundInterrupt': 'control:interrupt'}
    if routes != expected:
        raise ValueError('CLI control-route mapping differs from the formal inventory')
    ts = rust.tokens(source)
    structs = [i for i in range(len(ts)-1) if ts[i:i+2] == ['struct', 'Cli']]
    if len(structs) != 1:
        raise ValueError('expected one CLI parser declaration')
    command_attrs = [i for i in range(structs[0]) if ts[i:i+4] == ['#', '[', 'command', '(']
                     and rust.end(ts, i+1) == structs[0]-1]
    if len(command_attrs) != 1 or 'version' not in ts[command_attrs[0]:structs[0]]:
        raise ValueError('CLI version parser metadata is missing')
    derives = [i for i in range(command_attrs[0]) if ts[i:i+4] == ['#', '[', 'derive', '(']
               and rust.end(ts, i+1) == command_attrs[0]-1]
    if len(derives) != 1 or not contains(ts[derives[0]:command_attrs[0]], ['derive', '(', 'Parser', ')']):
        raise ValueError('CLI help parser metadata is missing')
    if not contains(function_tokens(source, 'main'), ['Cli', ':', ':', 'try_parse', '(', ')']):
        raise ValueError('CLI startup does not invoke the declared parser')
    if not contains(function_tokens(source, 'run_foreground_index'),
                    ['tokio', ':', ':', 'signal', ':', ':', 'ctrl_c', '(', ')']):
        raise ValueError('foreground interrupt route is missing')


def check_backend(sources, inventory, manifest_sites, legal_tui):
    sites = re.findall(r'^tuiSite\s+(\w+)\s*=\s*site\s+(\w+)\s+"([^"\\]+)"\s*$', inventory, re.M)
    rust.check('formal TUI source sites', list(legal_tui), [name for name, _, _ in sites])
    actual = {name: owner + ':' + symbol for name, owner, symbol in sites}
    if actual != manifest_sites:
        raise ValueError('TUI backend source-site mapping differs from the formal inventory')
    ts = rust.tokens(sources['crates/cli/src/tui/backend.rs'])
    starts = [i for i in range(len(ts)-2) if ts[i:i+3] == ['trait', 'Backend', '{']]
    if len(starts) != 1:
        raise ValueError('expected one editor backend trait')
    start, stop = starts[0] + 2, rust.end(ts, starts[0] + 2)
    methods = [ts[i+1] for i in range(start, stop-1) if ts[i] == 'fn']
    rust.check('editor backend trait', ['load', 'check', 'save', 'start', 'start_with_progress'], methods)
    editor = rust.tokens(sources['crates/cli/src/tui/mod.rs'])
    for method in ('load', 'check', 'save', 'start_with_progress'):
        if not contains(editor, ['backend', '.', method, '(']):
            raise ValueError(f'editor does not call backend {method}')
    if not contains(ts[start:stop], ['self', '.', 'start', '(']):
        raise ValueError('progress-start adapter does not route to start')
    main = sources['crates/cli/src/main.rs']
    if not contains(rust.tokens(main), ['fn', 'persist_global']):
        raise ValueError('global settings persistence entry is missing')
    global_route = function_tokens(main, 'handle_global_config')
    if not contains(global_route, ['tui', ':', ':', 'global', ':', ':', 'run', '(']) or not contains(global_route, ['persist_global', '(']):
        raise ValueError('global editor does not route through settings persistence')


def validate(manifest, sources, catalog, inputs, inventory):
    expected_groups = {
        'commands': ('crates/cli/src/main.rs', 'Commands'),
        'config_operations': ('crates/cli/src/main.rs', 'ConfigOp'),
        'family_actions': ('crates/cli/src/tui/mod.rs', 'Action'),
        'family_confirmations': ('crates/cli/src/tui/mod.rs', 'Confirm'),
        'family_modals': ('crates/cli/src/tui/mod.rs', 'Modal'),
        'global_actions': ('crates/cli/src/tui/global.rs', 'Action'),
        'global_modals': ('crates/cli/src/tui/global.rs', 'Modal'),
        'family_fields': ('crates/cli/src/tui/model.rs', 'Field'),
        'family_views': ('crates/cli/src/tui/model.rs', 'View'),
    }
    if set(manifest) != set(expected_groups) | {'arguments', 'argument_details', 'scope_details', 'control_routes', 'backend_sites'}:
        raise ValueError('manifest groups do not match required CLI and TUI declarations')
    legal = {
        'cli': set(constructors(catalog, 'CliLeaf')),
        'tui': set(constructors(catalog, 'TuiEffect')),
        'ui': set(constructors(inputs, 'UiAction')),
        'control': set(constructors(inputs, 'Control')),
    }
    check_controls(sources['crates/cli/src/main.rs'], manifest['control_routes'])
    for target in manifest['control_routes'].values():
        kind, entry = target.split(':')
        if kind != 'control' or entry not in legal['control']:
            raise ValueError(f'unknown formal control target {target}')
    check_backend(sources, inventory, manifest['backend_sites'], legal['tui'])
    if scope_fields(sources['crates/cli/src/main.rs']) != manifest['scope_details']:
        raise ValueError('global scope argument type or parser attributes changed')
    arguments = manifest['arguments']
    details = manifest['argument_details']
    if not isinstance(arguments, dict) or set(arguments) != {'commands', 'config_operations'}:
        raise ValueError('argument inventory must cover commands and config operations')
    if not isinstance(details, dict) or set(details) != {'commands', 'config_operations'}:
        raise ValueError('argument details must cover commands and config operations')
    for group, function in [('commands', 'main'), ('config_operations', 'handle_global_config')]:
        filename, enum = expected_groups[group]
        actual = enum_fields(sources[filename], enum)
        expected = arguments[group]
        if enum_fields(sources[filename], enum, detailed=True) != details[group]:
            raise ValueError(f'{group}: argument type or parser attributes changed')
        if set(actual) != set(expected):
            raise ValueError(f'{group}: argument inventory misses variants')
        for variant, fields in actual.items():
            rust.check(f'{group}.{variant} arguments', fields, expected[variant])
        rust.check(f'{group} dispatch', list(actual), dispatch_variants(sources[filename], function, enum))
    used = {kind: set() for kind in legal}
    for group, (filename, enum) in expected_groups.items():
        mapping = manifest[group]
        if not isinstance(mapping, dict):
            raise ValueError(f'{group}: expected variant mapping')
        rust.check(group, variants(sources[filename], enum), list(mapping))
        for variant, targets in mapping.items():
            if not isinstance(targets, list) or not targets or len(targets) != len(set(targets)):
                raise ValueError(f'{group}.{variant}: targets must be a nonempty unique list')
            for target in targets:
                if not isinstance(target, str) or target.count(':') != 1:
                    raise ValueError(f'{group}.{variant}: invalid target')
                kind, entry = target.split(':')
                if kind not in legal or entry not in legal[kind]:
                    raise ValueError(f'{group}.{variant}: unknown formal target {target}')
                used[kind].add(entry)
    for kind in ('cli', 'tui', 'ui'):
        missing = legal[kind] - used[kind]
        if missing:
            raise ValueError(f'unmapped formal {kind} entries: {sorted(missing)}')
    return sum(len(manifest[group]) for group in expected_groups)


def main():
    manifest = json.loads((ROOT / 'spec/CLI-TUI-COVERAGE.json').read_text(), object_pairs_hook=unique_pairs)
    sources = {name: (ROOT / name).read_text() for name in {
        'crates/cli/src/main.rs', 'crates/cli/src/tui/mod.rs',
        'crates/cli/src/tui/global.rs', 'crates/cli/src/tui/model.rs', 'crates/cli/src/tui/backend.rs'}}
    count = validate(manifest, sources, (ROOT / 'spec/Muninn/Catalog.agda').read_text(),
                     (ROOT / 'spec/Muninn/CatalogInputs.agda').read_text(),
                     (ROOT / 'spec/Muninn/CatalogSources.agda').read_text())
    print(f'{count} CLI/TUI declaration variants have formal catalog mappings')
    print('Branch behavior, proof registration and effect correspondence remain unchecked (#51, #52).')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, json.JSONDecodeError) as error:
        print(f'CLI/TUI catalog check: {error}', file=sys.stderr)
        sys.exit(1)
