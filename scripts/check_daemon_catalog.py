#!/usr/bin/env python3
"""Check the finite daemon job inventory against current source call sites.

This detects drift in recorded sites; it does not prove Rust behavior or cover
effects hidden behind arbitrary library calls. Proof enforcement belongs to
the dispatcher and implementation-correspondence work.
"""
from collections import Counter
import json
from pathlib import Path
import re
import sys

import check_mcp_catalog as rust
import check_cli_catalog as cli

ROOT = Path(__file__).resolve().parents[1]
FILES = {
    'main': 'crates/indexer/src/main.rs',
    'watcher': 'crates/indexer/src/watcher.rs',
    'logging': 'crates/indexer/src/logging.rs',
}
FUNCTIONS = {
    'main': ('main', 'wait_for_dispatch', 'scan_and_dispatch'),
    'watcher': ('watch_repo', 'watch_family'),
    'logging': ('start_summaries', 'flush_stderr'),
}
NAMESPACES = {'db', 'store', 'pipeline', 'worktrees', 'family_store', 'watcher', 'tokio', 'notify'}


def call_counts(source, function):
    all_tokens = rust.tokens(source)
    local = {all_tokens[i+1] for i in range(len(all_tokens)-1)
             if all_tokens[i] == 'fn' and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', all_tokens[i+1])}
    local |= {'index_repo', 'index_file'}
    ts = cli.function_tokens(source, function)
    calls = Counter()
    for i, token in enumerate(ts):
        if token in NAMESPACES and i+2 < len(ts) and ts[i+1:i+3] == [':', ':']:
            parts, j = [token], i+1
            while j+2 < len(ts) and ts[j:j+2] == [':', ':']:
                parts.append(ts[j+2])
                j += 3
            if j < len(ts) and ts[j] == '(':
                calls['::'.join(parts)] += 1
        if token in local and i+1 < len(ts) and ts[i+1] == '(' and not (i and ts[i-1] in {'fn', ':', '.'}):
            calls[token] += 1
        if (token in local or token in {'execute', 'query', 'query_one', 'query_opt'}) and i and ts[i-1] == '.' and i+1 < len(ts) and ts[i+1] == '(':
            calls['.' + token] += 1
    return dict(sorted(calls.items()))


RUST_TOKEN = re.compile(r'''\s+|//[^\n]*|/\*.*?\*/|(?:br|r)(?P<hashes>\#*)".*?"(?P=hashes)|b?"(?:\\.|[^"\\])*"|b?'(?:\\.|[^'\\])'|[A-Za-z_][A-Za-z_0-9]*|[^\s]''', re.S)


def definition_tokens(source):
    parts = [match.group(0) for match in RUST_TOKEN.finditer(source)]
    if ''.join(parts) != source:
        raise ValueError('source contains unsupported Rust tokens')
    if any(part.startswith('/*') and '/*' in part[2:] for part in parts):
        raise ValueError('nested comments require a Rust-aware parser')
    return [part for part in parts if not part.isspace() and not part.startswith(('//', '/*'))]


def formal_sites(source):
    paths = re.findall(r'^path\s+(\w+)\s*=\s*"([^"\\]+)"\s*$', source, re.M)
    sites = re.findall(r'^jobCoverage\s+(\w+)\s*=\s*(sourceRecorded|missing)\s+\(site\s+(\w+)\s+"([^"\\]+)"\)(?:\s+(\d+))?\s*$', source, re.M)
    clauses = [line for line in source.splitlines() if line.startswith('jobCoverage ') and '=' in line]
    if len(paths) != len(dict(paths)) or len(sites) != len(clauses):
        raise ValueError('unsupported or duplicate formal source mapping')
    result = {}
    for job, status, owner, symbol, issue in sites:
        if job in result or owner not in dict(paths):
            raise ValueError(f'duplicate job or unknown source for {job}')
        if (status == 'missing') != bool(issue):
            raise ValueError(f'invalid source status for {job}')
        result[job] = {'status': status, 'source': owner, 'symbol': symbol, 'path': dict(paths)[owner],
                       'issue': int(issue) if issue else None}
    return result


def check_schedule(main, watcher):
    ts = cli.function_tokens(main, 'main')
    for channel in ('"LISTEN muninn_repos_changed"', '"LISTEN muninn_family_policy_changed"'):
        if ts.count(channel) != 1:
            raise ValueError(f'missing or duplicate listener registration {channel}')
    scans = [i for i in range(len(ts)-1) if ts[i:i+2] == ['scan_and_dispatch', '(']]
    waits = [i for i in range(len(ts)-1) if ts[i:i+2] == ['wait_for_dispatch', '(']]
    if len(scans) != 2 or len(waits) != 1 or not (scans[0] < waits[0] < scans[1]):
        raise ValueError('initial scan and scan after each wake are not in the expected order')
    listener = cli.function_tokens(main, 'wait_for_dispatch')
    required = [
        ['rx', '.', 'recv', '(', ')', ',', 'if', '*', 'notifications_open', '=>'],
        ['*', 'notifications_open', '=', 'false'],
        ['tokio', ':', ':', 'time', ':', ':', 'sleep', '('],
        ['Duration', ':', ':', 'from_secs', '(', '6', '0', ')'],
    ]
    if any(not cli.contains(listener, pattern) for pattern in required):
        raise ValueError('notification wait or 60-second fallback route changed')
    family = cli.function_tokens(watcher, 'watch_family')
    if not cli.contains(family, ['Duration', ':', ':', 'from_secs', '(', '6', '0', ')']):
        raise ValueError('family watcher fallback interval changed')


def validate(manifest, sources, inputs, inventory, definitions):
    if set(manifest) != {'jobs', 'calls'}:
        raise ValueError('daemon inventory must contain jobs and calls')
    legal_jobs = set(cli.constructors(inputs, 'Job'))
    legal_controls = set(cli.constructors(inputs, 'Control'))
    sites = formal_sites(inventory)
    rust.check('formal jobs', list(legal_jobs), list(sites))
    if manifest['jobs'] != sites:
        raise ValueError('daemon job source inventory differs from the formal catalog')
    for job, site in sites.items():
        if site['status'] == 'sourceRecorded':
            if site['path'] not in definitions:
                raise ValueError(f'missing source file for {job}')
            ts = definition_tokens(definitions[site['path']])
            if not cli.contains(ts, ['fn', site['symbol']]):
                raise ValueError(f'recorded source definition is absent for {job}')
    required = {f'{group}:{fn}' for group, names in FUNCTIONS.items() for fn in names}
    if set(manifest['calls']) != required:
        raise ValueError('daemon function inventory is incomplete')
    for group, names in FUNCTIONS.items():
        for function in names:
            entries = manifest['calls'][f'{group}:{function}']
            observed = call_counts(sources[FILES[group]], function)
            expected = {}
            for call, entry in entries.items():
                if not isinstance(entry, dict) or set(entry) != {'count', 'targets'}:
                    raise ValueError(f'invalid call inventory for {group}:{function}:{call}')
                if not isinstance(entry['count'], int) or isinstance(entry['count'], bool) or entry['count'] < 1:
                    raise ValueError(f'invalid call count for {group}:{function}:{call}')
                targets = entry['targets']
                if not isinstance(targets, list) or not targets or any(not isinstance(t, str) for t in targets) or len(targets) != len(set(targets)):
                    raise ValueError(f'invalid targets for {group}:{function}:{call}')
                for target in targets:
                    if target.count(':') != 1:
                        raise ValueError(f'invalid target {target}')
                    kind, name = target.split(':')
                    if not ((kind == 'job' and name in legal_jobs) or (kind == 'control' and name in legal_controls)):
                        raise ValueError(f'unknown formal target {target}')
                expected[call] = entry['count']
            if observed != expected:
                raise ValueError(f'daemon calls changed in {group}:{function}: expected {expected}, found {observed}')
    check_schedule(sources[FILES['main']], sources[FILES['watcher']])
    return len(sites), sum(len(entries) for entries in manifest['calls'].values())


def main():
    manifest = json.loads((ROOT / 'spec/DAEMON-COVERAGE.json').read_text(), object_pairs_hook=cli.unique_pairs)
    inputs = (ROOT / 'spec/Muninn/CatalogInputs.agda').read_text()
    inventory = (ROOT / 'spec/Muninn/CatalogSources.agda').read_text()
    sites = formal_sites(inventory)
    sources = {filename: (ROOT / filename).read_text() for filename in FILES.values()}
    definitions = {}
    for site in sites.values():
        if site['status'] != 'sourceRecorded':
            continue
        path = (ROOT / site['path']).resolve()
        if not path.is_relative_to(ROOT):
            raise ValueError('recorded source path escapes the repository')
        definitions[site['path']] = path.read_text()
    jobs, calls = validate(manifest, sources, inputs, inventory, definitions)
    missing = sum(site['status'] == 'missing' for site in sites.values())
    print(f'{jobs} formal jobs and {calls} recorded daemon call identities checked; {missing} adapters remain incomplete')
    print('Registered proofs and complete Rust effect correspondence remain unchecked (#51, #52).')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, json.JSONDecodeError) as error:
        print(f'daemon catalog check: {error}', file=sys.stderr)
        sys.exit(1)
