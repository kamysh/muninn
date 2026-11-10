#!/usr/bin/env python3
"""Check current literal MCP names against the formal catalog.

This check deliberately does not claim handler/proof correspondence. Unsupported
Rust syntax is an error so the check cannot silently skip a new registration.
"""
from collections import Counter
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
TOKEN = re.compile(r'''\s+|//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|=>|[^\s]''', re.S)
PAIR = {'{': '}', '[': ']', '(': ')'}


def tokens(source):
    parts = TOKEN.findall(source)
    if ''.join(parts) != source:
        raise ValueError('source contains an unsupported token')
    if any(part.startswith('/*') and '/*' in part[2:] for part in parts):
        raise ValueError('nested Rust comments require a Rust-aware catalog parser')
    result = [p for p in parts if not p.isspace() and not p.startswith(('//', '/*'))]
    if any(token in ('r', 'br') and index + 1 < len(result) and
           (result[index + 1] == '#' or result[index + 1].startswith('"'))
           for index, token in enumerate(result)):
        raise ValueError('raw string syntax requires a Rust-aware catalog parser')
    return result


def string(token):
    if not (token.startswith('"') and token.endswith('"')) or '\\' in token:
        raise ValueError('expected an unescaped literal wire name: ' + token)
    return token[1:-1]


def end(tokens_, start):
    stack = []
    for i in range(start, len(tokens_)):
        token = tokens_[i]
        if token in PAIR:
            stack.append(PAIR[token])
        elif token in PAIR.values():
            if not stack or stack.pop() != token:
                raise ValueError('unbalanced delimiters')
            if not stack:
                return i
    raise ValueError('unterminated group')


def advertised(ts):
    handlers = [i for i in range(len(ts) - 1) if ts[i:i+2] == ['fn', 'handle_request']]
    if len(handlers) != 1:
        raise ValueError('expected one MCP request handler')
    handler_start = next((i for i in range(handlers[0] + 2, len(ts)) if ts[i] == '{'), None)
    if handler_start is None:
        raise ValueError('missing MCP request handler body')
    handler_end = end(ts, handler_start)
    branches = [i for i in range(handler_start, handler_end - 2)
                if ts[i:i+3] == ['"tools/list"', '=>', '{']]
    if len(branches) != 1:
        raise ValueError('expected one literal tools/list branch')
    branch_start = branches[0] + 2
    branch_end = end(ts, branch_start)
    matches = [i for i in range(branch_start, branch_end - 2) if ts[i:i+3] == ['"tools"', ':', '[']]
    if len(matches) != 1:
        raise ValueError('expected one literal tools list in tools/list branch')
    start = matches[0] + 2
    stop = end(ts, start)
    i, names = start + 1, []
    while i < stop:
        if ts[i] == ',':
            i += 1
            continue
        if ts[i] != '{':
            raise ValueError('tool entry is not a literal object')
        last = end(ts, i)
        j, found = i + 1, []
        while j < last:
            if ts[j] == '"name"' and j + 2 < last and ts[j+1] == ':':
                found.append(string(ts[j+2]))
                j += 3
            elif ts[j] in PAIR:
                j = end(ts, j) + 1
            else:
                j += 1
        if len(found) != 1:
            raise ValueError('tool entry must contain exactly one literal name')
        names.extend(found)
        i = last + 1
    return names


def dispatched(ts):
    starts = [i for i in range(len(ts)-1) if ts[i:i+2] == ['fn', 'dispatch_tool']]
    if len(starts) != 1:
        raise ValueError('expected one dispatch_tool function')
    function_start = next((i for i in range(starts[0] + 2, len(ts)) if ts[i] == '{'), None)
    if function_start is None:
        raise ValueError('missing dispatch_tool body')
    function_end = end(ts, function_start)
    starts = [i for i in range(function_start, function_end - 2) if ts[i:i+3] == ['match', 'name', '{']]
    if len(starts) != 1:
        raise ValueError('expected one match on the tool name')
    start = starts[0] + 2
    stop = end(ts, start)
    i, names, fallback = start + 1, [], False
    while i < stop:
        if ts[i] == ',':
            i += 1
            continue
        if i + 1 >= stop or ts[i+1] != '=>':
            raise ValueError('unsupported dispatch arm')
        if ts[i].startswith('"'):
            if fallback:
                raise ValueError('tool arm follows fallback')
            name = string(ts[i])
        elif ts[i] in ('_', 'other') and not fallback:
            fallback = True
            name = None
        else:
            raise ValueError('unsupported dispatch pattern')
        i += 2
        body_start = i
        if i < stop and ts[i] == '{':
            i = end(ts, i) + 1
        else:
            while i < stop and ts[i] != ',':
                if ts[i] in PAIR:
                    i = end(ts, i) + 1
                else:
                    i += 1
        if name is not None:
            calls = [ts[j + 3] for j in range(body_start, i - 4)
                     if ts[j:j+3] == ['tools', ':', ':'] and ts[j+4] == '(']
            if len(calls) != 1:
                raise ValueError(f'{name}: expected exactly one direct tools handler call')
            names.append((name, calls[0]))
    if not fallback:
        raise ValueError('missing dispatch fallback')
    return names


def formal(source):
    declarations = re.findall(r'^wireName\s+(\w+)\s*=\s*"([^"\\]+)"\s*$', source, re.M)
    matches = re.findall(r'^data McpTool : Set where\s*\n(.*?)(?=\n\S)', source, re.M | re.S)
    if len(matches) != 1:
        raise ValueError('expected one McpTool declaration')
    constructors = []
    for line in matches[0].splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r'\s*([A-Za-z0-9_ ]+)\s*:\s*McpTool\s*', line)
        if not match:
            raise ValueError('unsupported McpTool declaration')
        constructors.extend(match.group(1).split())
    declared = [constructor for constructor, _ in declarations]
    check('formal constructors', constructors, declared)
    decoders = re.findall(r'^decodeTool\s+"([^"\\]+)"\s*=\s*just\s+(\w+)\s*$', source, re.M)
    decoder_clauses = re.findall(r'^decodeTool\s+(.+)$', source, re.M)
    decoder_clauses = [clause for clause in decoder_clauses if not clause.startswith(':')]
    if sum(clause.strip() == '_ = nothing' for clause in decoder_clauses) != 1 or len(decoder_clauses) != len(decoders) + 1:
        raise ValueError('formal decoder must reject every unknown name')
    check('formal decoder', [name + ':' + constructor for constructor, name in declarations],
          [name + ':' + constructor for name, constructor in decoders])
    intents = re.findall(r'^mcpIntent\s+(\w+)\s*=\s*[^\n]+$', source, re.M)
    check('formal intents', constructors, intents)
    return declarations


def check(label, expected, actual):
    for name, count in Counter(actual).items():
        if count != 1:
            raise ValueError(f'{label}: duplicate {name!r}')
    if Counter(expected) != Counter(actual):
        raise ValueError(f'{label}: expected {sorted(expected)}, found {sorted(actual)}')


def check_implementations(implementations, sites):
    for constructor, handler in sites:
        count = sum(implementations[i:i+2] == ['fn', handler] for i in range(len(implementations)-1))
        if count != 1:
            raise ValueError(f'{constructor}: expected exactly one handler definition for {handler}')


def main():
    rust = tokens((ROOT / 'crates/mcp/src/main.rs').read_text())
    declarations = formal((ROOT / 'spec/Muninn/Catalog.agda').read_text())
    inventory = (ROOT / 'spec/Muninn/CatalogSources.agda').read_text()
    sites = re.findall(r'^mcpSite\s+(\w+)\s*=\s*site\s+mcpTools\s+"([^"\\]+)"\s*$', inventory, re.M)
    check('formal source sites', [constructor for constructor, _ in declarations],
          [constructor for constructor, _ in sites])
    site_by_constructor = dict(sites)
    expected = [name for _, name in declarations]
    check('advertised tools', expected, advertised(rust))
    check('dispatch arms', [name + ':' + site_by_constructor[constructor]
                            for constructor, name in declarations],
          [name + ':' + handler for name, handler in dispatched(rust)])
    check_implementations(tokens((ROOT / 'crates/mcp/src/tools.rs').read_text()), sites)
    print(f'{len(expected)} advertised and dispatched tools match the formal wire names')
    print('Proof registration and Rust effect correspondence remain unchecked (#51, #52).')


if __name__ == '__main__':
    try:
        main()
    except ValueError as error:
        print(f'MCP catalog check: {error}', file=sys.stderr)
        sys.exit(1)
