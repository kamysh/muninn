#!/usr/bin/env python3
"""Check the adapter's CRASH_BOUNDARIES registration against the manifest.

A crash at an unregistered commit boundary cannot be retried against the
independently specified world outcome, so the coverage stays red until the
adapter registers every boundary from spec/CRASH-BOUNDARIES.json. A manifest
whose adapter status is "absent" has nothing to compare yet: the comparison
is skipped with a notice instead of blocking branches that legitimately
predate the adapter.
"""
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def verify(manifest, adapter):
    if manifest.get('schema') != 1:
        raise ValueError('unsupported manifest schema')
    required = [entry['name'] for entry in manifest['boundaries']]
    if len(required) != len(set(required)):
        raise ValueError('duplicate boundary name in the manifest')

    symbol = manifest['adapter_registration']['symbol']
    match = re.search(rf'pub const {re.escape(symbol)}: &\[&str\] = &\[(.*?)\];', adapter, re.S)
    if not match:
        raise ValueError(f'expected one {symbol} table in {manifest["adapter_registration"]["rust"]}')
    registered = re.findall(r'"([a-z.-]+)"', match.group(1))
    missing = sorted(set(required) - set(registered))
    extra = sorted(set(registered) - set(required))
    if missing or extra:
        raise ValueError('boundary registration mismatch: missing=' +
                         ', '.join(missing) + ' extra=' + ', '.join(extra))
    return registered


def main():
    manifest = json.loads((ROOT / 'spec/CRASH-BOUNDARIES.json').read_text())
    if manifest['adapter_registration'].get('status') == 'absent':
        print('Adapter registered as absent; boundary registration is not checked on this branch.')
        return
    adapter = (ROOT / manifest['adapter_registration']['rust']).read_text()
    registered = verify(manifest, adapter)
    print(f'{len(registered)} exclusion commit boundaries registered and matched.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, json.JSONDecodeError) as error:
        print(f'Crash boundary check: {error}', file=sys.stderr)
        sys.exit(1)
