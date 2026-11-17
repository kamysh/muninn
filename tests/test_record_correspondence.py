"""Negative checks for the mechanical record-correspondence comparison."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_record_correspondence', ROOT / 'scripts/check_record_correspondence.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class CorrespondenceCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest_path = ROOT / 'spec/RECORD-CORRESPONDENCE.json'
        cls.agda = (ROOT / 'spec/Muninn/OwnedState.agda').read_text()
        cls.manifest = json.loads(cls.manifest_path.read_text())

    def test_current_sources(self):
        check.main()

    def test_missing_formal_entry_is_rejected(self):
        changed = self.manifest.copy()
        del changed['formal']['chunk']
        with self.assertRaises(ValueError):
            check.main_with(changed)

    def test_unknown_write_table_is_rejected(self):
        changed = self.manifest.copy()
        del changed['physical']['mcp_usage']
        with self.assertRaises(ValueError):
            check.main_with(changed)

    def test_missing_site_is_rejected(self):
        changed = self.manifest.copy()
        changed['sites'] = [s for s in changed['sites'] if s['file'] != 'crates/core/src/knowledge.rs']
        with self.assertRaises(ValueError):
            check.main_with(changed)

    def test_wrong_site_table_is_rejected(self):
        changed = self.manifest.copy()
        for site in changed['sites']:
            if site['file'] == 'crates/mcp/src/main.rs':
                site['table'] = 'repos'
        with self.assertRaises(ValueError):
            check.main_with(changed)

    def test_statuses_are_valid(self):
        for name, entry in self.manifest['formal'].items():
            self.assertIn(entry['status'], check.STATUSES, name)


def main_with(manifest):
    constructors = check.formal_constructors(
        (ROOT / 'spec/Muninn/OwnedState.agda').read_text())
    check._verify(constructors, manifest, check.rust_sites())


check.main_with = main_with

if __name__ == '__main__':
    unittest.main()
