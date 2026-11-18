"""Negative checks for the mechanical crash-boundary comparison."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_crash_boundaries', ROOT / 'scripts/check_crash_boundaries.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class CrashBoundaryCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest_path = ROOT / 'spec/CRASH-BOUNDARIES.json'
        cls.manifest = json.loads(cls.manifest_path.read_text())
        cls.adapter_path = ROOT / cls.manifest['adapter_registration']['rust']
        cls.adapter = cls.adapter_path.read_text()

    def test_current_sources(self):
        check.main()

    def test_unregistered_boundary_is_rejected(self):
        changed = json.loads(json.dumps(self.manifest))
        changed['boundaries'].append({'name': 'exclusion.never-registered',
                                      'spec': 'CleanupFinalization',
                                      'description': 'planted'})
        with self.assertRaises(ValueError):
            check.verify(changed, self.adapter)

    def test_extra_registration_is_rejected(self):
        tampered = self.adapter.replace('"exclusion.finalization",',
                                        '"exclusion.finalization",\n    "exclusion.planted",')
        with self.assertRaises(ValueError):
            check.verify(self.manifest, tampered)

    def test_missing_registration_table_is_rejected(self):
        tampered = self.adapter.replace('pub const CRASH_BOUNDARIES',
                                        'pub const RETIRED_BOUNDARIES')
        with self.assertRaises(ValueError):
            check.verify(self.manifest, tampered)

    def test_absent_registration_skips_the_comparison(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            manifest = json.loads(json.dumps(self.manifest))
            manifest['adapter_registration'] = {'rust': 'crates/core/src/cleanup.rs',
                                                'symbol': 'CRASH_BOUNDARIES',
                                                'status': 'absent'}
            (Path(tmp) / 'spec').mkdir()
            (Path(tmp) / 'spec/CRASH-BOUNDARIES.json').write_text(json.dumps(manifest))
            old, check.ROOT = check.ROOT, Path(tmp)
            try:
                check.main()  # must not raise
            finally:
                check.ROOT = old


if __name__ == '__main__':
    unittest.main()
