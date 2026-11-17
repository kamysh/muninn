"""Focused negative checks for daemon job and source inventory."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('daemon_check', ROOT / 'scripts/check_daemon_catalog.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class DaemonCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((ROOT / 'spec/DAEMON-COVERAGE.json').read_text(), object_pairs_hook=check.cli.unique_pairs)
        cls.inputs = (ROOT / 'spec/Muninn/CatalogInputs.agda').read_text()
        cls.inventory = (ROOT / 'spec/Muninn/CatalogSources.agda').read_text()
        cls.sources = {filename: (ROOT / filename).read_text() for filename in check.FILES.values()}
        sites = check.formal_sites(cls.inventory)
        cls.definitions = {site['path']: (ROOT / site['path']).read_text()
                           for site in sites.values() if site['status'] == 'sourceRecorded'}

    def validate(self, manifest=None, sources=None, inputs=None, inventory=None, definitions=None):
        return check.validate(manifest if manifest is not None else self.manifest,
                              sources if sources is not None else self.sources,
                              inputs if inputs is not None else self.inputs,
                              inventory if inventory is not None else self.inventory,
                              definitions if definitions is not None else self.definitions)

    def test_current_inventory(self):
        jobs, calls = self.validate()
        self.assertGreater(jobs, 0)
        self.assertGreater(calls, 0)

    def test_missing_or_extra_job_is_rejected(self):
        for action in ('missing', 'extra'):
            manifest = copy.deepcopy(self.manifest)
            if action == 'missing':
                del manifest['jobs']['fleetScan']
            else:
                manifest['jobs']['imaginary'] = copy.deepcopy(manifest['jobs']['fleetScan'])
            with self.subTest(action=action), self.assertRaises(ValueError):
                self.validate(manifest=manifest)

    def test_unregistered_daemon_call_is_rejected(self):
        sources = dict(self.sources)
        name = check.FILES['main']
        marker = '    let repos = match store::list_repos(client).await {'
        changed = sources[name].replace(marker, '    store::unregistered_change();\n' + marker, 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_new_local_daemon_helper_call_is_rejected(self):
        sources = dict(self.sources)
        name = check.FILES['main']
        marker = '    let repos = match store::list_repos(client).await {'
        changed = sources[name].replace(marker, '    unregistered_maintenance();\n' + marker, 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed + '\nfn unregistered_maintenance() {}\n'
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_missing_formal_job_or_target_is_rejected(self):
        changed = self.inputs.replace('preparePublic prepareFamily prepareGraph fleetScan',
                                      'preparePublic prepareFamily prepareGraph', 1)
        self.assertNotEqual(changed, self.inputs)
        with self.assertRaises(ValueError):
            self.validate(inputs=changed)
        manifest = copy.deepcopy(self.manifest)
        manifest['calls']['main:main']['scan_and_dispatch']['targets'] = ['job:imaginary']
        with self.assertRaises(ValueError):
            self.validate(manifest=manifest)

    def test_missing_recorded_definition_is_rejected(self):
        definitions = dict(self.definitions)
        name = 'crates/core/src/repo_resolver.rs'
        changed = definitions[name].replace('fn list_git_worktrees(', 'fn renamed_worktrees(', 1)
        self.assertNotEqual(changed, definitions[name])
        definitions[name] = changed
        with self.assertRaises(ValueError):
            self.validate(definitions=definitions)

    def test_missing_listener_or_changed_fallback_is_rejected(self):
        name = check.FILES['main']
        for before, after in [('LISTEN muninn_repos_changed', 'LISTEN other_channel'),
                              ('std::time::Duration::from_secs(60)', 'std::time::Duration::from_secs(61)')]:
            sources = dict(self.sources)
            changed = sources[name].replace(before, after, 1)
            self.assertNotEqual(changed, sources[name])
            sources[name] = changed
            with self.subTest(before=before), self.assertRaises(ValueError):
                self.validate(sources=sources)

    def test_missing_closed_listener_handling_is_rejected(self):
        sources = dict(self.sources)
        name = check.FILES['main']
        changed = sources[name].replace('*notifications_open = false', '*notifications_open = true', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_closed_receiver_guard_cannot_be_removed(self):
        sources = dict(self.sources)
        name = check.FILES['main']
        changed = sources[name].replace('rx.recv(), if *notifications_open', 'rx.recv()', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_nested_comment_is_not_treated_as_source(self):
        with self.assertRaises(ValueError):
            check.definition_tokens('/* outer /* hidden */ remainder */')

    def test_fake_definition_in_raw_string_is_not_a_function(self):
        tokens = check.definition_tokens('const VALUE: &str = r#"fn not_a_function() {}"#;')
        self.assertFalse(check.cli.contains(tokens, ['fn', 'not_a_function']))


if __name__ == '__main__':
    unittest.main()
