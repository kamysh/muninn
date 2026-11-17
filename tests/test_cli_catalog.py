"""Focused negative checks for the CLI/TUI declaration inventory."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('check_cli_catalog', ROOT / 'scripts/check_cli_catalog.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class CatalogCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((ROOT / 'spec/CLI-TUI-COVERAGE.json').read_text(), object_pairs_hook=check.unique_pairs)
        cls.sources = {name: (ROOT / name).read_text() for name in (
            'crates/cli/src/main.rs', 'crates/cli/src/tui/mod.rs',
            'crates/cli/src/tui/global.rs', 'crates/cli/src/tui/model.rs', 'crates/cli/src/tui/backend.rs')}
        cls.catalog = (ROOT / 'spec/Muninn/Catalog.agda').read_text()
        cls.inputs = (ROOT / 'spec/Muninn/CatalogInputs.agda').read_text()
        cls.inventory = (ROOT / 'spec/Muninn/CatalogSources.agda').read_text()

    def validate(self, manifest=None, sources=None):
        return check.validate(manifest if manifest is not None else self.manifest,
                              sources if sources is not None else self.sources, self.catalog, self.inputs, self.inventory)

    def test_current_declarations(self):
        self.assertGreater(self.validate(), 0)

    def test_missing_or_extra_variant_mapping(self):
        for change in ('remove', 'extra'):
            manifest = copy.deepcopy(self.manifest)
            if change == 'remove':
                del manifest['commands']['Usage']
            else:
                manifest['commands']['Imaginary'] = ['cli:usageDays']
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.validate(manifest)

    def test_new_editor_action_requires_mapping(self):
        sources = dict(self.sources)
        name = 'crates/cli/src/tui/global.rs'
        changed = sources[name].replace('enum Action {', 'enum Action {\n    NewAction,', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_missing_or_unknown_formal_target(self):
        for targets in ([], ['cli:imaginary']):
            manifest = copy.deepcopy(self.manifest)
            manifest['commands']['Usage'] = targets
            with self.subTest(targets=targets), self.assertRaises(ValueError):
                self.validate(manifest)

    def test_added_argument_requires_inventory(self):
        sources = dict(self.sources)
        name = 'crates/cli/src/main.rs'
        changed = sources[name].replace('    Usage {\n', '    Usage {\n        new_option: bool,\n', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_changed_argument_flag_is_rejected(self):
        sources = dict(self.sources)
        name = 'crates/cli/src/main.rs'
        changed = sources[name].replace('#[arg(long, requires = "path")]', '#[arg(short, requires = "path")]', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_changed_global_scope_flag_is_rejected(self):
        sources = dict(self.sources)
        name = 'crates/cli/src/main.rs'
        changed = sources[name].replace('#[arg(long, global = true)]', '#[arg(long, global = false)]', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_missing_command_dispatch_is_rejected(self):
        sources = dict(self.sources)
        name = 'crates/cli/src/main.rs'
        changed = sources[name].replace('Commands::Usage { days }', 'Commands::Other { days }', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_missing_interrupt_or_version_route_is_rejected(self):
        name = 'crates/cli/src/main.rs'
        cases = [('tokio::signal::ctrl_c()', 'tokio::signal::other_signal()'),
                 ('about = "muninn repository index manager", version',
                  'about = "muninn repository index manager"')]
        for before, after in cases:
            sources = dict(self.sources)
            changed = sources[name].replace(before, after, 1)
            self.assertNotEqual(changed, sources[name])
            sources[name] = changed
            with self.subTest(before=before), self.assertRaises(ValueError):
                self.validate(sources=sources)

    def test_missing_editor_backend_call_is_rejected(self):
        sources = dict(self.sources)
        name = 'crates/cli/src/tui/mod.rs'
        changed = sources[name].replace('backend.save(&draft)', 'backend.other(&draft)')
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_missing_global_editor_persistence_is_rejected(self):
        sources = dict(self.sources)
        name = 'crates/cli/src/main.rs'
        changed = sources[name].replace('persist_global(&path, existed, &base, &new)', 'other_persist(&path, existed, &base, &new)', 1)
        self.assertNotEqual(changed, sources[name])
        sources[name] = changed
        with self.assertRaises(ValueError):
            self.validate(sources=sources)

    def test_missing_formal_interrupt_is_rejected(self):
        changed = self.inputs.replace('notification openEditor interrupt : Control', 'notification openEditor : Control', 1)
        self.assertNotEqual(changed, self.inputs)
        with self.assertRaises(ValueError):
            check.validate(self.manifest, self.sources, self.catalog, changed, self.inventory)

    def test_missing_argument_details_are_rejected(self):
        manifest = copy.deepcopy(self.manifest)
        del manifest['argument_details']['commands']
        with self.assertRaises(ValueError):
            self.validate(manifest)

    def test_duplicate_manifest_key_is_rejected(self):
        with self.assertRaises(ValueError):
            json.loads('{"Usage": [], "Usage": []}', object_pairs_hook=check.unique_pairs)


if __name__ == '__main__':
    unittest.main()
