"""Negative checks for the mechanical MCP source catalog comparison."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_mcp_catalog', ROOT / 'scripts/check_mcp_catalog.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class CatalogCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rust = (ROOT / 'crates/mcp/src/main.rs').read_text()
        cls.agda = (ROOT / 'spec/Muninn/Catalog.agda').read_text()
        cls.expected = [name for _, name in check.formal(cls.agda)]
        cls.dispatch = check.dispatched(check.tokens(cls.rust))

    def test_current_sources(self):
        check.main()

    def test_missing_or_duplicate_advertised_tool(self):
        for before, after in [('"name": "search_hybrid"', '"name": "extra_tool"'),
                              ('"name": "search_fulltext"', '"name": "search_hybrid"')]:
            changed = self.rust.replace(before, after, 1)
            self.assertNotEqual(changed, self.rust)
            with self.assertRaises(ValueError):
                check.check('advertised', self.expected, check.advertised(check.tokens(changed)))

    def test_wrong_dispatch_handler(self):
        changed = self.rust.replace('tools::search_hybrid(ctx, params)',
                                    'tools::search_fulltext(ctx, params)', 1)
        self.assertNotEqual(changed, self.rust)
        before = [name + ':' + handler for name, handler in self.dispatch]
        after = [name + ':' + handler for name, handler in check.dispatched(check.tokens(changed))]
        with self.assertRaises(ValueError):
            check.check('dispatch', before, after)

    def test_extra_dispatch_arm_is_rejected(self):
        changed = self.rust.replace('        other => Err(anyhow::anyhow!("unknown tool: {}", other)),',
                                    '        "extra_tool" => tools::search_fulltext(ctx, args),\n'
                                    '        other => Err(anyhow::anyhow!("unknown tool: {}", other)),', 1)
        self.assertNotEqual(changed, self.rust)
        before = [name + ':' + handler for name, handler in self.dispatch]
        with self.assertRaises(ValueError):
            after = [name + ':' + handler for name, handler in check.dispatched(check.tokens(changed))]
            check.check('dispatch', before, after)

    def test_missing_literal_tools_list_is_rejected(self):
        changed = self.rust.replace('"tools/list" => {', '"other/list" => {', 1)
        self.assertNotEqual(changed, self.rust)
        with self.assertRaises(ValueError):
            check.advertised(check.tokens(changed))

    def test_missing_decoder_or_intent(self):
        for clause in ['decodeTool "search_hybrid" = just searchHybrid',
                       'mcpIntent searchHybrid = searchCode hybrid']:
            changed = self.agda.replace(clause, '', 1)
            self.assertNotEqual(changed, self.agda)
            with self.assertRaises(ValueError):
                check.formal(changed)

    def test_permissive_decoder_fallback_is_rejected(self):
        changed = self.agda.replace('decodeTool _ = nothing', 'decodeTool _ = just searchHybrid', 1)
        self.assertNotEqual(changed, self.agda)
        with self.assertRaises(ValueError):
            check.formal(changed)

    def test_decoy_tools_list_outside_handler_is_rejected(self):
        changed = self.rust.replace('"tools/list" => {', '"other/list" => {', 1)
        changed += '\nfn decoy() { match x { "tools/list" => { { "tools": [] } } } }\n'
        with self.assertRaises(ValueError):
            check.advertised(check.tokens(changed))

    def test_missing_handler_definition_is_rejected(self):
        source = (ROOT / 'crates/mcp/src/tools.rs').read_text()
        changed = source.replace('fn search_hybrid(', 'fn renamed_hybrid(', 1)
        self.assertNotEqual(changed, source)
        with self.assertRaises(ValueError):
            check.check_implementations(check.tokens(changed), [('searchHybrid', 'search_hybrid')])

    def test_unsupported_nested_comment(self):
        with self.assertRaises(ValueError):
            check.tokens('/* outer /* nested */ remaining */')

    def test_missing_or_duplicate_admin_name_is_rejected(self):
        cases = [('adminWireName inspect = "inspect_policy"', ''),
                 ('adminWireName check = "check_policy"', 'adminWireName check = "inspect_policy"')]
        for before, after in cases:
            changed = self.agda.replace(before, after, 1)
            self.assertNotEqual(changed, self.agda)
            with self.assertRaises(ValueError):
                check.formal_admin(changed)

    def test_missing_initialize_or_call_dispatch_is_rejected(self):
        cases = [('"initialize" =>', '"other_init" =>'),
                 ('dispatch_tool(ctx, tool_name, args)', 'other_dispatch(ctx, tool_name, args)')]
        for before, after in cases:
            changed = self.rust.replace(before, after, 1)
            self.assertNotEqual(changed, self.rust)
            with self.assertRaises(ValueError):
                check.request_methods(check.tokens(changed))

    def test_unsupported_raw_string(self):
        with self.assertRaises(ValueError):
            check.tokens('let value = r#"opaque"#;')


if __name__ == '__main__':
    unittest.main()
