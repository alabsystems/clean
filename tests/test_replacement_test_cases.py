# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Adversarial accounting controls: files are not cases, variants are not passes."""
import base64
import copy
import gzip
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    'cases', Path(__file__).resolve().parents[1] / 'scripts/replacement_test_cases.py')
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)

LAKE_GLOBS = '''
set(LAKE_TEST_GLOBS
  "${LEAN_SOURCE_DIR}/../tests/lake/examples/test.sh"
  "${LEAN_SOURCE_DIR}/../tests/lake/tests/test.sh"
)
'''


class CaseInventoryTests(unittest.TestCase):
    def fixture(self, registrations='add_test_pile(elab *.lean)', files=()):
        sources = {
            'tests/CMakeLists.txt': LAKE_GLOBS + registrations,
            'tests/util.sh': 'check_out_file() { :; }\n',
            'tests/with_env.sh.in': 'source "$1"\n',
            'tests/elab/run_test.sh': 'source_init "$1"\n',
            'tests/compile/run_test.sh': 'source_init "$1"\n',
            'tests/compile/run_bench.sh': '../compile_bench/run_bench.sh',
            'tests/compile_bench/run_bench.sh': 'source_init "$1"\n',
        }
        for path, content in files:
            sources[path] = content
        targets = {p: dict(blob=M.git_blob(v.encode()), mode='100644', type='blob')
                   for p, v in sources.items()}
        targets['tests/compile/run_bench.sh']['mode'] = '120000'
        return targets, sources

    def manifest(self, registrations='add_test_pile(elab *.lean)', files=()):
        targets, sources = self.fixture(registrations, files)
        return M.build_manifest(targets, sources, {'githash': M.REVISION})

    def test_pile_glob_is_not_recursive_and_sidecars_are_not_case_roots(self):
        result = self.manifest(files=[('tests/elab/a.lean', 'def a := 0'),
            ('tests/elab/a.lean.out.expected', 'hello'), ('tests/elab/a.lean.init.sh', '# setup'),
            ('tests/elab/sub/support.lean', 'def support := 0'), ('tests/elab/_tmp_b.lean', ''),
            ('tests/elab/a.txt', 'input')])
        self.assertEqual([x['path'] for x in result['cases']], ['tests/elab/a.lean'])
        roles = {x['path']: x['role'] for x in result['file_roles']}
        self.assertEqual(roles['tests/elab/a.lean.out.expected'], 'expected-output')
        self.assertEqual(roles['tests/elab/sub/support.lean'], 'unregistered-or-input-only-source')
        self.assertEqual(result['summary']['qualified_cases'], 0)
        self.assertTrue(all(v['status'] == M.STATUS for x in result['cases'] for v in x['variants']))

    def test_cmake_exclusions_and_no_test_do_not_remove_benchmark(self):
        result = self.manifest('add_test_pile(compile *.lean BENCH PART2 EXCEPT flaky.lean)', [
            ('tests/compile/a.lean', ''), ('tests/compile/a.lean.no_test', ''),
            ('tests/compile/flaky.lean', '')])
        self.assertEqual(len(result['cases']), 1)
        case = result['cases'][0]
        self.assertEqual(case['profiles'], ['bench'])
        self.assertEqual([x['id'].split('#')[1] for x in case['variants']], ['bench:compile'])
        self.assertEqual(len(result['exclusions']), 2)

    def test_compile_and_interpret_variants_obey_specific_marker_precedence(self):
        result = self.manifest('add_test_pile(compile *.lean BENCH PART2)', [
            ('tests/compile/a.lean', ''), ('tests/compile/a.lean.no_compile_test', ''),
            ('tests/compile/a.lean.do_compile', ''), ('tests/compile/a.lean.no_interpret', ''),
            ('tests/compile/a.lean.do_interpret_test', '')])
        ids = [x['id'].split('#')[1] for x in result['cases'][0]['variants']]
        self.assertEqual(ids, ['test:interpret', 'bench:compile'])

    def test_default_compile_has_two_test_variants_but_one_benchmark_variant(self):
        result = self.manifest('add_test_pile(compile *.lean BENCH PART2)', [('tests/compile/a.lean', '')])
        self.assertEqual(result['summary']['case_roots'], 1)
        self.assertEqual(result['summary']['execution_variants'], 3)
        self.assertEqual(result['summary']['profiles'], {'bench': 1, 'test': 2})

    def test_aggregate_directory_inputs_do_not_become_independent_cases(self):
        result = self.manifest('add_dir_of_test_dirs(pkg EXCEPT excluded)', [
            ('tests/pkg/a/run_test.sh', 'lake build\nlake exe test\n'),
            ('tests/pkg/a/Main.lean', ''), ('tests/pkg/a/Sub/Input.lean', ''),
            ('tests/pkg/excluded/run_test.sh', ''), ('tests/pkg/excluded/X.lean', '')])
        self.assertEqual([x['path'] for x in result['cases']], ['tests/pkg/a'])
        self.assertEqual(result['cases'][0]['input_scope'], 'aggregate-directory')
        self.assertIn('aggregate-script-subcases-not-enumerated', result['cases'][0]['unresolved'])
        self.assertEqual(len(result['cases'][0]['supporting_inputs']), 3)

    def test_lake_selection_keeps_optional_extra_and_records_network_exclusions(self):
        result = self.manifest('add_test_pile(elab *.lean)', [('tests/lake/tests/plain/test.sh', 'lake build'),
            ('tests/lake/tests/online/test.sh', ''), ('tests/lake/examples/bootstrap/test.sh', ''),
            ('tests/lake/extra/trace/test.sh', 'lake build')])
        self.assertEqual(result['summary']['case_selection'], {'LAKE_CI=ON': 1, 'default': 1})
        self.assertEqual(len(result['exclusions']), 2)
        self.assertTrue(all(x['packages'] == ['B13'] for x in result['cases']))

    def test_output_ignore_precedence_and_nonzero_exit_literal(self):
        result = self.manifest('add_test_pile(compile *.lean BENCH PART2)', [
            ('tests/compile/a.lean', ''), ('tests/compile/a.lean.init.sh', 'TEST_EXIT=nonzero\nTEST_ARGS=( a "b c" )\n'),
            ('tests/compile/a.lean.out.expected', 'x'), ('tests/compile/a.lean.out.ignored', '')])
        variant = result['cases'][0]['variants'][0]
        self.assertEqual(variant['expected_exit'], 'nonzero')
        self.assertEqual(variant['variable_options']['settings']['TEST_ARGS'], ['a', 'b c'])
        self.assertEqual(variant['output']['mode'], 'ignored-by-upstream')

    def test_dynamic_setup_never_executes_or_partially_guesses(self):
        with tempfile.TemporaryDirectory() as directory:
            sentinel = Path(directory) / 'must-not-exist'
            settings, state = M.initial_settings('TEST_EXIT=0\nTEST_ARGS=($(touch ' + str(sentinel) + '))\n')
            self.assertEqual(settings, {})
            self.assertEqual(state, 'dynamic-shell')
            self.assertFalse(sentinel.exists())
        self.assertEqual(M.initial_settings('unset LEAN_ABORT_ON_NONLINEAR\n'),
                         ({'LEAN_ABORT_ON_NONLINEAR': None}, 'literal-assignments'))

    def test_symlink_runner_resolves_and_cycle_or_missing_source_refuses(self):
        targets, sources = self.fixture()
        self.assertEqual(M.resolve_runner('tests/compile/run_bench.sh', targets, sources)[0],
                         'tests/compile_bench/run_bench.sh')
        sources['tests/compile/run_bench.sh'] = 'run_bench.sh'
        with self.assertRaises(ValueError):
            M.resolve_runner('tests/compile/run_bench.sh', targets, sources)
        with self.assertRaises(ValueError):
            M.resolve_runner('tests/elab/run_test.sh', targets, {})

    def test_duplicate_registration_refuses_instead_of_inflating_denominator(self):
        with self.assertRaises(ValueError):
            self.manifest('add_test_pile(elab *.lean)\nadd_test_pile(elab *.lean)', [('tests/elab/a.lean', '')])

    def test_spaces_and_fully_disabled_inputs_keep_their_identity(self):
        result = self.manifest('add_dir_of_test_dirs(pkg)', [
            ('tests/pkg/path with spaces/run_test.sh', 'lake build'),
            ('tests/pkg/path with spaces/Main.lean', '')])
        self.assertEqual(result['cases'][0]['id'], 'lean4:tests/pkg/path with spaces')
        result = self.manifest('add_test_pile(compile *.lean BENCH PART2)', [
            ('tests/compile/a.lean', ''), ('tests/compile/a.lean.no_test', ''),
            ('tests/compile/a.lean.no_bench', '')])
        self.assertEqual(result['summary']['case_roots'], 1)
        self.assertEqual(result['summary']['roots_with_execution'], 0)
        self.assertEqual(result['summary']['execution_variants'], 0)
        self.assertEqual(result['cases'][0]['status'], M.STATUS)

    def test_input_pins_refuse_wrong_revision_tampering_and_missing_harness(self):
        targets, sources = self.fixture()
        rows = [dict(id=p, target=t) for p, t in targets.items()]
        bundle = dict(upstream_revision=M.REVISION, files=[dict(path=p, **targets[p],
            sha256=M.hashlib.sha256(v.encode()).hexdigest(), bytes=len(v.encode()),
            content_base64=base64.b64encode(v.encode()).decode()) for p, v in sources.items()])
        inventory = dict(worlds={'v4.35.0': M.REVISION}, files=rows)
        with tempfile.TemporaryDirectory() as directory, patch.object(M, 'CATALOG_BLOB', targets[M.CATALOG]['blob']), patch.object(M, 'INVENTORY_SHA256', M.hashlib.sha256(M.encoded(inventory)).hexdigest()):
            i, b = Path(directory) / 'inventory.json.gz', Path(directory) / 'sources.json.gz'
            def put(a, c):
                i.write_bytes(gzip.compress(M.encoded(a), mtime=0)); b.write_bytes(gzip.compress(M.encoded(c), mtime=0))
            put(inventory, bundle)
            self.assertEqual(M.load_inputs(i, b), (targets, sources))
            wrong = copy.deepcopy(inventory); wrong['worlds']['v4.35.0'] = '0' * 40
            put(wrong, bundle)
            with self.assertRaises(ValueError): M.load_inputs(i, b)
            wrong = copy.deepcopy(bundle); wrong['files'][0]['content_base64'] = base64.b64encode(b'forged').decode()
            put(inventory, wrong)
            with self.assertRaises(ValueError): M.load_inputs(i, b)
            wrong = copy.deepcopy(bundle); wrong['files'] = [x for x in wrong['files'] if x['path'] != 'tests/util.sh']
            put(inventory, wrong)
            with self.assertRaises(ValueError): M.load_inputs(i, b)


class DriverContractTests(unittest.TestCase):
    def test_directive_split_is_exact_and_columns_are_utf8_bytes(self):
        from replacement_driver_contracts import server_directives
        text = 'α\n  --^ goals: withPopups\n--^ ignored -- second marker\n-- ^ ignored\nλ--⬑ hover\n--v sync\nnext'
        steps = server_directives(text, {'goals':'processGoals'})[0]['directives']
        self.assertEqual([x['method'] for x in steps], ['goals','hover','sync'])
        self.assertEqual(steps[0]['position'], {'line':0,'character':4})
        self.assertEqual(steps[1]['position'], {'line':3,'character':2})
        self.assertEqual(steps[2]['position'], {'line':6,'character':2})
        self.assertEqual(steps[1]['params'], '{}')

    def test_reset_literal_splits_even_inside_lean_string_and_preserves_empty_sessions(self):
        from replacement_driver_contracts import server_directives
        sessions = server_directives('"-- RESET"\n--^ insert: "x"\n--^ waitForILeans\n--^ delete: "x"-- RESET', {})
        self.assertEqual(len(sessions), 3)
        steps = sessions[1]['directives']
        self.assertTrue(steps[2]['statically_unsynced_edit'])
        self.assertEqual(steps[2]['version_before'], 3)
        self.assertEqual(sessions[2]['initial_state']['versionNo'], 2)

    def test_direct_imports_mask_nested_comments_strings_and_fake_imports(self):
        from replacement_driver_contracts import import_records
        self.assertEqual([r['declaration'] for r in import_records(
            '/- import Fake\n /- nested -/ -/\npublic import Lean.Real\ndef x := "\nimport Fake2\n"\n-- import Fake3')], ['public import Lean.Real'])

    def pinned(self):
        root = Path(__file__).resolve().parents[1]
        return M.load_inputs(root/'reports/replacement-inventory-2026-11-12/files.json.gz',
                             root/'reports/replacement-inventory-2026-11-12/cases/harness-sources.json.gz')

    def test_genuine_docparse_prefix_collision_and_multiline_parser_expression(self):
        from replacement_driver_contracts import driver_contract, DOC
        targets, sources = self.pinned()
        path = next(p for p in sources if p.startswith('tests/docparse/arg_val_') and p.endswith('.txt'))
        c = driver_contract(path, DOC, sources, targets)
        self.assertEqual(c['selector']['key'], 'arg')
        self.assertEqual(c['selector']['parser_expression'], 'arg')
        path = next(p for p in sources if '/lookaheadOrderedListIndicator_' in p and p.endswith('.txt'))
        c = driver_contract(path, DOC, sources, targets)
        self.assertIn('fun type i =>', c['selector']['parser_expression'])
        self.assertFalse(c['dynamic_expansion_required'])

    def test_genuine_server_dispatch_and_fanout_are_retained(self):
        from replacement_driver_contracts import driver_contract, SERVER
        targets, sources = self.pinned()
        path = 'tests/server_interactive/1659.lean'
        c = driver_contract(path, SERVER, sources, targets)
        steps = [x for session in c['sessions'] for x in session['directives']]
        self.assertEqual(len(steps), 5)
        self.assertEqual(steps[0]['position'], {'line':9, 'character':23})
        self.assertIn('processCompletion', [x['handler'] for x in steps])
        self.assertIn('for i in r.items', c['handler_contracts']['processCompletion']['source'])
        self.assertTrue(c['dynamic_expansion_required'])
        generic = driver_contract('tests/server_interactive/1265.lean', SERVER, sources, targets)
        self.assertFalse(generic['dynamic_expansion_required'])
        self.assertEqual(generic['sessions'][0]['directives'][0]['method'], 'textDocument/completion')
        self.assertEqual(generic['sessions'][0]['directives'][0]['handler'], 'processGenericRequest')
        bad = dict(sources); bad[SERVER] += '\n-- changed'
        with self.assertRaises(ValueError): driver_contract(path, SERVER, bad, targets)
        bad = dict(sources); del bad[path]
        with self.assertRaises(ValueError): driver_contract(path, SERVER, bad, targets)

    def test_cohort_drop_duplicate_and_substitution_refuse(self):
        root = Path(__file__).resolve().parents[1]/'reports/replacement-inventory-2026-11-12/cases'
        frozen = json.loads((root/'driver-starting-ids.json').read_text())
        variants = [dict(id=i, behavioral_contract={}) for i in frozen['variant_ids']]
        manifest = dict(cases=[dict(variants=variants)])
        M.validate_driver_cohort(manifest, frozen)
        for changed in (variants[:-1], variants + variants[:1], variants[:-1] + [dict(id='replacement', behavioral_contract={})]):
            with self.assertRaises(ValueError):
                M.validate_driver_cohort(dict(cases=[dict(variants=changed)]), frozen)

    def test_frozen_accounting_and_every_source_digest(self):
        from replacement_driver_contracts import driver_contract
        targets, sources = self.pinned()
        root = Path(__file__).resolve().parents[1]/'reports/replacement-inventory-2026-11-12/cases'
        frozen = json.loads((root/'driver-starting-ids.json').read_text())['variant_ids']
        self.assertEqual(len(frozen), 355)
        self.assertEqual(len(set(frozen)), 355)
        counts = {}
        for identifier in frozen:
            path = identifier[6:].split('#')[0]
            driver = str(Path(path).parent/'run_test.lean')
            c = driver_contract(path, driver, sources, targets)
            counts[c['kind']] = counts.get(c['kind'], 0) + 1
            self.assertEqual(c['input']['blob'], M.git_blob(sources[path].encode()))
            self.assertEqual(c['input']['sha256'], M.hashlib.sha256(sources[path].encode()).hexdigest())
        self.assertEqual(counts, {'docparse':202, 'interactive-server':153})


if __name__ == '__main__':
    unittest.main()
