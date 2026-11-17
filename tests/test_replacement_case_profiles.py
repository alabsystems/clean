# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Release separation, complete-source custody and real docparse branch controls."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import replacement_test_cases as M
from replacement_docparse_436 import test_configs, directory_dispatch
from replacement_driver_contracts import driver_contract, DOC

OLD = ROOT / 'reports/replacement-inventory-2026-11-12'
NEW = ROOT / 'reports/replacement-inventory-2026-11-16'


def load(world):
    root = OLD if world == 'v4.35.0' else NEW
    targets, sources = M.load_inputs(root/'files.json.gz', root/'cases/harness-sources.json.gz', world)
    oracle = M.read_json(OLD/'lean-cli.json' if world == 'v4.35.0' else NEW/'cases/oracle.json')
    tool = {k: oracle[k] for k in ('world', 'version', 'githash', 'executable_sha256', 'archive_sha256')}
    return targets, sources, M.build_manifest(targets, sources, tool, world)


class CaseProfileTests(unittest.TestCase):
    def test_historical_default_manifest_bytes_and_original_355_ids_unchanged(self):
        _, _, manifest = load('v4.35.0')
        cohort = M.read_json(OLD/'cases/driver-starting-ids.json')
        M.validate_driver_cohort(manifest, cohort)
        manifest['driver_starting_cohort'] = cohort
        self.assertEqual(gzip.compress(M.encoded(manifest), mtime=0), (OLD/'cases/manifest.json.gz').read_bytes())
        self.assertEqual(len(cohort['variant_ids']), 355)
        self.assertEqual(manifest['summary']['case_roots'], 4243)
        self.assertEqual(manifest['summary']['execution_variants'], 4529)

    def test_latest_complete_catalog_and_new_cohort_are_separate_and_unmeasured(self):
        targets, sources, manifest = load('v4.36.0')
        cohort = M.read_json(NEW/'cases/driver-starting-ids.json')
        M.validate_driver_cohort(manifest, cohort, 'v4.36.0')
        self.assertEqual(hashlib.sha256(M.encoded(manifest)).hexdigest(), cohort['starting_manifest_sha256'])
        self.assertEqual(manifest['summary']['case_roots'], 4592)
        self.assertEqual(manifest['summary']['execution_variants'], 4914)
        self.assertEqual(len(cohort['variant_ids']), 489)
        self.assertEqual(manifest['summary']['qualified_cases'], 0)
        self.assertEqual(manifest['summary']['qualified_variants'], 0)
        self.assertEqual(len({c['id'] for c in manifest['cases']}), 4592)
        for case in manifest['cases']:
            self.assertEqual(case['status'], 'not-measured')
            if case['input']:
                self.assertEqual(case['input']['blob'], targets[case['path']]['blob'])
            for variant in case['variants']:
                self.assertEqual(variant['status'], 'not-measured')
                contract = variant.get('behavioral_contract')
                if contract:
                    self.assertFalse(contract['measured'])
                    self.assertEqual(contract['input']['blob'], M.git_blob(sources[case['path']].encode()))
        manifest['driver_starting_cohort'] = cohort
        self.assertEqual(gzip.compress(M.encoded(manifest), mtime=0), (NEW/'cases/manifest.json.gz').read_bytes())

    def test_latest_docparse_triples_last_entry_and_prefix_collision_are_real(self):
        targets, sources, _ = load('v4.36.0')
        configs = test_configs(sources[DOC])
        self.assertEqual(len(configs), 27)
        self.assertEqual(configs['documentIndented'], {'parser_expression': 'documentFn {baseColumn := 2}', 'validate_source_info': True})
        c = driver_contract('tests/docparse/arg_val_0001.txt', DOC, sources, targets, world='v4.36.0')
        self.assertEqual(c['selector']['key'], 'arg')
        self.assertEqual(c['selector']['parser_expression'], 'argFn')
        self.assertTrue(c['source_info_validation']['enabled'])
        self.assertIn('IO.println', c['output_transport'])
        self.assertEqual(c['expected_driver_exit'], 0)
        c = driver_contract('tests/docparse/inlineTextChar_0001.txt', DOC, sources, targets, world='v4.36.0')
        self.assertFalse(c['source_info_validation']['enabled'])
        c = driver_contract('tests/docparse/lookaheadOrderedListMarker_0001.txt', DOC, sources, targets, world='v4.36.0')
        self.assertIn('fakeAtom', c['selector']['parser_expression'])
        self.assertFalse(c['source_info_validation']['enabled'])

    def test_four_directory_branches_retain_every_input_and_runtime_filter(self):
        targets, sources, manifest = load('v4.36.0')
        expected = sorted(p for p in targets if str(Path(p).parent) == 'tests/docparse' and p.endswith('.txt'))
        self.assertEqual(len(expected), 334)
        aggregate = [c for c in manifest['cases'] if c['input_scope'] == 'driver-dispatch-file-and-directory-inputs']
        self.assertEqual(len(aggregate), 4)
        self.assertEqual({c['variants'][0]['behavioral_contract']['selector']['key'] for c in aggregate}, {'coverage', 'format', 'nodeinfo', 'blankPara'})
        for case in aggregate:
            contract = case['variants'][0]['behavioral_contract']
            self.assertEqual(contract['directory_inputs'], expected)
            self.assertEqual([r['path'] for r in case['supporting_inputs']], expected)
            self.assertTrue(contract['dynamic_expansion_required'])
            self.assertTrue(contract['dynamic_expansion'])
            self.assertEqual(contract['subcases'][0]['candidate_inputs'], expected)
            self.assertIn('runtime', contract['subcases'][0]['selection'])
            self.assertIn('1 if any fail', contract['expected_driver_exit'])
        trimmed = dict(sources)
        del trimmed[expected[0]]
        with self.assertRaisesRegex(ValueError, 'batch inputs'):
            driver_contract('tests/docparse/coverage_0001.txt', DOC, trimmed, targets, world='v4.36.0')

    def test_driver_world_pin_corruption_and_dispatch_change_refuse(self):
        targets, sources, _ = load('v4.36.0')
        path = 'tests/docparse/arg_0001.txt'
        for world in ['v4.35.0', 'v4.37.0']:
            with self.assertRaises(ValueError):
                driver_contract(path, DOC, sources, targets, world=world)
        bad = dict(sources)
        bad[DOC] += '\n-- changed\n'
        with self.assertRaisesRegex(ValueError, 'unreviewed driver grammar'):
            driver_contract(path, DOC, bad, targets, world='v4.36.0')
        with self.assertRaisesRegex(ValueError, 'directory dispatch'):
            directory_dispatch(sources[DOC].replace('kind == "coverage"', 'kind == "fake"'))
        arm = '    if kind == "coverage" then\n      return (← coverage)\n'
        with self.assertRaisesRegex(ValueError, 'directory dispatch'):
            directory_dispatch(sources[DOC].replace(arm, arm + arm))

    def test_array_boundaries_ignore_nested_comments_and_strings(self):
        text = ('def testConfigs : List (String × ParserFn × Bool) := [\n'
                '  ("x", fakeAtom "]" /- ] /- nested ] -/ -/, true),\n]\n'
                'def after := #["not a config"]\n')
        self.assertEqual(test_configs(text)['x']['validate_source_info'], True)
        self.assertNotIn('def after', test_configs(text)['x']['parser_expression'])
        for bad in [text.replace('true),', 'maybe),'), text.replace(']\ndef after', '\ndef after'), text + '\n/- unfinished']:
            with self.assertRaises(ValueError):
                test_configs(bad)

    def test_profile_wrong_world_and_whole_bundle_corruption_refuse(self):
        with self.assertRaisesRegex(ValueError, 'unreviewed test-case world'):
            M.load_inputs(NEW/'files.json.gz', NEW/'cases/harness-sources.json.gz', 'v4.99.0')
        for inventory, bundle, world in [(OLD/'files.json.gz', NEW/'cases/harness-sources.json.gz', 'v4.36.0'),
                (NEW/'files.json.gz', OLD/'cases/harness-sources.json.gz', 'v4.36.0')]:
            with self.assertRaises(ValueError):
                M.load_inputs(inventory, bundle, world)
        bundle = M.read_json(NEW/'cases/harness-sources.json.gz')
        for changed in [dict(bundle, files=bundle['files'][:-1]), dict(bundle, upstream_revision=M.REVISION)]:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)/'bundle.json'
                path.write_bytes(M.encoded(changed))
                with self.assertRaisesRegex(ValueError, 'reviewed complete source bundle'):
                    M.load_inputs(NEW/'files.json.gz', path, 'v4.36.0')

    def test_latest_cohort_cannot_drop_substitute_duplicate_or_borrow_old_ids(self):
        _, _, manifest = load('v4.36.0')
        cohort = M.read_json(NEW/'cases/driver-starting-ids.json')
        M.validate_driver_cohort(manifest, cohort, 'v4.36.0')
        for ids in [cohort['variant_ids'][:-1], cohort['variant_ids']+[cohort['variant_ids'][0]],
                    cohort['variant_ids'][:-1]+['replacement'], M.read_json(OLD/'cases/driver-starting-ids.json')['variant_ids']]:
            with self.assertRaises(ValueError):
                M.validate_driver_cohort(manifest, dict(cohort, variant_ids=ids), 'v4.36.0')
        with self.assertRaises(ValueError):
            M.validate_driver_cohort(manifest, dict(cohort, starting_manifest_sha256='0'*64), 'v4.36.0')

    def test_cli_refuses_wrong_oracle_before_output_even_under_optimization(self):
        oracle = M.read_json(NEW/'cases/oracle.json')
        oracle['githash'] = M.REVISION
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            path = directory/'oracle.json'; path.write_bytes(M.encoded(oracle))
            for optimized in [[], ['-O']]:
                out = directory/('optimized' if optimized else 'normal')
                result = subprocess.run([sys.executable, *optimized, str(ROOT/'scripts/replacement_test_cases.py'),
                    '--world', 'v4.36.0', '--inventory', str(NEW/'files.json.gz'),
                    '--harness-sources', str(NEW/'cases/harness-sources.json.gz'), '--oracle', str(path), '--out-dir', str(out)], capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(b'wrong recorded oracle', result.stderr)
                self.assertFalse(out.exists())


if __name__ == '__main__':
    unittest.main()
