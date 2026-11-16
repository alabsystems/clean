# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Accounting controls: an inventory or fast failed import cannot buy parity."""
import copy
import contextlib
import gzip
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    'performance_inventory', Path(__file__).resolve().parents[1]
    / 'scripts/replacement_performance_inventory.py')
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


class PerformanceInventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.objects, cls.provenance = M.load_inputs(M.ROOT)

    def fixture(self):
        original = self.objects['cases']
        chosen = []
        for phase, exit_contract in [('elaborate', '0'), ('elaborate', 'nonzero'), ('driver', None)]:
            case = next(c for c in original['cases'] if any(
                v['phase'] == phase and (exit_contract is None or v['expected_exit'] == exit_contract)
                for v in c['variants']))
            case = copy.deepcopy(case)
            case['variants'] = [next(v for v in case['variants'] if
                v['phase'] == phase and (exit_contract is None or v['expected_exit'] == exit_contract))]
            chosen.append(case)
        cases = dict(original, cases=chosen, summary={'case_roots': 3, 'execution_variants': 3})
        return cases, self.objects['files']

    def manifest(self, cases=None, files=None):
        if cases is None:
            cases, files = self.fixture()
        return M.build_manifest(cases, files, self.provenance)

    def test_full_frozen_cohort_preserves_every_elaborate_id_and_defers_rest(self):
        manifest = self.manifest(self.objects['cases'], self.objects['files'])
        wanted = {v['id'] for c in self.objects['cases']['cases'] for v in c['variants']
                  if v['phase'] == 'elaborate'}
        actual = {row['id'] for row in manifest['p02']}
        deferred = {row['id'] for row in manifest['deferred_b01_variants']}
        self.assertEqual(actual, wanted)
        self.assertEqual(len(actual), 3658)
        self.assertEqual(len(deferred), 871)
        self.assertFalse(actual & deferred)
        self.assertEqual(len(actual | deferred), 4529)
        self.assertEqual(manifest['summary']['p02_seed_roots'], 3595)
        self.assertEqual(manifest['summary']['p02_expected_exit'], {'0': 3344, 'nonzero': 314})

    def test_complete_contracts_remain_identical_not_just_exit_codes(self):
        cases, files = self.fixture()
        case = cases['cases'][0]
        case['hooks'] = [{'path': 'before.sh', 'blob': 'f' * 40}]
        variant = case['variants'][0]
        variant['variable_options'] = {'settings': {'TEST_LEAN_ARGS': ['-Dfoo=true']}, 'setup_state': 'dynamic'}
        variant['output'] = {'mode': 'ignored-by-upstream'}
        result = self.manifest(cases, files)
        row = next(r for r in result['p02'] if r['id'] == variant['id'])
        self.assertEqual(row['contract']['variant'], variant)
        self.assertEqual(row['contract']['case']['hooks'], case['hooks'])
        self.assertIn('separate-correctness-control-required', row['blockers'])
        self.assertEqual(row['state'], 'inventory')

    def test_duplicate_and_misbound_variant_ids_refuse(self):
        for misbound in (False, True):
            cases, files = self.fixture()
            variant = cases['cases'][0]['variants'][0]
            if misbound:
                variant['id'] = 'lean4:other.lean#test:elaborate'
            else:
                cases['cases'][0]['variants'].append(variant)
            with self.subTest(misbound=misbound), self.assertRaisesRegex(ValueError, 'variant ID'):
                self.manifest(cases, files)

    def test_missing_variant_cannot_shrink_denominator_silently(self):
        cases, files = self.fixture()
        cases['cases'][0]['variants'] = []
        with self.assertRaisesRegex(ValueError, 'denominator'):
            self.manifest(cases, files)

    def test_foreign_revision_and_claimed_measurement_refuse(self):
        for key, value in [('upstream_revision', 'wrong'), ('status', 'measured')]:
            cases, files = self.fixture()
            cases[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.manifest(cases, files)

    def test_changed_frozen_input_is_not_absorbed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for _, (path, _) in M.INPUTS.items():
                dst = root / path
                dst.parent.mkdir(parents=True, exist_ok=True)
                obj = json.loads(gzip.decompress((M.ROOT / path).read_bytes()))
                if 'cases' in obj:
                    obj['cases'].pop()
                dst.write_bytes(gzip.compress(M.encoded(obj), mtime=0))
            with self.assertRaisesRegex(ValueError, 'unreviewed inventory'):
                M.load_inputs(root)

    def test_import_source_hashes_and_missing_mathlib_are_explicit(self):
        result = self.manifest()
        for row in result['p01']:
            self.assertEqual(M.sha256(row['fixture']['utf8'].encode()), row['fixture']['sha256'])
            self.assertTrue(row['fixture']['utf8'].startswith('prelude\n'))
            self.assertIn('dependency-closed-replay', row['operations'])
            self.assertIn('v4.35.0-replay-world-selection-not-qualified', row['blockers'])
            if row['module'].startswith('Mathlib'):
                self.assertIsNone(row['root_source'])
                self.assertIn('compatible-mathlib-revision-and-root-source-not-bound', row['blockers'])
            else:
                self.assertEqual(len(row['root_source']['blob']), 40)
        for key in ('ready', 'measured', 'qualified', 'full_workload_manifests_closed'):
            self.assertEqual(result['summary'][key], 0)

    def test_shuffled_case_order_regenerates_identical_bytes(self):
        cases, files = self.fixture()
        before = M.artifacts(self.manifest(cases, files))
        cases['cases'].reverse()
        self.assertEqual(M.artifacts(self.manifest(cases, files)), before)

    def test_changed_expected_exit_contract_is_not_guessed(self):
        cases, files = self.fixture()
        cases['cases'][0]['variants'][0]['expected_exit'] = 'unknown'
        with self.assertRaisesRegex(ValueError, 'exit contract'):
            self.manifest(cases, files)

    def test_check_refuses_tampered_summary_without_rewriting(self):
        with tempfile.TemporaryDirectory() as tmp:
            args = ['--out-dir', tmp]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(M.main(args), 0)
            path = Path(tmp) / 'summary.json'
            data = json.loads(path.read_bytes())
            data['summary']['qualified'] = 1
            path.write_bytes(M.encoded(data))
            forged = path.read_bytes()
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(M.main(args + ['--check']), 1)
            self.assertEqual(path.read_bytes(), forged)


if __name__ == '__main__':
    unittest.main()
