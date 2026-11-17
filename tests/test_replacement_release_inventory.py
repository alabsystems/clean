# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Inventory must not silently omit scope or carry success across source changes."""
import importlib.util
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    'inventory', Path(__file__).resolve().parents[1] / 'scripts/replacement_release_inventory.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
ROOT = Path(__file__).resolve().parents[1]
HISTORICAL = ROOT / 'reports/replacement-inventory-2026-11-12'
CURRENT = ROOT / 'reports/replacement-inventory-2026-11-16'


class ReleaseInventoryTests(unittest.TestCase):
    def sample(self):
        return {'sha': 'a' * 40, 'truncated': False, 'tree': [
            {'path': p + 'fixture', 'type': 'blob', 'sha': 'b' * 40, 'mode': '100644'}
            for p in ('tests/elab/', 'src/Lean/', 'src/Init/', 'src/lake/', 'src/runtime/')
        ]}

    def load(self, data):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'tree.json'
            path.write_text(json.dumps(data))
            return MODULE.load_tree(path, 'a' * 40)

    def test_incomplete_or_wrong_world_is_refused(self):
        for patch in ({'truncated': True}, {'sha': 'c' * 40}):
            with self.subTest(patch=patch), self.assertRaises(ValueError):
                self.load(dict(self.sample(), **patch))

    def test_missing_surface_and_duplicate_paths_are_refused(self):
        data = self.sample()
        data['tree'].pop()
        with self.assertRaises(ValueError):
            self.load(data)
        data = self.sample()
        data['tree'].append(data['tree'][0])
        with self.assertRaises(ValueError):
            self.load(data)

    def test_delta_never_grants_parity_credit(self):
        old = {'same': {'blob': 'a'}, 'changed': {'blob': 'a'}, 'removed': {'blob': 'a'}}
        new = {'same': {'blob': 'a'}, 'changed': {'blob': 'b'}, 'added': {'blob': 'a'}}
        rows = {row['id']: row for row in MODULE.inventory(old, new)}
        self.assertEqual({k: v['change'] for k, v in rows.items()},
                         {'same': 'unchanged', 'changed': 'changed',
                          'removed': 'removed', 'added': 'added'})
        for name in new:
            self.assertEqual(rows[name]['qualification'], 'not-measured')
        self.assertEqual(rows['removed']['qualification'], 'baseline-only')

    def test_default_cli_preserves_frozen_historical_artifacts_byte_for_byte(self):
        with tempfile.TemporaryDirectory() as directory:
            subprocess.run([
                sys.executable, str(ROOT / 'scripts/replacement_release_inventory.py'),
                '--baseline-tree', str(HISTORICAL / 'v4.30.0-rc2-tree.json.gz'),
                '--target-tree', str(HISTORICAL / 'v4.35.0-tree.json.gz'),
                '--out-dir', directory,
            ], check=True, capture_output=True)
            for name in ('files.json.gz', 'summary.json'):
                self.assertEqual((Path(directory) / name).read_bytes(),
                                 (HISTORICAL / name).read_bytes(), name)

    def test_current_pair_retains_complete_scope_without_qualification(self):
        with tempfile.TemporaryDirectory() as directory:
            summary = MODULE.write_inventory(
                HISTORICAL / 'v4.35.0-tree.json.gz',
                CURRENT / 'v4.36.0-tree.json.gz', directory,
                'v4.35.0..v4.36.0')
            raw = gzip.decompress((Path(directory) / 'files.json.gz').read_bytes())
            manifest = json.loads(raw)
            self.assertEqual(summary['acquired'], '2026-11-16')
            self.assertEqual(summary['semantic_cases_measured'], 0)
            self.assertEqual(list(manifest['worlds']), ['v4.35.0', 'v4.36.0'])
            baseline, _ = MODULE.load_tree(HISTORICAL / 'v4.35.0-tree.json.gz',
                                          MODULE.WORLDS['v4.35.0'])
            target, _ = MODULE.load_tree(CURRENT / 'v4.36.0-tree.json.gz',
                                        '611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9')
            self.assertEqual(summary['baseline_files'], len(baseline))
            self.assertEqual(summary['target_files'], len(target))
            self.assertEqual(summary['manifest_sha256'], hashlib.sha256(raw).hexdigest())
            rows = {row['id']: row for row in manifest['files']}
            self.assertEqual(set(rows), set(baseline) | set(target))
            for path, row in rows.items():
                self.assertEqual(row['baseline'], baseline.get(path), path)
                self.assertEqual(row['target'], target.get(path), path)
                expected = ('added' if path not in baseline else 'removed' if path not in target
                            else 'unchanged' if baseline[path] == target[path] else 'changed')
                self.assertEqual(row['change'], expected, path)
                self.assertEqual(row['qualification'],
                                 'not-measured' if path in target else 'baseline-only', path)
            self.assertEqual(sum(summary['changes'].values()), len(rows))
            for kind, count in summary['changes'].items():
                self.assertEqual(count, sum(row['change'] == kind for row in rows.values()))
            for name in ('files.json.gz', 'summary.json'):
                self.assertEqual((Path(directory) / name).read_bytes(),
                                 (CURRENT / name).read_bytes(), name)

    def test_release_profile_mismatch_refuses_before_writing(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'unwritten'
            pairs = [
                (HISTORICAL / 'v4.30.0-rc2-tree.json.gz', CURRENT / 'v4.36.0-tree.json.gz'),
                (HISTORICAL / 'v4.35.0-tree.json.gz', HISTORICAL / 'v4.35.0-tree.json.gz'),
            ]
            for before, after in pairs:
                with self.subTest(before=before, after=after), self.assertRaises(ValueError):
                    MODULE.write_inventory(before, after, output, 'v4.35.0..v4.36.0')
                self.assertFalse(output.exists())
            with self.assertRaisesRegex(ValueError, 'unreviewed release pair'):
                MODULE.write_inventory('unread', 'unread', output, 'arbitrary..revisions')
            self.assertFalse(output.exists())

    def test_unknown_cli_profile_is_refused_before_read_or_write(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'unwritten'
            result = subprocess.run([
                sys.executable, str(ROOT / 'scripts/replacement_release_inventory.py'),
                '--baseline-tree', 'unread', '--target-tree', 'unread',
                '--release-pair', 'v4.35.0..unreviewed', '--out-dir', str(output),
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn('invalid choice', result.stderr)
            self.assertFalse(output.exists())


if __name__ == '__main__':
    unittest.main()
