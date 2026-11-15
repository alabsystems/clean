# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Inventory must not silently omit scope or carry success across source changes."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    'inventory', Path(__file__).resolve().parents[1] / 'scripts/replacement_release_inventory.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


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


if __name__ == '__main__':
    unittest.main()
