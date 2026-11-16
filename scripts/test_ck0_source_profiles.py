#!/usr/bin/env python3
"""Explicit historical/current candidate scopes on private uncompiled Git data.

No compiler, proof checker, admission service or recorded image is executed.
Both validators are compiled from their actual source bytes, never pyc caches.
"""
import copy
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
LEGACY_INPUTS = ('Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', '.cargo/config.toml',
                 'reports/self-proof-q2-2026-11-12/seed.ndjson',
                 'crates/clean-kernel/src/level/fixtures/lean_kernel_verdicts_v4.30.0-rc2.tsv')
HELPER = 'scripts/resource_transport.py'


def source_module(name, path):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module


class SourceProfiles(unittest.TestCase):
    def setUp(self):
        self.lineage = source_module('ck0_profile_lineage', ROOT / 'scripts/check_ck0_lineage.py')
        self.assertEqual(self.lineage.LEGACY_BASE, LEGACY_INPUTS)
        self.assertEqual(self.lineage.BASE, (*LEGACY_INPUTS, HELPER))
        # Cache the real source lexer before changing only this isolated module's
        # ROOT to the private repository used for actual committed-object reads.
        self.lineage._rust_modules()
        self.temporary = tempfile.TemporaryDirectory(prefix='ck0-source-profiles-')
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name) / 'private repo'
        self.repo.mkdir()
        # Strip only Git repository selectors. Preserve every inherited native
        # resource field; these fixtures never request or assert admission.
        self.env = {name: value for name, value in os.environ.items()
                    if name not in self.lineage.PRODUCTION_GIT_LOCAL_ENV and
                    not name.startswith(('GIT_CONFIG_KEY_', 'GIT_CONFIG_VALUE_'))}
        self.env.update(GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
        self.enterContext(patch.dict(os.environ, self.env, clear=True))
        self.git('init', '-q', '-b', 'main')
        files = {name: b'# uncompiled profile fixture\n' for name in (*LEGACY_INPUTS, HELPER)}
        files.update({self.lineage.CRATE + '/Cargo.toml': b'# uncompiled fixture manifest\n',
                      self.lineage.CRATE + '/src/lib.rs': b'// uncompiled fixture source\n'})
        for name, data in files.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.git('add', '-A')
        self.git('-c', 'user.name=Source profile fixture', '-c',
                 'user.email=profiles@example.invalid', '-c', 'commit.gpgsign=false',
                 '-c', 'core.hooksPath=' + str(self.repo / '.git/hooks'),
                 'commit', '-qm', 'private uncompiled profile fixture')
        self.current = self.lineage.source_record(self.repo)
        self.assertEqual(self.current['schema'], 'clean.ck0-candidate-source/v2')
        self.assertEqual(self.current['files'],
                         {name: hashlib.sha256(data).hexdigest() for name, data in files.items()})
        self.legacy = copy.deepcopy(self.current)
        self.legacy['schema'] = 'clean.ck0-lineage/v1'
        self.legacy['files'].pop(HELPER)
        self.assertEqual(len(self.legacy['files']), 8)
        self.assertEqual(len(self.current['files']), 9)
        self.custody = source_module('ck0_profile_custody', ROOT / 'scripts/check_ck0_replay_custody.py')
        # Use the independently source-loaded real lineage over this private
        # committed repository; the public loader has separate actual CLI tests.
        self.custody.lineage = self.lineage
        self.enterContext(patch.object(self.custody.lineage, 'ROOT', self.repo))

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args],
                                       env=self.env, stderr=subprocess.PIPE)

    def test_real_legacy_six_base_record_authenticates(self):
        self.custody.committed_source(self.legacy)

    def test_helper_added_to_legacy_scope_refuses(self):
        record = copy.deepcopy(self.legacy)
        record['files'][HELPER] = self.current['files'][HELPER]
        with self.assertRaisesRegex(ValueError, 'input inventory changed'):
            self.custody.committed_source(record)

    def test_current_seven_base_record_authenticates(self):
        self.lineage.checked_source(self.repo, self.current)
        self.custody.committed_source(self.current)

    def test_current_scope_without_helper_refuses(self):
        record = copy.deepcopy(self.current)
        record['files'].pop(HELPER)
        with self.assertRaisesRegex(ValueError, 'input inventory changed'):
            self.custody.committed_source(record)
        with self.assertRaisesRegex(ValueError, 'input inventory changed'):
            self.lineage.checked_source(self.repo, record)

    def test_schema_downgrade_cannot_authenticate_new_roster(self):
        record = copy.deepcopy(self.current)
        record['schema'] = self.legacy['schema']
        with self.assertRaisesRegex(ValueError, 'input inventory changed'):
            self.custody.committed_source(record)

    def test_local_current_capture_rejects_legacy_schema(self):
        with self.assertRaisesRegex(ValueError, 'source schema'):
            self.lineage.checked_source(self.repo, self.legacy)

    def test_unknown_schema_refuses_both_validators(self):
        record = copy.deepcopy(self.current)
        record['schema'] = 'clean.ck0-candidate-source/unknown'
        with self.assertRaisesRegex(ValueError, 'archived source record shape/claim'):
            self.custody.committed_source(record)
        with self.assertRaisesRegex(ValueError, 'source schema'):
            self.lineage.checked_source(self.repo, record)


if __name__ == '__main__':
    program = unittest.main(exit=False, verbosity=2)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
