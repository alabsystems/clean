#!/usr/bin/env python3
"""Candidate source bookkeeping on private, uncompiled Git fixtures.

These controls establish no Rust execution, proof, genesis promotion or Q6
completion. The checker is compiled from its source bytes, never a pyc cache.
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

SCRIPT = Path(__file__).with_name('check_ck0_lineage.py')


def source_subject():
    module = types.ModuleType('ck0_candidate_context_subject')
    module.__file__ = str(SCRIPT)
    exec(compile(SCRIPT.read_bytes(), str(SCRIPT), 'exec', dont_inherit=True), module.__dict__)
    return module


class CandidateContext(unittest.TestCase):
    def setUp(self):
        self.s = source_subject()
        self.temp = tempfile.TemporaryDirectory(prefix='ck0-candidate-context-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        # Fixture setup isolates only Git context. Every native/resource field
        # is preserved; no test fabricates admission or executes a compiler.
        self.env = {key: value for key, value in os.environ.items()
                    if key not in self.s.PRODUCTION_GIT_LOCAL_ENV and
                    not key.startswith(('GIT_CONFIG_KEY_', 'GIT_CONFIG_VALUE_'))}
        self.env.update(GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
        controlled = patch.dict(os.environ, self.env, clear=True)
        controlled.start()
        self.addCleanup(controlled.stop)
        self.files = {name: b'# uncompiled source identity fixture\n' for name in self.s.BASE}
        self.relative = self.s.CRATE + '/src/lib.rs'
        self.files.update({
            self.s.CRATE + '/Cargo.toml': b'[package]\nname="fixture"\nversion="0.0.0"\n',
            self.relative: b'// uncompiled fixture source\n',
        })
        self.assertEqual(set(self.files), {*self.s.BASE,
                         self.s.CRATE + '/Cargo.toml', self.relative}, 'fixture input census')
        self.a, self.b = self.root / 'root A', self.root / 'root B'
        for repo, marker in ((self.a, 'A'), (self.b, 'B')):
            repo.mkdir()
            self.git(repo, 'init', '-q', '-b', 'main')
            for name, data in self.files.items():
                path = repo / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            (repo / 'outside-declared-inputs.txt').write_text(marker)
            self.git(repo, 'add', '-A')
            self.git(repo, '-c', 'user.name=Candidate fixture', '-c',
                     'user.email=candidate@example.invalid', '-c', 'commit.gpgsign=false',
                     '-c', 'core.hooksPath=' + str(repo / '.git/hooks'),
                     'commit', '-qm', 'private uncompiled source fixture')
        self.head_a = self.git(self.a, 'rev-parse', 'HEAD').decode().strip()
        self.head_b = self.git(self.b, 'rev-parse', 'HEAD').decode().strip()
        self.assertNotEqual(self.head_a, self.head_b)
        self.baseline = self.s.source_record(self.a)

    def git(self, repo, *args):
        return subprocess.check_output(['git', '-C', str(repo), *args],
                                       env=self.env, stderr=subprocess.PIPE)

    def put_dirty_replacement(self):
        dirty = self.files[self.relative] + b'// DIRTY uncompiled source control\n'
        (self.a / self.relative).write_bytes(dirty)
        old = self.git(self.a, 'rev-parse', self.head_a + ':' + self.relative).decode().strip()
        new = self.git(self.a, 'hash-object', '-w', self.relative).decode().strip()
        self.git(self.a, 'replace', old, new)
        original = self.git(self.a, '--no-replace-objects', 'show',
                            self.head_a + ':' + self.relative)
        self.assertNotEqual(original, dirty, 'real committed content differs')
        return dirty

    def test_legitimate_named_commits_and_historical_prefixes(self):
        self.assertEqual(self.baseline['revision'], self.head_a)
        self.assertEqual(set(self.baseline['files']), set(self.files))
        self.s.checked_source(self.a, self.baseline)
        other = self.s.source_record(self.b)
        self.assertEqual(other['revision'], self.head_b)
        self.assertEqual(other['files'], self.baseline['files'])
        self.s.checked_source(self.b, other)
        # An older commit remains usable when its declared input prefix is
        # unchanged; the contract does not require record.revision == HEAD.
        (self.a / 'outside-declared-inputs.txt').write_text('another committed outside change')
        self.git(self.a, 'add', 'outside-declared-inputs.txt')
        self.git(self.a, '-c', 'user.name=Candidate fixture', '-c',
                 'user.email=candidate@example.invalid', '-c', 'commit.gpgsign=false',
                 '-c', 'core.hooksPath=' + str(self.a / '.git/hooks'),
                 'commit', '-qm', 'outside input prefix')
        self.s.checked_source(self.a, self.baseline)

    def test_transport_helper_is_a_declared_committed_input(self):
        helper = self.s.RESOURCE_HELPER
        self.assertIn(helper, self.baseline['files'])
        self.assertEqual(self.baseline['files'][helper], self.s.digest((self.a / helper).read_bytes()))
        (self.a / helper).write_bytes(b'# changed uncompiled helper input\n')
        with self.assertRaisesRegex(ValueError, 'input differs from committed source'):
            self.s.source_record(self.a)
        with self.assertRaisesRegex(ValueError, 'input digest changed'):
            self.s.checked_source(self.a, self.baseline)

    def test_tree_revision_is_not_a_candidate_commit(self):
        tree = self.git(self.a, 'rev-parse', 'HEAD^{tree}').decode().strip()
        self.assertEqual(self.git(self.a, 'cat-file', '-t', tree), b'tree\n')
        record = copy.deepcopy(self.baseline)
        record['revision'] = tree
        with self.assertRaises((ValueError, subprocess.CalledProcessError)):
            self.s.checked_source(self.a, record)

    def test_named_root_wins_over_foreign_git_dir(self):
        with patch.dict(os.environ, {'GIT_DIR': str(self.b / '.git')}):
            actual = self.s.source_record(self.a)
            self.assertEqual(actual['revision'], self.head_a, 'candidate captured foreign HEAD')
            self.s.checked_source(self.a, actual)

    def test_foreign_revision_absent_from_named_root_is_refused(self):
        foreign = self.s.source_record(self.b)
        with self.assertRaises(subprocess.CalledProcessError):
            self.git(self.a, 'cat-file', '-t', self.head_b)
        with patch.dict(os.environ, {'GIT_DIR': str(self.b / '.git')}):
            with self.assertRaises((ValueError, subprocess.CalledProcessError)):
                self.s.checked_source(self.a, foreign)

    def test_ordinary_dirty_input_refuses(self):
        (self.a / self.relative).write_bytes(self.files[self.relative] + b'// dirty\n')
        with self.assertRaisesRegex(ValueError, 'input differs from committed source'):
            self.s.source_record(self.a)
        with self.assertRaisesRegex(ValueError, 'input digest changed'):
            self.s.checked_source(self.a, self.baseline)

    def test_dirty_blob_replace_cannot_make_capture_committed(self):
        self.put_dirty_replacement()
        with self.assertRaisesRegex(ValueError, 'input differs from committed source'):
            self.s.source_record(self.a)

    def test_dirty_blob_replace_cannot_authenticate_forged_record(self):
        dirty = self.put_dirty_replacement()
        record = copy.deepcopy(self.baseline)
        record['files'][self.relative] = hashlib.sha256(dirty).hexdigest()
        with self.assertRaisesRegex(ValueError, 'source commit mismatch'):
            self.s.checked_source(self.a, record)

    def test_committed_inputs_ignore_replacement_context(self):
        old = self.git(self.a, 'rev-parse', self.head_a + ':' + self.relative).decode().strip()
        replacement = self.a / 'outside-replacement.data'
        replacement.write_bytes(b'// unrelated uncompiled replacement\n')
        new = self.git(self.a, 'hash-object', '-w', replacement.name).decode().strip()
        self.git(self.a, 'replace', old, new)
        with patch.dict(os.environ, {'GIT_NO_REPLACE_OBJECTS': '0'}):
            self.assertEqual(self.s.source_record(self.a), self.baseline)
            self.s.checked_source(self.a, self.baseline)

    def test_foreign_selector_contexts_do_not_change_candidate_identity(self):
        contexts = [
            {'GIT_COMMON_DIR': str(self.b / '.git')},
            {'GIT_OBJECT_DIRECTORY': str(self.b / '.git/objects')},
            {'GIT_DIR': str(self.b / '.git'), 'GIT_WORK_TREE': str(self.b),
             'GIT_INDEX_FILE': str(self.b / '.git/index'), 'GIT_CONFIG_COUNT': '1',
             'GIT_CONFIG_KEY_0': 'core.worktree', 'GIT_CONFIG_VALUE_0': str(self.b)},
        ]
        for context in contexts:
            with self.subTest(context=sorted(context)), patch.dict(os.environ, context):
                actual = self.s.source_record(self.a)
                self.assertEqual(actual, self.baseline)
                self.s.checked_source(self.a, actual)

    def test_linked_worktree_and_outside_prefix_dirtiness_are_supported(self):
        worktree = self.root / 'linked worktree'
        self.git(self.a, 'worktree', 'add', '--detach', str(worktree), self.head_a)
        (worktree / 'outside-declared-inputs.txt').write_text('outside prefix dirty')
        (worktree / 'untracked-outside-prefix.txt').write_text('untracked outside prefix')
        with patch.dict(os.environ, {'GIT_DIR': str(self.b / '.git')}):
            actual = self.s.source_record(worktree)
            self.assertEqual(actual, self.baseline)
            self.s.checked_source(worktree, actual)


if __name__ == '__main__':
    program = unittest.main(exit=False)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
