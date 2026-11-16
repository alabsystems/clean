#!/usr/bin/env python3
"""Explicit historical/current candidate scopes on private uncompiled Git data.

No compiler, proof checker, admission service or recorded image is executed.
Both validators are compiled from their actual source bytes, never pyc caches.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
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


    def test_cli_source_duplicate_is_refused_before_semantics(self):
        path = self.repo / 'candidate.json'
        data = self.lineage.encoded(self.current)
        needle = b'"schema": "clean.ck0-candidate-source/v2"'
        self.assertEqual(data.count(needle), 1)
        path.write_bytes(data.replace(needle, b'"schema": "wrong", ' + needle))
        with patch.object(sys, 'argv', ['lineage', '--source', str(path)]):
            with self.assertRaisesRegex(self.lineage.EvidenceJSONError, 'duplicate JSON key'):
                self.lineage.main()

    def test_cli_production_duplicate_is_refused_before_semantics(self):
        source = self.repo / 'candidate.json'
        source.write_bytes(self.lineage.encoded(self.current))
        data = (ROOT / 'reports/self-proof-q6-2026-11-13/production.json').read_bytes()
        self.lineage.checked_production(self.lineage.decode_evidence(data))
        needle = b'"proof_claim": false'
        self.assertEqual(data.count(needle), 1)
        path = self.repo / 'production.json'
        path.write_bytes(data.replace(needle, b'"proof_claim": true, ' + needle))
        with patch.object(sys, 'argv', ['lineage', '--source', str(source), '--production', str(path)]):
            with self.assertRaisesRegex(self.lineage.EvidenceJSONError, 'duplicate JSON key'):
                self.lineage.main()


class EvidenceJSON(unittest.TestCase):
    """Actual nonlocal consumers over private inert bytes; no native execution."""
    def setUp(self):
        self.s = source_module('ck0_json_lineage', ROOT / 'scripts/check_ck0_lineage.py')
        self.temp = tempfile.TemporaryDirectory(prefix='ck0-json-evidence-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = {'files': {'uncompiled-fixture': '0' * 64}}
        self.records = {}
        self.data = {}
        for lane in ('stock', 'trust'):
            base = self.root / lane
            base.mkdir()
            (base / 'producer.py').write_bytes((ROOT / 'scripts/check_ck0_lineage.py').read_bytes())
            tools = {}
            for name in ('compiler', 'driver', 'ck0-replay', 'dependency.rlib'):
                p = self.root / name
                p.write_bytes(b'inert fixture; never executed\n')
                tools[name] = self.s.identity(p)
            artifact_paths = {tools[n]['path']: tools[n] for n in ('ck0-replay', 'dependency.rlib')}
            record = dict(schema=self.s.SCHEMA, kind='rustc-family-qualification', label=lane,
                ck0_package_id='fixture-ck0', source_sha256=self.s.digest(self.s.encoded(self.source)),
                compiler=tools['compiler'], driver=tools['driver'], family='rustc',
                independent_implementation=False, ddc=False, proof_claim=False,
                producer_sha256=self.s.digest((base / 'producer.py').read_bytes()),
                sysroot_files={'lib/stdlib': '0' * 64},
                dependency_sources={'dependency': dict(manifest_path=str(self.root / 'Cargo.toml'),
                    source=None, files={'Cargo.toml': '0' * 64})}, steps=[])
            for name in ('default', 'export', 'binary'):
                event = dict(reason='compiler-artifact', package_id='fixture-ck0',
                    profile={'test': name != 'binary'}, target={'name': 'fixture', 'kind': ['lib']},
                    filenames=[tools['ck0-replay']['path']])
                dependency = {**event, 'package_id': 'dependency', 'profile': {'test': False},
                              'filenames': [tools['dependency.rlib']['path']]}
                data = (json.dumps(event)+'\n'+json.dumps(dependency)+
                        '\ntest one ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored;\n').encode()
                (base / (name + '.log')).write_bytes(data)
                step = dict(name=name, argv=self.s.run_argv(tools['driver']['path'], lane, name),
                    exit_code=0, log=name+'.log', log_sha256=self.s.digest(data),
                    artifacts=artifact_paths, packages=['dependency', 'fixture-ck0'])
                if name != 'binary':
                    step.update(tests={'passed': 1, 'ignored': 0, 'targets': 1}, test_names=[['one', 'ok']],
                                test_targets=[{'name': 'fixture', 'kind': ['lib']}])
                record['steps'].append(step)
            self.records[lane] = record
            self.data[lane] = self.s.encoded(record)
            (base / 'run.json').write_bytes(self.data[lane])
        (self.root / 'production.json').write_bytes(b'private inert receipt payload\n')

    def check_run(self, subject=None):
        return (subject or self.s).checked_run(self.root / 'stock/run.json', self.source)

    def mutant(self, old, new):
        path = ROOT / 'scripts/check_ck0_lineage.py'
        data = path.read_text()
        self.assertEqual(data.count(old), 2 if old == 'except json.JSONDecodeError:' else 1)
        # Only the receiver's (last) mixed-log handler is omitted. The producer
        # handler is deliberately unchanged by that control.
        changed = new.join(data.rsplit(old, 1))
        module = types.ModuleType('omitted_json_control')
        module.__file__ = str(path)
        exec(compile(changed, str(path), 'exec', dont_inherit=True), module.__dict__)
        return module

    def duplicate_run(self, escaped=False, nested=False):
        data = self.data['stock']
        old = b'"exit_code": 0' if nested else b'"proof_claim": false'
        new = b'"exit_code": 1, ' + old if nested else b'"proof_claim": true, ' + old
        if escaped:
            new = b'"\\u0070roof_claim": true, ' + old
        self.assertEqual(data.count(old), 3 if nested else 1)
        (self.root / 'stock/run.json').write_bytes(data.replace(old, new, 1))

    def append_log(self, event):
        record = copy.deepcopy(self.records['stock'])
        path = self.root / 'stock/default.log'
        data = path.read_bytes() + event + b'\n'
        path.write_bytes(data)
        record['steps'][0]['log_sha256'] = self.s.digest(data)
        (self.root / 'stock/run.json').write_bytes(self.s.encoded(record))

    def receipt(self):
        names = {'production.json'} | {lane+'/'+name for lane in ('stock', 'trust')
                 for name in ('run.json', 'producer.py', 'default.log', 'export.log', 'binary.log')}
        value = dict(schema='clean.ck0-evidence/v1', proof_claim=False, q6_complete=False,
                     genesis_promoted=False, source_sha256=self.s.digest(self.s.encoded(self.source)),
                     files={p: self.s.digest((self.root / p).read_bytes()) for p in names})
        return self.s.encoded(value)

    def test_valid_run_receipt_and_mixed_log_text(self):
        self.check_run()
        self.append_log(b'ordinary libtest text\n{"reason":"build-finished","extra":1.25}')
        self.check_run()
        (self.root / 'EVIDENCE.json').write_bytes(self.receipt())
        self.s.checked_receipt(self.root, self.source)

    def test_duplicate_run_claim_refuses(self):
        self.duplicate_run()
        with self.assertRaisesRegex(self.s.EvidenceJSONError, 'duplicate JSON key'):
            self.check_run()

    def test_nested_duplicate_step_refuses(self):
        self.duplicate_run(nested=True)
        with self.assertRaisesRegex(self.s.EvidenceJSONError, 'duplicate JSON key'):
            self.check_run()

    def test_escaped_equivalent_key_refuses(self):
        self.duplicate_run(escaped=True)
        with self.assertRaisesRegex(self.s.EvidenceJSONError, 'duplicate JSON key'):
            self.check_run()

    def test_receipt_duplicate_inventory_refuses(self):
        data = self.receipt()
        old = b'"files": {'
        self.assertEqual(data.count(old), 1)
        (self.root / 'EVIDENCE.json').write_bytes(data.replace(old, b'"files": {}, ' + old))
        with self.assertRaisesRegex(self.s.EvidenceJSONError, 'duplicate JSON key'):
            self.s.checked_receipt(self.root, self.source)

    def test_duplicate_ignored_event_refuses(self):
        self.append_log(b'{"reason":"compiler-artifact","reason":"build-finished"}')
        with self.assertRaisesRegex(self.s.EvidenceJSONError, 'duplicate JSON key'):
            self.check_run()

    def test_nonfinite_ignored_event_refuses(self):
        path = self.root / 'stock/default.log'
        original = path.read_bytes()
        for number in (b'NaN', b'Infinity', b'-Infinity', b'1e999', b'-1e999'):
            with self.subTest(number=number):
                path.write_bytes(original)
                self.append_log(b'{"reason":"build-finished","noise":'+number+b'}')
                with self.assertRaisesRegex(self.s.EvidenceJSONError, 'non-finite JSON number'):
                    self.check_run()

    def test_non_json_semantic_prefix_text_remains_ignorable(self):
        path = self.root / 'stock/default.log'
        original = path.read_bytes()
        lines = (b'NaN is expected here', b'Infinity is a prose sentinel',
                 b'-Infinity is a prose sentinel', b'1e999 is the test input',
                 b'-1e999 is the test input', b'{"key":1,"key":2} is prose')
        for line in lines:
            with self.subTest(line=line):
                path.write_bytes(original)
                self.append_log(line)
                self.check_run()

    def test_omitted_duplicate_hook_accepts_actual_ambiguous_run(self):
        self.duplicate_run()
        mutant = self.mutant('object_pairs_hook=unique_object,', '')
        self.assertEqual(self.check_run(mutant), self.records['stock'])

    def test_omitted_constant_hook_accepts_actual_nan_log(self):
        self.append_log(b'{"reason":"build-finished","noise":NaN}')
        self.check_run(self.mutant('parse_constant=nonfinite,', ''))

    def test_omitted_float_hook_accepts_actual_overflow_log(self):
        self.append_log(b'{"reason":"build-finished","noise":1e999}')
        self.check_run(self.mutant('parse_float=finite_float', 'parse_float=float'))

    def test_swallowed_semantic_refusal_accepts_actual_ambiguous_log(self):
        self.append_log(b'{"reason":"compiler-artifact","reason":"build-finished"}')
        self.check_run(self.mutant('except json.JSONDecodeError:', 'except ValueError:'))


if __name__ == '__main__':
    program = unittest.main(exit=False, verbosity=2)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
