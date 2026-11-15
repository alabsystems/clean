# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Crashes/caps must not earn negative-conformance credit."""
import importlib.util
from contextlib import redirect_stderr, redirect_stdout
import hashlib
import gzip
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location(
    'probe', Path(__file__).resolve().parents[1] / 'scripts/replacement_false_accept_probe.py')
PROBE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROBE)


def result(rc, timed_out=False):
    return {'rc': rc, 'timed_out': timed_out}


class FalseAcceptanceClassificationTests(unittest.TestCase):
    def test_launcher_hash_cannot_stand_in_for_native_binary_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'launcher'
            path.write_text('#!/bin/sh\nexec /some/other/program "$@"\n')
            with self.assertRaises(ValueError):
                PROBE.native_path(path)

    def test_semantic_agreement_and_disagreement(self):
        self.assertEqual(PROBE.classify(result(1), result(0)), 'false-accept')
        self.assertEqual(PROBE.classify(result(1), result(1)), 'agree-reject')

    def test_oracle_acceptance_cannot_confirm_historical_rejection(self):
        self.assertEqual(PROBE.classify(result(0), result(1)), 'oracle-contract-changed')

    def test_timeout_cannot_earn_rejection_credit(self):
        self.assertEqual(PROBE.classify(result(1), result(-9, True)), 'unmeasured-timeout')

    def test_signal_and_panic_cannot_earn_rejection_credit(self):
        self.assertEqual(PROBE.classify(result(1), result(-11)), 'unmeasured-signal')
        self.assertEqual(PROBE.classify(result(1), result(101)), 'unmeasured-exit')
        self.assertEqual(PROBE.classify(result(2), result(1)), 'unmeasured-exit')


class ExecutableProvenanceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.lean = self.root / 'sdk' / 'bin' / 'lean'
        self.clean = self.root / 'clean'
        self.lean.parent.mkdir(parents=True)
        self.lean.write_bytes(b'fake lean executable')
        self.clean.write_bytes(b'fake clean executable')
        self.out = self.root / 'report'
        fixture = self.out / 'fixtures' / 'elab_fail' / 'case.lean'
        fixture.parent.mkdir(parents=True)
        data = b'example : False := True.intro\n'
        fixture.write_bytes(data)
        self.acquisition = {'world': 'v4.35.0', 'files': [{
            'path': 'elab_fail/case.lean',
            'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
        }]}
        self.acquisition_raw = json.dumps(self.acquisition).encode()
        (self.out / 'acquisition.json').write_bytes(self.acquisition_raw)
        self.calls = []

    def fake_execute(self, command, cwd, timeout):
        self.calls.append((command, cwd, timeout))
        stdout = ''
        if command[1:] == ['--version']:
            stdout = 'Lean (version 4.35.0, test)\n' if command[0] == str(self.lean) else 'clean test\n'
        return {'rc': 0 if stdout else 1, 'timed_out': False,
                'stdout': stdout, 'stderr': ''}

    def run_probe(self, execute, timeout='2', output_name=None):
        argv = ['probe', '--lean-bin', str(self.lean), '--clean-bin', str(self.clean),
                '--report-dir', str(self.out), '--timeout', str(timeout)]
        if output_name is not None:
            argv.extend(['--output-name', output_name])
        with mock.patch('sys.argv', argv), mock.patch.object(PROBE, 'execute', side_effect=execute), redirect_stdout(io.StringIO()):
            PROBE.main()

    def test_launcher_is_refused_before_any_invocation(self):
        for path in [self.lean, self.clean]:
            with self.subTest(executable=path):
                previous = path.read_bytes()
                path.write_bytes(b'#!/bin/sh\nexec /different/executable "$@"\n')
                execute = mock.Mock(side_effect=self.fake_execute)
                with self.assertRaisesRegex(ValueError, 'native executable'):
                    self.run_probe(execute)
                execute.assert_not_called()
                self.assertFalse((self.out / 'measurement.json').exists())
                path.write_bytes(previous)

    def assert_producer_change_refused(self, mutation_point):
        producer = self.root / 'producer-copy.py'
        producer.write_bytes(Path(PROBE.__file__).read_bytes())

        def mutate_producer(command, cwd, timeout):
            measured = self.fake_execute(command, cwd, timeout)
            if command[1:] == mutation_point:
                producer.write_bytes(producer.read_bytes() + b'\n# changed during measurement\n')
            return measured

        with mock.patch.object(PROBE, '__file__', str(producer)):
            with self.assertRaisesRegex(ValueError, 'producer changed'):
                self.run_probe(mutate_producer)
        self.assertFalse((self.out / 'measurement.json').exists())
        self.assertEqual(list(self.out.glob('producer-*.py.gz')), [])

    def test_producer_change_during_version_cannot_be_attributed_to_new_source(self):
        self.assert_producer_change_refused(['--version'])

    def test_producer_change_during_cohort_cannot_be_attributed_to_new_source(self):
        self.assert_producer_change_refused(['check', '--json', 'case.lean'])

    def test_named_output_retains_exact_producer_and_previous_measurement(self):
        previous = self.out / 'measurement.json'
        previous.write_bytes(b'previous measurement\n')
        self.run_probe(self.fake_execute, output_name='measurement-source.json')
        report = json.loads((self.out / 'measurement-source.json').read_bytes())
        self.assertEqual(previous.read_bytes(), b'previous measurement\n')
        producer = gzip.decompress((self.out / ('producer-' + report['probe_sha256'][:12] + '.py.gz')).read_bytes())
        self.assertEqual(producer, Path(PROBE.__file__).read_bytes())
        self.assertEqual(hashlib.sha256(producer).hexdigest(), report['probe_sha256'])
        self.assertEqual(report['wall_timeout_s'], 2)

    def test_invalid_output_names_do_not_launch_executables(self):
        for name in ['../measurement.json', '/tmp/measurement.json', 'measurement.txt']:
            with self.subTest(output_name=name), redirect_stderr(io.StringIO()):
                execute = mock.Mock(side_effect=self.fake_execute)
                with self.assertRaises(SystemExit) as error:
                    self.run_probe(execute, output_name=name)
                self.assertEqual(error.exception.code, 2)
                execute.assert_not_called()

    def test_invalid_timeouts_do_not_launch_executables(self):
        for value in ['0', '-1', 'nan', 'inf', '-inf']:
            with self.subTest(timeout=value), redirect_stderr(io.StringIO()):
                execute = mock.Mock(side_effect=self.fake_execute)
                with self.assertRaises(SystemExit) as error:
                    self.run_probe(execute, timeout=value)
                self.assertEqual(error.exception.code, 2)
                execute.assert_not_called()
                self.assertFalse((self.out / 'measurement.json').exists())

    def test_stable_paths_preserve_options_and_bind_parsed_acquisition(self):
        original_sha256 = PROBE.sha256
        hashes = []

        def hashed(path):
            hashes.append(path)
            return original_sha256(path)

        def execute(command, cwd, timeout):
            if not self.calls:
                # The report must identify the bytes actually parsed, rather
                # than a later file at the acquisition path.
                (self.out / 'acquisition.json').write_text(json.dumps(dict(self.acquisition, later=True)))
            return self.fake_execute(command, cwd, timeout)

        with mock.patch.object(PROBE, 'sha256', side_effect=hashed):
            self.run_probe(execute)
        report = json.loads((self.out / 'measurement.json').read_bytes())
        self.assertEqual(report['counts'], {'agree-reject': 1})
        self.assertEqual(len(report['files']), 1)
        self.assertEqual(report['acquisition_sha256'], hashlib.sha256(self.acquisition_raw).hexdigest())
        self.assertEqual([call[0] for call in self.calls], [
            [str(self.lean), '--version'], [str(self.clean), '--version'],
            [str(self.lean), '--root=..', '-DprintMessageEndPos=true', '-Dlinter.all=false', '-DElab.inServer=true', 'case.lean'],
            [str(self.clean), 'check', '--json', 'case.lean'],
        ])
        self.assertTrue(all(timeout == 2 for _, _, timeout in self.calls))
        for name, path in [('lean', self.lean), ('clean', self.clean)]:
            binding = report['executable_bookends'][name]
            self.assertEqual(binding['path'], str(path))
            self.assertEqual(binding['initial'], binding['final'])
            self.assertEqual(hashes.count(path), 2, 'Hash large binaries only at the two bookends')

    def test_parent_alias_cannot_count_the_same_fixture_twice(self):
        self.acquisition['files'].append(dict(
            self.acquisition['files'][0], path='elab_fail/../elab_fail/case.lean'))
        (self.out / 'acquisition.json').write_text(json.dumps(self.acquisition))
        with self.assertRaisesRegex(ValueError, 'duplicate fixture path'):
            self.run_probe(self.fake_execute)
        self.assertFalse((self.out / 'measurement.json').exists())
        self.assertEqual(len(self.calls), 4, 'Only the first case may execute')

    def test_symlink_alias_cannot_count_the_same_fixture_twice(self):
        (self.out / 'fixtures/alias').symlink_to('elab_fail', target_is_directory=True)
        self.acquisition['files'].append(dict(
            self.acquisition['files'][0], path='alias/case.lean'))
        (self.out / 'acquisition.json').write_text(json.dumps(self.acquisition))
        with self.assertRaisesRegex(ValueError, 'duplicate fixture path'):
            self.run_probe(self.fake_execute)
        self.assertFalse((self.out / 'measurement.json').exists())
        self.assertEqual(len(self.calls), 4, 'Only the first case may execute')

    def test_distinct_paths_with_identical_contents_remain_distinct_cases(self):
        original = self.out / 'fixtures/elab_fail/case.lean'
        (self.out / 'fixtures/elab_fail/second.lean').write_bytes(original.read_bytes())
        self.acquisition['files'].append(dict(
            self.acquisition['files'][0], path='elab_fail/second.lean'))
        (self.out / 'acquisition.json').write_text(json.dumps(self.acquisition))
        self.run_probe(self.fake_execute)
        report = json.loads((self.out / 'measurement.json').read_bytes())
        self.assertEqual(report['counts'], {'agree-reject': 2})
        self.assertEqual([row['path'] for row in report['files']], [
            'elab_fail/case.lean', 'elab_fail/second.lean'])

    def test_executable_change_during_cohort_writes_no_measurement(self):
        def execute(command, cwd, timeout):
            response = self.fake_execute(command, cwd, timeout)
            if command[0] == str(self.clean) and command[1:] != ['--version']:
                self.clean.write_bytes(b'replaced clean executable during measurement')
            return response

        with self.assertRaisesRegex(ValueError, 'executable changed during measurement'):
            self.run_probe(execute)
        self.assertFalse((self.out / 'measurement.json').exists())

    def test_fixture_change_between_oracles_writes_no_measurement(self):
        def execute(command, cwd, timeout):
            response = self.fake_execute(command, cwd, timeout)
            if command[0] == str(self.lean) and command[1:] != ['--version']:
                (self.out / 'fixtures/elab_fail/case.lean').write_bytes(
                    b'example : True := True.intro\n')
            return response

        with self.assertRaisesRegex(ValueError, 'acquired source digest changed'):
            self.run_probe(execute)
        self.assertFalse((self.out / 'measurement.json').exists())
        self.assertFalse(any(command[0] == str(self.clean) and command[1:] != ['--version']
                             for command, _, _ in self.calls))

    def test_fixture_change_after_clean_writes_no_measurement(self):
        def execute(command, cwd, timeout):
            response = self.fake_execute(command, cwd, timeout)
            if command[0] == str(self.clean) and command[1:] != ['--version']:
                (self.out / 'fixtures/elab_fail/case.lean').write_bytes(
                    b'example : True := True.intro\n')
            return response

        with self.assertRaisesRegex(ValueError, 'acquired source digest changed'):
            self.run_probe(execute)
        self.assertFalse((self.out / 'measurement.json').exists())

    def test_later_case_cannot_change_an_earlier_fixture(self):
        data = b'example : False := True.intro\n'
        (self.out / 'fixtures/elab_fail/second.lean').write_bytes(data)
        self.acquisition['files'].append({
            'path': 'elab_fail/second.lean',
            'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
        })
        (self.out / 'acquisition.json').write_text(json.dumps(self.acquisition))

        def execute(command, cwd, timeout):
            response = self.fake_execute(command, cwd, timeout)
            if command[0] == str(self.clean) and command[-1] == 'second.lean':
                (self.out / 'fixtures/elab_fail/case.lean').write_bytes(
                    b'example : True := True.intro\n')
            return response

        with self.assertRaisesRegex(ValueError, 'acquired source digest changed'):
            self.run_probe(execute)
        self.assertFalse((self.out / 'measurement.json').exists())

    def test_version_timeouts_write_no_measurement(self):
        for path in [self.lean, self.clean]:
            with self.subTest(executable=path):
                def execute(command, cwd, timeout):
                    if command == [str(path), '--version']:
                        return {'rc': -9, 'timed_out': True, 'stdout': '', 'stderr': 'version timed out'}
                    return self.fake_execute(command, cwd, timeout)

                with self.assertRaisesRegex(ValueError, 'executable version failed'):
                    self.run_probe(execute)
                self.assertFalse((self.out / 'measurement.json').exists())

    def test_existing_measurement_is_refused_before_any_invocation(self):
        measurement = self.out / 'measurement.json'
        measurement.write_bytes(b'previous measurement\n')
        execute = mock.Mock(side_effect=self.fake_execute)
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            self.run_probe(execute)
        self.assertEqual(error.exception.code, 2)
        execute.assert_not_called()
        self.assertEqual(measurement.read_bytes(), b'previous measurement\n')

    def test_final_hash_refuses_a_change_not_visible_in_stat_bookends(self):
        def execute(command, cwd, timeout):
            response = self.fake_execute(command, cwd, timeout)
            if command[0] == str(self.clean) and command[1:] != ['--version']:
                self.clean.write_bytes(b'replaced clean executable')
            return response

        # Model metadata missing an in-place mutation: the final content hash
        # must still refuse, independently of the cheap per-invocation guard.
        with mock.patch.object(PROBE, 'executable_identity', return_value={'stat': 'unchanged'}):
            with self.assertRaisesRegex(ValueError, 'executable digest changed'):
                self.run_probe(execute)
        self.assertFalse((self.out / 'measurement.json').exists())


if __name__ == '__main__':
    unittest.main()
