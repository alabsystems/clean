#!/usr/bin/env python3
"""Real genesis capture boundaries on private Python emitters.

Four cases execute the public CLI; the read-fault case calls source-loaded check().

No compiler, Rust, proof, recorded image or native resource grant executes.
The private emitter writes real bytes and exits 1; process replies are not mocked.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
CHECKER = 'scripts/check_ck0_genesis_history.py'
HELPER = 'scripts/resource_transport.py'
INPUTS = (CHECKER, 'genesis/ck0/MANIFEST.txt', 'genesis/ck0/generate_manifest.sh',
          'genesis/ck0/verify.sh', HELPER)
PREFIX = 'Q6 REFUSED: retired capture fixture λ\n'.encode('utf-8')
LIMIT = 65536
REFUSAL = 'fixture execution refused: '
PAYLOAD = '''import os
data = EXPRESSION
remaining = memoryview(data)
while remaining:
    written = os.write(2, remaining)
    if written <= 0:
        raise RuntimeError('private emitter made no write progress')
    remaining = remaining[written:]
raise SystemExit(1)
'''


def sha(data):
    return hashlib.sha256(data).hexdigest()


class GenesisCapture(unittest.TestCase):
    def setUp(self):
        parent = Path(tempfile.gettempdir()) / '.ubd'
        parent.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='ck0-cap-', dir=parent)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / 'source'
        self.originals = {name: (ROOT / name).read_bytes() for name in INPUTS}
        for name, data in self.originals.items():
            target = self.source / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            if name.endswith('.sh'):
                target.chmod(0o755)
        self.transport = types.ModuleType('genesis_capture_resource_transport')
        self.transport.__file__ = str(ROOT / HELPER)
        exec(compile(self.originals[HELPER], str(ROOT / HELPER), 'exec', dont_inherit=True),
             self.transport.__dict__)
        self.receipt = {'case': self.id(), 'Rust_execution': False, 'proof_claim': False,
                        'q6_complete': False, 'native_resource_grant': False}

    def tearDown(self):
        print(json.dumps(self.receipt, sort_keys=True), flush=True)

    def cli(self, expression, expected):
        alias = self.root / 'python'
        alias.symlink_to(Path(sys.executable).resolve(strict=True))
        self.assertNotIn(' ', str(alias), 'private shebang alias requires a no-space path')
        payload = PAYLOAD.replace('EXPRESSION', expression)
        compile(payload, 'private-byte-emitter', 'exec', dont_inherit=True)
        script = ('#!' + str(alias) + '\n' + payload).encode()
        (self.source / 'genesis/ck0/generate_manifest.sh').write_bytes(script)
        before = {name: sha((self.source / name).read_bytes()) for name in INPUTS}
        argv = [sys.executable, '-B', str(self.source / CHECKER)]
        self.receipt.update(argv=argv, cwd=str(self.source),
            original_source_sha256={name: sha(data) for name, data in self.originals.items()},
            copied_source_sha256=before, expected_stderr_hex=expected.hex(),
            expected_stderr_bytes=len(expected))
        child = subprocess.Popen(argv, cwd=self.source, env=os.environ.copy(),
            pass_fds=self.transport.resource_fds(os.environ),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            stdout, stderr = child.communicate(timeout=15)
        except BaseException:
            child.kill()
            stdout, stderr = child.communicate()
            self.receipt.update(direct_exit=child.returncode,
                                stdout_hex=stdout.hex(), stderr_hex=stderr.hex(), harness_interrupted=True)
            raise
        after = {name: sha((self.source / name).read_bytes()) for name in INPUTS}
        self.receipt.update(direct_exit=child.returncode, stdout_hex=stdout.hex(),
                            stderr_hex=stderr.hex(), copied_source_sha256_after=after)
        self.assertEqual(before, after, 'copied source bytes changed during actual CLI')
        self.assertEqual({name: sha((ROOT / name).read_bytes()) for name in INPUTS},
                         {name: sha(data) for name, data in self.originals.items()},
                         'current source endpoint changed during actual CLI')
        return child.returncode, stdout, stderr

    def accepted(self, expression, expected):
        code, stdout, stderr = self.cli(expression, expected)
        self.assertEqual(code, 0, stderr)
        self.assertEqual(stderr, b'')
        result = json.loads(stdout)
        self.receipt['actual_checker_result'] = result
        self.assertEqual(result['cases'], 24)
        self.assertEqual(result['guarded_tool_calls'], 0)
        self.assertIs(result['fixture_state_unchanged'], True)
        self.assertIs(result['proof_claim'], False)
        self.assertIs(result['q6_complete'], False)

    def refused(self, expression, expected):
        code, stdout, stderr = self.cli(expression, expected)
        self.assertEqual(code, 1, stdout + stderr)
        self.assertEqual(stdout, b'')
        text = stderr.decode('utf-8')
        self.assertIn(REFUSAL, text)
        record = json.loads(text.split(REFUSAL, 1)[1])
        self.receipt['actual_error_record'] = record
        self.assertEqual(record['case'], {'entrypoint': 'genesis/ck0/generate_manifest.sh',
                                         'cwd': '.', 'arguments': [], 'index': 0})
        self.assertEqual(record['deadline_seconds'], 5)
        self.assertIs(record['timed_out'], False)
        self.assertEqual(record['leader_exit'], 1)
        self.assertEqual(record['stdout_hex'], '')
        self.assertEqual(record['stdout_bytes'], 0)
        self.assertEqual(record['stderr_hex'], expected[:LIMIT].hex())
        self.assertEqual(record['stderr_bytes'], len(expected))
        self.assertIs(record['cleanup_uncertain'], False)
        self.assertIs(record['fixture_retained'], False)
        self.assertIs(record['cleanup']['group_drained'], True)
        self.assertIs(record['cleanup']['leader_reaped'], True)
        self.assertEqual(record['cleanup']['errors'], [])
        return record

    def test_valid_unicode_stderr_prefix_accepted(self):
        self.receipt['payload_kind'] = 'valid-unicode-prefix'
        self.accepted(repr(PREFIX), PREFIX)

    def test_invalid_utf8_stderr_refused(self):
        self.receipt['payload_kind'] = 'invalid-utf8'
        expected = PREFIX + b'\xff'
        record = self.refused(repr(expected), expected)
        self.assertEqual(record['reason'], 'invalid UTF-8 fixture response')
        self.assertEqual(record['error']['type'], 'UnicodeDecodeError')
        self.assertIs(record['capture_truncated'], False)

    def test_exact_capture_limit_accepted(self):
        self.receipt['payload_kind'] = 'exact-capture-limit'
        expected = PREFIX + b'A' * (LIMIT - len(PREFIX))
        self.accepted(repr(PREFIX) + ' + b"A" * (65536 - ' + str(len(PREFIX)) + ')', expected)

    def test_one_over_capture_limit_refused(self):
        self.receipt['payload_kind'] = 'one-over-capture-limit'
        expected = PREFIX + b'A' * (LIMIT + 1 - len(PREFIX))
        record = self.refused(repr(PREFIX) + ' + b"A" * (65537 - ' + str(len(PREFIX)) + ')', expected)
        self.assertEqual(record['reason'], 'fixture response exceeded 64KiB capture prefix')
        self.assertIs(record['capture_truncated'], True)

    def _capture_read_case(self, inject):
        """Fault only an owned data fd after real cleanup, then restore it."""
        import fcntl
        control = Path(tempfile.mkdtemp(prefix='cap-read-', dir=self.root.parent))
        records, streams, cleanup = [], [], []
        result = {'injected': inject, 'method': 'actual source-loaded check()',
                  'faults': records, 'cleanup': cleanup, 'Rust_execution': False,
                  'proof_claim': False, 'q6_complete': False}
        self.receipt.setdefault('read_error_controls', []).append(result)
        try:
            source = control / 'source'
            for name, data in self.originals.items():
                path = source / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                if name.endswith('.sh'):
                    path.chmod(0o755)
            alias = control / 'python'
            alias.symlink_to(Path(sys.executable).resolve(strict=True))
            self.assertNotIn(' ', str(alias))
            forbidden = b'FORBIDDEN stdout from real capture emitter\n'
            payload = ('import os\nfor fd,data in '+repr(((1, forbidden), (2, PREFIX)))+':\n'
                ' remaining=memoryview(data)\n while remaining:\n'
                '  written=os.write(fd,remaining)\n'
                '  if written<=0:raise RuntimeError("emitter made no progress")\n'
                '  remaining=remaining[written:]\nraise SystemExit(1)\n')
            (source / 'genesis/ck0/generate_manifest.sh').write_bytes(
                ('#!'+str(alias)+'\n'+payload).encode())
            hashes = {name: sha((source / name).read_bytes()) for name in INPUTS}
            module = types.ModuleType('actual_capture_read_subject')
            module.__file__ = str(source / CHECKER)
            exec(compile((source / CHECKER).read_bytes(), module.__file__, 'exec',
                         dont_inherit=True), module.__dict__)
            real_cleanup, real_prefix = module._cleanup_fixture, module._prefix
            def cleaned(process, details, *args):
                try:
                    return real_cleanup(process, details, *args)
                finally:
                    cleanup.append({'pid': process.pid, 'returncode': process.returncode,
                        'leader_exit': details['leader_exit'],
                        'certain': not details['cleanup_uncertain'],
                        **details['cleanup']})
            module._cleanup_fixture = cleaned
            def prefix(stream):
                name = getattr(stream, 'name', None)
                if not isinstance(name, str) or not Path(name).name.startswith('fixture-stdout-'):
                    return real_prefix(stream)
                path = Path(name)
                self.assertIn(str(path.parent), [scope.name for scope in module._ACTIVE_SCRATCH])
                self.assertTrue(cleanup and cleanup[-1]['certain'])
                self.assertTrue(cleanup[-1]['group_drained'] and cleanup[-1]['leader_reaped'])
                self.assertEqual(cleanup[-1]['returncode'], 1)
                self.assertEqual(cleanup[-1]['errors'], [])
                self.assertLessEqual(path.stat().st_size, LIMIT)
                row = {'path': str(path), 'raw_before_hex': path.read_bytes().hex(),
                       'cleanup_pid': cleanup[-1]['pid'], 'injected': inject}
                records.append(row)
                streams.append(stream)
                if not inject:
                    return real_prefix(stream)
                fd = stream.fileno()
                self.assertNotIn(fd, self.transport.resource_fds(os.environ))
                identity = os.fstat(fd)
                flags = fcntl.fcntl(fd, fcntl.F_GETFL)
                inheritable = os.get_inheritable(fd)
                backup = os.dup(fd)
                write_only = None
                try:
                    write_only = os.open(path, os.O_WRONLY)  # No truncation or write.
                    view = os.fstat(write_only)
                    self.assertEqual((identity.st_dev, identity.st_ino), (view.st_dev, view.st_ino))
                    os.dup2(write_only, fd, inheritable=inheritable)
                    row['fault_access_mode'] = fcntl.fcntl(fd, fcntl.F_GETFL) & os.O_ACCMODE
                    try:
                        return real_prefix(stream)
                    except OSError as error:
                        row['actual_error'] = {'errno': error.errno, 'type': type(error).__name__,
                                               'message': str(error)}
                        raise
                finally:
                    try:
                        os.dup2(backup, fd, inheritable=inheritable)
                        restored = os.fstat(fd)
                        row['restored'] = ((identity.st_dev, identity.st_ino) ==
                            (restored.st_dev, restored.st_ino) and
                            fcntl.fcntl(fd, fcntl.F_GETFL) == flags and
                            os.get_inheritable(fd) == inheritable)
                    finally:
                        os.close(backup)
                        if write_only is not None:
                            os.close(write_only)
                    row['raw_after_hex'] = path.read_bytes().hex()
            module._prefix = prefix
            try:
                result['returned'] = module.check()
            except module.FixtureExecutionRefused as error:
                result['refusal'] = error.details
            except ValueError as error:
                result['ordinary_refusal'] = str(error)
            finally:
                result['capture_streams_closed'] = [stream.closed for stream in streams]
                result['source_before'] = hashes
                result['source_after'] = {name: sha((source / name).read_bytes()) for name in INPUTS}
                self.assertEqual(result['source_before'], result['source_after'])
                self.assertEqual({name: sha((ROOT / name).read_bytes()) for name in INPUTS},
                                 {name: sha(data) for name, data in self.originals.items()})
            return result
        finally:
            # Uncertain actual writers retain the private source too. Never
            # erase it merely because the unittest is unwinding an exception.
            if cleanup and all(row['certain'] and row['leader_reaped'] and row['group_drained']
                               and not row['errors'] for row in cleanup):
                shutil.rmtree(control)
                result['control_source_removed'] = True
            else:
                result['retained_control_source'] = str(control)

    def test_capture_read_error_refuses_after_certain_cleanup(self):
        import errno
        normal = self._capture_read_case(False)
        self.assertIn('missing explicit historical refusal', normal['ordinary_refusal'])
        self.assertEqual(bytes.fromhex(normal['faults'][0]['raw_before_hex']),
                         b'FORBIDDEN stdout from real capture emitter\n')
        fault = self._capture_read_case(True)
        self.assertTrue(fault['faults'])
        for row in fault['faults']:
            self.assertEqual(row['fault_access_mode'], os.O_WRONLY)
            self.assertEqual(row['actual_error']['errno'], errno.EBADF)
            self.assertEqual(row['actual_error']['type'], 'OSError')
            self.assertIs(row['restored'], True)
            self.assertEqual(row['raw_before_hex'], row['raw_after_hex'])
        self.assertEqual(fault['faults'][0]['raw_before_hex'], normal['faults'][0]['raw_before_hex'])
        self.assertTrue(all(fault['capture_streams_closed']))
        self.assertIs(fault['control_source_removed'], True)
        self.assertNotIn('returned', fault, 'failed stdout capture was accepted')
        record = fault['refusal']
        self.assertEqual(record['reason'], 'fixture capture unavailable')
        self.assertEqual(record['capture_error']['type'], 'OSError')
        self.assertEqual(record['leader_exit'], 1)
        self.assertEqual(record['stdout_hex'], '')
        self.assertEqual(record['stderr_hex'], PREFIX.hex())
        self.assertIs(record['timed_out'], False)
        self.assertIs(record['capture_truncated'], False)
        self.assertIs(record['cleanup_uncertain'], False)
        self.assertIs(record['fixture_retained'], False)
        self.assertTrue(record['cleanup']['group_drained'] and record['cleanup']['leader_reaped'])
        self.assertEqual(record['cleanup']['errors'], [])


if __name__ == '__main__':
    program = unittest.main(exit=False, verbosity=2)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
