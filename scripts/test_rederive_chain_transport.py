#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
"""Replay launch transport over inert pipes; no native authority or Rust job."""
import contextlib
import gc
import hashlib
import io
import json
import os
from pathlib import Path
import shlex
import sys
import tempfile
import types
import unittest
import warnings
from unittest.mock import patch

SOURCE_ROOT = Path(__file__).resolve().parents[1]


def source_module(name, filename):
    path = SOURCE_ROOT / 'scripts' / filename
    module = types.ModuleType(name)
    module.__file__ = str(path)
    # Dataclasses resolve their defining module through sys.modules.
    sys.modules[name] = module
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module


class ReplayTransport(unittest.TestCase):
    def setUp(self):
        self.chain = source_module('rederive_transport_chain', 'rederive_chain.py')
        self.registry = source_module('rederive_transport_registry', 'check_gate_registry.py')
        self.temp = tempfile.TemporaryDirectory(prefix='rederive-transport-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for path in ('scripts', 'inputs', 'data', 'crates/inert', 'sandbox'):
            (self.root / path).mkdir(parents=True)
        self.log = self.root / 'calls.jsonl'
        self.fds = []
        for _ in range(7):
            self.fds.extend(os.pipe())
        self.addCleanup(lambda: [os.close(fd) for fd in self.fds])
        a, b, sdk, store, implicit, cpu1, cpu2, fence1, fence2, host1, host2, *unused = self.fds
        self.unrelated = unused[-1]
        os.set_inheritable(self.unrelated, True)
        self.env = {
            'PATH': os.environ.get('PATH', ''),
            'CARGO_MAKEFLAGS': f'-j2 --jobserver-auth={a},{b}',
            'MAKEFLAGS': f'--jobserver-fds={a},{b}', 'MFLAGS': f'--jobserver-auth={a},{b}',
            'ATERM_SDK_LEASE_V3': str(sdk), 'ATERM_WORKLOAD_HOST_STORE_FD_V1': str(store),
            'TRUST_CPU_IMPLICIT_FD': str(implicit),
            'ATERM_WORKLOAD_CPU_FDS_V1': f'{cpu1},{cpu2}', 'BUILD_SLOT_FENCE_FDS': f'{fence1},{fence2}',
            'ATERM_WORKLOAD_HOST_CONTROL_FDS_V1': f'{host1},{host2}',
            'TRUST_CPU_HANDOFF': 'inert-fixture-cpu-route',
            'CARGO_JOBSERVER_HANDOFF': 'inert-fixture-gnu-route',
            'TRUST_FIXED_CLAIM_HANDOFF_V1': 'inert-fixture-fixed-route',
            'BUILD_SLOT_HELD': 'fixture-not-authority', 'BUILD_SLOT_CPU_PROTOCOL': 'fixture-not-authority',
            'HEAVY_GATE_HELD': 'fixture-not-authority', 'TARGO_PLANNED_JOBS': '2', 'TARGO_CALLER_JOBS': '1',
        }
        self.expected = {key: value for key, value in self.env.items() if key != 'PATH'}
        selected = self.fds[:11]
        self.identities = {str(fd): [os.fstat(fd).st_dev, os.fstat(fd).st_ino] for fd in selected}
        self.config = self.root / 'probe.json'
        self.write_config()
        program = '''import json,os,sys
from pathlib import Path
expected,identities,unrelated,log,root=json.loads(Path(CONFIG).read_text())
args=sys.argv[1:]
with open(log,'a') as out: out.write(json.dumps(args)+'\\n')
for key,value in expected.items():
    if os.environ.get(key)!=value: raise SystemExit('changed advertisement: '+key)
for fd,want in identities.items():
    try: current=os.fstat(int(fd))
    except OSError: raise SystemExit('closed advertised descriptor: '+fd)
    if [current.st_dev,current.st_ino]!=want: raise SystemExit('replaced descriptor: '+fd)
try: os.fstat(unrelated)
except OSError: pass
else: raise SystemExit('unadvertised descriptor inherited')
if args[:1]==['--frontend']: print(str(Path(root)/'scripts/targo'))
elif args==['--pinned-inputs']: print('inputs/x.txt')
elif args[:1]==['clean']:
    expected_target=str(Path(root)/'sandbox/target')
    if os.environ.get('CARGO_TARGET_DIR')!=expected_target or os.environ.get('CARGO_BUILD_BUILD_DIR')!=expected_target:
        raise SystemExit('changed sandbox target routing')
    print('inert endpoint')
elif args==['invalid-output']: os.write(1, bytes([255]))
else: print('inert endpoint')
'''.replace('CONFIG', repr(str(self.config)))
        self.probe = self.root / 'scripts/probe.py'
        self.probe.write_text(program)
        (self.root / 'inputs/x.txt').write_text('inert input\n')
        for name, arguments in [('targo', ''), ('rust_frontend.sh', '--frontend '), ('subject.sh', '')]:
            target = self.root / 'scripts' / name
            target.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' -B ' + shlex.quote(str(self.probe)) + ' ' + arguments + '"$@"\n')
            target.chmod(0o700)
        self.subject = self.root / 'scripts/subject.sh'
        self.table = {'rows': [{'id': 'inert', 'path': 'scripts/subject.sh', 'claims': 'quality',
                              'demonstrated': {'kind': 'selftest-inline', 'ref': 'scripts/subject.sh --selftest',
                                               'script_sha256': hashlib.sha256(self.subject.read_bytes()).hexdigest()}}]}
        (self.root / 'data/gate_registry.json').write_text(json.dumps(self.table))
        (self.root / 'Cargo.toml').write_text('[workspace]\nmembers=["crates/inert"]\n')
        (self.root / 'crates/inert/Cargo.toml').write_text('[package]\nname="inert"\nversion="0.0.0"\n')
        self.registry.ROOT = self.root
        self.registry._TARGO_CACHE.clear()

    def write_config(self):
        self.config.write_text(json.dumps([self.expected, self.identities, self.unrelated, str(self.log), str(self.root)]))

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def invoke(self, route):
        with patch.dict(os.environ, self.env, clear=True):
            if route in ('context', 'stream'):
                return self.chain.Context(self.root).run(('scripts/probe.py', route), stream=(route == 'stream'))
            if route == 'query':
                return self.registry._derived_inputs(self.root, 'scripts/subject.sh')
            if route == 'frontend':
                return self.registry._canonical_targo()
            if route == 'arm':
                return self.registry._run_demo_command(shlex.join([sys.executable, '-B', str(self.probe), 'arm']), 'inert', False, self.root, self.env)
            if route == 'ref':
                return self.registry.repin(self.root, 'inert')
            if route == 'eviction':
                # Own sandbox target routing is retained by _sandbox_env.
                self.registry._TARGO_CACHE[:] = [str(self.root/'scripts/targo')]
                return self.registry._evict_mutated_units(self.root/'sandbox', self.root, 'crates/inert/src/lib.rs')
            raise AssertionError('unknown route')

    def check_positive(self, route):
        result = self.invoke(route)
        if route in ('context', 'stream'):
            self.assertEqual(result, (0, 'inert endpoint\n'))
        elif route == 'query':
            self.assertEqual(result, ({'inputs/x.txt': hashlib.sha256((self.root/'inputs/x.txt').read_bytes()).hexdigest()}, ''))
        elif route == 'frontend':
            self.assertEqual(result, str(self.root/'scripts/targo'))
        elif route == 'arm':
            self.assertEqual(result.returncode, 0, result.stderr)
        elif route == 'ref':
            self.assertEqual(result, 0)
            row = json.loads((self.root/'data/gate_registry.json').read_text())['rows'][0]
            self.assertEqual(row['demonstrated']['replayed']['by'], '`scripts/subject.sh --selftest` exited 0')
        elif route == 'eviction':
            self.assertEqual(self.calls(), [['clean', '-p', 'inert'], ['clean', '-p', 'inert', '--release']])
        self.assertEqual(len(self.calls()), 2 if route == 'eviction' else 1)

    def test_context_preserves_live_pipe_identity_and_exact_fields(self): self.check_positive('context')
    def test_stream_preserves_live_pipe_identity_and_exact_fields(self): self.check_positive('stream')
    def test_query_preserves_live_pipe_identity_and_exact_fields(self): self.check_positive('query')
    def test_frontend_preserves_live_pipe_identity_and_exact_fields(self): self.check_positive('frontend')
    def test_arm_shell_preserves_live_pipe_identity_and_exact_fields(self): self.check_positive('arm')
    def test_runnable_ref_preserves_live_pipe_identity_and_exact_fields(self): self.check_positive('ref')
    def test_both_evictions_preserve_live_pipe_identity_and_exact_fields(self): self.check_positive('eviction')

    def test_context_closes_output_on_success_stream_and_decode_error(self):
        for route in ('context', 'stream', 'invalid-output'):
            with self.subTest(route=route), warnings.catch_warnings(record=True) as observed:
                warnings.simplefilter('always', ResourceWarning)
                if route == 'invalid-output':
                    with patch.dict(os.environ, self.env, clear=True):
                        with self.assertRaises(UnicodeDecodeError):
                            self.chain.Context(self.root).run(('scripts/probe.py', route))
                else:
                    self.assertEqual(self.invoke(route), (0, 'inert endpoint\n'))
                gc.collect()
                self.assertEqual([str(w.message) for w in observed
                                  if issubclass(w.category, ResourceWarning)], [])

    def check_prelaunch_refusal(self, route):
        before = (self.root/'data/gate_registry.json').read_bytes()
        if route in ('context', 'stream'):
            code, message = self.invoke(route)
            self.assertEqual(code, 127)
            self.assertIn('descriptor', message)
        elif route == 'query':
            derived, why = self.invoke(route)
            self.assertIsNone(derived)
            self.assertIn('resource transport refused', why)
        else:
            with self.assertRaisesRegex(self.registry.Red, 'resource transport refused'):
                self.invoke(route)
        self.assertEqual(self.calls(), [])
        self.assertEqual((self.root/'data/gate_registry.json').read_bytes(), before)

    def test_closed_descriptor_refuses_every_route_before_endpoint(self):
        read_fd, write_fd = os.pipe()
        os.close(read_fd); os.close(write_fd)
        self.env['ATERM_SDK_LEASE_V3'] = str(write_fd)
        for route in ('context', 'stream', 'query', 'frontend', 'arm', 'ref', 'eviction'):
            with self.subTest(route=route): self.check_prelaunch_refusal(route)

    def test_malformed_descriptor_refuses_every_route_before_endpoint(self):
        self.env['ATERM_WORKLOAD_CPU_FDS_V1'] = 'x'
        for route in ('context', 'stream', 'query', 'frontend', 'arm', 'ref', 'eviction'):
            with self.subTest(route=route): self.check_prelaunch_refusal(route)

    def test_endpoint_rejects_changed_exact_advertisement(self):
        self.expected['TRUST_CPU_HANDOFF'] = 'different-inert-route'
        self.write_config()
        code, message = self.invoke('context')
        self.assertNotEqual(code, 0)
        self.assertIn('changed advertisement: TRUST_CPU_HANDOFF', message)
        self.assertEqual(self.calls(), [['context']])

    def test_malformed_frontend_does_not_fall_back_to_path(self):
        self.env['TRUST_CPU_IMPLICIT_FD'] = '2'
        with self.assertRaisesRegex(self.registry.Red, 'resource transport refused'):
            self.invoke('frontend')
        self.assertEqual(self.registry._TARGO_CACHE, [])
        self.assertEqual(self.calls(), [])

    def test_both_repin_flags_preserve_normal_replay_precedence(self):
        with patch.object(self.registry, 'repin', return_value=23) as replay:
            self.assertEqual(self.registry.main(['--repin', 'normal', '--repin-undemonstrated', 'other']), 23)
        replay.assert_called_once_with(self.root, 'normal')

    def test_main_repin_turns_transport_refusal_into_clean_nonzero(self):
        self.env['ATERM_SDK_LEASE_V3'] = 'x'
        stderr = io.StringIO()
        with patch.dict(os.environ, self.env, clear=True), contextlib.redirect_stderr(stderr):
            self.assertEqual(self.registry.main(['--repin', 'inert']), 1)
        self.assertIn('GATE_REGISTRY=fail resource transport refused', stderr.getvalue())
        self.assertNotIn('Traceback', stderr.getvalue())
        self.assertEqual(self.calls(), [])


if __name__ == '__main__':
    unittest.main(verbosity=2)
