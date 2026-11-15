#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
"""Lint client transport controls using inert subprocess endpoints.

Fixture locators route ordinary pipes only. No endpoint imports native authority,
compiles Rust, authenticates a scheduler/SDK, or earns a proof claim.
"""
import hashlib
import importlib.util
import json
import marshal
import os
from pathlib import Path
import py_compile
import shlex
import subprocess
import struct
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/check_lint_coverage.py'


def source_module(path=SCRIPT):
    module = types.ModuleType('lint_transport_test_subject')
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module


class LintTransport(unittest.TestCase):
    def setUp(self):
        self.subject = source_module()
        self.temp = tempfile.TemporaryDirectory(prefix='lint-transport-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.root.joinpath('scripts').mkdir()
        self.root.joinpath('bin').mkdir()
        self.root.joinpath('sysroot/lib').mkdir(parents=True)
        self.log = self.root / 'calls.jsonl'
        self.fds = []
        for _ in range(6):
            self.fds.extend(os.pipe())
        self.addCleanup(lambda: [os.close(fd) for fd in self.fds])
        a,b,*rest = self.fds
        self.unrelated = rest[-1]
        self.env = {'PATH': os.environ.get('PATH', ''),
                    'CARGO_MAKEFLAGS': f'-j2 --jobserver-auth={a},{b}',
                    'MAKEFLAGS': f'--jobserver-fds={a},{b}',
                    'MFLAGS': f'--jobserver-auth={a},{b}',
                    'ATERM_SDK_LEASE_V3': str(rest[0]),
                    'ATERM_WORKLOAD_HOST_STORE_FD_V1': str(rest[1]),
                    'TRUST_CPU_IMPLICIT_FD': str(rest[2]),
                    'ATERM_WORKLOAD_CPU_FDS_V1': ','.join(map(str,rest[3:5])),
                    'BUILD_SLOT_FENCE_FDS': ','.join(map(str,rest[5:7])),
                    # The native owner checks the required nine originals.
                    # These inert fixtures exercise only numeric transport.
                    'ATERM_WORKLOAD_HOST_CONTROL_FDS_V1': str(rest[7]),
                    'TRUST_CPU_HANDOFF': 'inert-fixture-cpu-route',
                    'CARGO_JOBSERVER_HANDOFF': 'inert-fixture-gnu-route',
                    'TRUST_FIXED_CLAIM_HANDOFF_V1': 'inert-fixture-fixed-route',
                    'BUILD_SLOT_HELD': 'fixture-not-authority',
                    'BUILD_SLOT_CPU_PROTOCOL': 'fixture-not-authority',
                    'HEAVY_GATE_HELD': 'fixture-not-authority',
                    'TARGO_PLANNED_JOBS': '2', 'TARGO_CALLER_JOBS': '1'}
        self.expected_fds = self.subject.custody_fds(self.env)
        identities = {str(fd): [os.fstat(fd).st_dev, os.fstat(fd).st_ino]
                      for fd in self.expected_fds}
        program = '''import json,os,sys
from pathlib import Path
expected,identities,unrelated,log,root = json.loads(CONFIG)
for key,value in expected.items():
    if os.environ.get(key)!=value: raise SystemExit('changed advertisement: '+key)
for fd,want in identities.items():
    try: s=os.fstat(int(fd))
    except OSError: raise SystemExit('closed advertised descriptor: '+fd)
    if [s.st_dev,s.st_ino]!=want: raise SystemExit('replaced descriptor: '+fd)
try: os.fstat(unrelated)
except OSError: pass
else: raise SystemExit('unadvertised descriptor inherited')
args=sys.argv[1:]
with open(log,'a') as out: out.write(json.dumps(args)+'\\n')
if args[:1]==['--frontend']: print(str(Path(root)/'bin/targo'))
elif Path(sys.argv[0]).stem=='trustc':
    if args!=['--print=sysroot']: raise SystemExit('noncanonical query')
    print(str(Path(root)/'sysroot'))
elif args[:1]==['metadata']: print('{"packages":[]}')
elif args[:1]==['-Zunstable-options']: pass
else: print('fixture endpoint')
'''
        config = json.dumps([self.env, identities, self.unrelated, str(self.log), str(self.root)])
        program = program.replace('CONFIG', repr(config))
        for name in ['targo','trustc']:
            path = self.root/'bin'/name
            source = path.with_suffix('.py'); source.write_text(program)
            path.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '+shlex.quote(str(source))+' \"$@\"\n')
            path.chmod(0o700)
        frontend = self.root / self.subject.FRONTEND
        frontend.write_text('#!/bin/bash\nexec '+shlex.quote(str(self.root/'bin/targo'))+' --frontend "$@"\n')

    def calls(self):
        return [json.loads(x) for x in self.log.read_text().splitlines()] if self.log.exists() else []

    def test_resolver_preserves_fields_and_descriptor_identities(self):
        with patch.object(self.subject, 'ROOT', self.root):
            self.assertEqual(self.subject.resolve_targo(self.env),str(self.root/'bin/targo'))
        self.assertEqual(self.calls(), [['--frontend','--targo']])

    def test_metadata_preserves_fields_and_descriptor_identities(self):
        with patch.object(self.subject,'ROOT',self.root), patch.dict(os.environ,self.env,clear=True):
            self.assertEqual(self.subject.cargo_metadata(), {'packages':[]})
        self.assertEqual(len(self.calls()),2)

    def test_config_preserves_fields_and_descriptor_identities(self):
        self.assertEqual(self.subject.config_problems(self.root,self.env,str(self.root/'bin/targo')),[])
        self.assertEqual(len(self.calls()),1)

    def test_runner_preserves_fields_and_descriptor_identities(self):
        self.assertEqual(self.subject._run([str(self.root/'bin/targo'),'probe'],self.root,self.env),(0,'fixture endpoint\n'))
        self.assertEqual(self.calls(),[['probe']])

    def test_types_query_preserves_fields_and_descriptor_identities(self):
        with patch.object(self.subject,'_run',return_value=(1,'intentional fixture build refusal')):
            binary,why=self.subject.build_types(self.root,self.env,str(self.root/'bin/targo'))
        self.assertIsNone(binary)
        self.assertIn('intentional fixture build refusal',why)
        self.assertEqual(self.calls(),[['--print=sysroot']])

    def test_sanitizer_preserves_only_exact_resource_fields(self):
        poisoned={**self.env,'RUSTFLAGS':'--cap-lints=allow','RUSTC_WRAPPER':'bad',
                  'CARGO_ENCODED_RUSTFLAGS':'bad','TRUST_UNKNOWN_AUTHORITY':'bad',
                  'ATERM_UNKNOWN_TOKEN':'bad'}
        self.assertEqual(self.subject.sanitized_env(poisoned),self.env)
        for name in ['BUILD_SLOT_CPU_MODE','BUILD_SLOT_CPU_SOURCE','BUILD_SLOT_CPU_BUDGET',
                     'BUILD_SLOT_POOL_SLOTS','BUILD_SLOT_DIR','BUILD_SLOT_EXCLUSIVE',
                     'BUILD_SLOT_LEGACY_DIR','BUILD_SLOT_V2_DIR','BUILD_SLOT_V2_SLOTS']:
            with self.subTest(name=name):
                self.assertEqual(self.subject.sanitized_env({name:'unchanged'}),{name:'unchanged'})

    def test_malformed_locator_refuses_before_launch(self):
        for value in ['', '0', '-1','3,3','3,,4','garbage']:
            with self.subTest(value=value), patch.object(self.subject,'ROOT',self.root):
                env={**self.env,'ATERM_WORKLOAD_HOST_CONTROL_FDS_V1':value}
                with self.assertRaisesRegex(self.subject.CoverageFailure,'transport refused'):
                    self.subject.resolve_targo(env)
        self.assertEqual(self.calls(),[])

    def test_closed_locator_refuses_before_launch(self):
        fd=os.dup(self.fds[0]);os.close(fd)
        env={**self.env,'ATERM_SDK_LEASE_V3':str(fd)}
        rc,out=self.subject._run([str(self.root/'bin/targo'),'probe'],self.root,env)
        self.assertEqual(rc,127);self.assertIn('not live',out);self.assertEqual(self.calls(),[])

    def test_no_advertisement_synthesized(self):
        self.assertEqual(self.subject.sanitized_env({}),{})
        self.assertEqual(self.subject.custody_fds({}),())

    def test_effective_gnu_precedence_ignores_obsolete_descriptors(self):
        a,b=self.fds[:2]
        fd=os.dup(a);os.close(fd)
        selected=f'--jobserver-auth={a},{b}'
        for env in [
                {'CARGO_MAKEFLAGS':selected,'MAKEFLAGS':f'--jobserver-auth={fd},{fd}'},
                {'CARGO_MAKEFLAGS':f'--jobserver-auth={fd},{fd} '+selected},
                {'CARGO_MAKEFLAGS':f'--jobserver-fds={fd},{fd} '+selected},
                {'CARGO_MAKEFLAGS':f'--jobserver-auth=+00{a},00{b}'},
                {'MAKEFLAGS':selected,'MFLAGS':f'--jobserver-auth={fd},{fd}'}]:
            with self.subTest(env=env):
                self.assertEqual(self.subject.custody_fds(env),tuple(sorted([a,b])))
        for value in ['', '-j2', '--jobserver-auth=fifo:/inert-fixture', '--jobserver-auth=-1,-1']:
            self.assertEqual(self.subject.custody_fds(
                {'CARGO_MAKEFLAGS':value,'MAKEFLAGS':f'--jobserver-auth={fd},{fd}'}),())

    def test_effective_gnu_bad_pair_refuses(self):
        a,b=self.fds[:2]
        fd=os.dup(a);os.close(fd)
        for value in [f'{fd},{fd}', 'garbage','fifo:', '999999999999,3',
                      '2147483648,3',f'{a},{b}\t-j2']:
            with self.subTest(value=value),self.assertRaises(self.subject.CoverageFailure):
                self.subject.custody_fds({'CARGO_MAKEFLAGS':'--jobserver-auth='+value})
        with self.assertRaises(self.subject.CoverageFailure):
            self.subject.custody_fds({'ATERM_SDK_LEASE_V3':'9999999999'})

    def test_types_sysroot_path_keeps_whitespace_and_refuses_ambiguous_output(self):
        compiler=self.root/'bin/trustc.py';original=compiler.read_text()
        def output(text):
            compiler.write_text(original.replace("print(str(Path(root)/'sysroot'))",
                                                'sys.stdout.write('+repr(text)+')'))
        spaced=self.root/'sysroot with trailing space '
        (spaced/'lib').mkdir(parents=True)
        output(str(spaced)+'\n')
        with patch.object(self.subject,'_run',return_value=(1,'fixture stop')) as run:
            self.subject.build_types(self.root,self.env,str(self.root/'bin/targo'))
        self.assertIn(f'link-arg=-Wl,-rpath,{spaced / "lib"}',run.call_args.args[0])
        for text in ['', '\n',str(spaced)+'\n'+str(spaced)+'\n',
                     str(spaced)+'\r\n','relative\n',str(spaced)+'\x00\n']:
            with self.subTest(text=text):
                output(text)
                with patch.object(self.subject,'_run') as run:
                    binary,why=self.subject.build_types(self.root,self.env,str(self.root/'bin/targo'))
                self.assertIsNone(binary);self.assertIn('named no sysroot',why)
                run.assert_not_called()

    def test_missing_fd_transport_mutant_is_detected(self):
        with patch.object(self.subject,'custody_fds',return_value=()):
            rc,out=self.subject._run([str(self.root/'bin/targo'),'probe'],self.root,self.env)
        self.assertNotEqual(rc,0);self.assertIn('closed advertised descriptor',out)
        self.assertEqual(self.calls(),[])

    def test_stripped_field_mutant_is_detected(self):
        env=dict(self.env);env.pop('TRUST_CPU_HANDOFF')
        rc,out=self.subject._run([str(self.root/'bin/targo'),'probe'],self.root,env)
        self.assertNotEqual(rc,0);self.assertIn('changed advertisement',out);self.assertEqual(self.calls(),[])


class SourceCacheBinding(unittest.TestCase):
    def test_helper_executes_source_despite_matching_cache(self):
        for mode in [py_compile.PycInvalidationMode.TIMESTAMP,py_compile.PycInvalidationMode.CHECKED_HASH]:
            with self.subTest(mode=mode),tempfile.TemporaryDirectory(prefix='lint-source-cache-') as directory:
                root=Path(directory);scripts=root/'scripts';scripts.mkdir()
                subject=scripts/SCRIPT.name;subject.write_bytes(SCRIPT.read_bytes())
                helper=scripts/'resource_transport.py'
                poison='def resource_fds(env):\n    return (999,)\n'
                clean ='def resource_fds(env):\n    return (111,)\n'
                for source in [clean,'this is invalid Python !!!\n']:
                    helper.write_text(source)
                    header=importlib.util.MAGIC_NUMBER
                    if mode==py_compile.PycInvalidationMode.TIMESTAMP:
                        header+=struct.pack('<III',0,int(helper.stat().st_mtime)&0xffffffff,
                                            len(helper.read_bytes()))
                    else:
                        header+=struct.pack('<I',3)+importlib.util.source_hash(helper.read_bytes())
                    cache=Path(importlib.util.cache_from_source(str(helper)))
                    cache.parent.mkdir(exist_ok=True)
                    cache.write_bytes(header+marshal.dumps(compile(poison,str(helper),'exec')))
                    # Prove these headers really are accepted by the previous loader.
                    spec=importlib.util.spec_from_file_location('legacy_cache_control',helper)
                    legacy=importlib.util.module_from_spec(spec);spec.loader.exec_module(legacy)
                    self.assertEqual(legacy.resource_fds({}),(999,))
                    if source==clean:
                        self.assertEqual(source_module(subject).custody_fds({}),(111,))
                    else:
                        with self.assertRaises(SyntaxError):source_module(subject)


if __name__=='__main__':
    unittest.main()
