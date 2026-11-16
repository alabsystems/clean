#!/usr/bin/env python3
"""Harmless Python/pipe transport controls, never native resource authority."""
from pathlib import Path
import contextlib
import importlib.util
import io
import json
import marshal
import os
import py_compile
import shlex
import stat
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/check_ck0_lineage.py'
SYNTHETIC_FIELD = 'ATERM_WORKLOAD_HOST_CONTROL_FDS_V1'
GIT_LOCAL = {
    'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_CONFIG', 'GIT_CONFIG_PARAMETERS',
    'GIT_CONFIG_COUNT', 'GIT_OBJECT_DIRECTORY', 'GIT_DIR', 'GIT_WORK_TREE',
    'GIT_IMPLICIT_WORK_TREE', 'GIT_GRAFT_FILE', 'GIT_INDEX_FILE',
    'GIT_NO_REPLACE_OBJECTS', 'GIT_REPLACE_REF_BASE', 'GIT_PREFIX',
    'GIT_SHALLOW_FILE', 'GIT_COMMON_DIR', 'GIT_NAMESPACE',
}
GIT_POLICY = {'GIT_NO_REPLACE_OBJECTS': '1', 'GIT_NO_LAZY_FETCH': '1',
              'GIT_TERMINAL_PROMPT': '0'}
PROBE = '''import json,os
def live(fd):
 try: os.fstat(fd); return True
 except OSError: return False
fd=int(os.environ['Q6_SYNTHETIC_PIPE_FD'])
ok=live(fd)
print(json.dumps({'pipe_live':ok,'byte':os.read(fd,1).hex() if ok else None,
 'unrelated_live':live(int(os.environ.get('Q6_UNRELATED_PIPE_FD','-1'))),
 'git_names':sorted(k for k in os.environ if k.startswith('GIT_')),
 'git_policy':{k:os.environ.get(k) for k in
 ('GIT_NO_REPLACE_OBJECTS','GIT_NO_LAZY_FETCH','GIT_TERMINAL_PROMPT')}}))
'''


def subject(root=None):
    script = SCRIPT if root is None else Path(root) / 'scripts/check_ck0_lineage.py'
    module = types.ModuleType('q6_transport_subject')
    module.__file__ = str(script)
    exec(compile(script.read_bytes(), str(script), 'exec', dont_inherit=True), module.__dict__)
    return module


@contextlib.contextmanager
def pipes():
    read_fd, write_fd = os.pipe()
    unused_read, unused_write = os.pipe()
    try:
        os.write(write_fd, b'Q')
        env = dict(os.environ)
        # Append only our synthetic locators, retaining any genuine advertised
        # descriptors and all other caller fields. No owner authenticates this
        # harmless child, so no CPU/SDK/jobserver authority is asserted.
        old = env.get(SYNTHETIC_FIELD)
        env[SYNTHETIC_FIELD] = (old + ',' if old else '') + f'{read_fd},{write_fd}'
        env['Q6_SYNTHETIC_PIPE_FD'] = str(read_fd)
        env['Q6_UNRELATED_PIPE_FD'] = str(unused_read)
        yield env, read_fd, write_fd
    finally:
        for descriptor in (read_fd, write_fd, unused_read, unused_write):
            os.close(descriptor)


class CommandTransport(unittest.TestCase):
    def test_advertised_pipe_is_forwarded(self):
        module = subject()
        with pipes() as (env, _read, _write):
            observed = json.loads(module.command([sys.executable, '-c', PROBE], env=env))
        self.assertTrue(observed['pipe_live'], 'advertised synthetic pipe was closed in command() child')
        self.assertEqual(observed['byte'], '51')
        self.assertFalse(observed['unrelated_live'])

    def test_default_environment_forwards_advertised_pipe(self):
        module = subject()
        with pipes() as (env, _read, _write), patch.dict(os.environ, env):
            observed = json.loads(module.command([sys.executable, '-c', PROBE]))
        self.assertTrue(observed['pipe_live'])
        self.assertEqual(observed['byte'], '51')

    def test_normalized_git_environment_reaches_child_without_fd_loss(self):
        module = subject()
        poison = {name: '/synthetic/foreign/repository' for name in GIT_LOCAL}
        poison.update(GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='core.worktree',
                      GIT_CONFIG_VALUE_0='/synthetic/foreign/worktree')
        with pipes() as (env, _read, _write), patch.dict(os.environ, {**env, **poison}):
            normalized = module._production_env()
            observed = json.loads(module.command([sys.executable, '-c', PROBE], env=normalized))
        self.assertTrue(observed['pipe_live'])
        self.assertEqual(observed['git_policy'], GIT_POLICY)
        self.assertFalse((set(observed['git_names']) & GIT_LOCAL) - {'GIT_NO_REPLACE_OBJECTS'})
        self.assertFalse(any(name.startswith(('GIT_CONFIG_KEY_', 'GIT_CONFIG_VALUE_'))
                             for name in observed['git_names']))

    def test_malformed_locator_refuses_before_child_marker(self):
        module = subject()
        with tempfile.TemporaryDirectory(prefix='q6-bad-transport-') as tmp:
            marker = Path(tmp) / 'child-started'
            env = dict(os.environ)
            old = env.get(SYNTHETIC_FIELD)
            env[SYNTHETIC_FIELD] = (old + ',' if old else '') + 'not-a-descriptor'
            with self.assertRaises((ValueError, RuntimeError)):
                module.command([sys.executable, '-c',
                                'from pathlib import Path;Path(' + repr(str(marker)) + ').touch()'], env=env)
            self.assertFalse(marker.exists())

    def test_closed_locator_refuses_before_child_marker(self):
        module = subject()
        read_fd, write_fd = os.pipe()
        os.close(read_fd)
        try:
            with tempfile.TemporaryDirectory(prefix='q6-closed-transport-') as tmp:
                marker = Path(tmp) / 'child-started'
                env = dict(os.environ)
                old = env.get(SYNTHETIC_FIELD)
                env[SYNTHETIC_FIELD] = (old + ',' if old else '') + str(read_fd)
                with self.assertRaises((ValueError, RuntimeError)):
                    module.command([sys.executable, '-c',
                                    'from pathlib import Path;Path(' + repr(str(marker)) + ').touch()'], env=env)
                self.assertFalse(marker.exists())
        finally:
            os.close(write_fd)

    def test_nonzero_python_child_status_is_preserved(self):
        module = subject()
        with self.assertRaises(subprocess.CalledProcessError) as error:
            module.command([sys.executable, '-c', 'raise SystemExit(86)'])
        self.assertEqual(error.exception.returncode, 86)


class HelperSourceTransport(unittest.TestCase):
    def helper_fixture(self, root):
        helper = root / 'scripts/resource_transport.py'
        helper.parent.mkdir(parents=True)
        helper.write_bytes((ROOT / 'scripts/resource_transport.py').read_bytes())
        return helper

    def test_matching_python_bytecache_cannot_replace_resource_source(self):
        module = subject()
        with tempfile.TemporaryDirectory(prefix='q6-source-transport-') as temporary:
            temporary = Path(temporary)
            helper = self.helper_fixture(temporary)
            cache = Path(py_compile.compile(str(helper), doraise=True))
            header = cache.read_bytes()[:16]  # Valid header for the unchanged real source.
            payload = compile("def resource_fds(env):\n raise RuntimeError('poisoned bytecache reached')\n",
                              str(helper), 'exec', dont_inherit=True)
            cache.write_bytes(header + marshal.dumps(payload))
            spec = importlib.util.spec_from_file_location('legacy_cached_resource_control', helper)
            legacy = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(legacy)
            with self.assertRaisesRegex(RuntimeError, 'poisoned bytecache reached'):
                legacy.resource_fds(dict(os.environ))
            module.ROOT = temporary
            with pipes() as (env, _read, _write):
                observed = json.loads(module.command([sys.executable, '-c', PROBE], env=env))
            self.assertTrue(observed['pipe_live'])
            self.assertEqual(observed['byte'], '51')

    def test_changed_helper_source_is_read_before_next_child(self):
        module = subject()
        with tempfile.TemporaryDirectory(prefix='q6-fresh-transport-') as temporary:
            temporary = Path(temporary)
            helper = self.helper_fixture(temporary)
            module.ROOT = temporary
            with pipes() as (env, _read, _write):
                observed = json.loads(module.command([sys.executable, '-c', PROBE], env=env))
                self.assertTrue(observed['pipe_live'])
                helper.write_text("raise RuntimeError('changed resource source reached')\n")
                marker = temporary / 'second-child-started'
                with self.assertRaisesRegex(ValueError, 'changed resource source reached'):
                    module.command([sys.executable, '-c',
                                    'from pathlib import Path;Path(' + repr(str(marker)) + ').touch()'], env=env)
                self.assertFalse(marker.exists())


class CompileStepTransport(unittest.TestCase):
    def committed_source(self, root):
        """Real private Git inputs; caller checkout dirtiness is irrelevant."""
        root.mkdir()
        template = subject()
        for name in {*template.PRODUCER_FILES, template.RESOURCE_HELPER}:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
        files = {
            'Cargo.toml': b'[workspace]\nmembers = ["crates/clean-ck0"]\nresolver = "2"\n',
            'Cargo.lock': b'# Uncompiled transport fixture; no dependency resolution claimed.\n',
            'rust-toolchain.toml': b'[toolchain]\nchannel = "trust"\n',
            '.cargo/config.toml': b'[build]\n',
            'reports/self-proof-q2-2026-11-12/seed.ndjson': b'{"uncompiled_fixture": true}\n',
            'crates/clean-kernel/src/level/fixtures/lean_kernel_verdicts_v4.30.0-rc2.tsv': b'# Uncompiled transport fixture\n',
            template.CRATE + '/Cargo.toml': b'[package]\nname = "clean-ck0"\nversion = "0.0.0"\nedition = "2021"\n',
            template.CRATE + '/src/lib.rs': b'// Uncompiled transport fixture: no Rust is run.\n',
        }
        for name, data in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        module = subject(root)
        env = module._production_env()
        descriptors = module._resource_fds(env)
        hooks = root / 'empty-fixture-hooks'
        hooks.mkdir()
        for args in (
            ['init', '-q', '-b', 'main'], ['add', '-A'],
            ['-c', 'user.name=Transport fixture', '-c', 'user.email=transport@example.invalid',
             '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=' + str(hooks),
             'commit', '-qm', 'private uncompiled transport fixture'],
        ):
            subprocess.run(['git', '-C', str(root), '-c', 'core.fsmonitor=false', *args],
                           env=env, pass_fds=descriptors, check=True, capture_output=True)
        source = module.source_record(root)
        self.assertEqual(set(source['files']), {*module.BASE,
                         module.CRATE + '/Cargo.toml', module.CRATE + '/src/lib.rs'})
        module.checked_source(root, source)
        return module, source

    def test_harmless_step_forwards_pipe_and_git_context_then_refuses86(self):
        """Actual producer control flow; fake metadata/tools, never a cohort.

        Private committed source, real helper bytes, hashes and snapshots are
        checked normally; no clean/committed caller checkout is required.
        A Python driver supplies explicitly synthetic metadata and exits86 at
        the first test step. No cargo/rustc/Lean executable is invoked.
        """
        with tempfile.TemporaryDirectory(prefix='q6-harmless-step-') as temporary, pipes() as (env, _read, _write):
            temporary = Path(temporary)
            source_root = temporary / 'committed-source'
            module, source = self.committed_source(source_root)
            sysroot = temporary / 'synthetic-sysroot'
            (sysroot / 'lib').mkdir(parents=True)
            (sysroot / 'lib/fixture').write_text('Not a Rust library; synthetic transport input.\n')
            observations = temporary / 'observations.jsonl'
            marker = temporary / 'step-started'
            manifest = source_root / module.CRATE / 'Cargo.toml'
            package = 'path+file://' + str(manifest.parent) + '#q6-synthetic-transport'
            metadata = {'packages': [{'id': package, 'name': 'clean-ck0', 'version': '0.0.0',
                          'manifest_path': str(manifest), 'source': None,
                          'targets': [{'name': 'synthetic_transport', 'kind': ['lib']}]}],
                        'resolve': {'nodes': [{'id': package, 'dependencies': [], 'features': []}]}}
            observe = '''import json,os,sys
from pathlib import Path
def live(fd):
 try: os.fstat(fd); return True
 except OSError: return False
observation={'argv':sys.argv[1:],'pipe_live':live(int(os.environ['Q6_SYNTHETIC_PIPE_FD'])),
 'git_names':sorted(k for k in os.environ if k.startswith('GIT_')),
 'git_policy':{k:os.environ.get(k) for k in
 ('GIT_NO_REPLACE_OBJECTS','GIT_NO_LAZY_FETCH','GIT_TERMINAL_PROMPT')}}
with Path(os.environ['Q6_SYNTHETIC_OBSERVATIONS']).open('a') as output:
 output.write(json.dumps(observation)+'\\n')
'''
            compiler_code = observe + "\nif sys.argv[1:]==['-Vv']: print('Q6 synthetic Python compiler descriptor; NO RUST')\nelif sys.argv[1:]==['--print','sysroot']: print(" + repr(str(sysroot)) + ")\nelse: raise SystemExit(90)\n"
            driver_code = observe + "\nif sys.argv[1:2]==['metadata']: print(" + repr(json.dumps(metadata)) + ")\nelse:\n Path(" + repr(str(marker)) + ").touch()\n print(json.dumps(observation))\n raise SystemExit(86)\n"
            driver, compiler = temporary / 'python-fixture-driver', temporary / 'python-fixture-compiler'
            for path, code in ((driver, driver_code), (compiler, compiler_code)):
                path.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' -c ' + shlex.quote(code) + ' "$@"\n')
                path.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR)
            env['Q6_SYNTHETIC_OBSERVATIONS'] = str(observations)
            poison = {name: '/synthetic/foreign/repository' for name in GIT_LOCAL}
            poison.update(GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='core.worktree',
                          GIT_CONFIG_VALUE_0='/synthetic/foreign/worktree')
            output = temporary / 'partial-unqualified-run'
            with patch.dict(os.environ, {**env, **poison}), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError, 'trust/default exited 86'):
                    module.compile_record(driver, compiler, 'trust', output, source)
            self.assertTrue(marker.exists())
            record = json.loads((output / 'run.json').read_bytes())
            self.assertEqual([(step['name'], step['exit_code']) for step in record['steps']], [('default', 86)])
            self.assertNotIn('finished_at', record)
            self.assertIs(record['proof_claim'], False)
            self.assertEqual(set(record['input_snapshots']), {'before', 'after-default'})
            events = [json.loads(line) for line in observations.read_text().splitlines()]
            self.assertGreaterEqual(len(events), 5)
            self.assertTrue(any('test' in event['argv'] for event in events))
            for event in events:
                self.assertTrue(event['pipe_live'], 'synthetic descriptor lost at ' + repr(event['argv']))
                self.assertEqual(event['git_policy'], GIT_POLICY)
                self.assertFalse((set(event['git_names']) & GIT_LOCAL) - {'GIT_NO_REPLACE_OBJECTS'})
                self.assertFalse(any(name.startswith(('GIT_CONFIG_KEY_', 'GIT_CONFIG_VALUE_'))
                                     for name in event['git_names']))

    def test_dirty_private_source_refuses_before_child(self):
        with tempfile.TemporaryDirectory(prefix='q6-dirty-inner-source-') as temporary:
            temporary = Path(temporary)
            source_root = temporary / 'committed-source'
            module, source = self.committed_source(source_root)
            helper = source_root / module.RESOURCE_HELPER
            helper.write_bytes(helper.read_bytes() + b'\n# Deliberately dirty private input.\n')
            with self.assertRaisesRegex(ValueError, 'input differs from committed source'):
                module.source_record(source_root)
            marker = temporary / 'forbidden-child-started'
            child = temporary / 'harmless-python-child'
            code = 'from pathlib import Path;Path(' + repr(str(marker)) + ').touch()'
            child.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) +
                             ' -c ' + shlex.quote(code) + ' "$@"\n')
            child.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR)
            output = temporary / 'must-not-be-created'
            with self.assertRaisesRegex(ValueError, 'input digest changed'):
                module.compile_record(child, child, 'trust', output, source)
            self.assertFalse(marker.exists())
            self.assertFalse(output.exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
