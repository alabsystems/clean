"""Inert owned-pipe subprocess tests; no Rust, SDK, authority or model claim.

The subject/helper paths are fixed relative to this maintained test file. Each
case copies their exact bytes to an ordinary temporary repository layout and
replaces only gen_s1a/the formatter with explicitly inert Python children.
"""
from contextlib import contextmanager
import hashlib
import inspect
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
EMITTER = Path('reports/crystal-lane/2026-10-01-bytev1/s1a/emit_stage.py')
FENCE = 'BUILD_SLOT_FENCE_FDS'

# Both children validate actual object identities, not merely FD numbers.
# The child writes entry before validation, so refusal-before-launch is causal.
CHILD = r'''import hashlib,json,os,pathlib,stat,sys
meta=json.loads(os.environ['S1A_INERT_METADATA'])
if meta['kind']=='pipeline':
    script=str(pathlib.Path(sys.argv[0]).resolve())
    roles={path:kind for kind,path in meta['child_scripts'].items()}
    if script not in roles:
        raise SystemExit('unexpected INERT pipeline child')
    kind=roles[script]
    meta=dict(meta,kind=kind,
        entry=str(pathlib.Path(meta['entry']).with_name('entry-'+kind+'.json')),
        observation=str(pathlib.Path(meta['observation']).with_name('observation-'+kind+'.json')))
pathlib.Path(meta['entry']).write_text(json.dumps({'entered':meta['kind']})+'\n')
def fail(message):
    print('S1a INERT transport: '+message,file=sys.stderr)
    raise SystemExit(41)
for word,expected in meta['expected_fds'].items():
    try: info=os.fstat(int(word))
    except OSError: fail('advertised descriptor not live: '+word)
    actual=[info.st_dev,info.st_ino,stat.S_IMODE(info.st_mode)]
    if actual!=expected: fail('advertised object identity differs: '+word)
for word,excluded in meta['unrelated_fds'].items():
    try: info=os.fstat(int(word))
    except OSError: continue
    if [info.st_dev,info.st_ino,stat.S_IMODE(info.st_mode)]==excluded:
        fail('unadvertised owned pipe inherited: '+word)
for key,expected in meta['environment_hashes'].items():
    value=os.environ.get(key)
    if value is None or hashlib.sha256(os.fsencode(value)).hexdigest()!=expected:
        fail('received environment changed: '+key)
text=sys.stdin.read() if meta['kind']=='formatter' else None
observation={'kind':meta['kind'],'arguments':sys.argv[1:],'cwd':os.getcwd(),
    'expected_fds':meta['expected_fds'],'environment_preserved':True,'input':text}
pathlib.Path(meta['observation']).write_text(json.dumps(observation)+'\n')
if meta['kind']=='generator':
    print(json.dumps([{'name':name,'source':'INERT-PIPE-FIXTURE '+name} for name in meta['library_names']]))
else:
    sys.stdout.write(text)
'''


def fd_book(descriptor):
    info = os.fstat(descriptor)
    return [info.st_dev, info.st_ino, stat.S_IMODE(info.st_mode)]


class S1aEmitterTransportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='s1a-inert-transport-')
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name).resolve()
        script = self.repo / EMITTER
        script.parent.mkdir(parents=True)
        shutil.copyfile(ROOT / EMITTER, script)
        helper = self.repo / 'scripts/resource_transport.py'
        helper.parent.mkdir(parents=True)
        shutil.copyfile(ROOT / 'scripts/resource_transport.py', helper)
        self.subject = types.ModuleType('_s1a_owned_pipe_subject')
        self.subject.__file__ = str(script)
        exec(compile(script.read_bytes(), str(script), 'exec', dont_inherit=True), self.subject.__dict__)
        (script.parent / 'gen_s1a.py').write_text(CHILD)
        # Keep the kernel's shebang short even when the actual interpreter
        # pathname contains spaces. This explicit owned link is never on PATH;
        # no shell can rewrite PWD or another received environment value.
        interpreter_parent = Path('/tmp/.ubd')
        interpreter_parent.mkdir(exist_ok=True)
        self.interpreter_temporary = tempfile.TemporaryDirectory(
            prefix='s1a-py-', dir=interpreter_parent)
        self.addCleanup(self.interpreter_temporary.cleanup)
        interpreter = Path(self.interpreter_temporary.name) / 'python'
        interpreter.symlink_to(Path(sys.executable).resolve(strict=True))
        self.formatter = self.repo / 'inert_formatter.py'
        self.formatter.write_text('#!' + str(interpreter) + '\n' + CHILD)
        self.formatter.chmod(0o755)

    @contextmanager
    def advertised_pipes(self, kind):
        # Validate and preserve existing real advertisements. Add only numbers
        # returned by os.pipe; create no HELD/jobs/SDK/admission values.
        incoming = self.subject.inherited_resource_fds()
        owned = os.pipe()
        unrelated = os.pipe()
        for descriptor in (*owned, *unrelated):
            os.set_inheritable(descriptor, True)
        try:
            environment = dict(os.environ)
            previous = environment.get(FENCE)
            addition = ','.join(map(str, owned))
            environment[FENCE] = previous + ',' + addition if previous is not None else addition
            expected = {str(fd): fd_book(fd) for fd in sorted(set(incoming) | set(owned))}
            excluded = {str(fd): fd_book(fd) for fd in unrelated}
            entry = self.repo / ('entry-' + kind + '.json')
            observation = self.repo / ('observation-' + kind + '.json')
            metadata = {'kind': kind, 'entry': str(entry), 'observation': str(observation),
                'expected_fds': expected, 'unrelated_fds': excluded,
                'child_scripts': {'generator': str((self.repo / EMITTER).parent / 'gen_s1a.py'),
                    'formatter': str(self.formatter)},
                'library_names': [row[0] for row in self.subject.LIBRARY],
                'environment_hashes': {key: hashlib.sha256(os.fsencode(value)).hexdigest()
                    for key, value in environment.items()}}
            # Test-only metadata is ignored by the resource helper; received
            # environment values above remain exact except the explicit pipe list.
            environment['S1A_INERT_METADATA'] = json.dumps(metadata)
            with mock.patch.dict(os.environ, environment, clear=False):
                actual = self.subject.inherited_resource_fds()
                self.assertEqual(set(actual), set(incoming) | set(owned))
                yield actual, entry, observation, environment
        finally:
            for descriptor in (*owned, *unrelated):
                os.close(descriptor)

    def invoke(self, function, *args, **kwargs):
        try:
            return function(*args, **kwargs)
        except subprocess.CalledProcessError as error:
            self.fail(f'actual INERT child exit {error.returncode}: {error.stderr}')

    def test_owned_pipes_reach_real_generator_python_child(self):
        with self.advertised_pipes('generator') as (fds, entry, observation, _):
            rows = self.invoke(self.subject.sources, pass_fds=fds)
            self.assertEqual([row[0] for row in rows], [row[0] for row in self.subject.LIBRARY])
            self.assertEqual([row[2] for row in rows], ['INERT-PIPE-FIXTURE ' + row[0] for row in self.subject.LIBRARY])
            self.assertEqual(json.loads(entry.read_text()), {'entered': 'generator'})
            actual = json.loads(observation.read_text())
            self.assertEqual(actual['arguments'], [])
            self.assertEqual(actual['cwd'], os.getcwd())
            self.assertTrue(actual['environment_preserved'])
            self.assertEqual(set(actual['expected_fds']), set(map(str, fds)))

    def test_owned_pipes_reach_real_formatter_python_child(self):
        with self.advertised_pipes('formatter') as (fds, entry, observation, _):
            text = 'INERT formatter input: λ\nsecond line\n'
            formatted = self.invoke(self.subject.formatted, text, self.repo, str(self.formatter), pass_fds=fds)
            self.assertEqual(formatted, text)
            self.assertEqual(json.loads(entry.read_text()), {'entered': 'formatter'})
            actual = json.loads(observation.read_text())
            self.assertEqual(actual['arguments'], ['--edition', '2021', '--emit', 'stdout'])
            self.assertEqual(actual['cwd'], str(self.repo))
            self.assertEqual(actual['input'], text)
            self.assertTrue(actual['environment_preserved'])

    def test_owned_pipes_reach_render_generator_child(self):
        with self.advertised_pipes('generator') as (fds, entry, observation, _):
            text = self.invoke(self.subject.render, pass_fds=fds)
            self.assertEqual(json.loads(entry.read_text()), {'entered': 'generator'})
            actual = json.loads(observation.read_text())
            self.assertEqual(actual['arguments'], [])
            self.assertEqual(set(actual['expected_fds']), set(map(str, fds)))
            self.assertTrue(actual['environment_preserved'])
            for name, _, _ in self.subject.LIBRARY:
                self.assertIn('INERT-PIPE-FIXTURE ' + name, text)

    def test_owned_pipes_reach_main_generator_and_formatter_children(self):
        target = self.repo / 'crates/clean-verify/src/spec/core_spec/eval_ir_bmem_trie.rs'
        target.parent.mkdir(parents=True)
        with self.advertised_pipes('pipeline') as (fds, _, _, _):
            self.assertEqual(self.invoke(self.invoke_main, check=False), 0)
            text = target.read_text()
            for kind in ('generator', 'formatter'):
                entry = self.repo / ('entry-' + kind + '.json')
                observation = self.repo / ('observation-' + kind + '.json')
                self.assertEqual(json.loads(entry.read_text()), {'entered': kind})
                actual = json.loads(observation.read_text())
                self.assertEqual(set(actual['expected_fds']), set(map(str, fds)))
                self.assertTrue(actual['environment_preserved'])
                if kind == 'generator':
                    self.assertEqual(actual['arguments'], [])
                    self.assertEqual(actual['cwd'], os.getcwd())
                else:
                    self.assertEqual(actual['arguments'], ['--edition', '2021', '--emit', 'stdout'])
                    self.assertEqual(actual['cwd'], str(self.repo))
                    self.assertEqual(actual['input'], text)
            for name, _, _ in self.subject.LIBRARY:
                self.assertIn('INERT-PIPE-FIXTURE ' + name, text)

    def invoke_main(self, *, check=True):
        argv = [str(self.repo / EMITTER), str(self.repo), '--trustfmt', str(self.formatter)]
        if check:
            argv.append('--check')
        with mock.patch.object(sys, 'argv', argv):
            return self.subject.main()

    def test_main_check_compares_generated_text_without_writing_target(self):
        target = self.repo / 'crates/clean-verify/src/spec/core_spec/eval_ir_bmem_trie.rs'
        target.parent.mkdir(parents=True)
        metadata_fields = ('st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns')
        with self.advertised_pipes('pipeline') as (fds, _, _, _):
            self.assertEqual(self.invoke(self.invoke_main, check=False), 0)
            rendered = target.read_text()
            for expected_status, expected_text in (
                (0, rendered),
                (1, rendered + '\nINERT stale generated output\n'),
            ):
                for kind in ('generator', 'formatter'):
                    (self.repo / ('entry-' + kind + '.json')).unlink()
                    (self.repo / ('observation-' + kind + '.json')).unlink()
                target.write_text(expected_text)
                before = target.stat()
                self.assertEqual(self.invoke(self.invoke_main, check=True), expected_status)
                self.assertEqual(target.read_text(), expected_text)
                after = target.stat()
                for field in metadata_fields:
                    self.assertEqual(getattr(after, field), getattr(before, field),
                        'target metadata changed: ' + field)
                for kind in ('generator', 'formatter'):
                    entry = self.repo / ('entry-' + kind + '.json')
                    observation = self.repo / ('observation-' + kind + '.json')
                    self.assertEqual(json.loads(entry.read_text()), {'entered': kind})
                    actual = json.loads(observation.read_text())
                    self.assertEqual(set(actual['expected_fds']), set(map(str, fds)))
                    self.assertTrue(actual['environment_preserved'])

    def assert_no_child_entered(self):
        self.assertEqual(list(self.repo.glob('entry-*.json')), [])

    def test_fifo_helper_refuses_without_waiting_for_writer(self):
        fds = self.subject.inherited_resource_fds()
        helper = self.repo / 'scripts/resource_transport.py'
        helper.unlink()
        os.mkfifo(helper, 0o600)
        code = """import errno,os,runpy,sys
subject=runpy.run_path(sys.argv[1],run_name='_s1a_inert_fifo_subject')
opened=[]
real_open=os.open
def record_open(*args,**kwargs):
    descriptor=real_open(*args,**kwargs)
    opened.append(descriptor)
    return descriptor
os.open=record_open
try:
    subject['inherited_resource_fds']()
except RuntimeError:
    for descriptor in opened:
        try:
            os.fstat(descriptor)
        except OSError as error:
            if error.errno!=errno.EBADF:
                raise
        else:
            raise RuntimeError('S1a refused helper leaked its descriptor')
    print('S1A_FIFO_CLOSED_FDS='+str(len(opened)),flush=True)
    raise
"""
        argv = [sys.executable, *(['-O'] if sys.flags.optimize else []),
                '-c', code, str(self.repo / EMITTER)]
        try:
            child = subprocess.run(argv, cwd=self.repo, env=dict(os.environ),
                pass_fds=fds, capture_output=True, text=True, timeout=5)
        except subprocess.TimeoutExpired:
            self.fail('S1a FIFO helper blocked waiting for a writer instead of refusing')
        self.assertEqual(child.returncode, 1, child.stderr)
        self.assertRegex(child.stdout, r'^S1A_FIFO_CLOSED_FDS=[0-9]+\n$')
        self.assertEqual(child.stderr.splitlines()[-1],
            'RuntimeError: S1a transport helper must be an ordinary file')

    def test_malformed_advertisement_refuses_before_both_children(self):
        with self.advertised_pipes('generator') as (_, _, _, _environment):
            malformed = os.environ[FENCE] + ',not-a-descriptor'
            with mock.patch.dict(os.environ, {FENCE: malformed}, clear=False):
                with self.assertRaisesRegex(RuntimeError, 'row custody: malformed BUILD_SLOT_FENCE_FDS descriptor'):
                    self.invoke_main()
            self.assert_no_child_entered()

    def test_closed_owned_descriptor_refuses_before_both_children(self):
        with self.advertised_pipes('generator') as (_, _, _, _environment):
            closed, other = os.pipe()
            os.close(closed)
            os.close(other)
            with self.assertRaises(OSError):
                os.fstat(closed)
            with mock.patch.dict(os.environ, {FENCE: os.environ[FENCE] + ',' + str(closed)}, clear=False):
                with self.assertRaisesRegex(RuntimeError, 'row custody: BUILD_SLOT_FENCE_FDS descriptor is not live'):
                    self.invoke_main()
            self.assert_no_child_entered()

    def test_helper_alias_refuses_before_both_children(self):
        helper = self.repo / 'scripts/resource_transport.py'
        saved = helper.with_suffix('.source')
        helper.rename(saved)
        helper.symlink_to(saved.name)
        with self.assertRaisesRegex(RuntimeError, 'S1a transport helper must be an unaliased repository file'):
            self.invoke_main()
        self.assert_no_child_entered()

    def test_internal_calls_require_explicit_validated_descriptor_argument(self):
        for name in ('sources', 'render', 'formatted'):
            parameter = inspect.signature(getattr(self.subject, name)).parameters['pass_fds']
            self.assertEqual(parameter.kind, inspect.Parameter.KEYWORD_ONLY)
            self.assertEqual(parameter.default, inspect.Parameter.empty)
        self.assert_no_child_entered()


if __name__ == '__main__':
    unittest.main()
