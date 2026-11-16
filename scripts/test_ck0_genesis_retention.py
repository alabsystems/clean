#!/usr/bin/env python3
"""Real selftest retention under an injected census failure and actual SIGINT.

The failure injection never substitutes a native process reply or grants
authority. Only authenticated scratch directories created by the child are
removed after it is terminal. No Rust compiler or recorded image executes.
"""
import hashlib
import json
import os
from pathlib import Path
import secrets
import shutil
import stat
import subprocess
import sys
import tempfile
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
SUBJECT = ROOT / 'scripts/check_ck0_genesis_history.py'
HELPER = ROOT / 'scripts/resource_transport.py'
COOKIE = '.q6-retention-test-owner'
FALSE_SUCCESS = b'#!/bin/sh\nexit 0\n'

BOOTSTRAP = r'''
import ast,errno,hashlib,json,os,signal,subprocess,sys,types
from pathlib import Path
subject,receipt=map(Path,sys.argv[1:3]);nonce=sys.argv[3]
data=subject.read_bytes();module=types.ModuleType('actual_genesis_retention_subject')
module.__file__=str(subject)
exec(compile(data,str(subject),'exec',dont_inherit=True),module.__dict__)
record={'source_sha256':hashlib.sha256(data).hexdigest(),'scratches':[],
        'processes':[],'real_censuses_before_injected_failure':[],
        'signal_injected':False,'caught_KeyboardInterrupt':False,
        'nonce_sha256':hashlib.sha256(nonce.encode()).hexdigest(),
        'Rust_execution':False,'proof_claim':False}
def save():receipt.write_text(json.dumps(record,sort_keys=True,indent=2)+'\n')
real_enter=module.FixtureScratch.__enter__
def enter(instance):
 path=Path(real_enter(instance));info=path.lstat()
 (path/'.q6-retention-test-owner').write_text(nonce)
 record['scratches'].append({'path':str(path),'device':info.st_dev,'inode':info.st_ino})
 save();return str(path)
module.FixtureScratch.__enter__=enter
real_cleanup=module._cleanup_fixture
def cleanup(process,*args,**kwargs):
 row={'argv':process.args,'pid':process.pid,'forwarded_unchanged':True}
 record['processes'].append(row)
 try:return real_cleanup(process,*args,**kwargs)
 finally:
  row['returncode_after_selftest']=process.returncode;save()
module._cleanup_fixture=cleanup
check_roots=[];real_check=module.check
def check(*args,**kwargs):
 check_roots.append(str(args[0] if args else kwargs.get('root',module.ROOT)))
 try:return real_check(*args,**kwargs)
 finally:check_roots.pop()
module.check=check
active=[];real_run=module._run_fixture
def run(*args,**kwargs):
 argv=args[0] if args else kwargs['argv']
 selected=Path(argv[0]).read_bytes()==b'#!/bin/sh\nexit 0\n'
 active.append(selected)
 if selected:
  record['selected_inner']=str(args[4] if args else kwargs['directory'])
  record['selected_candidate']=check_roots[-1]
  record['selected_argv']=argv;save()
 try:return real_run(*args,**kwargs)
 finally:active.pop()
module._run_fixture=run
real_group=module._group_states
def group(*args,**kwargs):
 answer=real_group(*args,**kwargs)
 if active and active[-1]:
  record['real_censuses_before_injected_failure'].append(answer)
  record['uncertainty_injected']=True;save()
  raise OSError(errno.EIO,'owned retention test: census unavailable after real read')
 return answer
module._group_states=group
definition=next(node for node in ast.parse(data).body
                if isinstance(node,ast.FunctionDef) and node.name=='_run_fixture')
elapsed_lines=[node.lineno for node in ast.walk(definition)
 if isinstance(node,ast.Assign) and any(isinstance(target,ast.Subscript)
 and isinstance(target.value,ast.Name) and target.value.id=='details'
 and isinstance(target.slice,ast.Constant) and target.slice.value=='elapsed_seconds'
 for target in node.targets)]
if len(elapsed_lines)!=1:raise RuntimeError('retention hook requires one actual elapsed assignment')
original_trace=sys.gettrace();original_sigint=signal.getsignal(signal.SIGINT)
def trace(frame,event,arg):
 if frame.f_code is not real_run.__code__:return None
 if (event=='line' and active and active[-1] and record.get('uncertainty_injected')
     and not record['signal_injected'] and frame.f_lineno==elapsed_lines[0]):
  record['signal_handler_restored']=signal.getsignal(signal.SIGINT)==original_sigint
  if not record['signal_handler_restored']:
   raise RuntimeError('retention hook did not reach the restored SIGINT handler')
  record['signal_injected']=True;save()
  os.kill(os.getpid(),signal.SIGINT)
 return trace
sys.settrace(trace)
save()
try:
 module.selftest()
except KeyboardInterrupt:
 record['caught_KeyboardInterrupt']=True
except BaseException as error:
 record['unexpected_error']={'type':type(error).__name__,'message':str(error)}
finally:
 sys.settrace(original_trace)
 for row in record['scratches']:row['exists_after_interruption']=Path(row['path']).is_dir()
 if record.get('selected_candidate'):
  candidate=Path(record['selected_candidate'])/'genesis/ck0/generate_manifest.sh'
  record['candidate_exists']=candidate.is_file()
  record['candidate_hex']=candidate.read_bytes().hex() if candidate.is_file() else None
 record['source_sha256_after']=hashlib.sha256(subject.read_bytes()).hexdigest()
 save()
print(json.dumps(record,sort_keys=True),flush=True)
'''


def source_transport():
    module = types.ModuleType('retention_test_resource_transport')
    module.__file__ = str(HELPER)
    exec(compile(HELPER.read_bytes(), str(HELPER), 'exec', dont_inherit=True), module.__dict__)
    return module


class GenesisRetention(unittest.TestCase):
    def test_sigint_after_uncertainty_retains_nested_scratch_and_mutant(self):
        with tempfile.TemporaryDirectory(prefix='q6-retention-receipt-') as temporary:
            receipt = Path(temporary) / 'actual.json'
            nonce = secrets.token_hex(24)
            record = None
            cleanup = []
            retained_unknown = []
            argv = [sys.executable, '-B', '-c', BOOTSTRAP, str(SUBJECT), str(receipt), nonce]
            child = subprocess.Popen(argv, env=os.environ.copy(), cwd=ROOT,
                pass_fds=source_transport().resource_fds(os.environ),
                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                try:
                    stdout, stderr = child.communicate(timeout=60)
                except BaseException:
                    child.kill()
                    child.communicate()
                    raise
                record = json.loads(receipt.read_bytes())
                print(json.dumps({'actual_child_receipt': record,
                    'child_direct_exit': child.returncode, 'child_stdout_hex': stdout.hex(),
                    'child_stderr_hex': stderr.hex()}, sort_keys=True), flush=True)
                self.assertEqual(child.returncode, 0, stderr)
                self.assertNotIn('unexpected_error', record)
                self.assertTrue(record['real_censuses_before_injected_failure'])
                self.assertIs(record['signal_injected'], True)
                self.assertIs(record['signal_handler_restored'], True)
                self.assertIs(record['caught_KeyboardInterrupt'], True)
                self.assertEqual(record['source_sha256'], record['source_sha256_after'])
                self.assertTrue(all(type(row['returncode_after_selftest']) is int
                                    for row in record['processes']), 'real child not reaped')
                self.assertEqual([row['returncode_after_selftest'] for row in record['processes']],
                                 [1] * 24 + [0], 'did not reach the real first false-success mutant')
                retained = {row['path']: row['exists_after_interruption'] for row in record['scratches']}
                expected = [record['selected_inner'], str(Path(record['selected_candidate']).parent)]
                self.assertTrue(all(retained.get(path) is True for path in expected),
                                'uncertain nested scratch deleted after actual SIGINT: ' + json.dumps(retained))
                self.assertTrue(record['candidate_exists'])
                self.assertEqual(record['candidate_hex'], FALSE_SUCCESS.hex(),
                                 'uncertain selftest restored the candidate after actual SIGINT')
            finally:
                # The bootstrap is terminal. Delete only paths it actually
                # created, with matching inode/device and private ownership
                # cookie; never signal or sweep another process or directory.
                if receipt.exists():
                    record = json.loads(receipt.read_bytes())
                    writers_terminal = child.returncode is not None and all(
                        type(row.get('returncode_after_selftest')) is int
                        for row in record['processes'])
                    for row in reversed(record['scratches']):
                        path = Path(row['path'])
                        if not path.exists():
                            continue
                        if not writers_terminal:
                            retained_unknown.append(str(path))
                            continue
                        info = path.lstat()
                        self.assertTrue(stat.S_ISDIR(info.st_mode) and not path.is_symlink())
                        self.assertEqual((info.st_dev, info.st_ino), (row['device'], row['inode']))
                        self.assertEqual(path.parent.resolve(), (Path(tempfile.gettempdir()) / '.ubd').resolve())
                        self.assertTrue(path.name.startswith('q6-genesis-history-'))
                        self.assertEqual((path / COOKIE).read_text(), nonce)
                        shutil.rmtree(path)
                        cleanup.append(str(path))
                print(json.dumps({'authenticated_scratch_removed_after_child_terminal': cleanup,
                                  'scratch_retained_writer_status_unknown': retained_unknown,
                                  'child_terminal': child.returncode is not None,
                                  'other_process_signals': False}, sort_keys=True), flush=True)


if __name__ == '__main__':
    program = unittest.main(exit=False, verbosity=2)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
