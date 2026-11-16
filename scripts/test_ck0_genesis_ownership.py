#!/usr/bin/env python3
"""Real owned-child reap/ECHILD control; unsafe product signals are blocked.

No process outcome or Popen status is fabricated. The private Python emitter
does not fork, and no Rust compiler, native proof tool or resource grant runs.
"""
import errno
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
CHECKER = 'scripts/check_ck0_genesis_history.py'
HELPER = 'scripts/resource_transport.py'
INPUTS = (CHECKER, 'genesis/ck0/MANIFEST.txt', 'genesis/ck0/generate_manifest.sh',
          'genesis/ck0/verify.sh', HELPER)
COOKIE = '.q6-ownership-test-owner'
EMITTER = '''import os
remaining=memoryview(b'Q6 REFUSED: retired ownership fixture\\n')
while remaining:
 written=os.write(2,remaining)
 if written<=0:raise RuntimeError('private emitter made no progress')
 remaining=remaining[written:]
raise SystemExit(1)
'''

BOOTSTRAP = r'''
import errno,hashlib,json,os,signal,sys,types,threading
from pathlib import Path
subject,receipt=map(Path,sys.argv[1:3]);nonce=sys.argv[3];mode=sys.argv[4]
if mode not in ('lost-wait','completed-owner','sigchld-policy','extra-thread-policy'):raise ValueError('unknown ownership control')
data=subject.read_bytes();module=types.ModuleType('actual_genesis_ownership_subject')
module.__file__=str(subject)
exec(compile(data,str(subject),'exec',dont_inherit=True),module.__dict__)
record={'source_sha256':hashlib.sha256(data).hexdigest(),'mode':mode,'scopes':[],
        'blocked_calls':[],'real_wait':None,'echild':None,'cleanup_observation':None,
        'saved_real_group_signals':[],'Rust_execution':False,'proof_claim':False}
def save():receipt.write_text(json.dumps(record,sort_keys=True,indent=2)+'\n')
worker_ready=threading.Event();worker_stop=threading.Event()
def parked_worker():worker_ready.set();worker_stop.wait()
worker=threading.Thread(target=parked_worker,name='owned-nonreaping-policy-control') if mode=='extra-thread-policy' else None
record['initial_thread_count']=threading.active_count()
record['checker_is_main_thread']=threading.current_thread() is threading.main_thread()
record['worker_started']=False
saved_sigchld=signal.getsignal(signal.SIGCHLD);saved_waitpid=os.waitpid
record['sigchld_initial_default']=saved_sigchld==signal.SIG_DFL
record['sigchld_callbacks']=0
def nonreaping_sigchld(_signum,_frame):record['sigchld_callbacks']+=1
if mode=='sigchld-policy':signal.signal(signal.SIGCHLD,nonreaping_sigchld)
record['sigchld_active_default']=signal.getsignal(signal.SIGCHLD)==signal.SIG_DFL
real_enter=module.FixtureScratch.__enter__
def enter(scope):
 path=Path(real_enter(scope));info=path.lstat()
 (path/'.q6-ownership-test-owner').write_text(nonce)
 record['scopes'].append({'path':str(path),'device':info.st_dev,'inode':info.st_ino})
 save();return str(path)
module.FixtureScratch.__enter__=enter
saved_killpg=os.killpg
def tripwire(pid,signum):
 record['blocked_calls'].append({'pid':pid,'signal':signum,'forwarded':False});save()
 raise OSError(errno.EIO,'ownership test blocked a product group signal')
os.killpg=tripwire
real_observer=module._observe_exit;reaped=False;identity_lost=False;wait_started=False
def remember_echild(error,source):
 global identity_lost
 if error.errno==errno.ECHILD:
  identity_lost=True
  record['echild']={'errno':error.errno,'type':type(error).__name__,'source':source}
  save()
def observe(pid):
 global reaped,wait_started
 try:observed=real_observer(pid)
 except OSError as error:
  remember_echild(error,'real-observer');raise
 if not observed or reaped:return observed
 wait_started=True
 waited,status=os.waitpid(pid,0)
 if waited!=pid:raise RuntimeError('exact created child wait returned another identity')
 reaped=True
 record['real_wait']={'pid':waited,'status':status,'exit_code':os.waitstatus_to_exitcode(status)}
 save()
 try:
  returned=real_observer(pid)
 except OSError as error:
  remember_echild(error,'real-observer');raise
 record['observer_returned_after_reap']=returned;save()
 # A kqueue ESRCH can return rather than raise. This additional actual failed
 # wait establishes ECHILD without inventing an exception or a process status.
 try:os.waitpid(pid,os.WNOHANG)
 except OSError as error:
  remember_echild(error,'real-waitpid-after-observer-return');raise
 raise RuntimeError('actual post-reap wait unexpectedly returned')
if mode=='lost-wait':module._observe_exit=observe
def tracked_waitpid(pid,options):
 global wait_started,reaped
 wait_started=True
 waited,status=saved_waitpid(pid,options)
 if waited>0:
  reaped=True
  record['real_wait']={'pid':waited,'status':status,'exit_code':os.waitstatus_to_exitcode(status),
                       'source':'actual-product-os.waitpid'}
  save()
  try:real_observer(waited)
  except OSError as error:
   remember_echild(error,'real-observer')
   if error.errno!=errno.ECHILD:raise
  else:
   try:saved_waitpid(waited,os.WNOHANG)
   except OSError as error:
    remember_echild(error,'real-waitpid-after-observer-return')
    if error.errno!=errno.ECHILD:raise
 return waited,status
if mode in ('sigchld-policy','extra-thread-policy'):os.waitpid=tracked_waitpid
def completed_wait(process):
 global reaped,wait_started
 wait_started=True
 exit_code=process.wait(timeout=2)
 reaped=True
 record['real_wait']={'pid':process.pid,'exit_code':exit_code,'source':'actual-Popen.wait'}
 save()
 try:real_observer(process.pid)
 except OSError as error:
  remember_echild(error,'real-observer');return
 # kqueue can return ESRCH rather than raise. Require an actual failed wait.
 try:os.waitpid(process.pid,os.WNOHANG)
 except OSError as error:
  remember_echild(error,'real-waitpid-after-observer-return');return
 raise RuntimeError('completed Popen unexpectedly remained waitable')
real_cleanup=module._cleanup_fixture;owned=[]
def cleanup(process,*args,**kwargs):
 owned.append(process)
 identity=args[4] if len(args)>4 else kwargs['identity_held']
 row={'pid':process.pid,'argv':process.args,'identity_held':identity,
      'returncode_at_cleanup_entry':process.returncode,
      'thread_count_at_cleanup':threading.active_count()}
 record['cleanup_observation']=row
 if mode=='completed-owner':completed_wait(process)
 row['returncode_before']=process.returncode
 try:return real_cleanup(process,*args,**kwargs)
 finally:
  row['returncode_after']=process.returncode
  row['thread_count_after_cleanup']=threading.active_count();save()
module._cleanup_fixture=cleanup
save()
try:
 if worker is not None:
  worker.start();record['worker_started']=True
  if not worker_ready.wait(2):raise RuntimeError('owned Event worker did not become ready')
 record['thread_count_before_check']=threading.active_count()
 record['worker_alive_before_check']=worker is not None and worker.is_alive()
 save()
 module.check()
 record['check_returned']=True
except module.FixtureExecutionRefused as error:
 record['refusal']={'type':type(error).__name__,'details':error.details}
except BaseException as error:
 record['unexpected_error']={'type':type(error).__name__,'message':str(error)}
finally:
 if worker is not None and worker.ident is not None:
  worker_stop.set();worker.join(timeout=2)
 record['worker_joined']=worker is None or not worker.is_alive()
 record['thread_count_after_join']=threading.active_count()
 os.waitpid=saved_waitpid
 signal.signal(signal.SIGCHLD,saved_sigchld)
 record['sigchld_restored']=signal.getsignal(signal.SIGCHLD)==saved_sigchld
 os.killpg=saved_killpg
 # Only an unreaped child whose identity is still held may receive a saved
 # real signal. No signal is legal after this control's actual wait/ECHILD.
 for process in owned:
  if not wait_started and not reaped and not identity_lost and process.returncode is None:
   try:
    module._owner_policy()
    real_observer(process.pid)
    saved_killpg(process.pid,signal.SIGKILL)
    record['saved_real_group_signals'].append(process.pid)
    waited,status=os.waitpid(process.pid,0)
    record['emergency_real_wait']={'pid':waited,'status':status,
                                  'exit_code':os.waitstatus_to_exitcode(status)}
   except OSError as error:
    record['emergency_cleanup_error']={'errno':error.errno,'type':type(error).__name__}
 for row in record['scopes']:row['exists_after_check']=Path(row['path']).is_dir()
 record['source_sha256_after']=hashlib.sha256(subject.read_bytes()).hexdigest()
 save()
print(json.dumps(record,sort_keys=True),flush=True)
'''


class GenesisOwnership(unittest.TestCase):
    def setUp(self):
        parent = Path(tempfile.gettempdir()) / '.ubd'
        parent.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='ck0-own-', dir=parent)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / 'source'
        for name in INPUTS:
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
            if name.endswith('.sh'):
                path.chmod(0o755)
        self.transport = types.ModuleType('ownership_test_resource_transport')
        self.transport.__file__ = str(ROOT / HELPER)
        exec(compile((ROOT / HELPER).read_bytes(), str(ROOT / HELPER), 'exec', dont_inherit=True),
             self.transport.__dict__)
        alias = self.root / 'python'
        alias.symlink_to(Path(sys.executable).resolve(strict=True))
        self.assertNotIn(' ', str(alias), 'private shebang alias requires no spaces')
        self.receipt = {'case': self.id(), 'Rust_execution': False, 'proof_claim': False,
                        'q6_complete': False, 'authenticated_scratch_cleanup': [],
                        'retained_unknown': []}
        self.launch_marker = self.root / 'actual-emitter-launches'
        emitter = ('import os\nwith open(' + repr(str(self.launch_marker)) +
                   ", 'ab') as marker:marker.write(b'fixture-launched\\n')\n" + EMITTER)
        (self.source / 'genesis/ck0/generate_manifest.sh').write_bytes(
            ('#!' + str(alias) + '\n' + emitter).encode())

    def tearDown(self):
        print(json.dumps(self.receipt, sort_keys=True), flush=True)

    def _ownership_case(self, mode):
        path = self.root / 'receipt.json'
        nonce = secrets.token_hex(24)
        argv = [sys.executable, '-B', '-c', BOOTSTRAP, str(self.source / CHECKER), str(path), nonce, mode]
        self.receipt['source_hashes'] = {name: hashlib.sha256((self.source / name).read_bytes()).hexdigest()
                                         for name in INPUTS}
        child = subprocess.Popen(argv, cwd=self.source, env=os.environ.copy(),
            pass_fds=self.transport.resource_fds(os.environ),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        record = None
        try:
            try:
                stdout, stderr = child.communicate(timeout=15)
            except BaseException:
                child.kill();child.communicate();raise
            record = json.loads(path.read_bytes())
            self.receipt.update(argv=[sys.executable, '-B', '-c', '<source bootstrap>',
                                     str(self.source / CHECKER), str(path), '<private owner nonce>', mode],
                                direct_exit=child.returncode, stdout_hex=stdout.hex(),
                                stderr_hex=stderr.hex(), actual_child_receipt=record)
            self.assertEqual(child.returncode, 0, stderr)
            self.assertNotIn('unexpected_error', record)
            self.assertIs(record['sigchld_initial_default'], True)
            self.assertIs(record['sigchld_restored'], True)
            self.assertEqual(record['initial_thread_count'], 1)
            self.assertIs(record['checker_is_main_thread'], True)
            self.assertIs(record['worker_joined'], True)
            self.assertEqual(record['thread_count_after_join'], 1)
            self.assertEqual(record['thread_count_before_check'], 2 if mode == 'extra-thread-policy' else 1)
            self.assertIs(record['worker_started'], mode == 'extra-thread-policy')
            self.assertIs(record['worker_alive_before_check'], mode == 'extra-thread-policy')
            if mode in ('sigchld-policy', 'extra-thread-policy'):
                self.assertIs(record['sigchld_active_default'], mode == 'extra-thread-policy')
                self.assertIsNone(record['cleanup_observation'],
                                  'extra waiter thread allowed a fixture process' if mode == 'extra-thread-policy'
                                  else 'nondefault SIGCHLD handler allowed a fixture process')
                self.assertFalse(self.launch_marker.exists(), 'prelaunch refusal ran the actual emitter')
                self.assertIsNone(record['real_wait'])
                self.assertEqual(record['blocked_calls'], [])
                self.assertEqual(record['saved_real_group_signals'], [])
                details = record['refusal']['details']
                self.assertEqual(details['error']['type'], 'ValueError')
                self.assertEqual(details['error']['message'],
                                 'fixture requires one main-thread child waiter' if mode == 'extra-thread-policy'
                                 else 'fixture requires default SIGCHLD handling')
                self.assertNotIn('leader_pid', details)
                self.assertNotIn('capture_files', details)
                self.assertIsNone(details['leader_exit'])
                self.assertIs(details['cleanup_uncertain'], False)
                self.assertIs(details['fixture_retained'], False)
                self.assertEqual(details['cleanup']['errors'], [])
                self.assertTrue(record['scopes'])
                self.assertTrue(all(not row['exists_after_check'] for row in record['scopes']))
                self.assertEqual(record['source_sha256'], record['source_sha256_after'])
                return
            self.assertIs(record['sigchld_active_default'], True)
            self.assertEqual(self.launch_marker.read_bytes(), b'fixture-launched\n')
            self.assertIsNotNone(record['real_wait'], 'control did not reach the actual owning wait')
            self.assertIsNotNone(record['echild'], 'control did not observe actual ECHILD')
            self.assertEqual(record['real_wait']['exit_code'], 1)
            self.assertEqual(record['real_wait']['pid'], record['cleanup_observation']['pid'])
            self.assertEqual(record['echild']['errno'], errno.ECHILD)
            self.assertIn(record['echild']['source'], ('real-observer', 'real-waitpid-after-observer-return'))
            observation = record['cleanup_observation']
            self.assertEqual(record['mode'], mode)
            self.assertIsNone(observation['returncode_at_cleanup_entry'])
            self.assertIs(observation['identity_held'], mode == 'completed-owner')
            if mode == 'lost-wait':
                self.assertIsNone(observation['returncode_before'])
                self.assertIsNone(observation['returncode_after'])
            else:
                self.assertEqual(record['real_wait']['source'], 'actual-Popen.wait')
                self.assertEqual(observation['returncode_before'], 1)
                self.assertEqual(observation['returncode_after'], 1)
            self.assertEqual(record['blocked_calls'], [],
                             'product attempted group signal after real ownership loss')
            self.assertEqual(record['saved_real_group_signals'], [])
            details = record['refusal']['details']
            self.assertIsNone(details['leader_exit'])
            if mode == 'lost-wait':
                self.assertEqual(details['error']['type'], 'ChildProcessError')
            else:
                self.assertNotIn('error', details)
            self.assertEqual(details['stdout_hex'], '')
            self.assertEqual(details['stderr_hex'], b'Q6 REFUSED: retired ownership fixture\n'.hex())
            self.assertIs(details['cleanup_uncertain'], True)
            self.assertIs(details['fixture_retained'], True)
            self.assertIs(details['cleanup']['group_signal_attempted'], False)
            self.assertIs(details['cleanup']['group_signal_sent'], False)
            self.assertTrue(details['cleanup']['errors'])
            self.assertTrue(record['scopes'])
            self.assertTrue(all(row['exists_after_check'] for row in record['scopes']))
            self.assertEqual(record['source_sha256'], record['source_sha256_after'])
        finally:
            self.receipt['launch_marker_hex'] = self.launch_marker.read_bytes().hex() if self.launch_marker.exists() else ''
            if path.exists():
                record = json.loads(path.read_bytes())
                terminal = child.returncode is not None and (record.get('real_wait') or {}).get('exit_code') == 1
                for row in reversed(record['scopes']):
                    scratch = Path(row['path'])
                    if not scratch.exists():
                        continue
                    if not terminal:
                        self.receipt['retained_unknown'].append(str(scratch))
                        continue
                    info = scratch.lstat()
                    self.assertTrue(stat.S_ISDIR(info.st_mode) and not scratch.is_symlink())
                    self.assertEqual((info.st_dev, info.st_ino), (row['device'], row['inode']))
                    self.assertEqual(scratch.parent.resolve(), (Path(tempfile.gettempdir()) / '.ubd').resolve())
                    self.assertTrue(scratch.name.startswith('q6-genesis-history-'))
                    self.assertEqual((scratch / COOKIE).read_text(), nonce)
                    shutil.rmtree(scratch)
                    self.receipt['authenticated_scratch_cleanup'].append(str(scratch))

    def test_lost_wait_retains_scratch_without_group_signal(self):
        self._ownership_case('lost-wait')

    def test_completed_popen_retains_scratch_without_group_signal(self):
        self._ownership_case('completed-owner')

    def test_nondefault_sigchld_refused_before_launch(self):
        self._ownership_case('sigchld-policy')

    def test_extra_thread_refused_before_launch(self):
        self._ownership_case('extra-thread-policy')


if __name__ == '__main__':
    program = unittest.main(exit=False, verbosity=2)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
