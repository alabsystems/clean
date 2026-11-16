#!/usr/bin/env python3
"""Real private Python-process controls for the public genesis-history CLI.

No Rust/native proof tool or recorded image runs. Socket liveness is observed;
an orphan's eventual OS reaping is unknown, never inferred from kill(pid, 0).
"""
import hashlib
import json
import os
from pathlib import Path
import secrets
import socket
import subprocess
import sys
import tempfile
import threading
import time
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
CHECKER = 'scripts/check_ck0_genesis_history.py'
INPUTS = (CHECKER, 'genesis/ck0/MANIFEST.txt', 'genesis/ck0/generate_manifest.sh',
          'genesis/ck0/verify.sh')
HELPER = 'scripts/resource_transport.py'
OUT = b'Q6_BLOCK_STDOUT\n'
ERR = b'Q6 REFUSED: retired lifecycle fixture\nQ6_BLOCK_STDERR\n'
PREFIX = 'fixture execution refused: '

# This private payload never changes process groups or detaches. Its holder
# inherits the actual entrypoint's output descriptions and has a bounded TTL.
PAYLOAD = r'''
import json,os,select,socket,subprocess,sys,time
token=os.environ['Q6_GL_TOKEN'];deadline=time.monotonic()+20
mode=os.environ['Q6_GL_MODE'];holder=len(sys.argv)==3 and sys.argv[1]=='__q6_holder__'
role='holder' if holder else 'leader';leader=int(sys.argv[2]) if holder else os.getpid()
def fd_info(fd):
 s=os.fstat(fd);return [s.st_dev,s.st_ino,s.st_mode]
def send(value):
 connection.sendall((json.dumps(dict(value,token=token))+'\n').encode())
def receive():
 data=b''
 while not data.endswith(b'\n'):
  left=deadline-time.monotonic()
  if left<=0 or not select.select([connection],[],[],left)[0]:os._exit(0)
  part=connection.recv(1)
  if not part:os._exit(0)
  data+=part
 value=json.loads(data)
 if value.get('token')!=token:os._exit(91)
 return value['command']
connection=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM)
connection.connect(os.environ['Q6_GL_SOCKET'])
send({'role':role,'pid':os.getpid(),'ppid':os.getppid(),'pgid':os.getpgrp(),
      'leader':leader,'stdout_fd':fd_info(1),'stderr_fd':fd_info(2)})
if receive()!='ACK':os._exit(92)
if not holder and mode=='holder':
 child=subprocess.Popen([sys.executable,__file__,'__q6_holder__',str(os.getpid())])
 if receive()!='RELEASE':os._exit(93)
 print('Q6 REFUSED: retired lifecycle fixture',file=sys.stderr,flush=True)
 os._exit(1)
if not holder:
 sys.stdout.buffer.write(b'Q6_BLOCK_STDOUT\n');sys.stdout.buffer.flush()
 sys.stderr.buffer.write(b'Q6 REFUSED: retired lifecycle fixture\nQ6_BLOCK_STDERR\n');sys.stderr.buffer.flush()
while True:
 command=receive()
 if command=='PING':send({'command':'PONG','pid':os.getpid(),'role':role})
 elif command=='STOP':
  send({'command':'ACK_STOP','pid':os.getpid(),'role':role});os._exit(0)
 else:os._exit(94)
'''


def send(connection, token, command):
    connection.sendall((json.dumps({'token': token, 'command': command}) + '\n').encode())


def receive(connection):
    data = b''
    while not data.endswith(b'\n'):
        part = connection.recv(1)
        if not part:
            return None
        data += part
        if len(data) > 8192:
            raise ValueError('private control frame exceeded bound')
    return json.loads(data)


class ControlHub:
    def __init__(self, root):
        self.path = root / 'control.sock'
        self.token = secrets.token_hex(24)
        self.listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.listener.bind(str(self.path))
        self.path.chmod(0o600)
        self.listener.listen()
        self.listener.settimeout(0.1)
        self.entries, self.errors = [], []
        self.stop = threading.Event()
        self.thread = threading.Thread(target=self.accept, name='owned-genesis-control')
        self.thread.start()

    def accept(self):
        leaders = {}
        while not self.stop.is_set():
            try:
                connection, _ = self.listener.accept()
            except socket.timeout:
                continue
            except OSError:
                if not self.stop.is_set():
                    self.errors.append('private listener failed')
                break
            try:
                connection.settimeout(2)
                row = receive(connection)
                if not row or row.pop('token', None) != self.token:
                    raise ValueError('private HELLO authentication')
                if row['role'] == 'leader':
                    if row['pid'] != row['leader']:
                        raise ValueError('leader identity')
                    leaders[row['pid']] = (connection, row)
                elif row['role'] == 'holder':
                    parent, leader = leaders[row['leader']]
                    if row['ppid'] != leader['pid'] or any(
                            row[field] != leader[field] for field in ('stdout_fd', 'stderr_fd', 'pgid')):
                        raise ValueError('holder ancestry/output descriptions')
                else:
                    raise ValueError('unknown private role')
                self.entries.append((connection, row))
                send(connection, self.token, 'ACK')
                if row['role'] == 'holder':
                    send(parent, self.token, 'RELEASE')
            except (OSError, ValueError, KeyError) as error:
                self.errors.append(str(error))
                connection.close()

    def probe(self, entry):
        connection, row = entry
        try:
            send(connection, self.token, 'PING')
            response = receive(connection)
            if response is None:
                return {'state': 'EOF', 'pid': row['pid'], 'role': row['role']}
            if response != {'token': self.token, 'command': 'PONG',
                            'pid': row['pid'], 'role': row['role']}:
                raise ValueError('private PONG authentication')
            return {'state': 'alive', 'pid': row['pid'], 'role': row['role']}
        except (BrokenPipeError, ConnectionResetError):
            return {'state': 'EOF', 'pid': row['pid'], 'role': row['role']}
        except (OSError, ValueError) as error:
            return {'state': 'uncertain', 'pid': row['pid'], 'error': str(error)}

    def close(self):
        self.stop.set()
        self.thread.join(3)
        self.listener.close()
        cleanup = []
        for entry in self.entries:
            connection, row = entry
            state = self.probe(entry)
            try:
                if state['state'] == 'alive':
                    send(connection, self.token, 'STOP')
                    response = receive(connection)
                    if response != {'token': self.token, 'command': 'ACK_STOP',
                                    'pid': row['pid'], 'role': row['role']}:
                        raise ValueError('private STOP authentication')
                    if connection.recv(1) != b'':
                        raise ValueError('private STOP did not drain to EOF')
                    state = {**state, 'state': 'stopped-to-EOF'}
            except (OSError, ValueError) as error:
                self.errors.append(str(error))
            finally:
                connection.close()
            cleanup.append(state)
        return {'channels': cleanup, 'errors': self.errors,
                'server_thread_terminal': not self.thread.is_alive(),
                'OS_orphan_reaping': 'unknown; never asserted reaped'}


class GenesisLifecycle(unittest.TestCase):
    def setUp(self):
        parent = Path(tempfile.gettempdir()) / '.ubd'
        parent.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='ck0-gl-', dir=parent)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / 'source'
        for name in (*INPUTS, HELPER):
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
            if name.endswith('.sh'):
                path.chmod(0o755)
        # Loader scaffold, outside the four public inputs: exact maintained
        # source, needed when the fixed checker forwards genuine descriptors.
        helper_path = ROOT / HELPER
        self.transport = types.ModuleType('genesis_lifecycle_resource_transport')
        self.transport.__file__ = str(helper_path)
        exec(compile(helper_path.read_bytes(), str(helper_path), 'exec', dont_inherit=True),
             self.transport.__dict__)
        self.observations = {'case': self.id(), 'Rust_execution': False,
                             'proof_claim': False, 'OS_orphan_reaping': 'unknown'}
        self.hub = None

    def tearDown(self):
        if self.hub is not None:
            self.observations['harness_cleanup'] = self.hub.close()
            self.assertFalse(self.observations['harness_cleanup']['errors'])
            self.assertTrue(self.observations['harness_cleanup']['server_thread_terminal'])
            self.assertTrue(all(row['state'] in ('EOF', 'stopped-to-EOF')
                                for row in self.observations['harness_cleanup']['channels']))
        print(json.dumps(self.observations, sort_keys=True), flush=True)

    def cli(self, mode=None):
        env = dict(os.environ)
        if mode is not None:
            self.hub = ControlHub(self.root)
            # The private no-space executable alias binds exactly sys.executable;
            # it is not inside the checker's snapshotted execution fixture.
            alias = self.root / 'python'
            alias.symlink_to(Path(sys.executable).resolve(strict=True))
            payload = ('#!' + str(alias) + '\n' + PAYLOAD).encode()
            (self.source / 'genesis/ck0/generate_manifest.sh').write_bytes(payload)
            env.update(Q6_GL_SOCKET=str(self.hub.path), Q6_GL_TOKEN=self.hub.token, Q6_GL_MODE=mode)
        argv = [sys.executable, '-B', str(self.source / CHECKER)]
        child = subprocess.Popen(argv, cwd=self.source, env=env,
                                 pass_fds=self.transport.resource_fds(env),
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            stdout, stderr = child.communicate(timeout=15)
        except BaseException:
            child.kill()
            child.communicate()
            raise
        self.observations.update(argv=argv, direct_exit=child.returncode,
                                 stdout_hex=stdout.hex(), stderr_hex=stderr.hex())
        return child.returncode, stdout, stderr

    def test_actual_retired_entrypoints_positive(self):
        code, stdout, stderr = self.cli()
        self.assertEqual(code, 0, stderr)
        self.assertEqual(stderr, b'')
        result = json.loads(stdout)
        self.assertEqual(result['cases'], 24)
        self.assertIs(result['fixture_state_unchanged'], True)
        self.assertEqual(result['guarded_tool_calls'], 0)
        self.assertIs(result['proof_claim'], False)

    def test_exited_root_holder_is_automatically_drained(self):
        code, stdout, stderr = self.cli('holder')
        holders = [entry for entry in self.hub.entries if entry[1]['role'] == 'holder']
        states = [self.hub.probe(entry) for entry in holders]
        self.observations['holder_states_before_harness_cleanup'] = states
        self.assertTrue(holders, 'owned holder never completed its real handshake')
        self.assertTrue(all(row['state'] == 'EOF' for row in states),
                        'holder survived automatic checker cleanup: ' + json.dumps(states))
        self.assertEqual(code, 0, stderr)
        self.assertEqual(json.loads(stdout)['cases'], 24)
        self.assertEqual(len(holders), 12)
        self.assertFalse(self.hub.errors)

    def test_blocking_root_retains_typed_partial_diagnostics(self):
        code, stdout, stderr = self.cli('block')
        self.assertEqual(code, 1, stdout + stderr)
        text = stderr.decode()
        self.assertIn(PREFIX, text, 'timeout discarded typed partial-output diagnostics')
        record = json.loads(text.split(PREFIX, 1)[1])
        self.assertEqual(record['case'], {'entrypoint': 'genesis/ck0/generate_manifest.sh',
                                         'cwd': '.', 'arguments': [], 'index': 0})
        self.assertEqual(record['deadline_seconds'], 5)
        self.assertIs(record['timed_out'], True)
        self.assertEqual(record['stdout_hex'], OUT.hex())
        self.assertEqual(record['stderr_hex'], ERR.hex())
        self.assertEqual(record['stdout_bytes'], len(OUT))
        self.assertEqual(record['stderr_bytes'], len(ERR))
        self.assertIs(record['capture_truncated'], False)
        self.assertIs(record['cleanup']['leader_reaped'], True)
        self.assertEqual(record['cleanup']['errors'], [])
        self.assertFalse(self.hub.errors)


if __name__ == '__main__':
    program = unittest.main(exit=False, verbosity=2)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
