#!/usr/bin/env python3
"""Untrusted checks that historical seed entry points refuse without promotion.

Copies exact public script bytes into owned fixtures, never invokes real Rust,
and observes exit/output, known command sentinels and final filesystem state.
This is not a sandbox, continuous write monitor, proof, build or Q6 completion.
"""
import argparse
import errno
import hashlib
import json
import os
from pathlib import Path
import re
import select
import shutil
import shlex
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
import types

ROOT = Path(__file__).resolve().parents[1]
HISTORY = 'genesis/ck0/MANIFEST.txt'
ENTRYPOINTS = ('genesis/ck0/generate_manifest.sh', 'genesis/ck0/verify.sh')
HISTORICAL_SHA256 = '12552fdf6250c74d0a3115cfd304d9724c93b438202c78367b8065e72c220c81'
MAX_SOURCE_BYTES = 64 * 1024
FIXTURE_SECONDS = 5
CLEANUP_SECONDS = 2
RESOURCE_HELPER = 'scripts/resource_transport.py'
LIFECYCLE_TEST = 'scripts/test_ck0_genesis_lifecycle.py'
RETENTION_TEST = 'scripts/test_ck0_genesis_retention.py'
ANSWERS_PINNED_INPUTS = True
TOOLS = ('git', 'trustc', 'targo', 'rustc', 'cargo', 'find', 'sha256sum', 'shasum')
_ACTIVE_SCRATCH = []


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def regular(root, relative):
    path = root
    for number, part in enumerate(Path(relative).parts):
        path /= part
        try:
            mode = path.lstat().st_mode
        except FileNotFoundError as error:
            raise ValueError('missing history input: ' + relative) from error
        need(not stat.S_ISLNK(mode), 'symlink history input: ' + relative)
        need(stat.S_ISREG(mode) if number == len(Path(relative).parts) - 1 else
             stat.S_ISDIR(mode), 'nonregular history input: ' + relative)
    need(path.stat().st_size <= MAX_SOURCE_BYTES, 'history input size: ' + relative)
    with path.open('rb') as stream:
        data = stream.read(MAX_SOURCE_BYTES + 1)
    need(len(data) <= MAX_SOURCE_BYTES, 'history input size: ' + relative)
    return path, data


def snapshot(root):
    result = {}
    def walk_error(error):
        raise ValueError('fixture walk failed: ' + str(error)) from error
    paths = [root]
    for directory, directories, files in os.walk(root, onerror=walk_error, followlinks=False):
        paths.extend(Path(directory) / name for name in sorted(directories + files))
    for path in paths:
        mode = path.lstat().st_mode
        need(not stat.S_ISLNK(mode), 'fixture created a symlink')
        if stat.S_ISDIR(mode):
            info = path.stat()
            result[str(path.relative_to(root))] = ['directory', stat.S_IMODE(mode), info.st_mtime_ns]
        else:
            need(stat.S_ISREG(mode), 'fixture created a nonregular entry')
            info = path.stat()
            need(info.st_size <= MAX_SOURCE_BYTES, 'fixture file exceeds supported size')
            with path.open('rb') as stream:
                data = stream.read(MAX_SOURCE_BYTES + 1)
            need(len(data) <= MAX_SOURCE_BYTES, 'fixture file exceeds supported size')
            result[str(path.relative_to(root))] = [sha(data),
                                                  stat.S_IMODE(mode), info.st_mtime_ns]
    return result


def scratch():
    parent = Path(tempfile.gettempdir()) / '.ubd'
    parent.mkdir(exist_ok=True)
    return FixtureScratch(parent)


class FixtureExecutionRefused(ValueError):
    def __init__(self, details):
        self.details = details
        super().__init__('fixture execution refused')

    def __str__(self):
        return 'fixture execution refused: ' + json.dumps(self.details, sort_keys=True)


class FixtureScratch:
    """Never remove paths a possibly live owned writer can still use."""
    def __init__(self, parent):
        self.parent = parent

    def __enter__(self):
        self.name = tempfile.mkdtemp(prefix='q6-genesis-history-', dir=self.parent)
        self.retained = False
        _ACTIVE_SCRATCH.append(self)
        return self.name

    def __exit__(self, _kind, _error, _traceback):
        try:
            if not self.retained:
                shutil.rmtree(self.name)
        finally:
            _ACTIVE_SCRATCH.remove(self)


def _retention_required():
    return any(scope.retained for scope in _ACTIVE_SCRATCH)


def _mark_cleanup_uncertain(details):
    """Persist safety state before any later handler/error can replace it."""
    details['cleanup_uncertain'] = True
    paths = details.setdefault('retained_scratch', [])
    for scope in _ACTIVE_SCRATCH:
        scope.retained = True
        if scope.name not in paths:
            paths.append(scope.name)
    details['fixture_retained'] = bool(paths)


def _resource_fds(env):
    path, data = regular(ROOT, RESOURCE_HELPER)
    helper = types.ModuleType('q6_genesis_resource_source')
    helper.__file__ = str(path)
    exec(compile(data, str(path), 'exec', dont_inherit=True), helper.__dict__)
    return helper.resource_fds(env)


def _owner_policy():
    need(hasattr(signal, 'SIGCHLD') and signal.getsignal(signal.SIGCHLD) == signal.SIG_DFL,
         'fixture requires default SIGCHLD handling')
    need(threading.current_thread() is threading.main_thread() and threading.active_count() == 1,
         'fixture requires one main-thread child waiter')


def _observer_available():
    return (all(hasattr(os, name) for name in ('waitid', 'P_PID', 'WEXITED', 'WNOWAIT', 'WNOHANG')) or
            all(hasattr(select, name) for name in ('kqueue', 'kevent', 'KQ_FILTER_PROC',
                'KQ_EV_ADD', 'KQ_EV_ONESHOT', 'KQ_NOTE_EXIT', 'KQ_EV_ERROR')))


class _IdentityLost(RuntimeError):
    pass


def _observe_exit(pid):
    """Maintained waitid/kqueue pattern: observe, never reap the held leader."""
    if all(hasattr(os, name) for name in ('waitid', 'P_PID', 'WEXITED', 'WNOWAIT', 'WNOHANG')):
        result = os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT | os.WNOHANG)
        if result is not None and result.si_pid != pid:
            raise _IdentityLost('unexpected owned child observation')
        return result is not None
    with select.kqueue() as events:
        try:
            ready = events.control([select.kevent(pid, filter=select.KQ_FILTER_PROC,
                flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT, fflags=select.KQ_NOTE_EXIT)], 1, 0)
        except ProcessLookupError:
            return True  # Exited before registration; the sole waiter has not reaped it.
        if not ready:
            return False
        if ready[0].flags & select.KQ_EV_ERROR:
            if ready[0].data == errno.ESRCH:
                return True
            raise OSError(ready[0].data, 'cannot observe owned child exit')
        if len(ready) != 1 or ready[0].ident != pid or not ready[0].fflags & select.KQ_NOTE_EXIT:
            raise _IdentityLost('owned child exit notification was not established')
        return True


def _prefix(stream):
    stream.flush()
    size = os.fstat(stream.fileno()).st_size
    stream.seek(0)
    data = stream.read(MAX_SOURCE_BYTES + 1)
    return data[:MAX_SOURCE_BYTES], max(size, len(data)), size > MAX_SOURCE_BYTES or len(data) > MAX_SOURCE_BYTES


def _group_states(pid, directory, env, descriptors, deadline):
    """A complete bounded census; zombies are stopped, not claimed OS-reaped."""
    remaining = deadline - time.monotonic()
    need(remaining > 0, 'owned group cleanup deadline expired')
    with tempfile.TemporaryFile(dir=directory) as stdout, tempfile.TemporaryFile(dir=directory) as stderr:
        result = subprocess.run(['/bin/ps', '-axo', 'pgid=,stat='], env=env,
            pass_fds=descriptors, stdout=stdout, stderr=stderr, timeout=min(1, remaining))
        out, _out_size, out_truncated = _prefix(stdout)
        err, _err_size, err_truncated = _prefix(stderr)
    need(result.returncode == 0 and not err and not out_truncated and not err_truncated,
         'owned group census unavailable or incomplete')
    states = []
    for row in out.decode('ascii').splitlines():
        fields = row.split()
        need(len(fields) == 2 and re.fullmatch(r'[0-9]+', fields[0]) and
             re.fullmatch(r'[?DIRSTtUWXZP][+<>AELNSsVWXl]*', fields[1]),
             'malformed owned group census')
        if int(fields[0]) == pid:
            states.append(fields[1])
    return states


def _cleanup_fixture(process, details, directory, env, descriptors, identity_held):
    cleanup = details['cleanup']
    deadline = time.monotonic() + CLEANUP_SECONDS
    def failed(operation, error):
        _mark_cleanup_uncertain(details)
        cleanup['errors'].append({'operation': operation, 'type': type(error).__name__,
                                  'message': str(error)})
    if not identity_held or process.returncode is not None:
        failed('ownership', _IdentityLost('leader identity is no longer held; no group signal permitted'))
        return
    try:
        _owner_policy()
    except BaseException as error:
        failed('ownership', error)
        return
    try:
        cleanup['group_signal_attempted'] = True
        try:
            os.killpg(process.pid, signal.SIGKILL)
            cleanup['group_signal_sent'] = True
        except ProcessLookupError:
            pass
        except PermissionError as error:
            # Darwin may refuse a zombie-only group. No live or hidden member
            # may be excused; a failed/partial census remains a refusal.
            states = _group_states(process.pid, directory, env, descriptors, deadline)
            if error.errno != errno.EPERM or not states or any(not s.startswith('Z') for s in states):
                raise
        while True:
            states = _group_states(process.pid, directory, env, descriptors, deadline)
            if not states or all(state.startswith('Z') for state in states):
                cleanup['group_state'] = 'zombies-only' if states else 'absent'
                cleanup['group_drained'] = True
                break
            need(time.monotonic() < deadline, 'owned group still has live members after cleanup')
            time.sleep(0.01)
    except BaseException as error:
        failed('group cleanup', error)
    try:
        while not _observe_exit(process.pid):
            need(time.monotonic() < deadline, 'owned leader did not exit during cleanup')
            time.sleep(0.01)
        # Exactly one owning wait, after the final signal. Unlike Popen.wait,
        # ECHILD is not converted into a synthetic successful exit status.
        waited, status = os.waitpid(process.pid, os.WNOHANG)
        need(waited == process.pid, 'owning wait did not return the created leader')
        process.returncode = os.waitstatus_to_exitcode(status)
        details['leader_exit'] = process.returncode
        cleanup['leader_reaped'] = True
    except BaseException as error:
        failed('leader reap', error)
    if cleanup['errors'] or not (cleanup['group_drained'] and cleanup['leader_reaped']):
        _mark_cleanup_uncertain(details)


def _run_fixture(argv, cwd, env, case, directory):
    """Own one fixture group; no escaped-descendant or sandbox guarantee."""
    started = time.monotonic()
    details = {'case': case, 'argv': argv, 'deadline_seconds': FIXTURE_SECONDS,
        'timed_out': False, 'leader_exit': None, 'elapsed_seconds': 0,
        'stdout_hex': '', 'stderr_hex': '', 'stdout_bytes': 0, 'stderr_bytes': 0,
        'capture_truncated': False, 'cleanup_uncertain': False, 'fixture_retained': False,
        'cleanup': {'group_signal_sent': False, 'group_signal_attempted': False,
                    'group_drained': False, 'group_state': 'uncertain',
                    'leader_reaped': False, 'errors': []}}
    process = None
    captures = []
    old_handlers = {}
    interrupted = []
    reason = None
    identity_held = True
    try:
        _owner_policy()
        need(hasattr(os, 'killpg') and _observer_available(), 'nonreaping fixture observation unavailable')
        descriptors = _resource_fds(env)
        for name in ('stdout', 'stderr'):
            stream = tempfile.NamedTemporaryFile(prefix='fixture-' + name + '-', dir=directory, delete=False)
            captures.append(stream)
        details['capture_files'] = dict(zip(('stdout', 'stderr'), (stream.name for stream in captures)))
        def interruption(signum, _frame):
            if not interrupted:
                interrupted.append(signum)
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            old_handlers[sig] = signal.signal(sig, interruption)
        spawning = time.monotonic()
        process = subprocess.Popen(argv, cwd=cwd, env=env, stdout=captures[0], stderr=captures[1],
                                   start_new_session=True, pass_fds=descriptors)
        details.update(leader_pid=process.pid, group_id=process.pid,
                       spawn_seconds=time.monotonic() - spawning)
        deadline = time.monotonic() + FIXTURE_SECONDS
        while True:
            if interrupted:
                break
            if time.monotonic() >= deadline:
                details['timed_out'] = True
                break
            if _observe_exit(process.pid):
                break
            time.sleep(0.01)
    except BaseException as error:
        reason = 'fixture launch or observation failed'
        details['error'] = {'type': type(error).__name__, 'message': str(error)}
        identity_held = not isinstance(error, (ChildProcessError, _IdentityLost)) and not (
            isinstance(error, OSError) and error.errno == errno.ECHILD)
    finally:
        if process is not None:
            try:
                _cleanup_fixture(process, details, directory, env, descriptors, identity_held)
            except BaseException as error:
                _mark_cleanup_uncertain(details)
                details['cleanup']['errors'].append({'operation': 'unexpected cleanup failure',
                    'type': type(error).__name__, 'message': str(error)})
        for sig, handler in old_handlers.items():
            try:
                signal.signal(sig, handler)
            except BaseException as error:
                _mark_cleanup_uncertain(details)
                details['cleanup']['errors'].append({'operation': 'restore signal handler',
                    'type': type(error).__name__, 'message': str(error)})
        try:
            for name, stream in zip(('stdout', 'stderr'), captures):
                try:
                    data, size, truncated = _prefix(stream)
                    details[name + '_hex'] = data.hex()
                    details[name + '_bytes'] = size
                    details['capture_truncated'] |= truncated
                except BaseException as error:
                    reason = reason or 'fixture capture unavailable'
                    details['capture_error'] = {'type': type(error).__name__, 'message': str(error)}
        finally:
            for stream in captures:
                try:
                    stream.close()
                except BaseException as error:
                    _mark_cleanup_uncertain(details)
                    details['cleanup']['errors'].append({'operation': 'close capture',
                        'type': type(error).__name__, 'message': str(error)})
            # The scratch scope owns capture deletion. Keeping names until its
            # exit also preserves them if a later interrupt replaces this error.
        details['elapsed_seconds'] = time.monotonic() - started
    if details['timed_out']:
        reason = 'fixture exceeded 5-second deadline'
    elif interrupted:
        reason = 'fixture interrupted by signal'
        details['signals'] = interrupted
    elif details['cleanup_uncertain']:
        reason = 'fixture cleanup uncertain'
    elif details['capture_truncated']:
        reason = 'fixture response exceeded 64KiB capture prefix'
    if reason is None:
        try:
            stdout = bytes.fromhex(details['stdout_hex']).decode('utf-8')
            stderr = bytes.fromhex(details['stderr_hex']).decode('utf-8')
        except UnicodeError as error:
            reason = 'invalid UTF-8 fixture response'
            details['error'] = {'type': type(error).__name__, 'message': str(error)}
    if reason is not None:
        details['reason'] = reason
        raise FixtureExecutionRefused(details)
    return subprocess.CompletedProcess(argv, details['leader_exit'], stdout, stderr)


def absent(path):
    try:
        path.lstat()
    except FileNotFoundError:
        return True
    return False


def check(root=ROOT):
    root = Path(root)
    _, archive = regular(root, HISTORY)
    need(sha(archive) == HISTORICAL_SHA256, 'historical manifest digest changed')
    scripts = {}
    for relative in ENTRYPOINTS:
        path, data = regular(root, relative)
        need(path.stat().st_mode & 0o111, 'entry point is not executable: ' + relative)
        scripts[relative] = data
    rows = []
    with scratch() as temporary:
        outer = Path(temporary)
        fixture = outer / 'fixture'
        (fixture / 'genesis/ck0').mkdir(parents=True)
        (fixture / 'nested').mkdir()
        (fixture / HISTORY).write_bytes(archive)
        for relative, data in scripts.items():
            (fixture / relative).write_bytes(data)
            (fixture / relative).chmod(0o755)
        fake_bin = fixture / 'sentinel-bin'
        fake_bin.mkdir()
        calls = fixture / 'tool-calls'
        calls.write_bytes(b'')
        for name in TOOLS:
            path = fake_bin / name
            path.write_text('#!/bin/sh\nprintf "%s\\n" "' + name +
                            '" >> ' + shlex.quote(str(calls)) + '\nexit 97\n')
            path.chmod(0o755)
        env = {**os.environ, 'PATH': str(fake_bin) + ':/usr/bin:/bin'}
        outside = outer / 'must-not-be-written'
        arguments = ((), ('--help',), ('--historical',), ('--require-q6',),
                     ('--output', str(outside)), ('--', '../MANIFEST.txt'))
        original = snapshot(fixture)
        for relative in ENTRYPOINTS:
            for cwd in (fixture, fixture / 'nested'):
                for flags in arguments:
                    argv = [str(fixture / relative), *flags]
                    case = {'entrypoint': relative, 'cwd': str(cwd.relative_to(fixture)),
                            'arguments': list(flags), 'index': len(rows)}
                    result = _run_fixture(argv, cwd, env, case, outer)
                    need(result.returncode == 1, 'historical entry point did not refuse: ' + relative)
                    need(not result.stdout and 'Q6 REFUSED:' in result.stderr and
                         'retired' in result.stderr, 'missing explicit historical refusal: ' + relative)
                    _, observed_calls = regular(fixture, 'tool-calls')
                    need(observed_calls == b'', 'historical entry point invoked a guarded tool')
                    need(snapshot(fixture) == original and absent(outside),
                         'historical entry point changed fixture state')
                    rows.append({'entrypoint': relative, 'cwd': str(cwd.relative_to(fixture)),
                                 'arguments': list(flags), 'exit': result.returncode})
    return {'kind': 'historical-genesis-refusal-consistency', 'cases': len(rows),
            'manifest_sha256': sha(archive), 'entrypoint_sha256':
            {name: sha(data) for name, data in scripts.items()},
            'guarded_tool_calls': 0, 'fixture_state_unchanged': True,
            'proof_claim': False, 'q6_complete': False, 'genesis_promoted': False,
            'rust_execution': False}


def selftest():
    positive = check()
    outcomes = []
    with scratch() as temporary:
        root = Path(temporary) / 'candidate'
        (root / 'genesis/ck0').mkdir(parents=True)
        for relative in (HISTORY, *ENTRYPOINTS):
            shutil.copy2(ROOT / relative, root / relative)

        def refuses(label, relative, data, reason, symlink=False, absent=False):
            path = root / relative
            original = path.read_bytes()
            mode = path.stat().st_mode
            retain = False
            try:
                if symlink:
                    path.unlink()
                    path.symlink_to(ROOT / relative)
                elif absent:
                    path.unlink()
                else:
                    path.write_bytes(data)
                try:
                    check(root)
                except FixtureExecutionRefused as error:
                    if error.details['cleanup_uncertain']:
                        retain = True
                        raise
                    need(reason in str(error), label + ': wrong refusal: ' + str(error))
                    outcomes.append({'case': label, 'refused': True, 'reason': str(error)})
                except (ValueError, OSError) as error:
                    need(reason in str(error), label + ': wrong refusal: ' + str(error))
                    outcomes.append({'case': label, 'refused': True, 'reason': str(error)})
                else:
                    raise ValueError('negative control accepted: ' + label)
            finally:
                if not retain and not _retention_required():
                    if path.is_symlink():
                        path.unlink()
                    path.write_bytes(original)
                    path.chmod(stat.S_IMODE(mode))

        for relative in ENTRYPOINTS:
            label = Path(relative).stem
            refuses(label + '-false-success', relative, b'#!/bin/sh\nexit 0\n', 'did not refuse')
            refusal = b'printf "%s\\n" "Q6 REFUSED: retired" >&2\n'
            refuses(label + '-tool-call', relative,
                    b'#!/bin/sh\ntrustc --version\n' + refusal + b'exit 1\n', 'guarded tool')
            refuses(label + '-archive-overwrite', relative,
                    b'#!/bin/sh\nprintf changed > genesis/ck0/MANIFEST.txt\n' + refusal +
                    b'exit 1\n', 'changed fixture state')
            refuses(label + '-empty-directory', relative,
                    b'#!/bin/sh\nmkdir undeclared-directory\n' + refusal + b'exit 1\n',
                    'changed fixture state')
            refuses(label + '-directory-mode', relative,
                    b'#!/bin/sh\nchmod 700 nested\n' + refusal + b'exit 1\n',
                    'changed fixture state')
            refuses(label + '-tool-log-fifo', relative,
                    b'#!/bin/sh\nrm tool-calls\nmkfifo tool-calls\n' + refusal + b'exit 1\n',
                    'nonregular history input')
            refuses(label + '-redirect-tool-log-env', relative,
                    b'#!/bin/sh\nQ6_HISTORY_TOOL_LOG=/dev/null trustc --version 2>/dev/null || :\n' +
                    refusal + b'exit 1\n', 'guarded tool')
            refuses(label + '-dangling-output-link', relative,
                    b'#!/bin/sh\nif [ "${1:-}" = --output ]; then ln -s nonexistent "$2"; fi\n' +
                    refusal + b'exit 1\n', 'changed fixture state')
            refuses(label + '-misleading-output', relative,
                    b'#!/bin/sh\nprintf "REPRODUCED\\n"\n' + refusal + b'exit 1\n',
                    'missing explicit historical refusal')
            refuses(label + '-silent-refusal', relative, b'#!/bin/sh\nexit 1\n',
                    'missing explicit historical refusal')
            refuses(label + '-linked-entrypoint', relative, b'', 'symlink history input', symlink=True)
        refuses('modified-manifest', HISTORY, b'forged promotion\n', 'historical manifest digest changed')
        refuses('empty-manifest', HISTORY, b'', 'historical manifest digest changed')
        refuses('linked-manifest', HISTORY, b'', 'symlink history input', symlink=True)
        refuses('missing-manifest', HISTORY, b'', 'missing history input', absent=True)
        check(root)
    for controls in (LIFECYCLE_TEST, RETENTION_TEST):
        lifecycle = subprocess.run([sys.executable, '-B', str(ROOT / controls)],
                                   pass_fds=_resource_fds(os.environ))
        need(lifecycle.returncode == 0, controls + ' genesis lifecycle controls failed')
    print(json.dumps({'positive': positive, 'negative_controls': len(outcomes),
                      'outcomes': outcomes, 'proof_claim': False, 'q6_complete': False}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selftest', action='store_true')
    parser.add_argument('--pinned-inputs', action='store_true')
    args = parser.parse_args()
    need(not (args.selftest and args.pinned_inputs), 'conflicting action modes')
    if args.pinned_inputs:
        print('\n'.join((HISTORY, *ENTRYPOINTS, RESOURCE_HELPER, LIFECYCLE_TEST, RETENTION_TEST)))
    elif args.selftest:
        selftest()
    else:
        print(json.dumps(check(), sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        print('Q6 GENESIS HISTORY REFUSED: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
