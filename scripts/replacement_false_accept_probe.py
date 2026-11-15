#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Re-measure a frozen acquired false-accept cohort; never updates a ratchet.

Run differential sweeps through build-slot and scripts/heavy_gate.sh. The supplied
executables, not this checkout's source, determine the result. Acquisition paths
and Git blob identities must be recorded in acquisition.json beside fixtures/.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import gzip
import json
import math
import os
from pathlib import Path
import signal
import stat
import subprocess


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as source:
        for chunk in iter(lambda: source.read(1 << 20), b''):
            digest.update(chunk)
    return digest.hexdigest()


def executable_identity(path):
    info = path.lstat()
    if not stat.S_ISREG(info.st_mode):
        raise ValueError(f'executable is no longer a regular file: {path}')
    return {'device': info.st_dev, 'inode': info.st_ino, 'mode': info.st_mode,
            'size': info.st_size, 'mtime_ns': info.st_mtime_ns,
            'ctime_ns': info.st_ctime_ns}


def bind_executable(path):
    # Preserve the binary's SDK-relative location, rather than copying Lean
    # away from its libraries. Hash large executables only at the bookends.
    path = path.resolve(strict=True)
    identity = executable_identity(path)
    native_path(path)
    digest = sha256(path)
    if executable_identity(path) != identity:
        raise ValueError(f'executable changed while binding: {path}')
    return {'path': path, 'identity': identity, 'sha256': digest}


def guard_executable(binding):
    if executable_identity(binding['path']) != binding['identity']:
        raise ValueError(f'executable changed during measurement: {binding["path"]}')


def finish_executable(binding):
    guard_executable(binding)
    digest = sha256(binding['path'])
    guard_executable(binding)
    if digest != binding['sha256']:
        raise ValueError(f'executable digest changed: {binding["path"]}')
    return {'identity': binding['identity'], 'sha256': digest}


def native_path(path):
    resolved = path.resolve()
    with resolved.open('rb') as stream:
        if stream.read(2) == b'#!':
            raise ValueError('pass the native executable, not a launcher; use aterm pkg which')
    return resolved


def execute(command, cwd, timeout):
    with subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, start_new_session=True) as process:
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
        return {'rc': process.returncode, 'timed_out': timed_out,
                'stdout': stdout.decode('utf-8', errors='replace'),
                'stderr': stderr.decode('utf-8', errors='replace')}


def execute_bound(binding, arguments, cwd, timeout):
    guard_executable(binding)
    try:
        return execute([str(binding['path']), *arguments], cwd, timeout)
    finally:
        guard_executable(binding)


def executable_version(binding, timeout):
    result = execute_bound(binding, ['--version'], None, timeout)
    if result['timed_out'] or result['rc'] != 0:
        raise ValueError(f'executable version failed: {binding["path"]}: '
                         f'rc={result["rc"]}, timed_out={result["timed_out"]}; '
                         f'{result["stderr"]}')
    return result['stdout'].strip()


def classify(lean, clean):
    if lean['timed_out'] or clean['timed_out']:
        return 'unmeasured-timeout'
    if lean['rc'] < 0 or clean['rc'] < 0:
        return 'unmeasured-signal'
    if lean['rc'] not in (0, 1) or clean['rc'] not in (0, 1):
        return 'unmeasured-exit'
    if lean['rc'] == 0:
        return 'oracle-contract-changed'
    return 'false-accept' if clean['rc'] == 0 else 'agree-reject'


def checked_fixture_blob(path, entry):
    data = path.read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    if hashlib.sha256(data).hexdigest() != entry['sha256'] or blob != entry['blob']:
        raise ValueError(f'acquired source digest changed: {entry["path"]}')
    return blob


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', required=True, type=Path)
    parser.add_argument('--clean-bin', required=True, type=Path)
    parser.add_argument('--report-dir', required=True, type=Path)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--output-name', default='measurement.json')
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('--timeout must be finite and positive')
    if Path(args.output_name).name != args.output_name or not args.output_name.endswith('.json'):
        parser.error('--output-name must be a JSON filename within report-dir')
    out = args.report_dir.resolve()
    output = out / args.output_name
    if output.exists() or output.is_symlink():
        parser.error(f'refusing to overwrite an existing measurement: {output}')
    producer_path = Path(__file__).resolve()
    producer = producer_path.read_bytes()
    acquisition_raw = (out / 'acquisition.json').read_bytes()
    acquisition = json.loads(acquisition_raw)
    acquisition_sha256 = hashlib.sha256(acquisition_raw).hexdigest()
    lean, clean = bind_executable(args.lean_bin), bind_executable(args.clean_bin)
    version = executable_version(lean, args.timeout)
    if 'version 4.35.0,' not in version:
        raise ValueError('this cohort requires the acquired v4.35.0 oracle')
    if acquisition['world'] != 'v4.35.0':
        raise ValueError('wrong acquisition world')
    clean_version = executable_version(clean, args.timeout)
    rows = []
    fixtures = []
    seen = set()
    for entry in acquisition['files']:
        name = entry['path']
        path = (out / 'fixtures' / name).resolve()
        if not path.is_relative_to(out / 'fixtures') or path in seen:
            raise ValueError('unsafe or duplicate fixture path')
        seen.add(path)
        blob = checked_fixture_blob(path, entry)
        fixtures.append((path, entry))
        oracle = execute_bound(lean, ['--root=..', '-DprintMessageEndPos=true',
                                     '-Dlinter.all=false', '-DElab.inServer=true', path.name],
                               path.parent, args.timeout)
        checked_fixture_blob(path, entry)
        measured = execute_bound(clean, ['check', '--json', path.name],
                                 path.parent, args.timeout)
        checked_fixture_blob(path, entry)
        rows.append({'path': name, 'blob': blob, 'lean': oracle, 'clean': measured,
                     'outcome': classify(oracle, measured)})
        print(name, rows[-1]['outcome'], flush=True)
    bookends = {name: {'path': str(binding['path']),
                      'initial': {'identity': binding['identity'], 'sha256': binding['sha256']},
                      'final': finish_executable(binding)}
                for name, binding in [('lean', lean), ('clean', clean)]}
    for path, entry in fixtures:
        checked_fixture_blob(path, entry)
    if producer_path.read_bytes() != producer:
        raise ValueError('producer changed during measurement')
    report = {
        'schema': 'clean-false-accept-cohort-v1',
        'generated_at': datetime.now(timezone.utc).isoformat(),
        'acquisition_sha256': acquisition_sha256,
        'probe_sha256': hashlib.sha256(producer).hexdigest(),
        'wall_timeout_s': args.timeout,
        'lean_version': version, 'lean_sha256': lean['sha256'],
        'lean_binary': str(lean['path']),
        'clean_version': clean_version, 'clean_sha256': clean['sha256'],
        'clean_binary': str(clean['path']), 'executable_bookends': bookends,
        'provenance_scope': 'Resolved executable file identities checked around every invocation and hashes checked before versions/cohort and after the cohort. Acquired fixture hashes checked around each oracle invocation and after the cohort. Producer bytes captured before executable invocations and checked unchanged before publishing. Not a hermetic SDK, dependency or process trace.',
        'scope': 'Frozen historical false-accept cohort only; executable measurement, not checkout source qualification. Zero exit from Clean against oracle rejection is a false acceptance even with parser recovery.',
        'counts': dict(Counter(row['outcome'] for row in rows)), 'files': rows,
    }
    (out / ('producer-' + report['probe_sha256'][:12] + '.py.gz')).write_bytes(
        gzip.compress(producer, mtime=0))
    with output.open('x') as stream:
        stream.write(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
