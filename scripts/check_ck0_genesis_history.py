#!/usr/bin/env python3
"""Untrusted checks that historical seed entry points refuse without promotion.

Copies exact public script bytes into owned fixtures, never invokes real Rust,
and observes exit/output, known command sentinels and final filesystem state.
This is not a sandbox, continuous write monitor, proof, build or Q6 completion.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import shlex
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HISTORY = 'genesis/ck0/MANIFEST.txt'
ENTRYPOINTS = ('genesis/ck0/generate_manifest.sh', 'genesis/ck0/verify.sh')
HISTORICAL_SHA256 = '12552fdf6250c74d0a3115cfd304d9724c93b438202c78367b8065e72c220c81'
MAX_SOURCE_BYTES = 64 * 1024
ANSWERS_PINNED_INPUTS = True
TOOLS = ('git', 'trustc', 'targo', 'rustc', 'cargo', 'find', 'sha256sum', 'shasum')


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
    return tempfile.TemporaryDirectory(prefix='q6-genesis-history-', dir=parent)


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
                    result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True,
                                            text=True, timeout=5)
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
                except (ValueError, OSError) as error:
                    need(reason in str(error), label + ': wrong refusal: ' + str(error))
                    outcomes.append({'case': label, 'refused': True, 'reason': str(error)})
                else:
                    raise ValueError('negative control accepted: ' + label)
            finally:
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
    print(json.dumps({'positive': positive, 'negative_controls': len(outcomes),
                      'outcomes': outcomes, 'proof_claim': False, 'q6_complete': False}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selftest', action='store_true')
    parser.add_argument('--pinned-inputs', action='store_true')
    args = parser.parse_args()
    need(not (args.selftest and args.pinned_inputs), 'conflicting action modes')
    if args.pinned_inputs:
        print('\n'.join((HISTORY, *ENTRYPOINTS)))
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
