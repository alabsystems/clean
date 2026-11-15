#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""X5's bounded dependency inventory, not a semantic or binary validator.

Enumerate source paths in explicit runtime/link/CLI envelopes. Require exact
coverage and a decision approving each row's full contents. Source contents,
external dependency closure, compiled reachability and byte lineage are not
established by this gate. Tests are deliberately included in the envelopes.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = Path('data/kcheck_trusted_rows.json')
DECISIONS = Path('docs/DECISIONS.md')
SCOPES = {
    'runtime': ('crates/clean-runtime',),
    'native-link-and-shims': ('crates/clean-native',),
}
OPTIONAL_SCOPE = ('linked-kcheck-shell', 'crates/clean-kcheck')


def safe(root: Path, relative: str) -> Path:
    path = Path(relative)
    if path.is_absolute() or '..' in path.parts:
        raise ValueError(f'unsafe path: {relative}')
    current = root
    for part in path.parts:
        current /= part
        if current.is_symlink():
            raise ValueError(f'symlink in inventory path: {relative}')
    return current


def observed(root: Path) -> dict[str, list[str]]:
    result = {}
    scopes = dict(SCOPES)
    if safe(root, OPTIONAL_SCOPE[1]).exists():
        scopes[OPTIONAL_SCOPE[0]] = (OPTIONAL_SCOPE[1],)
    for key, directories in scopes.items():
        files = []
        for directory in directories:
            base = safe(root, directory)
            if not base.is_dir():
                raise ValueError(f'missing source envelope: {directory}')
            for path in base.rglob('*'):
                if path.is_symlink():
                    raise ValueError(f'symlink in source envelope: {path.relative_to(root)}')
                if path.is_file() and not any(
                    part in {'.git', 'target', '.lake'} for part in path.relative_to(base).parts
                ):
                    files.append(path.relative_to(root).as_posix())
        if not files:
            raise ValueError(f'empty source envelope: {key}')
        result[key] = sorted(files)
    cli = safe(root, 'crates/clean-cli/src')
    if not cli.is_dir():
        raise ValueError('missing CLI source envelope')
    files = set()
    for pattern in ('cmd_run*.rs', 'cmd_compile*.rs', 'cmd_native_runtime.rs'):
        for path in cli.glob(pattern):
            relative = path.relative_to(root).as_posix()
            if not safe(root, relative).is_file():
                raise ValueError(f'not a regular adapter source: {relative}')
            files.add(relative)
    required = {'cmd_run.rs', 'cmd_compile.rs', 'cmd_run_trustcg.rs', 'cmd_native_runtime.rs'}
    if not required <= {Path(p).name for p in files}:
        raise ValueError('missing required CLI adapters')
    result['cli-adapters'] = sorted(files)
    return result


def digest(row: dict) -> str:
    payload = {k: v for k, v in row.items() if k != 'decision'}
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def section(text: str, title: str) -> str:
    lines = text.splitlines()
    matches = [i for i, line in enumerate(lines) if line == title]
    if len(matches) != 1 or not re.fullmatch(r'#{1,6} .+', title):
        raise ValueError(f'decision heading missing or ambiguous: {title}')
    start = matches[0]
    level = len(title.split(' ', 1)[0])
    end = len(lines)
    for i in range(start + 1, len(lines)):
        match = re.match(r'^(#{1,6}) ', lines[i])
        if match and len(match[1]) <= level:
            end = i
            break
    return '\n'.join(lines[start:end])


def check(root: Path) -> int:
    artifact = json.loads(safe(root, str(ARTIFACT)).read_text())
    if artifact.get('schema') != 'clean.kcheck-trusted-rows/v1' or artifact.get('status') != 'pre-authority-inventory':
        raise ValueError('wrong schema or status: this inventory cannot claim compiled authority')
    if not isinstance(artifact.get('limits'), list) or not artifact['limits']:
        raise ValueError('inventory must state its limits')
    rows = artifact.get('rows')
    if not isinstance(rows, list):
        raise ValueError('rows must be a list')
    actual = observed(root)
    decisions = safe(root, str(DECISIONS)).read_text()
    seen = set()
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'id', 'files', 'responsibility', 'proof_status', 'decision'}:
            raise ValueError('row must contain exactly id/files/responsibility/proof_status/decision')
        key = row['id']
        if not isinstance(key, str) or key in seen:
            raise ValueError(f'duplicate or invalid row id: {key}')
        seen.add(key)
        if key not in actual or row['files'] != actual[key]:
            raise ValueError(f'source envelope differs for row {key}; inspect and record the change')
        if row['proof_status'] != 'unproved' or not isinstance(row['responsibility'], str) or not row['responsibility'].strip():
            raise ValueError(f'row {key} needs an explicit unproved responsibility')
        decision = row['decision']
        if not isinstance(decision, str):
            raise ValueError(f'invalid decision for row {key}')
        token = f'X5-ROW {key} sha256={digest(row)}'
        if token not in section(decisions, decision).splitlines():
            raise ValueError(f'row {key} has no exact decision approval: {token}')
    if seen != set(actual):
        raise ValueError(f'unlisted source envelopes: {sorted(set(actual) - seen)}')
    count = sum(len(files) for files in actual.values())
    print(f'KCHECK_TRUSTED_ROWS=ok rows={len(rows)} source_paths={count} status=pre-authority-inventory')
    return 0


def selftest() -> int:
    with tempfile.TemporaryDirectory(prefix='clean-x5-') as tmp:
        root = Path(tmp)
        for directory in ('data', 'docs', 'crates/clean-runtime/src', 'crates/clean-native/src', 'crates/clean-cli/src'):
            (root / directory).mkdir(parents=True)
        for path in ('crates/clean-runtime/src/lib.rs', 'crates/clean-native/src/lib.rs'):
            (root / path).write_text('// fixture\n')
        for name in ('cmd_run.rs', 'cmd_compile.rs', 'cmd_run_trustcg.rs', 'cmd_native_runtime.rs'):
            (root / 'crates/clean-cli/src' / name).write_text('// fixture\n')
        title = '## X5 fixture decision'
        data = {'schema': 'clean.kcheck-trusted-rows/v1', 'status': 'pre-authority-inventory',
                'limits': ['fixture; no semantic claim'], 'rows': [
                    {'id': key, 'files': files, 'responsibility': 'fixture', 'proof_status': 'unproved', 'decision': title}
                    for key, files in observed(root).items()]}
        approved = title + '\n' + '\n'.join(f"X5-ROW {r['id']} sha256={digest(r)}" for r in data['rows']) + '\n'
        def run(payload, text=approved):
            (root / ARTIFACT).write_text(json.dumps(payload))
            (root / DECISIONS).write_text(text)
            return subprocess.run([sys.executable, str(Path(__file__).resolve()), '--root', str(root)],
                                  capture_output=True, text=True)
        def expect(label, payload, signature, text=approved):
            result = run(payload, text)
            if result.returncode != 1 or signature not in result.stderr:
                raise AssertionError(f'{label}: wrong refusal {result.returncode}: {result.stdout}{result.stderr}')
            print(f'SELFTEST {label}=refused')
        if run(data).returncode != 0:
            raise AssertionError('honest fixture refused')
        print('SELFTEST honest=accepted')
        bad = copy.deepcopy(data); bad['rows'].pop()
        expect('missing-row', bad, 'unlisted source envelopes')
        bad = copy.deepcopy(data); bad['rows'].append(copy.deepcopy(bad['rows'][0]))
        expect('duplicate-row', bad, 'duplicate or invalid row id')
        bad = copy.deepcopy(data); bad['rows'][0]['responsibility'] = 'silently widened'
        expect('changed-row-with-old-decision', bad, 'no exact decision approval')
        expect('missing-decision', data, 'decision heading missing', '## Other decision\n')
        expect('approval-in-other-section', data, 'no exact decision approval', title + '\n## Other\n' + approved.split('\n', 1)[1])
        bad = copy.deepcopy(data); bad['status'] = 'compiled-authority'
        expect('authority-overclaim', bad, 'wrong schema or status')
        bad = copy.deepcopy(data); bad['rows'][0]['proof_status'] = 'proved'
        expect('unqualified-proof-claim', bad, 'explicit unproved responsibility')
        blob = root / 'crates/clean-runtime/src/runtime.blob'; blob.write_bytes(b'new dependency')
        expect('unlisted-nonstandard-file', data, 'source envelope differs')
        blob.unlink()
        new = root / 'crates/clean-runtime/src/added.rs'; new.write_text('// new runtime source\n')
        expect('new-runtime-source', data, 'source envelope differs')
        updated = copy.deepcopy(data)
        updated['rows'][0]['files'] = observed(root)['runtime']
        expect('new-source-with-old-decision', updated, 'no exact decision approval')
        text = title + '\n' + '\n'.join(f"X5-ROW {r['id']} sha256={digest(r)}" for r in updated['rows']) + '\n'
        if run(updated, text).returncode != 0:
            raise AssertionError('explicitly decided update refused')
        print('SELFTEST decided-update=accepted')
        new.unlink()
        new.symlink_to(root / 'crates/clean-runtime/src/lib.rs')
        expect('symlink-source', data, 'symlink in source envelope')
        new.unlink()
        future = root / OPTIONAL_SCOPE[1] / 'src'; future.mkdir(parents=True)
        (future / 'lib.rs').write_text('// future linked shell\n')
        expect('unlisted-linked-shell', data, 'unlisted source envelopes')
        print('KCHECK_TRUSTED_ROWS_SELFTEST=ok')
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    try:
        return selftest() if args.selftest else check(args.root.resolve())
    except (ValueError, OSError, KeyError, TypeError, AssertionError) as exc:
        print(f'KCHECK_TRUSTED_ROWS=refused {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
