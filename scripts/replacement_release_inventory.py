#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Freeze complete upstream file scope and release delta from GitHub tree responses.

Acquisition (GitHub access uses agh):
  agh api 'repos/leanprover/lean4/git/trees/<commit>?recursive=1' > tree.json

This inventories files, not semantic capabilities or test verdicts. No file is
credited as passed. Includes sidecars, scripts and generated stage0 sources so
unclassified surface cannot disappear through a source-extension filter.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

WORLDS = {
    'v4.30.0-rc2': '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc',
    'v4.35.0': 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc',
}


def load_tree(path, expected):
    raw = Path(path).read_bytes()
    if str(path).endswith('.gz'):
        raw = gzip.decompress(raw)
    data = json.loads(raw)
    if data.get('sha') != expected or data.get('truncated') is not False:
        raise ValueError('wrong revision or incomplete upstream tree')
    files = {}
    seen = set()
    for entry in data['tree']:
        name = entry['path']
        if (not name or name.startswith('/') or '..' in PurePosixPath(name).parts
                or str(PurePosixPath(name)) != name or name in seen):
            raise ValueError(f'invalid or duplicate upstream path: {name!r}')
        seen.add(name)
        if entry['type'] == 'tree':
            continue
        if entry['type'] not in ('blob', 'commit'):
            raise ValueError(f'unknown git object type: {entry["type"]}')
        if not re.fullmatch('[0-9a-f]{40}', entry['sha']):
            raise ValueError(f'invalid git object id: {name}')
        files[name] = {'blob': entry['sha'], 'mode': entry['mode'], 'type': entry['type']}
    for prefix in ('tests/elab/', 'src/Lean/', 'src/Init/', 'src/lake/', 'src/runtime/'):
        if not any(name.startswith(prefix) for name in files):
            raise ValueError(f'missing required source surface: {prefix}')
    return files, hashlib.sha256(raw).hexdigest()


def area(path):
    if path.startswith('tests/'):
        return '/'.join(path.split('/')[:2]) if path.count('/') > 1 else 'tests/harness'
    for prefix, label in (
        ('src/lake/', 'lake-source'), ('src/Init/', 'init-source'),
        ('src/Std/', 'std-source'), ('src/Lean/', 'lean-source'),
        ('src/kernel/', 'kernel-source'), ('src/runtime/', 'runtime-source'),
        ('src/', 'other-source'), ('stage0/', 'stage0-generated'),
        ('doc/', 'documentation'),
    ):
        if path.startswith(prefix):
            return label
    return 'other-upstream'


def inventory(old, new):
    rows = []
    for path in sorted(old.keys() | new.keys()):
        before, after = old.get(path), new.get(path)
        change = ('added' if before is None else 'removed' if after is None
                  else 'unchanged' if before == after else 'changed')
        rows.append({'id': path, 'area': area(path), 'change': change,
                     'baseline': before, 'target': after,
                     'qualification': 'not-measured' if after else 'baseline-only'})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-tree', required=True)
    parser.add_argument('--target-tree', required=True)
    parser.add_argument('--out-dir', required=True)
    args = parser.parse_args()
    baseline, old_hash = load_tree(args.baseline_tree, WORLDS['v4.30.0-rc2'])
    target, new_hash = load_tree(args.target_tree, WORLDS['v4.35.0'])
    rows = inventory(baseline, target)
    manifest = {'schema': 'clean-replacement-file-inventory-v1',
                'worlds': WORLDS, 'files': rows}
    encoded = (json.dumps(manifest, sort_keys=True, separators=(',', ':')) + '\n').encode()
    counts = {}
    for row in rows:
        counts.setdefault(row['area'], Counter())[row['change']] += 1
    summary = {
        'schema': 'clean-replacement-file-inventory-summary-v1',
        'worlds': WORLDS, 'acquired': '2026-11-12',
        'input_sha256': {'baseline': old_hash, 'target': new_hash},
        'manifest_sha256': hashlib.sha256(encoded).hexdigest(),
        'baseline_files': len(baseline), 'target_files': len(target),
        'changes': dict(Counter(row['change'] for row in rows)),
        'areas': {key: dict(value) for key, value in sorted(counts.items())},
        'semantic_cases_measured': 0,
        'remaining_inventory': ['CLI flags and invocation contracts',
                                'LSP/infoview methods and wire contracts',
                                'runtime externs and ABI contracts',
                                'individual cases and harness options inside test files',
                                'Mathlib corpus at compatible pinned revision'],
        'claim': 'Complete upstream tracked-file inventory and hash delta only; no parity verdicts.',
    }
    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    (out / 'files.json.gz').write_bytes(gzip.compress(encoded, mtime=0))
    (out / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: summary[key] for key in
                      ('baseline_files', 'target_files', 'changes')}, indent=2))


if __name__ == '__main__':
    main()
