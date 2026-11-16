#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Mint X1's true-mutual-group evidence with pinned Lean (under heavy_gate).

--negative-control inspects original acyclic c24, requires rejection by the
same constant-use predicate, and never writes the positive artifact.

CLEAN_X1_LEAN_BIN selects an installed Lean directly. Both selection routes
must pass the same exact pinned identity check before inspecting any probe.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'tests/fixtures/advice_replay_checker'
SELECTED_LEAN = os.environ.get('CLEAN_X1_LEAN_BIN')
LEAN = ([str(Path(SELECTED_LEAN).resolve(strict=True))] if SELECTED_LEAN is not None
        else ['elan', 'run', 'leanprover/lean4:v4.30.0-rc2', 'lean'])
PROBES = {
    'c34_r4_i_call_cycle_shared_counter': ['whnf', 'conv', 'infer'],
    'c35_r4_ix_walk_call_cycle': ['whnf', 'conv', 'walk'],
    'c36_r4_x_report_call_cycle': ['whnf', 'conv', 'walk'],
}


def lean_identity():
    version = subprocess.check_output(LEAN + ['--version'], text=True).strip()
    assert 'version 4.30.0-rc2,' in version, version
    assert version == (FIXTURE / 'expected/LEAN_VERSION').read_text().strip(), version
    return version


def inspect_probe(name, members):
    source = FIXTURE / 'programs' / (name + '.lean')
    with tempfile.TemporaryDirectory(prefix='x1-mutual-') as tmp:
        tmp = Path(tmp)
        (tmp / 'Probe.lean').write_bytes(source.read_bytes())
        subprocess.run(LEAN + ['-Dlinter.all=false', '-o', 'Probe.olean', 'Probe.lean'], cwd=tmp, check=True)
        names = ', '.join('``' + m for m in members)
        inspector = '''import Lean
import Probe
open Lean in
run_cmd do
  let env ← Lean.getEnv
  for n in [MEMBERS] do
    let some info := env.find? n | throwError "missing {n}"
    let some value := info.value? | throwError "no value {n}"
    logInfo m!"{n}: {value.getUsedConstants.toList}"
'''.replace('MEMBERS', names)
        (tmp / 'Inspect.lean').write_text(inspector)
        output = subprocess.check_output(LEAN + ['Inspect.lean'], cwd=tmp,
                                        env=dict(os.environ, LEAN_PATH=str(tmp)), text=True)
    uses = {}
    for member in members:
        match = re.search(r'^' + member + r': \[([^\]]+)\]$', output, re.M)
        assert match, output
        uses[member] = sorted(match[1].split(', '))
    print(output, end='')
    return {'program': name, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'source': source.read_text(), 'members': members, 'used_constants': uses}


def is_shared_group(probe):
    members, uses = probe['members'], probe['used_constants']
    return all('Nat.brecOn' in uses[member]
               and all(callee + '._f' in uses[member] for callee in members)
               for member in members)


def mint():
    version = lean_identity()
    rows = [inspect_probe(name, members) for name, members in PROBES.items()]
    assert all(is_shared_group(row) for row in rows), rows
    artifact = {'lean_version': version,
                'command': 'scripts/heavy_gate.sh run 2 x1-mutual-evidence -- python3 scripts/x1_mutual_evidence.py',
                'probes': rows}
    (FIXTURE / 'mutual_groups.json').write_text(json.dumps(artifact, indent=2) + '\n')


def negative_control():
    lean_identity()
    probe = inspect_probe('c24_r4_i_mutual_block_shared_counter', ['whnf', 'conv', 'infer'])
    assert not is_shared_group(probe), 'acyclic c24 incorrectly passed the mutual-group predicate'
    for member in probe['members']:
        used = probe['used_constants'][member]
        assert 'Nat.brecOn' in used and member + '._f' in used, probe
        assert all(callee + '._f' not in used for callee in probe['members'] if callee != member), probe
    print('X1_MUTUAL_NEGATIVE_CONTROL=refused acyclic c24: each member uses only its own _f')



if __name__ == '__main__':
    if sys.argv[1:] == ['--negative-control']:
        negative_control()
    elif sys.argv[1:]:
        raise SystemExit('usage: x1_mutual_evidence.py [--negative-control]')
    else:
        mint()
