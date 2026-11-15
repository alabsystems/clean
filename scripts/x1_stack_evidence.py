#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Measure upstream compiled loops and Clean's stack sensitivity under heavy_gate.

Usage: python3 scripts/x1_stack_evidence.py /absolute/path/to/clean
Requires elan's explicitly pinned oracle and CLEAN_TRUST_CG_BIN for both lanes.
Stores commands, limits, return codes and exact bytes; no compiler correctness claim.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import tempfile

from x1_execution_evidence import input_identity

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'tests/fixtures/advice_replay_checker'
LEAN = ['elan', 'run', 'leanprover/lean4:v4.30.0-rc2']
NAMES = ['c37_head_loop_100000', 'c27_r4_iv_head_loop_million', 'c36_r4_x_report_call_cycle']


def capture(command, stack_kb=8192, cwd=ROOT):
    def limits():
        resource.setrlimit(resource.RLIMIT_STACK, (stack_kb * 1024, resource.getrlimit(resource.RLIMIT_STACK)[1]))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    p = subprocess.run([str(x) for x in command], cwd=cwd, capture_output=True,
                       timeout=600, preexec_fn=limits)
    return {'command': [str(x) for x in command], 'stack_kb': stack_kb,
            'exit_code': p.returncode, 'stdout': p.stdout.decode(), 'stderr': p.stderr.decode()}


def main():
    clean = Path(sys.argv[1]).resolve(strict=True)
    report = {'lean_toolchain': LEAN[2], 'clean_sha256': hashlib.sha256(clean.read_bytes()).hexdigest(),
              'inputs': input_identity(),
              'note': 'subprocess signal exits are negative signal numbers; shell 139 is signal 11',
              'programs': []}
    report['lean_identity'] = capture(LEAN + ['lean', '--version'])
    assert report['lean_identity']['stdout'].strip() == (FIXTURE / 'expected/LEAN_VERSION').read_text().strip()
    dest = ROOT / 'reports/x1-recheck/stack-comparison.json'
    dest.parent.mkdir(exist_ok=True)
    for name in NAMES:
        source = FIXTURE / 'programs' / (name + '.lean')
        expected = (FIXTURE / 'expected' / (name + '.stdout')).read_text()
        row = {'name': name, 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        row['lean_run'] = capture(LEAN + ['lean', '--run', source])
        assert row['lean_run']['exit_code'] == 0 and row['lean_run']['stdout'] == expected, row
        with tempfile.TemporaryDirectory(prefix='x1-stack-') as tmp:
            tmp = Path(tmp)
            c = tmp / 'probe.c'
            binary = tmp / 'probe'
            row['lean_emit_c'] = capture(LEAN + ['lean', '-c', c, source])
            assert row['lean_emit_c']['exit_code'] == 0, row
            row['lean_leanc'] = capture(LEAN + ['leanc', '-O3', '-o', binary, c])
            assert row['lean_leanc']['exit_code'] == 0, row
            ctext = c.read_text()
            row['lean_goto_start_count'] = ctext.count('goto _start;')
            loop_name = 'whnf' if name.startswith('c36') else 'headLoop'
            row['lean_self_tail_loops'] = {
                chunk.splitlines()[0]: chunk
                for chunk in re.split(r'(?=^LEAN_EXPORT )', ctext, flags=re.M)
                if loop_name in chunk.splitlines()[0] and 'goto _start;' in chunk
            }
            assert row['lean_self_tail_loops'], (name, 'missing upstream self tail loop')
            row['lean_binary'] = capture([binary])
            assert row['lean_binary']['exit_code'] == 0 and row['lean_binary']['stdout'] == expected, row
            row['clean'] = {}
            for lane in ['c', 'trust-cg']:
                args = [clean, 'run', source, '--decl', 'main', '--keep-temp']
                if lane == 'trust-cg':
                    args += ['--backend', lane, '--receipt', tmp / 'receipt.json']
                first = capture(args, cwd=tmp)
                match = re.search(r'kept build directory at (.+)', first['stderr'])
                assert match, first
                kept = Path(match[1])
                try:
                    executable = kept / 'program'
                    if not executable.is_file():
                        candidates = [p for p in kept.rglob('*') if p.is_file() and os.access(p, os.X_OK)]
                        assert len(candidates) == 1, candidates
                        executable = candidates[0]
                    measurements = [capture([executable], size) for size in [8192, 65520]]
                    row['clean'][lane] = {'build_and_run': first, 'binary_runs': measurements}
                    if lane == 'trust-cg':
                        row['clean'][lane]['receipt'] = json.loads((tmp / 'receipt.json').read_text())
                        assert row['clean'][lane]['receipt']['stage'] == 'built'
                    for sample in measurements:
                        assert expected.startswith(sample['stdout']), sample
                        assert sample['exit_code'] in [0, -11], sample
                        if sample['exit_code'] == 0:
                            assert sample['stdout'] == expected and not sample['stderr'], sample
                finally:
                    shutil.rmtree(kept)  # Only the directory this invocation retained.
        report['programs'].append(row)
        dest.write_text(json.dumps(report, indent=2) + '\n')
        print(name, {lane: [s['exit_code'] for s in result['binary_runs']]
                     for lane, result in row['clean'].items()}, flush=True)


if __name__ == '__main__':
    main()
