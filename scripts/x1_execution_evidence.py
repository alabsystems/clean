#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Record X1 production CLI outcomes on both backends; run under heavy_gate.

Usage: python3 scripts/x1_execution_evidence.py [--report PATH] /absolute/path/to/clean [program...]
The output is evidence for explicit re-pinning, never an automatic green gate.
A full run also mints head_loop_samples in the artifact the Rust test reads,
but only if the live measurements still match its existing execution pins.
--mint-head-loop-samples validates and publishes an existing execution report
without re-running it; changed declared inputs refuse that operation.
--report names the execution report a unit writes (and the one
--mint-head-loop-samples reads); it defaults to X1's reports/x1-fixup/execution.json.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'tests/fixtures/advice_replay_checker'
HEAD_LOOP_SAMPLES = [(10000, 'c37_head_loop_10000'),
                     (100000, 'c37_head_loop_100000'),
                     (1000000, 'c27_r4_iv_head_loop_million'),
                     (10000000, 'c37_head_loop_10000000')]
# Every program runs on the default 8 MiB main-thread stack (`ulimit -s 8176`),
# set here so that no caller's larger limit hides a recursion that is not a loop.
STACK_KB = 8176


def default_stack():
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (STACK_KB * 1024, hard))


def run(command, cwd):
    p = subprocess.run(command, cwd=cwd, capture_output=True, timeout=600,
                       preexec_fn=default_stack)
    return {'command': [str(x) for x in command], 'exit_code': p.returncode,
            'stdout': p.stdout.decode(), 'stderr': p.stderr.decode()}


def outcome(record, expected, receipt=None):
    code, out, err = (record[k] for k in ['exit_code', 'stdout', 'stderr'])
    if receipt is not None and receipt['stage'] != 'built':
        classes = {'core': 'EMIT_TRUSTIR_REFUSED', 'trust-cg': 'TRUSTCG_REFUSED', 'link': 'LINK_FAILED'}
        return {'outcome': classes[receipt['stage']], 'refusal': receipt['step'] + ': ' + receipt['cause'].splitlines()[0]}
    if code == 0 and out == expected and not err:
        return {'outcome': 'BYTE_EQUAL', 'refusal': ''}
    if receipt is None and code == 1 and not out:
        line = next((l for l in err.splitlines() if l.startswith('Error: ')), None)
        if line:
            return {'outcome': 'REFUSED_BUILD', 'refusal': line}
    if code != 0 and expected.startswith(out):
        for line in err.splitlines():
            if 'clean panic: ' in line:
                return {'outcome': 'REFUSED_RUNTIME', 'refusal': line}
            if line.startswith('clean run: program terminated by signal '):
                return {'outcome': 'CRASHED', 'refusal': line}
    raise RuntimeError('Unclassifiable outcome: ' + json.dumps(record))


def input_identity():
    digest = hashlib.sha256()
    count = 0
    paths = list((ROOT / 'crates').rglob('*')) + [ROOT / p for p in [
        'Cargo.toml', 'Cargo.lock', '.cargo/config.toml', 'rust-toolchain.toml']]
    for path in sorted(paths):
        if not path.is_file() or path.suffix not in {'.rs', '.c', '.h', '.toml', '.lock'}:
            continue
        relative = path.relative_to(ROOT).as_posix()
        digest.update(relative.encode() + b'\0' + hashlib.sha256(path.read_bytes()).digest())
        count += 1
    return {'scope': 'crates/**/*.{rs,c,h,toml,lock}; root Cargo.toml, Cargo.lock, .cargo/config.toml, rust-toolchain.toml',
            'files': count, 'sha256': digest.hexdigest()}


def mint_head_loop_samples(report):
    """Publish samples only over unchanged inputs and unchanged execution pins."""
    assert report['inputs'] == input_identity(), 'production/source context changed: re-measure'
    path = ROOT / 'data/kcheck_execution_gaps.json'
    pins = json.loads(path.read_text())
    measured = {r['name']: r for r in report['programs']}
    programs = {r['name']: r for r in pins['programs']}
    samples = []
    base = (FIXTURE / 'programs/c27_r4_iv_head_loop_million.lean').read_text()
    for steps, name in HEAD_LOOP_SAMPLES:
        row = measured[name]
        source = FIXTURE / 'programs' / (name + '.lean')
        assert row['source_sha256'] == hashlib.sha256(source.read_bytes()).hexdigest(), name
        assert source.read_text() == base.replace('1000000', str(steps)).replace('1000001', str(steps + 1)), name
        expected = (FIXTURE / 'expected' / (name + '.stdout')).read_text()
        sample = {'steps': steps, 'program': name, 'clean_sha256': report['clean_sha256'],
                  'source_sha256': row['source_sha256'], 'measurement': {}}
        for lane in ['c_lane', 'trust_cg_lane']:
            record = row[lane]
            receipt = record.get('receipt')
            if lane == 'trust_cg_lane':
                assert receipt['stage'] == 'built', record
            live = outcome(record, expected, receipt)
            pin = programs[name][lane]
            assert live['outcome'] in ['BYTE_EQUAL', 'CRASHED'], live
            assert all(live[k] == pin[k] for k in ['outcome', 'refusal']), (name, lane, live, pin)
            sample[lane] = copy.deepcopy(pin)
            sample['measurement'][lane] = copy.deepcopy(record)
        samples.append(sample)
    pins['head_loop_samples'] = samples
    path.write_text(json.dumps(pins, indent=2, ensure_ascii=False) + '\n')
    print('X1_HEAD_LOOP_SAMPLES=minted n=%d' % len(samples), flush=True)


def main():
    args = sys.argv[1:]
    out = ROOT / 'reports/x1-fixup/execution.json'
    if args[:1] == ['--report']:
        out = (ROOT / args[1]).resolve()
        args = args[2:]
    if args == ['--mint-head-loop-samples']:
        report = json.loads(out.read_text())
        mint_head_loop_samples(report)
        return
    clean = Path(args[0]).resolve(strict=True)
    assert os.environ.get('CLEAN_TRUST_CG_BIN'), 'name the pinned trust-cg consumer'
    report = {'clean_sha256': hashlib.sha256(clean.read_bytes()).hexdigest(),
              'inputs': input_identity(),
              'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'lean_version': (FIXTURE / 'expected/LEAN_VERSION').read_text().strip(),
              'stack_kb': STACK_KB, 'programs': []}
    selected = set(args[1:])
    for source in sorted((FIXTURE / 'programs').glob('*.lean')):
        name = source.stem
        if selected and name not in selected:
            continue
        row = {'name': name, 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        expected = (FIXTURE / 'expected' / (name + '.stdout')).read_text()
        with tempfile.TemporaryDirectory(prefix='x1-run-') as tmp:
            row['check'] = run([str(clean), 'check', '--json', str(source)], tmp)
            checked = json.loads(row['check']['stdout'])
            row['check']['accepted_without_recovery'] = (row['check']['exit_code'] == 0
                and checked['status'] == 'pass' and not checked['parser_recovery'])
            for lane in ['c_lane', 'trust_cg_lane']:
                command = [str(clean), 'run', str(source), '--decl', 'main']
                receipt = None
                if lane == 'trust_cg_lane':
                    receipt_path = Path(tmp) / 'receipt.json'
                    command += ['--backend', 'trust-cg', '--receipt', str(receipt_path)]
                result = run(command, tmp)
                if lane == 'trust_cg_lane':
                    receipt = json.loads(receipt_path.read_text())
                    result['receipt'] = receipt
                result['pin'] = outcome(result, expected, receipt)
                row[lane] = result
                print(name, lane, result['pin'], flush=True)
        report['programs'].append(row)
        # Retain completed measurements even if a later program fails.
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=2) + '\n')
    if all(n in {r['name'] for r in report['programs']} for _, n in HEAD_LOOP_SAMPLES):
        mint_head_loop_samples(report)


if __name__ == '__main__':
    main()
