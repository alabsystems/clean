#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Replay X1's four CLI regression mutations in an owned isolated worktree.

Run AFTER the default-feature large_stack_cli test passes and while no other
job is using this worktree. Every build/test is admitted separately. The
original production bytes are restored in finally, then rebuilt and re-tested.
Usage: python3 scripts/x1_fixup_mutations.py /absolute/path/to/large_stack_cli-test-binary
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / 'crates/clean-cli/src/lib.rs'
COMPILE = ROOT / 'crates/clean-native/src/compile.rs'
REPORT = ROOT / 'reports/x1-fixup/mutations.json'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    assert (ROOT / '.git').is_file(), 'use an isolated worktree, never the shared checkout'
    binary = Path(sys.argv[1]).resolve(strict=True)
    original = {p: p.read_bytes() for p in [LIB, COMPILE]}
    env = dict(os.environ, CARGO_TARGET_DIR=str(ROOT / 'target/x1-build'))
    rows = []
    logdir = ROOT / 'reports/x1-fixup/mutation-logs'
    logdir.mkdir(parents=True, exist_ok=True)
    report = {'test_binary': str(binary), 'test_binary_sha256': sha(binary.read_bytes()),
              'baseline_sources': {str(p.relative_to(ROOT)): sha(b) for p, b in original.items()}, 'runs': rows}

    def save():
        REPORT.write_text(json.dumps(report, indent=2) + '\n')

    def run(label, argv, expected):
        log = logdir / (label + '.log')
        with log.open('w') as out:
            # Each leg owns this process group. On interruption stop and reap
            # only that group before finally restores production source bytes.
            p = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=out,
                                 stderr=subprocess.STDOUT, start_new_session=True)
            try:
                p.wait()
            except BaseException:
                if p.poll() is None:
                    os.killpg(p.pid, signal.SIGTERM)
                    p.wait()
                raise
        row = {'label': label, 'command': [str(a) for a in argv], 'CARGO_TARGET_DIR': env['CARGO_TARGET_DIR'],
               'exit_code': p.returncode, 'expected_exit_code': expected, 'log': str(log.relative_to(ROOT))}
        rows.append(row)
        save()
        print(label, 'exit', p.returncode, 'expected', expected, flush=True)
        assert p.returncode == expected, row
        if expected == 101:
            text = log.read_text()
            assert '1 failed' in text and '0 passed' in text, text

    def build(label):
        run(label, ['scripts/heavy_gate.sh', 'run', '13', label, '--',
                    'targo', '--unverified', 'build', '--locked', '-p', 'clean'], 0)

    def test(label, name, code):
        run(label, ['scripts/heavy_gate.sh', 'run', '2', label, '--',
                    str(binary), '--exact', name, '--nocapture'], code)
        text = (logdir / (label + '.log')).read_text()
        if code == 0:
            assert '1 passed' in text and '0 failed' in text, text
        else:
            reasons = {
                'x1-mutation-run-route-test': ['the dispatched worker was named and observed'],
                'x1-mutation-compile-route-test': ['the dispatched worker was named and observed'],
                'x1-mutation-lower-cause-test': ['c28_r4_v_one_function_over_requests', 'native build cannot satisfy prelude extern'],
                'x1-mutation-probe-cause-test': ['c23_nat_literal_of_129_bits', 'native build cannot satisfy prelude extern'],
            }
            for reason in reasons[label]:
                assert reason in text, (label, reason, text)

    stack = 'run_and_compile_dispatch_get_a_large_stack_by_default'
    cause = 'source_dependency_refusal_keeps_the_lowering_cause'
    run('x1-mutation-fetch', ['targo', 'fetch', '--locked'], 0)
    test('x1-mutation-baseline-stack', stack, 0)
    test('x1-mutation-baseline-cause', cause, 0)
    lib = original[LIB].decode()
    comp = original[COMPILE].decode()
    run_route = '''        Commands::Run(args) => {
            large_stack::run_on_large_stack("clean-run", move || cmd_run::handle_run_command(args))?
        }'''
    compile_route = '''        Commands::Compile(args) => large_stack::run_on_large_stack("clean-compile", move || {
            cmd_compile::handle_compile_command(args)
        })?,'''
    lower_guard = '''                if policy
                    .source_decls
                    .is_some_and(|names| names.contains(&dep_name)) =>'''
    probe_guard = '''            if policy
                .source_decls
                .is_some_and(|names| names.contains(&dep_name))
            {'''
    mutations = [
        ('run-route', LIB, lib, run_route, '        Commands::Run(args) => cmd_run::handle_run_command(args)?,', stack),
        ('compile-route', LIB, lib, compile_route, '        Commands::Compile(args) => cmd_compile::handle_compile_command(args)?,', stack),
        ('lower-cause', COMPILE, comp, lower_guard, '                if false =>', cause),
        ('probe-cause', COMPILE, comp, probe_guard, '            if false {', cause),
    ]
    for _, _, text, before, _, _ in mutations:
        assert text.count(before) == 1, before
    try:
        for label, path, text, before, after, target in mutations:
            for p, b in original.items():
                p.write_bytes(b)
            path.write_text(text.replace(before, after, 1))
            build('x1-mutation-' + label + '-build')
            test('x1-mutation-' + label + '-test', target, 101)
    finally:
        for p, b in original.items():
            p.write_bytes(b)
        report['restored_sources'] = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in original}
        assert report['restored_sources'] == report['baseline_sources']
        save()
    build('x1-mutation-restored-build')
    test('x1-mutation-restored-stack', stack, 0)
    test('x1-mutation-restored-cause', cause, 0)
    report['restored_cli_sha256'] = sha((ROOT / 'target/x1-build/debug/clean').read_bytes())
    save()


if __name__ == '__main__':
    def stop(signum, frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, stop)
    main()
