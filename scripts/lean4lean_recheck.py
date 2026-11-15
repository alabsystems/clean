#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Qualify the pinned Lean4Lean quorum member and run it on one export.

Fetches and builds nothing; the binary is the one `data/lean4lean_q4_pin.json`
names by digest. Lean4Lean (`lean4lean --import`, the Lean Kernel Arena entry
point) prints `checked N declarations`, N counting its `addDecl` calls; it
skips unsafe and partial declarations and polices no axioms. So this runner
owns three things Lean4Lean does not: the declaration count it must report,
the subject's axioms (only Ax0, each at its pinned statement digest), and the
declarations it would skip (any makes a subject not accepted).

Every run is classified by how Lean4Lean ended (`DECISIONS`, before any
runner policy): its kernel accepted, its kernel refused and Lean4Lean reported
it, its kernel raised its exception and the error renderer then panicked, it
crashed before its kernel decided, or it is undecided (timeout, unrecognized
failure). A Lean `PANIC` (fatal here: LEAN_ABORT_ON_PANIC is set) is recorded
as a panic, never as a refusal and never as an acceptance. A crash before the
kernel decided is never judged, whatever its pinned signature. Exit 0 from
--out requires every arena case judged and every runner control refused for
its reason.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import tarfile
import tempfile
import time

import nanoda_recheck as nano

ROOT = Path(__file__).resolve().parents[1]
ARENA = nano.ARENA
PIN = 'data/lean4lean_q4_pin.json'
REASONS = 'data/lean4lean_q4_arena_reasons.json'
AX0 = nano.AX0
ANSWERS_PINNED_INPUTS = True
CHECKED = re.compile(r'^checked (\d+) declarations$')
TIMING = re.compile(r'^.*: lean4lean took \d+$')
PANIC = re.compile(r'PANIC at (\S+ \S+:\d+:\d+): ([^\n]*)')
EXPR_KEY = re.compile(rb'"ie":(\d+)')
# How Lean4Lean ended, before any runner policy. A panic is never a refusal;
# only `JUDGEABLE` decisions can match a bad arena case's pinned reason.
DECISIONS = {
    'accepted': 'the kernel added every declaration and Lean4Lean printed its count',
    'refused': 'the kernel raised its exception and Lean4Lean reported it '
               '(exit 1, `uncaught exception: ...`)',
    'kernel-raised-then-panicked': 'the kernel raised its exception '
                                   '(Lean4Lean.Replay.throwKernelException on the panic stack), then '
                                   'the error renderer panicked: a rejection whose reason is lost; '
                                   'recorded as a panic, never a refusal',
    'crashed-before-deciding': 'a panic with no kernel exception raised: no kernel verdict; never '
                               'judged, never a refusal',
    'undecided': 'a timeout or an unrecognized failure: not knowable here',
}
JUDGEABLE = ('refused', 'kernel-raised-then-panicked')
# The runner's own refusals on the Q3 controls, by control name.
RUNNER_CONTROLS = {'empty-export': 'empty-export',
                   'extra-axiom': 'axiom outside Ax0: q3_extra_axiom',
                   'wrong-statement-propext': 'Ax0 statement mismatch: propext'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def _level(levels, params, i):
    if i == 0:
        return ['zero']
    kind, v = levels[i]
    if kind == 'succ':
        return ['succ', _level(levels, params, v)]
    if kind in ('max', 'imax'):
        return [kind, _level(levels, params, v[0]), _level(levels, params, v[1])]
    if kind == 'param':
        return ['param', params.index(v)] if v in params else ['free', list(v)]
    raise ValueError(f'unknown level {kind}')


def _expr(exprs, names, levels, params, i, memo):
    if i in memo:
        return memo[i]
    kind, d = exprs[i]
    rec = lambda j: _expr(exprs, names, levels, params, j, memo)  # noqa: E731
    if kind == 'mdata':  # transparent to the kernel
        out = rec(d['expr'])
    elif kind == 'bvar':
        out = ['bvar', d]
    elif kind == 'sort':
        out = ['sort', _level(levels, params, d)]
    elif kind == 'const':
        out = ['const', list(names[d['name']]), [_level(levels, params, u) for u in d['us']]]
    elif kind == 'app':
        out = ['app', rec(d['fn']), rec(d['arg'])]
    elif kind in ('lam', 'forallE'):  # binder names and annotations are not kernel data
        out = [kind, rec(d['type']), rec(d['body'])]
    elif kind == 'letE':
        out = ['letE', rec(d['type']), rec(d['value']), rec(d['body'])]
    elif kind == 'proj':
        out = ['proj', list(names[d['typeName']]), d['idx'], rec(d['struct'])]
    elif kind in ('natVal', 'strVal'):
        out = [kind, d]
    else:
        raise ValueError(f'unknown expression {kind}')
    memo[i] = out
    return out


def model(data):
    """What Lean4Lean must report on `data`, and the subject's axioms.

    The count is Lean4Lean's `replay`: one per safe, non-partial definition,
    theorem, opaque and axiom record, one per safe inductive block, and one
    for the quotient. Each Ax0-named axiom's type is digested up to what the
    kernel ignores (binder names and annotations, mdata; universe parameters
    by position)."""
    lines = data.split(b'\n')
    names, levels, decls = {0: ()}, {}, []
    for line in lines:
        if not line or expr_id(line) is not None:
            continue
        r = json.loads(line)
        if 'in' in r:
            v = r.get('str', r.get('num'))
            names[r['in']] = names[v['pre']] + (v['str'] if 'str' in v else v['i'],)
        elif 'il' in r:
            kind = next(k for k in r if k != 'il')
            levels[r['il']] = (kind, names[r[kind]] if kind == 'param' else r[kind])
        elif 'meta' not in r and 'ie' not in r:
            decls.append(r)
    expected, unchecked, quot, axioms, need = 0, [], False, {}, {}
    for r in decls:
        kind = next(iter(r))
        d = r[kind]
        if kind == 'inductive':
            unsafe = any(t.get('isUnsafe') for t in d['types'])
            if unsafe:
                unchecked += ['.'.join(map(str, names[t['name']])) for t in d['types']]
            else:
                expected += 1
            continue
        name = '.'.join(map(str, names[d['name']]))
        if kind == 'quot':
            quot = True
            continue
        if d.get('isUnsafe') or d.get('safety') in ('unsafe', 'partial'):
            unchecked.append(name)
            continue
        expected += 1
        if kind == 'axiom':
            axioms[name] = d
            if name in AX0:
                need[name] = d['type']
    expected += 1 if quot else 0
    statements = {}
    if need:
        wanted, exprs = set(need.values()), {}
        for line in reversed(lines):
            ie = expr_id(line)
            if ie is None or ie not in wanted:
                continue
            r = json.loads(line)
            kind = next(k for k in r if k != 'ie')
            exprs[ie] = (kind, r[kind])
            body = r[kind]
            for key in ('fn', 'arg', 'type', 'body', 'value', 'struct', 'expr'):
                if isinstance(body, dict) and key in body:
                    wanted.add(body[key])
        for name, root in need.items():
            params = [names[p] for p in axioms[name]['levelParams']]
            canon = [len(params), _expr(exprs, names, levels, params, root, {})]
            statements[name] = sha(json.dumps(canon, separators=(',', ':'), ensure_ascii=False).encode())
    return dict(expected_checked=expected, unchecked=sorted(unchecked),
                axioms=sorted(axioms), ax0_statements=statements)


def expr_id(line):
    """The id of an expression record, read without parsing it. Only an
    expression record has the key `ie`, and a JSON string cannot hold an
    unescaped quote, so the key's bytes occur nowhere else."""
    m = EXPR_KEY.search(line)
    return int(m[1]) if m else None


def failure_signature(rc, out, err):
    if rc is None:
        return dict(kind='timeout', reason='timeout')
    panic = PANIC.search(err)
    if panic:
        return dict(kind='panic', location=panic[1], reason=panic[2].strip(),
                    after_kernel_exception='Lean4Lean.Replay.throwKernelException' in err)
    error = re.search(r'^uncaught exception: ([^\n]+)', err, re.M)
    if rc == 1 and error:
        return dict(kind='error', reason=error[1].strip())
    return dict(kind='unrecognized-failure', reason='no pinned diagnostic')


def decision(failure):
    """How Lean4Lean ended (`DECISIONS`), from its own failure signature."""
    if failure is None:
        return 'accepted'
    if failure['kind'] == 'error':
        return 'refused'
    if failure['kind'] == 'panic':
        return 'kernel-raised-then-panicked' if failure['after_kernel_exception'] else 'crashed-before-deciding'
    return 'undecided'


def sandbox_command(binary, wd):
    return nano.sandbox_command(binary, wd)[:-1] + ['--import', 'input.ndjson']


def run(binary, data, seconds, binary_digest):
    """Lean4Lean's own verdict on `data`, with no runner policy applied."""
    with tempfile.TemporaryDirectory(prefix='lean4lean-q4-') as td:
        wd = Path(td).resolve()
        (wd / 'input.ndjson').write_bytes(data)
        if nano.digest(binary) != binary_digest:
            raise ValueError('binary changed before checking')
        started = time.monotonic()
        proc = subprocess.Popen(sandbox_command(binary, wd), cwd=wd,
                                env={'PATH': '/usr/bin:/bin', 'HOME': str(wd), 'TMPDIR': str(wd),
                                     'LEAN_ABORT_ON_PANIC': '1'},
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        try:
            stdout, stderr = proc.communicate(timeout=seconds)
            rc = proc.returncode
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            stdout, stderr = proc.communicate()
            rc = None
        out = stdout.decode(errors='replace').replace(str(wd), '<scratch>')
        err = stderr.decode(errors='replace').replace(str(wd), '<scratch>')
        elapsed = time.monotonic() - started
    if nano.digest(binary) != binary_digest:
        raise ValueError('binary changed during checking')
    lines = [x for x in out.splitlines() if x.strip()]
    counts = [int(m[1]) for m in map(CHECKED.match, lines) if m]
    stray = [x for x in lines if not CHECKED.match(x) and not TIMING.match(x)]
    kernel_accepted = (rc == 0 and len(counts) == 1 and bool(lines) and CHECKED.match(lines[-1])
                       is not None and not stray and 'PANIC' not in out + err)
    peak = re.search(r'(\d+)\s+maximum resident set size', err)
    failure = None if kernel_accepted else failure_signature(rc, out, err)
    return dict(exit_status=rc, kernel_accepted=bool(kernel_accepted),
                checked_count=counts[0] if len(counts) == 1 else None,
                failure=failure, decision=decision(failure),
                input_sha256=sha(data), wall_seconds=elapsed,
                peak_rss_bytes=int(peak[1]) if peak else None,
                stdout=out.strip()[-20000:], stderr=err.strip()[-20000:],
                command=['sandbox-exec', '<network/credential-denying profile>', '/usr/bin/time', '-l',
                         '<digest-pinned lean4lean>', '--import', 'input.ndjson'],
                environment='PATH=/usr/bin:/bin HOME=TMPDIR=<scratch> LEAN_ABORT_ON_PANIC=1')


def policy(r, data, pin, ax0=True):
    """Apply the runner's count, coverage and (with `ax0`) axiom policy."""
    m = model(data)
    refusals = []
    if ax0:
        outside = [a for a in m['axioms'] if a not in AX0]
        if outside:
            refusals.append('axiom outside Ax0: ' + ', '.join(outside))
        wrong = [a for a, h in sorted(m['ax0_statements'].items()) if h != pin['ax0_statement_sha256'][a]]
        if wrong:
            refusals.append('Ax0 statement mismatch: ' + ', '.join(wrong))
        if m['unchecked']:
            refusals.append(f"declarations Lean4Lean skips: {len(m['unchecked'])}")
    if r['kernel_accepted'] and r['checked_count'] == 0:
        refusals.append('empty-export')
    elif r['kernel_accepted'] and r['checked_count'] != m['expected_checked']:
        refusals.append('declaration-count-mismatch')
    accepted = r['kernel_accepted'] and not refusals
    failure = r['failure']
    if r['kernel_accepted'] and refusals:
        failure = dict(kind='runner', reason=refusals[0])
    verdict = ('accepted' if accepted else 'panic' if failure['kind'] == 'panic'
               else 'not knowable here' if failure['kind'] in ('timeout', 'unrecognized-failure')
               else 'refused')
    return dict(r, model=m, runner_refusals=refusals, accepted=accepted, failure=failure,
                verdict=verdict, axioms=m['axioms'] if accepted else None,
                axiom_report='runner: the export inventory, Ax0 at pinned statement digests; Lean4Lean reports none')


def recheck(binary, data, seconds, binary_digest):
    pin = json.loads((ROOT / PIN).read_text())
    return policy(run(binary, data, seconds, binary_digest), data, pin)


def pinned_inputs():
    table = json.loads((ARENA / 'round-2026-09.table.json').read_text())
    arena = ARENA.relative_to(ROOT)
    return sorted({PIN, REASONS, 'scripts/nanoda_recheck.py', 'scripts/lean4lean_selftest.py',
                   str(arena / 'round-2026-09.table.json'),
                   str(arena / table['archive']['file'])} |
                  {nano.CONTROLS[n]['path'] for n in RUNNER_CONTROLS})


def judge(r, row, reasons):
    r.update(name=row['path'], expected=row['outcome'], expected_export_sha256=row['sha256'])
    r['undecided'] = r['decision'] not in ('accepted', *JUDGEABLE)
    if row['outcome'] == 'reject':
        r['expected_failure'] = reasons[row['path']]['failure']
        r['reason_matches'] = r['failure'] == r['expected_failure']
        # A crash before the kernel decided matches its pinned signature and
        # still decides nothing: it is never judged.
        r['judged'] = (not r['kernel_accepted'] and r['decision'] in JUDGEABLE
                       and r['reason_matches'])
    else:
        r['reason_matches'] = None
        r['judged'] = r['accepted']
    r['contradiction'] = not r['judged'] and not r['undecided']
    return r


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--pinned-inputs', action='store_true')
    ap.add_argument('--binary', type=Path)
    ap.add_argument('--out', type=Path)
    args = ap.parse_args(argv)
    if args.selftest:
        from lean4lean_selftest import selftest
        return selftest()
    if args.pinned_inputs:
        print('\n'.join(pinned_inputs())); return 0
    if not (args.binary and args.out):
        ap.error('--binary and --out are required')
    record = None
    def save():
        (args.out / 'verdict.json').write_text(json.dumps(record, indent=2) + '\n')
    try:
        pin_bytes = (ROOT / PIN).read_bytes()
        pin = json.loads(pin_bytes)
        binary = args.binary.resolve()
        if sys.platform != 'darwin' or nano.digest(binary) != pin['binary_sha256']:
            raise ValueError('platform or binary identity mismatch')
        table = json.loads((ARENA / 'round-2026-09.table.json').read_bytes())
        reason_table = json.loads((ROOT / REASONS).read_bytes())
        reasons = reason_table['fixtures']
        if (reason_table['binary_sha256'] != pin['binary_sha256']
                or set(reasons) != {r['path'] for r in table['tests'] if r['outcome'] == 'reject'}):
            raise ValueError('arena reason inventory mismatch')
        archive = ARENA / table['archive']['file']
        if nano.digest(archive) != nano.ARCHIVE_SHA or table['archive']['sha256'] != nano.ARCHIVE_SHA:
            raise ValueError('arena archive identity mismatch')
        args.out.mkdir(parents=True, exist_ok=False)
        commit, dirty = nano.repository_state()
        record = dict(schema='clean.lean4lean-recheck.v1', checker=pin, pin_sha256=sha(pin_bytes),
                      runner_sha256=nano.digest(__file__), git_commit=commit, dirty_status=dirty,
                      utc=datetime.now(timezone.utc).isoformat(), host=platform.platform(),
                      arena_reason_table_sha256=nano.digest(ROOT / REASONS),
                      qualification=[], runner_controls={}, qualified=False,
                      decisions=DECISIONS,
                      policy='arena: kernel verdicts, fixture axioms admitted; a panic after the kernel raised '
                             'its exception is judged on its pinned signature but counted as a panic, never a '
                             'refusal; a crash before the kernel decided, a timeout and an unrecognized '
                             'failure are never judged',
                      limitations='Implementation agreement, not a proof; Lean4Lean derives from the C++ '
                                  'kernel and may share its bugs. The quorum stays.')
        save()
        with tarfile.open(archive) as tar:
            files = {m.name: m for m in tar.getmembers() if m.isfile()}
            if set(files) != {r['path'] for r in table['tests']} or len(files) != nano.ARENA_COUNT:
                raise ValueError('arena inventory mismatch')
            for i, row in enumerate(table['tests']):
                data = tar.extractfile(files[row['path']]).read()
                if sha(data) != row['sha256']:
                    raise ValueError('arena case identity mismatch')
                r = policy(run(binary, data, row['timeout_s'] or 120, pin['binary_sha256']), data, pin, ax0=False)
                for k in ('stdout', 'model'):
                    r.pop(k)
                record['qualification'].append(judge(r, row, reasons)); save()
                print(f"arena {i + 1}/{len(table['tests'])} {row['path']} {r['verdict']} "
                      f"decision={r['decision']} judged={r['judged']}", flush=True)
        for name, reason in RUNNER_CONTROLS.items():
            control = nano.CONTROLS[name]
            data = (ROOT / control['path']).read_bytes()
            if sha(data) != control['sha256']:
                raise ValueError(f'{name}: committed control changed')
            r = policy(run(binary, data, 120, pin['binary_sha256']), data, pin)
            r['refused_for_reason'] = r['failure'] == dict(kind='runner', reason=reason)
            record['runner_controls'][name] = r; save()
        q = record['qualification']
        record['panics'] = sorted(r['name'] for r in q if r['failure'] and r['failure']['kind'] == 'panic')
        record['undecided'] = sorted(r['name'] for r in q if r['undecided'])
        record['decision_counts'] = {d: sum(r['decision'] == d for r in q) for d in DECISIONS}
        record['qualified'] = (all(r['judged'] for r in q) and len(q) == nano.ARENA_COUNT
                               and all(c['refused_for_reason'] for c in record['runner_controls'].values()))
        record['completed_utc'] = datetime.now(timezone.utc).isoformat()
        save()
        return 0 if record['qualified'] else 1
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, subprocess.SubprocessError) as exc:
        if record is not None:
            record['error'] = str(exc); save()
        print(f'lean4lean_recheck: identity/invocation failure: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
