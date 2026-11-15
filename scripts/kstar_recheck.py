#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Q4 engineering gate: every member reads one immutable snapshot per subject.

A subject is the Ax0 restriction of the export named by --subject
(`kstar_subjects.restrict`): every declaration whose axiom closure leaves Ax0
is removed and reported by name with its axioms; the rest is byte-identical.
Exit 0 requires all subjects accepted, equal member-owned Ax0 inventories,
qualified pinned Lean4Lean and all three fixed controls refused for their
pinned reasons. Missing tools, incomplete reports, crashes, panics and
timeouts never vote; a panic is recorded as a panic, not a refusal. Fenced
Clean's refusals are classified (`kstar_subjects.classify_clean`), never
filtered. --members is a local build receipt, not a claim of compiler
verification. --check-record checks the standing dated result and its exact
source inputs; it never promotes a red result. Binary availability is
required for replay.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import tempfile
import time

import kstar_subjects as subj
import lean4lean_recheck as l4l
import nanoda_recheck as nano

ROOT = Path(__file__).resolve().parents[1]
AX0 = sorted(nano.AX0)
ANSWERS_PINNED_INPUTS = True
MEMBERS = ('lean', 'clean-reference', 'ck0-stock', 'lean4lean')
CONTROL_NAMES = ('extra-axiom', 'ill-typed-body', 'forged-recursor')
# The pinned exports (CIC_L, Lean v4.30.0-rc2 Init) and their Ax0 restrictions.
SOURCE_PINS = {
    '6c6c68a02a925b183747f2a4f8969ea281285b0b07d23a9f1f287241d4e69499',
    '2d6910ddbb751d79c7b5688878e5e9ffcadee9299f60ec80f738d567454742f4',
}
SUBJECT_PINS = {
    '6c6c68a02a925b183747f2a4f8969ea281285b0b07d23a9f1f287241d4e69499',
    'f7e9f661e137da8b9b3d71a8487d9b2ef7f96a0fc953f219e5f50d5fe9bd2d3f',
}
# Lean4Lean's pinned refusal of each control (its kernel's, or the runner's
# Ax0 policy). A panic matches none: it is recorded as a panic, with its
# decision class (`l4l.DECISIONS`). The pinned build ends ill-typed-body as
# `kernel-raised-then-panicked` (its `Kernel.Exception.mapEnvM` leaves a
# `declTypeMismatch`'s environment unmapped, so the renderer reads a stale
# extension), and no invocation of it or later commit reports it cleanly
# (docs/DECISIONS.md, Q4 residuals): that control stays red with that cause.
LEAN4LEAN_CONTROLS = {
    'extra-axiom': dict(kind='runner', reason='axiom outside Ax0: q3_extra_axiom'),
    'ill-typed-body': dict(kind='error', reason="at forged_bad: (kernel) declaration type mismatch, 'forged_bad' has type"),
    'forged-recursor': dict(kind='error', reason='at forged_rec_false: (kernel) application type mismatch'),
}


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def pinned_inputs():
    return ['scripts/kstar_recheck.sh', 'scripts/kstar_recheck.py',
            'scripts/kstar_selftest.py', 'scripts/kstar_subjects.py',
            'scripts/kstar_subjects_selftest.py',
            'scripts/lean4lean_recheck.py', 'scripts/lean4lean_selftest.py',
            'scripts/nanoda_recheck.py',
            'scripts/lean_export_replay.sh', 'scripts/lean_export_replay/Upstream.lean',
            l4l.PIN, l4l.REASONS,
            *[nano.CONTROLS[n]['path'] for n in CONTROL_NAMES]]


def source_inputs():
    paths = ['Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', '.cargo/config.toml',
             'scripts/kstar_recheck.sh', 'scripts/kstar_recheck.py', 'scripts/kstar_selftest.py',
             'scripts/kstar_subjects.py', 'scripts/lean4lean_recheck.py',
             'scripts/lean4lean_selftest.py', 'scripts/nanoda_recheck.py',
             'scripts/lean_export_replay.sh', 'scripts/lean_export_mint.sh', 'scripts/heavy_gate.sh',
             'scripts/lean_export_replay/Upstream.lean', l4l.PIN, l4l.REASONS,
             'theories/cic_l/lean-toolchain', 'theories/cic_l/ORDER']
    for directory, suffixes in [('crates', ('.rs', '.toml')), ('theories/cic_l', ('.lean', '.toml'))]:
        paths += [str(p.relative_to(ROOT)) for p in (ROOT / directory).rglob('*')
                  if p.is_file() and p.suffix in suffixes and '.lake' not in p.parts]
    for name in CONTROL_NAMES:
        paths.append(nano.CONTROLS[name]['path'])
    return {p: digest(ROOT / p) for p in sorted(set(paths))}


def invoke(argv, seconds=600):
    started = time.monotonic()
    try:
        p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, cwd=ROOT, start_new_session=True)
        try:
            stdout, stderr = p.communicate(timeout=seconds)
            code = p.returncode
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            stdout, stderr = p.communicate()
            stderr += '\nquorum member timed out; its owned process group was stopped'
            code = None
        return dict(command=list(map(str, argv)), exit_code=code,
                    stdout=stdout, stderr=stderr, seconds=time.monotonic() - started)
    except OSError as e:
        return dict(command=list(map(str, argv)), exit_code=None, stdout='',
                    stderr=str(e), seconds=time.monotonic() - started)


def last_json(out):
    for line in reversed(out.splitlines()):
        try:
            obj = json.loads(line)
            if isinstance(obj, dict):
                return obj
        except ValueError:
            pass
    return {}


def component_name(parts):
    # ck0 emits tagged string/number components. Numeric Ax0 aliases cannot vote.
    if not all(isinstance(p, dict) and set(p) == {'str'} for p in parts):
        raise ValueError('non-string axiom component')
    return '.'.join(p['str'] for p in parts)


def evaluate(member, raw, expected_count, expected_axioms):
    """A zero exit alone is insufficient, including for an empty report."""
    obj = last_json(raw['stdout'])
    axioms, count, accepted = None, None, False
    try:
        if member == 'lean':
            axioms = sorted(obj['axioms'])
            count = obj['declarations']
            accepted = obj['verdict'] == 'accepted'
        elif member == 'clean-reference':
            axioms = sorted(obj['axioms'])
            count = obj['admitted']
            accepted = (obj['accepted'] is True and count == obj['declarations']
                        and not obj['refusals'] and not obj['unpermitted_axioms']
                        and obj['reader_error'] is None)
        elif member == 'ck0-stock':
            if obj['kind'] != 'coverage':
                raise ValueError('no completed coverage')
            axioms = sorted(component_name(a) for a in obj['axioms'])
            count = obj['accepted']
            accepted = count == obj['total'] and obj['refused'] == {}
        else:
            raise ValueError('unknown member')
        accepted = (accepted and raw['exit_code'] == 0 and count > 0
                    and count == expected_count and axioms == expected_axioms
                    and set(axioms) <= set(AX0))
    except (KeyError, TypeError, ValueError):
        accepted = False
    return dict(**raw, accepted=accepted, axioms=axioms, checked_count=count,
                verdict='accepted' if accepted else 'not knowable here' if raw['exit_code'] is None else 'refused')


def agreed(rows):
    return (set(rows) == set(MEMBERS) and all(r['accepted'] for r in rows.values())
            and len({tuple(r['axioms']) for r in rows.values()}) == 1)


def control_refused(member, name, row):
    if member == 'lean4lean':
        # The runner's Ax0 refusal follows a zero exit; a panic matches nothing.
        return not row['accepted'] and row.get('failure') == LEAN4LEAN_CONTROLS[name]
    if row['accepted'] or row.get('exit_code') in (None, 0):
        return False
    # Nonzero is not enough: require a control-specific kernel/policy diagnostic.
    text = row.get('stdout', '') + row.get('stderr', '')
    if name == 'extra-axiom':
        return 'q3_extra_axiom' in text and any(s in text.lower() for s in ('axiom', 'foundation'))
    if name == 'ill-typed-body':
        return any(s in text.lower() for s in ('type mismatch', 'typemismatch', 'not defeq', 'type-mismatch'))
    if member == 'lean':
        # Replay checks the forged use before comparing postponed recursors.
        # Pin that observed target; this is no isolated recursor-validation claim.
        return ("while replaying declaration 'forged_rec_false'" in text
                and 'application type mismatch' in text and '@FRT.rec' in text)
    if member == 'clean-reference':
        return ('FRT.rec: the structural tier refused it' in text
                and 'file (0, 0, 1, 0), kernel generates (0, 0, 1, 2)' in text)
    return 'malformed: recursor numMinors' in text


def identity(path):
    p = Path(path).resolve(strict=True)
    if not os.access(p, os.X_OK):
        raise ValueError(f'not executable: {p}')
    return dict(path=str(p), sha256=digest(p))


def prepare(args):
    receipt = json.loads(args.members.read_text())
    if receipt['source_inputs'] != source_inputs():
        raise ValueError('build receipt inputs differ from the current source')
    identities = {}
    for name in ('clean-reference', 'ck0-stock'):
        entry = receipt[name]
        if entry['build_exit_code'] != 0:
            raise ValueError(f'{name}: build did not complete')
        actual = identity(entry['binary']['path'])
        if actual != entry['binary']:
            raise ValueError(f'{name}: binary identity changed')
        identities[name] = entry
        print(f"kstar member {name}: {entry['lane']}; {entry['compiler_version'].splitlines()[0]}", flush=True)
    stock = receipt['ck0-stock']
    if stock['lane'] != 'STOCK EXCEPTION' or 'trust' in stock['compiler_version'].lower():
        raise ValueError('ck0 has no stock compiler build receipt')
    if digest(stock['compiler_path']) != stock['compiler_sha256']:
        raise ValueError('stock compiler identity changed')
    lean = Path.home() / '.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'
    gh = invoke([str(lean), '--githash'])
    if gh['exit_code'] != 0 or gh['stdout'].strip() != '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc':
        raise ValueError('pinned Lean unavailable or wrong commit')
    identities['lean'] = dict(binary=identity(lean), commit=gh['stdout'].strip(),
                              toolchain='leanprover/lean4:v4.30.0-rc2',
                              reader='lean4export Export.parseStream at 12581a6b680d8478175596338eb2d53383a323e3',
                              runtime={p.name: digest(p) for p in sorted((lean.parent.parent / 'lib/lean').glob('*.dylib'))})
    pin = json.loads((ROOT / l4l.PIN).read_text())
    binary = args.lean4lean or Path.home() / '.cache/clean-lean4lean/sha256' / pin['binary_sha256'] / 'lean4lean'
    actual = identity(binary)
    if actual['sha256'] != pin['binary_sha256']:
        raise ValueError('lean4lean binary differs from its pin')
    identities['lean4lean'] = dict(binary=actual, commit=pin['commit'], toolchain=pin['lean_toolchain'],
                                   lean_githash=pin['lean_githash'], repository=pin['repository'])
    return identities


def replay(data, ids, timeout, graph, excluded=()):
    inv = nano.inventory(data)
    expected_axioms = inv['axioms']
    count = len(inv['declarations'])
    with tempfile.TemporaryDirectory(prefix='kstar-') as td:
        path = Path(td) / 'subject.ndjson'
        path.write_bytes(data)
        permits = sum((['--permit', a] for a in AX0), [])
        commands = {
            'lean': [str(ROOT / 'scripts/lean_export_replay.sh'), '--reader', 'upstream', str(path), *permits],
            'clean-reference': [ids['clean-reference']['binary']['path'], '--reference', '--json', str(path), *permits],
            'ck0-stock': [ids['ck0-stock']['binary']['path'], str(path)],
        }
        rows = {name: evaluate(name, invoke(cmd, timeout), count, expected_axioms)
                for name, cmd in commands.items()}
        pin = ids['lean4lean']['binary']
        r = l4l.recheck(Path(pin['path']), data, timeout, pin['sha256'])
        r['accepted'] = (r['accepted'] and r['axioms'] == expected_axioms
                         and r['checked_count'] == r['model']['expected_checked'])
        r.pop('model')
        if not r['accepted'] and r['verdict'] == 'accepted':
            r['verdict'] = 'refused'
        rows['lean4lean'] = dict(r, exit_code=r['exit_status'], seconds=r['wall_seconds'])
        if path.read_bytes() != data:
            raise ValueError('member modified the subject snapshot')
    clean = rows['clean-reference']
    if not clean['accepted']:
        report = last_json(clean['stdout'])
        if isinstance(report.get('refusals'), list):
            c = subj.classify_clean(report['refusals'], graph, excluded)
            c['consistent'] = (c['refused'] == c['left_out'] == report['declarations'] - report['admitted']
                               and not c['unresolved'])
            clean['classification'] = c
    ck0 = rows['ck0-stock']
    if not ck0['accepted']:
        ck0['refusal'] = last_json(ck0['stdout'])
    for name, entry in ids.items():
        if digest(entry['binary']['path']) != entry['binary']['sha256']:
            raise ValueError(f'{name}: binary changed during replay')
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data), declarations=count,
                input_axioms=expected_axioms, members=rows, accepted=agreed(rows))


def check_record(path):
    try:
        r = json.loads(path.read_text())
        if r['source_inputs'] != source_inputs():
            raise ValueError('stale source inputs')
        if not r['success'] or not r['subjects'] or not r['qualified_lean4lean']:
            raise ValueError('record is red or incomplete')
        if (len(r['subjects']) != len(SUBJECT_PINS)
                or {s['sha256'] for s in r['subjects']} != SUBJECT_PINS
                or {s['source_sha256'] for s in r['subjects']} != SOURCE_PINS):
            raise ValueError('standing record does not cover the two pinned subjects')
        if set(r['identities']) != set(MEMBERS):
            raise ValueError('standing record lacks a member identity')
        if not all(agreed(s['members']) for s in r['subjects']):
            raise ValueError('a subject lacks every member acceptance')
        if set(r['controls']) != set(CONTROL_NAMES) or not all(
            control_refused(m, n, c['members'][m]) for n, c in r['controls'].items() for m in MEMBERS):
            raise ValueError('a control lacks a member refusal')
        if any(c['sha256'] != nano.CONTROLS[n]['sha256'] for n, c in r['controls'].items()):
            raise ValueError('standing control bytes differ from the committed pins')
        for name, entry in r['identities'].items():
            if identity(entry['binary']['path']) != entry['binary']:
                raise ValueError(f'{name}: binary unavailable or changed')
        print('KSTAR_RECHECK=accepted'); return 0
    except (OSError, ValueError, KeyError, TypeError) as e:
        print(f'KSTAR_RECHECK=not knowable here: {e}'); return 1


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--pinned-inputs', action='store_true')
    ap.add_argument('--check-record', type=Path)
    ap.add_argument('--members', type=Path)
    ap.add_argument('--lean4lean', type=Path)
    ap.add_argument('--subject', type=Path, action='append')
    ap.add_argument('--out', type=Path)
    ap.add_argument('--timeout', type=int, default=600)
    args = ap.parse_args()
    if args.selftest:
        from kstar_selftest import selftest
        return selftest()
    if args.pinned_inputs:
        print('\n'.join(pinned_inputs())); return 0
    if args.check_record:
        return check_record(args.check_record)
    if not args.members or not args.subject or not args.out:
        print('KSTAR_RECHECK=not knowable here: --members, --subject and --out required')
        return 1
    record = dict(source_commit=invoke(['git', 'rev-parse', 'HEAD'])['stdout'].strip(),
                  dirty_status=invoke(['git', 'status', '--porcelain'])['stdout'],
                  schema='clean.kstar-recheck.v1', utc=datetime.now(timezone.utc).isoformat(),
                  success=False, qualified_lean4lean=False, subjects=[], controls={}, source_inputs=source_inputs(),
                  limits='Implementation agreement, not semantic soundness. Per-bound claims only; no generation exceeds its base; independent quorum required.')
    args.out.mkdir(parents=True, exist_ok=False)
    def save():
        (args.out / 'replay.json').write_text(json.dumps(record, indent=2) + '\n')
    save()
    try:
        ids = prepare(args)
        record['identities'] = ids; save()
        # Arena qualification is executed afresh; no historical JSON can confer a vote.
        binary = ids['lean4lean']['binary']['path']
        rc = l4l.main(['--binary', binary, '--out', str(args.out / 'lean4lean-qualification')])
        record['qualified_lean4lean'] = rc == 0
        record['lean4lean_qualification_exit'] = rc; save()
        # Run every member even after a finding; never filter the subject
        # beyond its Ax0 restriction, whose removals are named.
        for path in args.subject:
            source = path.read_bytes()
            data, excluded, graph = subj.restrict(source)
            row = replay(data, ids, args.timeout, graph, [n for e in excluded for n in e['names']])
            row.update(path=str(path.resolve()), source_sha256=hashlib.sha256(source).hexdigest(),
                       source_bytes=len(source), excluded=excluded,
                       restriction='kstar_subjects.restrict: declarations whose axiom closure leaves Ax0, removed by name')
            record['subjects'].append(row); save()
        for name in CONTROL_NAMES:
            control = nano.CONTROLS[name]
            path = ROOT / control['path']
            if digest(path) != control['sha256']:
                raise ValueError(f'{name}: committed control changed')
            data = path.read_bytes()
            # A control is replayed as committed, never restricted.
            row = replay(data, ids, args.timeout, subj.restrict(data)[2])
            row['all_refused_for_reason'] = all(control_refused(m, name, row['members'][m]) for m in MEMBERS)
            row['refused_for_reason'] = {m: control_refused(m, name, row['members'][m]) for m in MEMBERS}
            row['panicked'] = sorted(m for m, r in row['members'].items() if r.get('verdict') == 'panic')
            record['controls'][name] = row; save()
        if source_inputs() != record['source_inputs']:
            raise ValueError('source inputs changed during replay')
        record['success'] = (record['qualified_lean4lean'] and all(s['accepted'] for s in record['subjects'])
                             and all(c['all_refused_for_reason'] for c in record['controls'].values()))
        save()
        print('KSTAR_RECHECK=' + ('accepted' if record['success'] else 'refused: see replay.json'))
        return 0 if record['success'] else 1
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as e:
        record['error'] = str(e); save()
        print(f'KSTAR_RECHECK=not knowable here: {e}'); return 1


if __name__ == '__main__':
    sys.exit(main())
