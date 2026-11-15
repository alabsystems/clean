#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Qualify the committed nanoda pin and re-check an explicitly named subject.

Fetches nothing. Exit 0 requires an accepted expect:accept subject, qualification,
all pinned controls, statement/count/inventory agreement and unchanged binary.
Exit 1 records a measured failure; exit 2 is invocation/identity failure.
A matched Rust panic is an observed failure signature, not a deliberate refusal.
"""
import argparse
from datetime import datetime, timezone
import gzip
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

ROOT = Path(__file__).resolve().parents[1]
ARENA = ROOT / 'crates/clean-olean/tests/fixtures/kernel_arena/round-2026-09'
REPORT = 'reports/self-proof-q3-2026-11-12/'
ARENA_COUNT = 193
ARCHIVE_SHA = '98a69742b538296c5f413d0527dfeef8c4d1815fe64b12c8623cd33de63bee0d'
AX0_STATEMENTS = {
    'propext': 'axiom propext {a b : Prop} : Iff a b → Eq a b',
    'Quot.sound': 'axiom Quot.sound.{u} {α : Sort u} {r : α → α → Prop} {a b : α} : r a b → Eq (Quot.mk r a) (Quot.mk r b)',
    'Classical.choice': 'axiom Classical.choice.{u} {α : Sort u} : Nonempty α → α',
}
AX0 = sorted(AX0_STATEMENTS)
UNSUPPORTED = {
    'good/other/level-index-out-of-order.ndjson': 'Declined: Level back-reference mismatch',
    'good/other/sparse-name-index.ndjson': 'Declined: Name back-reference mismatch',
}
# Path, bytes, policy and reason are runner-owned, never caller-selected.
CONTROLS = {}  # populated below with literal digest pins
ANSWERS_PINNED_INPUTS = True


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(p):
    return sha(Path(p).read_bytes())


def resolve(p):
    p = Path(p)
    return (p if p.is_absolute() else ROOT / p).resolve()


def inventory(data, permitted=AX0):
    """Decode names without flattening away string/number component identity."""
    names = {0: ()}
    declarations, axioms = [], []
    for line in data.splitlines():
        r = json.loads(line)
        if 'in' in r:
            v = r.get('str', r.get('num'))
            part = v['str'] if 'str' in v else v['i']
            names[r['in']] = names[v['pre']] + (part,)
        for kind in ('axiom', 'def', 'thm', 'opaque', 'quot', 'inductive'):
            if kind not in r:
                continue
            d = r[kind]
            entries = sum((d[k] for k in ('types', 'ctors', 'recs')), []) if kind == 'inductive' else [d]
            for entry in entries:
                parts = names[entry['name']]
                name = '.'.join(map(str, parts))
                if kind == 'axiom':
                    axioms.append(name)
                    # Nanoda flattens names for its whitelist. Reject aliases of Ax0.
                    if name in AX0 and parts != tuple(name.split('.')):
                        raise ValueError('ambiguous Ax0 name components')
                    if name not in permitted:
                        continue
                declarations.append(name)
    return dict(declarations=sorted(declarations), axioms=sorted(axioms))


def failure_signature(rc, err):
    if rc is None:
        return dict(kind='timeout', reason='timeout')
    panic = re.search(r'panicked at (src/[^\n]+):\n(.*?)(?=\nnote:|\Z)', err, re.S)
    if rc == 101 and panic:
        return dict(kind='panic', location=panic[1], reason=panic[2].strip())
    error = re.search(r'^Error: ([^\n]+)', err, re.M)
    if rc == 1 and error:
        return dict(kind='error', reason=error[1])
    return dict(kind='unrecognized-failure', reason='no pinned diagnostic')


def sandbox_command(binary, wd):
    profile = f'''(version 1)
(allow default)
(deny network*)
(deny file-read* (subpath "/Users") (subpath "/Volumes") (subpath "/Library/Keychains"))
(allow file-read-metadata)
(deny file-write*)
(allow file-write* (subpath "{wd}"))
'''
    return ['/usr/bin/sandbox-exec', '-p', profile, '/usr/bin/time', '-l', str(binary), 'config.json']


def run(binary, data, permitted, hard, seconds, binary_digest):
    # Snapshot once: inventory, written bytes and recorded digest share these bytes.
    inv = inventory(data, permitted)
    with tempfile.TemporaryDirectory(prefix='nanoda-q3-') as td:
        wd = Path(td).resolve()
        (wd / 'input.ndjson').write_bytes(data)
        cfg = dict(export_file_path='input.ndjson', num_threads=1,
                   stack_size_bytes=1073741824, permitted_axioms=permitted,
                   unpermitted_axiom_hard_error=hard, nat_extension=True,
                   string_extension=True, print_success_message=True, print_axioms=True, pp_to_stdout=True)
        (wd / 'config.json').write_text(json.dumps(cfg))
        if digest(binary) != binary_digest:
            raise ValueError('binary changed before checking')
        started = time.monotonic()
        proc = subprocess.Popen(sandbox_command(binary, wd), cwd=wd,
                                env={'PATH': '/usr/bin:/bin', 'HOME': str(wd),
                                     'TMPDIR': str(wd), 'RUST_BACKTRACE': '0'},
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        try:
            stdout, stderr = proc.communicate(timeout=seconds)
            rc = proc.returncode
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            stdout, stderr = proc.communicate()
            rc = None
        out, err = stdout.decode(errors='replace'), stderr.decode(errors='replace')
        elapsed = time.monotonic() - started
        out, err = out.replace(str(wd), '<scratch>'), err.replace(str(wd), '<scratch>')
    if digest(binary) != binary_digest:
        raise ValueError('binary changed during checking')
    peak = re.search(r'(\d+)\s+maximum resident set size', err)
    counts = re.findall(r'^Checked (\d+) declarations with no errors(?:, skipping exported but unpermitted axioms .*|)$', out, re.M)
    count = int(counts[0]) if len(counts) == 1 else None
    statements = re.findall(r'^axiom .+$', out, re.M)
    reported = sorted(s.split()[1].split('.{')[0] for s in statements)
    checker_accepted = rc == 0 and count is not None
    count_ok = count is not None and count > 0 and count == len(inv['declarations'])
    return dict(config=cfg, reported_axioms=reported, reported_axiom_statements=statements,
                input_sha256=sha(data), export_axioms=inv['axioms'], declaration_names=inv['declarations'],
                checked_count=count, count_consistent=count_ok, checker_accepted=checker_accepted,
                permitted_axioms=permitted, unpermitted_axiom_hard_error=hard, exit_status=rc,
                accepted=checker_accepted and count_ok, failure=failure_signature(rc, err),
                wall_seconds=elapsed, peak_rss_bytes=int(peak[1]) if peak else None,
                stdout=out.strip(), stderr=err.strip(),
                command=['sandbox-exec', '<credential/network-denying profile>', '/usr/bin/time', '-l', '<digest-pinned nanoda>', 'config.json'])


def qualification_result(r, row, reasons):
    unsupported = (row['path'] in UNSUPPORTED and row['outcome'] == 'accept'
                   and r['exit_status'] == 2 and UNSUPPORTED[row['path']] in r['stderr'])
    r.update(name=row['path'], expected=row['outcome'], unsupported=unsupported,
             expected_export_sha256=row['sha256'])
    if row['outcome'] == 'reject':
        r['expected_failure'] = reasons[row['path']]['failure']
        r['target_evidence'] = reasons[row['path']]['target_evidence']
        r['reason_matches'] = r['failure'] == r['expected_failure']
        r['judged'] = not r['checker_accepted'] and r['reason_matches']
        r['contradiction'] = r['checker_accepted'] or not r['reason_matches']
    else:
        r['reason_matches'] = None
        r['judged'] = r['accepted'] or unsupported
        r['contradiction'] = not r['judged']
    return r


def evaluate_recheck(r, row, sidecar):
    admitted = sorted(set(r['export_axioms']) & set(AX0))
    expected_statements = sorted(AX0_STATEMENTS[a] for a in admitted)
    r['axiom_report_consistent'] = (r['reported_axioms'] == admitted and
                                   sorted(r['reported_axiom_statements']) == expected_statements)
    # Sidecar counts exclude omitted axioms and name requirements must be declarations.
    r['mint_consistent'] = (sidecar['export']['sha256'] == r['input_sha256'] and
                            sidecar['checked_declaration_count'] == r['checked_count'] and
                            set(sidecar['decls']) <= set(r['declaration_names']) and
                            sidecar['admitted_declaration_names'] == r['declaration_names'])
    failures = []
    if not r['count_consistent']:
        failures.append('empty-export' if r['checked_count'] == 0 else 'declaration-count-mismatch')
    if r['checker_accepted'] and not r['axiom_report_consistent']:
        failures.append('Ax0-statement-or-report-mismatch')
    if r['checker_accepted'] and not r['mint_consistent']:
        failures.append('mint-inventory-mismatch')
    r['runner_refusals'] = failures
    r['accepted'] = r['accepted'] and not failures
    if row['expect'] == 'accept':
        matched = r['accepted']
    elif row.get('runner_reason'):
        matched = row['runner_reason'] in failures
    else:
        matched = (r['exit_status'] in (1, 101) and bool(row.get('reason')) and
                   row['reason'] in r['failure']['reason'] and
                   r['failure']['kind'] in ('error', 'panic'))
    r.update(name=row['name'], expected=row['expect'], matches_expected=matched,
             expected_export_sha256=row['sha256'], admitted_export_axioms=admitted,
             omitted_export_axioms=sorted(set(r['export_axioms']) - set(AX0)))
    return r


def validate_manifest(manifest, subject):
    by_name = {r['name']: r for r in manifest}
    if len(by_name) != len(manifest):
        raise ValueError('duplicate manifest names')
    if subject not in by_name or by_name[subject]['expect'] != 'accept':
        raise ValueError('subject must name an expect:accept row')
    if not set(CONTROLS) <= set(by_name):
        raise ValueError('missing pinned control')
    for name, pin in CONTROLS.items():
        row = by_name[name]
        for k, value in pin.items():
            if row.get(k) != value:
                raise ValueError(f'control {name}: {k} identity mismatch')
        if any(row.get(k) != pin.get(k) for k in ('reason', 'runner_reason')):
            raise ValueError('control diagnostic policy mismatch')
        if row['expect'] != 'reject':
            raise ValueError('control must expect rejection')
    for row in manifest:
        if row['expect'] not in ('accept', 'reject') or not re.fullmatch('[0-9a-f]{64}', row['sha256']):
            raise ValueError('invalid expectation or export digest')
        if row['expect'] == 'accept' and not row.get('sidecar'):
            raise ValueError('accepted row needs mint sidecar')


def pinned_inputs():
    arena_rel = ARENA.relative_to(ROOT)
    table = json.loads((ARENA / 'round-2026-09.table.json').read_text())
    return sorted(['data/nanoda_q3_pin.json', 'data/nanoda_q3_arena_reasons.json',
                   str(arena_rel / 'round-2026-09.table.json'), str(arena_rel / table['archive']['file'])] +
                  list({p[k] for p in CONTROLS.values() for k in ('path', 'sidecar')}))


def repository_state():
    git = lambda *a: subprocess.check_output(['git', '-C', str(ROOT), *a], text=True).strip()
    return git('rev-parse', 'HEAD'), git('status', '--porcelain=v1', '--untracked-files=all')


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--pinned-inputs', action='store_true')
    ap.add_argument('--binary', type=Path)
    ap.add_argument('--manifest', type=Path)
    ap.add_argument('--subject')
    ap.add_argument('--out', type=Path)
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    if args.pinned_inputs:
        print('\n'.join(pinned_inputs())); return 0
    if not all((args.binary, args.manifest, args.subject, args.out)):
        ap.error('--binary, --manifest, --subject and --out are required')
    record = None
    def save():
        (args.out / 'verdict.json').write_text(json.dumps(record, indent=2) + '\n')
    try:
        pin_bytes = (ROOT / 'data/nanoda_q3_pin.json').read_bytes()
        pin = json.loads(pin_bytes)
        binary = args.binary.resolve()
        binary_digest = pin['binary_sha256']
        if sys.platform != 'darwin' or digest(binary) != binary_digest:
            raise ValueError('platform or binary identity mismatch')
        manifest_bytes = args.manifest.read_bytes()
        manifest = json.loads(manifest_bytes)
        validate_manifest(manifest, args.subject)
        table_bytes = (ARENA / 'round-2026-09.table.json').read_bytes()
        table = json.loads(table_bytes)
        reasons_bytes = (ROOT / 'data/nanoda_q3_arena_reasons.json').read_bytes()
        reason_table = json.loads(reasons_bytes)
        reasons = reason_table['fixtures']
        if reason_table['checker_commit'] != pin['commit'] or set(reasons) != {r['path'] for r in table['tests'] if r['outcome'] == 'reject'}:
            raise ValueError('arena reason inventory mismatch')
        archive = ARENA / table['archive']['file']
        if digest(archive) != ARCHIVE_SHA or table['archive']['sha256'] != ARCHIVE_SHA:
            raise ValueError('arena archive identity mismatch')
        args.out.mkdir(parents=True, exist_ok=False)
        commit, dirty = repository_state()
        record = dict(schema='clean.nanoda-recheck.v2', checker=pin, pin_sha256=sha(pin_bytes),
                      ax0_statements=AX0_STATEMENTS, runner_sha256=digest(__file__),
                      git_commit=commit, dirty=bool(dirty), dirty_status=dirty,
                      utc=datetime.now(timezone.utc).isoformat(), host=platform.platform(),
                      manifest_sha256=sha(manifest_bytes), arena_table_sha256=sha(table_bytes),
                      arena_reason_table_sha256=sha(reasons_bytes), subject=args.subject,
                      qualification=[], rechecks=[], qualified=False, success=False,
                      qualification_policy='explicit fixture axioms; matched panic signatures are not deliberate refusals',
                      limitations='Independent Rust implementation agreement, not a proof. Per-bound soundness; no generation exceeds base consistency; the quorum stays.')
        save()
        with tarfile.open(archive) as tar:
            files = [m for m in tar.getmembers() if m.isfile()]
            members = {m.name: m for m in files}
            if len(files) != len(members) or set(members) != {r['path'] for r in table['tests']} or len(members) != ARENA_COUNT:
                raise ValueError('arena inventory mismatch')
            for i, row in enumerate(table['tests']):
                data = tar.extractfile(members[row['path']]).read()
                if sha(data) != row['sha256']:
                    raise ValueError('arena case identity mismatch')
                permitted = sorted(set(AX0 + inventory(data)['axioms']))
                r = run(binary, data, permitted, True, row['timeout_s'] or 120, binary_digest)
                record['qualification'].append(qualification_result(r, row, reasons)); save()
                print(f"arena {i+1}/193 {row['path']} accepted={r['accepted']} reason_match={r['reason_matches']} contradiction={r['contradiction']}", flush=True)
                if row['outcome'] == 'reject' and r['checker_accepted']:
                    record['disqualified_by'] = row['path']; save(); return 1
        record['qualified'] = all(r['judged'] and not r['contradiction'] for r in record['qualification'])
        save()
        if not record['qualified']:
            return 1
        for row in manifest:
            data = resolve(row['path']).read_bytes()
            if row['path'].endswith('.gz'):
                data = gzip.decompress(data)
            if sha(data) != row['sha256']:
                raise ValueError(f"export identity mismatch: {row['name']}")
            sidecar_bytes = resolve(row['sidecar']).read_bytes()
            if sha(sidecar_bytes) != row['sidecar_sha256']:
                raise ValueError('sidecar identity mismatch')
            r = run(binary, data, AX0, row.get('hard_error', False), row.get('timeout_s', 600), binary_digest)
            r = evaluate_recheck(r, row, json.loads(sidecar_bytes))
            r['sidecar_sha256'] = sha(sidecar_bytes)
            record['rechecks'].append(r); save()
            print(f"recheck {row['name']} checker_accepted={r['checker_accepted']} accepted={r['accepted']} matched={r['matches_expected']} runner_refusals={r['runner_refusals']}", flush=True)
        record['success'] = (all(r['matches_expected'] for r in record['rechecks']) and
                             any(r['name'] == args.subject and r['expected'] == 'accept' and r['accepted'] for r in record['rechecks']) and
                             set(CONTROLS) <= {r['name'] for r in record['rechecks'] if r['expected'] == 'reject' and r['matches_expected']})
        record['completed_utc'] = datetime.now(timezone.utc).isoformat()
        save()
        return 0 if record['success'] else 1
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, subprocess.SubprocessError) as exc:
        if record is not None:
            record['error'] = str(exc); record['success'] = False; save()
        print(f'nanoda_recheck: identity/invocation failure: {exc}', file=sys.stderr)
        return 2


CONTROLS = {'empty-export': {'hard_error': False,
                  'path': 'reports/self-proof-q3-2026-11-12/empty-export.ndjson',
                  'runner_reason': 'empty-export',
                  'sha256': 'cc289e5f658e2e6048a1a7ca01f7507399deaee24ad08f92b35e12e3bb183f58',
                  'sidecar': 'reports/self-proof-q3-2026-11-12/review-sidecars/empty-export.json',
                  'sidecar_sha256': '5ad600b40e88c596c061bcfb8cb70cb7195d7475ad8a79042c126226a2274d65'},
 'extra-axiom': {'hard_error': True,
                 'path': 'reports/self-proof-q3-2026-11-12/extra-axiom.ndjson',
                 'reason': 'export file declares unpermitted axiom "q3_extra_axiom"',
                 'sha256': '02287bb5cc83317682f9000a48ef99dd06b90d7b040fb2f3bd0ee4014f720d47',
                 'sidecar': 'reports/self-proof-q3-2026-11-12/review-sidecars/extra-axiom.json',
                 'sidecar_sha256': 'cf089607ac0721fce83795b12d62b01ea34ac09c233e23077271b3267a7594ae'},
 'extra-axiom-used': {'hard_error': False,
                      'path': 'reports/self-proof-q3-2026-11-12/extra-axiom.ndjson',
                      'reason': 'depends on q3_extra_axiom which was not found in the environment',
                      'sha256': '02287bb5cc83317682f9000a48ef99dd06b90d7b040fb2f3bd0ee4014f720d47',
                      'sidecar': 'reports/self-proof-q3-2026-11-12/review-sidecars/extra-axiom-used.json',
                      'sidecar_sha256': 'cf089607ac0721fce83795b12d62b01ea34ac09c233e23077271b3267a7594ae'},
 'forged-recursor': {'hard_error': False,
                     'path': 'reports/self-proof-q3-2026-11-12/forged-recursor.ndjson',
                     'reason': 'assertion failed: old_r.aux_data_ck(new_r)',
                     'sha256': '8c5c3d6e450cd92b6a44f7fe29dfcc4f5181495b850a35f23cc234ecee94ecc1',
                     'sidecar': 'reports/self-proof-q3-2026-11-12/review-sidecars/forged-recursor.json',
                     'sidecar_sha256': '4ad4bf1d407361c3569093ed9235b34497a521ff8c32a992fd99da75f7ad5bf9'},
 'ill-typed-body': {'hard_error': False,
                    'path': 'reports/self-proof-q3-2026-11-12/ill-typed-body.ndjson',
                    'reason': 'assertion failed: self.def_eq(u, v)',
                    'sha256': 'd5bdd8e30e77638c1bcfd6e4e7e6c557096bcbf18497dacbf39fe72e280c5430',
                    'sidecar': 'reports/self-proof-q3-2026-11-12/review-sidecars/ill-typed-body.json',
                    'sidecar_sha256': '44e138f4ad39b1b1eea47c11f18600574107df9d82b3fdd039fcf86c91d72e83'},
 'wrong-statement-propext': {'hard_error': False,
                             'path': 'reports/self-proof-q3-2026-11-12/wrong-statement-propext.ndjson',
                             'runner_reason': 'Ax0-statement-or-report-mismatch',
                             'sha256': 'fd34a3d95272f48ea5ab5942bb69df9f3cdf116e8f264830853ee78a43a16bf1',
                             'sidecar': 'reports/self-proof-q3-2026-11-12/review-sidecars/wrong-statement-propext.json',
                             'sidecar_sha256': 'bad245f8bd0d7d281db969c97d0a16c1ac88ea85aeaa17f9552fa32fec3d2b76'}}

def selftest():
    """Execute a local stub binary through the real process/timeout/output path.

    Only the macOS sandbox command is replaced. The stub is first-party test
    data; production has no switch to replace its pin, table or controls.
    Synthetic identities exercise the complete main orchestration cheaply.
    """
    import contextlib
    import copy
    import io
    from unittest.mock import patch
    checks = []
    def check(label, condition):
        if not condition:
            raise AssertionError(label)
        checks.append(label)

    with tempfile.TemporaryDirectory(prefix='nanoda-selftest-') as td:
        base = Path(td)
        stub = base / 'stub.py'
        stub.write_text('''import json,sys,time,pathlib
cfg=json.load(open('config.json'))
data=[json.loads(l) for l in open(cfg['export_file_path'])]
a=data[0]['meta'].get('stub',{})
if a.get('mutate'): pathlib.Path(sys.argv[0]).write_text('# changed')
if a.get('sleep'): time.sleep(5)
print(a.get('stdout','Checked 1 declarations with no errors'))
print(a.get('stderr',''),file=sys.stderr)
sys.exit(a.get('rc',0))
''')
        stub_digest = digest(stub)
        def blob(action=None, axiom=None):
            records = [{'meta': {'stub': action or {}}}, {'in': 1, 'str': {'pre': 0, 'str': axiom or 'subject'}}]
            records.append({'axiom' if axiom else 'def': {'name': 1}})
            return (''.join(json.dumps(r) + '\n' for r in records)).encode()
        def launch(binary, wd):
            return [sys.executable, str(binary)]
        with patch.dict(globals(), sandbox_command=launch):
            invoke = lambda data, seconds=2: run(stub, data, AX0, False, seconds, stub_digest)
            data = blob()
            green = invoke(data)
            side = dict(export={'sha256': sha(data)}, checked_declaration_count=1,
                        decls=['subject'], admitted_declaration_names=['subject'])
            row = dict(name='subject', expect='accept', sha256=sha(data))
            check('accepted control', evaluate_recheck(copy.deepcopy(green), row, side)['matches_expected'])
            for label, action in [
                ('pretty-printer failure', {'stdout':'Checked 1 declarations with no typechecker errors, 1 pretty printer errors:'}),
                ('missing success message', {'stdout':''}),
                ('zero declarations', {'stdout':'Checked 0 declarations with no errors'}),
                ('checked count mismatch', {'stdout':'Checked 2 declarations with no errors'}),
                ('duplicate success lines', {'stdout':'Checked 1 declarations with no errors\nChecked 1 declarations with no errors'}),
                ('good case crash', {'rc':101, 'stderr':"thread 'x' panicked at src/tc.rs:1:1:\nboom\nnote: test"}),
                ('timeout', {'sleep':True}),
            ]:
                r=invoke(blob(action), .05 if action.get('sleep') else 2)
                check(label, not r['accepted'])
            for label, altered in [('mint count', dict(checked_declaration_count=2)),
                                   ('missing required declaration', dict(decls=['absent'])),
                                   ('mint inventory', dict(admitted_declaration_names=['other'])),
                                   ('mint digest', dict(export={'sha256':'0'*64}))]:
                s=copy.deepcopy(side);s.update(altered)
                check(label, not evaluate_recheck(copy.deepcopy(green), row, s)['matches_expected'])
            a=blob({'stdout':'axiom propext : False\nChecked 1 declarations with no errors'}, 'propext')
            r=invoke(a);s=dict(side,export={'sha256':sha(a)},decls=['propext'],admitted_declaration_names=['propext'])
            check('wrong-statement propext', not evaluate_recheck(r,row,s)['accepted'])
            a=blob({'stdout':'Checked 1 declarations with no errors'}, 'propext')
            r=invoke(a);s=dict(s,export={'sha256':sha(a)})
            check('axiom report missing', not evaluate_recheck(r,row,s)['accepted'])
            a=blob({'stdout':'axiom extra : False\nChecked 1 declarations with no errors'})
            check('extra reported axiom', not evaluate_recheck(invoke(a),row,side)['accepted'])
            alias=(json.dumps({'in':2,'str':{'pre':0,'str':'Quot.sound'}})+'\n'+json.dumps({'axiom':{'name':2}})+'\n').encode()
            try: inventory(alias)
            except ValueError: checks.append('flattened Ax0 alias')
            else: raise AssertionError('flattened Ax0 alias')
            badrow=dict(path='bad/test',outcome='reject',sha256=sha(data))
            reason={'bad/test':dict(failure={'kind':'error','reason':'fixture refusal'},target_evidence='test')}
            check('bad fixture accepted', qualification_result(copy.deepcopy(green),badrow,reason)['contradiction'])
            r=invoke(blob({'rc':1,'stderr':'Error: fixture refusal'}))
            check('expected reason control', not qualification_result(r,badrow,reason)['contradiction'])
            for label, action in [('wrong refusal reason',{'rc':1,'stderr':'Error: unrelated'}),
                                  ('crash is not deliberate error',{'rc':101,'stderr':"thread 'x' panicked at src/tc.rs:1:1:\nfixture refusal\nnote: test"}),
                                  ('unjudged exit',{'rc':3}),
                                  ('signal exit',{'rc':137})]:
                check(label, qualification_result(invoke(blob(action)),badrow,reason)['contradiction'])
            decline=invoke(blob({'rc':2,'stderr':'Declined: Level back-reference mismatch'}))
            check('decline bad fixture', qualification_result(copy.deepcopy(decline),badrow,reason)['contradiction'])
            goodrow=dict(path='good/unknown',outcome='accept',sha256=sha(data))
            check('decline other good fixture', qualification_result(copy.deepcopy(decline),goodrow,reason)['contradiction'])
            goodrow['path']='good/other/level-index-out-of-order.ndjson'
            check('pinned good decline', qualification_result(copy.deepcopy(decline),goodrow,reason)['unsupported'])
            check('recheck reason mismatch', not evaluate_recheck(invoke(blob({'rc':1,'stderr':'Error: wrong'})),dict(row,expect='reject',reason='fixture refusal'),side)['matches_expected'])
            check('recheck crash without signature', not evaluate_recheck(invoke(blob({'rc':101})),dict(row,expect='reject',reason='fixture refusal'),side)['matches_expected'])
            check('recheck timeout cannot reject', not evaluate_recheck(invoke(blob({'sleep':True}),.05),dict(row,expect='reject',reason='fixture refusal'),side)['matches_expected'])
            # Full main on a two-case synthetic archive and pinned test controls.
            arena=base/'arena';arena.mkdir();(base/'data').mkdir()
            bad=blob({'rc':1,'stderr':'Error: fixture refusal'})
            archive=arena/'cases.tar'
            with tarfile.open(archive,'w') as tar:
                for name,payload in [('good/test',data),('bad/test',bad)]:
                    info=tarfile.TarInfo(name);info.size=len(payload);tar.addfile(info,io.BytesIO(payload))
            table={'archive':{'file':'cases.tar','sha256':digest(archive)},'tests':[
                dict(path='good/test',sha256=sha(data),outcome='accept',timeout_s=2),
                dict(path='bad/test',sha256=sha(bad),outcome='reject',timeout_s=2)]}
            pin={'commit':'test-commit','binary_sha256':stub_digest}
            reason_table={'checker_commit':'test-commit','fixtures':reason}
            (base/'data/nanoda_q3_pin.json').write_text(json.dumps(pin))
            (base/'data/nanoda_q3_arena_reasons.json').write_text(json.dumps(reason_table))
            (arena/'round-2026-09.table.json').write_text(json.dumps(table))
            (base/'input.ndjson').write_bytes(data);(base/'bad.ndjson').write_bytes(bad)
            (base/'sidecar.json').write_text(json.dumps(side));sd=digest(base/'sidecar.json')
            manifest=[dict(row,path='input.ndjson',sidecar='sidecar.json',sidecar_sha256=sd)]
            controls={}
            for name in CONTROLS:
                c=dict(name=name,path='bad.ndjson',expect='reject',sha256=sha(bad),hard_error=False,reason='fixture refusal',sidecar='sidecar.json',sidecar_sha256=sd)
                manifest.append(c);controls[name]={k:c[k] for k in ('path','sha256','hard_error','reason')}
            mp=base/'manifest.json'
            counter=0
            def full(m=None, subject='subject', binary=stub):
                nonlocal counter
                counter+=1;mp.write_text(json.dumps(manifest if m is None else m))
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    rc=main(['--binary',str(binary),'--manifest',str(mp),'--subject',subject,'--out',str(base/f'out{counter}')])
                return rc
            with patch.dict(globals(),ROOT=base,ARENA=arena,ARCHIVE_SHA=digest(archive),ARENA_COUNT=2,CONTROLS=controls,repository_state=lambda:('test-head',' M script')), patch.object(sys, 'platform', 'darwin'):
                check('main green',full()==0)
                for label,change in [
                    ('missing control',lambda m:m.pop()),
                    ('duplicate names',lambda m:m.append(m[0].copy())),
                    ('control bytes pin',lambda m:m[1].update(sha256='0'*64)),
                    ('control path pin',lambda m:m[1].update(path='input.ndjson')),
                    ('control reason pin',lambda m:m[1].update(reason='a')),
                    ('control policy pin',lambda m:m[1].update(hard_error=True)),
                    ('control reason branch substitution',lambda m:m[1].update(runner_reason='declaration-count-mismatch')),
                    ('reject subject',lambda m:m[0].update(expect='reject')),
                    ('missing mint sidecar',lambda m:m[0].pop('sidecar')),
                    ('input digest',lambda m:m[0].update(sha256='0'*64)),
                    ('sidecar digest',lambda m:m[0].update(sidecar_sha256='0'*64)),
                    ('invalid expectation',lambda m:m[0].update(expect='anything')),
                    ('missing input',lambda m:m[0].update(path='absent.ndjson')),
                ]:
                    m=copy.deepcopy(manifest);change(m);check(label,full(m)==2)
                m=copy.deepcopy(manifest);m=[r for r in m if r['name']!='extra-axiom-used']
                check('missing omission-mode control',full(m)==2)
                check('missing subject',full(subject='absent')==2)
                check('missing binary exit 2',full(binary=base/'missing')==2)
                pinpath=base/'data/nanoda_q3_pin.json'
                pinpath.write_text(json.dumps(dict(pin,binary_sha256='0'*64)))
                check('binary identity',full()==2);pinpath.write_text(json.dumps(pin))
                with patch.dict(globals(),ARCHIVE_SHA='0'*64):check('archive identity',full()==2)
                reasonpath=base/'data/nanoda_q3_arena_reasons.json'
                reasonpath.write_text(json.dumps(dict(reason_table,fixtures={})))
                check('reason inventory',full()==2);reasonpath.write_text(json.dumps(reason_table))
                broken=copy.deepcopy(table);broken['tests'][0]['sha256']='0'*64
                (arena/'round-2026-09.table.json').write_text(json.dumps(broken));check('arena case digest',full()==2)
                (arena/'round-2026-09.table.json').write_text(json.dumps(table))
                with patch.dict(globals(),ARENA_COUNT=3):check('arena inventory',full()==2)
                # A failed accepted subject remains red even with accepted qualification.
                m=copy.deepcopy(manifest);m[0].update(path='bad.ndjson',sha256=sha(bad))
                check('refused subject exit 1',full(m)==1)
            # The source path changing after snapshot cannot change recorded bytes.
            source=base/'snapshot.ndjson';source.write_bytes(data)
            snapshot=source.read_bytes();source.write_bytes(b'changed after snapshot')
            check('hash actual checked snapshot',invoke(snapshot)['input_sha256']==sha(data))
            # Mutation during execution must not mint a record for the new binary.
            try:invoke(blob({'mutate':True}))
            except ValueError as e:check('binary changed mid-run','changed during' in str(e))
            else:raise AssertionError('binary changed mid-run')
            try:invoke(data)
            except ValueError as e:check('binary changed before run','changed before' in str(e))
            else:raise AssertionError('binary changed before run')
    print(f'NANODA_RECHECK_SELFTEST=ok checks={len(checks)}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
