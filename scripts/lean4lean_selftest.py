#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Local controls for the Lean4Lean runner. A stub stands in for the binary
through the real process, timeout and output path; no stub is ever a vote."""
import json
from pathlib import Path
import sys
import tempfile
from unittest.mock import patch

import lean4lean_recheck as l
import nanoda_recheck as nano

STUB = '''import json,sys,time,pathlib
data=[json.loads(x) for x in open(sys.argv[-1]) if x.strip()]
a=data[0]['meta'].get('stub',{}) if data and 'meta' in data[0] else {}
if a.get('mutate'): pathlib.Path(sys.argv[0]).write_text('# changed')
if a.get('sleep'): time.sleep(5)
sys.stdout.write(a.get('stdout','checked 1 declarations\\n'))
sys.stderr.write(a.get('stderr',''))
sys.exit(a.get('rc',0))
'''


def blob(action=None, records=None):
    head = [{'meta': {'stub': action or {}}}, {'in': 1, 'str': {'pre': 0, 'str': 'subject'}},
            {'ie': 0, 'sort': 0}]
    body = records if records is not None else [
        {'def': {'name': 1, 'levelParams': [], 'type': 0, 'value': 0, 'hints': 'abbrev',
                 'safety': 'safe', 'all': [1]}}]
    return ''.join(json.dumps(r) + '\n' for r in head + body).encode()


def selftest(checks=None):
    own = checks is None
    checks = [] if own else checks
    def check(label, condition):
        if not condition:
            raise AssertionError(label)
        checks.append('lean4lean: ' + label)
    pin = json.loads((l.ROOT / l.PIN).read_text())
    with tempfile.TemporaryDirectory(prefix='lean4lean-selftest-') as td:
        stub = Path(td) / 'stub.py'
        stub.write_text(STUB)
        digest = nano.digest(stub)
        launch = lambda binary, wd: [sys.executable, str(binary), '--import', 'input.ndjson']  # noqa: E731
        with patch.object(l, 'sandbox_command', launch):
            def go(data, seconds=5, ax0=True):
                return l.policy(l.run(stub, data, seconds, digest), data, pin, ax0=ax0)
            check('honest report', go(blob())['accepted'])
            check('timing lines', go(blob({'stdout': '[anonymous]:subject: lean4lean took 1200\nchecked 1 declarations\n'}))['accepted'])
            for label, action in [('stray output', {'stdout': 'hello\nchecked 1 declarations\n'}),
                                  ('duplicate count', {'stdout': 'checked 1 declarations\nchecked 1 declarations\n'}),
                                  ('count not last', {'stdout': 'checked 1 declarations\n[anonymous]:x: lean4lean took 9\n'}),
                                  ('missing count', {'stdout': ''}),
                                  ('nonzero exit', {'rc': 1})]:
                check(label, not go(blob(action))['accepted'])
            r = go(blob({'stdout': 'checked 2 declarations\n'}))
            check('count drift', r['runner_refusals'] == ['declaration-count-mismatch'] and r['verdict'] == 'refused')
            r = go(blob({'stdout': 'checked 0 declarations\n'}, records=[]))
            check('empty export', r['failure'] == dict(kind='runner', reason='empty-export'))
            panic = 'PANIC at Foo.bar Foo.Baz:1:2: boom\n  Lean4Lean.Replay.throwKernelException\n'
            r = go(blob({'stderr': panic, 'rc': 134}))
            check('panic is a panic', r['verdict'] == 'panic' and not r['accepted']
                  and r['failure']['after_kernel_exception'] and r['failure']['reason'] == 'boom')
            check('panic after the kernel raised', r['decision'] == 'kernel-raised-then-panicked')
            r = go(blob({'stderr': 'PANIC at Foo.bar Foo.Baz:1:2: boom\n'}))
            check('panic with exit 0 never accepts', r['verdict'] == 'panic' and not r['failure']['after_kernel_exception'])
            check('panic before the kernel decided', r['decision'] == 'crashed-before-deciding')
            r = go(blob({'stderr': 'uncaught exception: at subject: (kernel) type expected\n', 'rc': 1}))
            check('kernel refusal', r['verdict'] == 'refused' and r['failure'] == dict(kind='error', reason='at subject: (kernel) type expected'))
            check('kernel refusal decision', r['decision'] == 'refused')
            r = go(blob({'sleep': True}), seconds=0.2)
            check('timeout cannot vote', r['verdict'] == 'not knowable here' and r['decision'] == 'undecided')
            r = go(blob({'rc': 3}))
            check('unrecognized failure cannot vote', r['verdict'] == 'not knowable here' and r['decision'] == 'undecided')
            r = go(blob({'stdout': 'checked 2 declarations\n'}))
            check('runner refusal keeps the kernel decision', r['decision'] == 'accepted' and r['verdict'] == 'refused')
            unsafe = blob(records=[{'def': {'name': 1, 'levelParams': [], 'type': 0, 'value': 0, 'hints': 'opaque',
                                            'safety': 'unsafe', 'all': [1]}}])
            r = go(unsafe, ax0=True)
            check('skipped declarations refuse the subject', r['runner_refusals'][:1] == ['declarations Lean4Lean skips: 1'])
            for name, reason in l.RUNNER_CONTROLS.items():
                data = (l.ROOT / nano.CONTROLS[name]['path']).read_bytes()
                count = l.model(data)['expected_checked']
                stdout = f'checked {count} declarations\n'
                meta = json.loads(data.splitlines()[0]) if data else {}
                if 'meta' in meta:
                    meta['meta']['stub'] = {'stdout': stdout}
                    data = (json.dumps(meta) + '\n').encode() + b'\n'.join(data.splitlines()[1:]) + b'\n'
                else:
                    data = blob({'stdout': stdout}, records=[])
                r = go(data)
                check('runner control ' + name, r['failure'] == dict(kind='runner', reason=reason))
            row = dict(path='bad/x', outcome='reject', sha256='0' * 64)
            reasons = {'bad/x': dict(failure=dict(kind='error', reason='at subject: (kernel) type expected'))}
            ok = go(blob({'stderr': 'uncaught exception: at subject: (kernel) type expected\n', 'rc': 1}), ax0=False)
            check('bad case judged on its pinned reason', l.judge(ok, row, reasons)['judged'])
            check('bad case accepted is a contradiction', l.judge(go(blob(), ax0=False), row, reasons)['contradiction'])
            wrong = go(blob({'stderr': 'uncaught exception: at subject: (kernel) other\n', 'rc': 1}), ax0=False)
            check('bad case on another reason', l.judge(wrong, row, reasons)['contradiction'])
            raised = 'PANIC at R.render R.M:1:2: boom\n  Lean4Lean.Replay.throwKernelException\n'
            crashed = 'PANIC at L.toCtorWhenStruct L.R:63:43: unreachable code has been reached\n'
            for label, stderr, judged in [('a panic after the kernel raised is judged on its pinned signature', raised, True),
                                          ('a crash before deciding is never judged', crashed, False)]:
                r = go(blob({'stderr': stderr, 'rc': 134}), ax0=False)
                pinned = {'bad/x': dict(failure=r['failure'])}
                j = l.judge(r, row, pinned)
                check(label, j['reason_matches'] and j['judged'] is judged and j['verdict'] == 'panic'
                      and j['undecided'] is not judged and not j['contradiction'])
            check('a timeout on a bad case is undecided, not judged',
                  l.judge(go(blob({'sleep': True}), seconds=0.2, ax0=False), row,
                          {'bad/x': dict(failure=dict(kind='timeout', reason='timeout'))})['undecided'])
            good = dict(path='good/x', outcome='accept', sha256='0' * 64)
            refused = {'stderr': 'uncaught exception: at subject: (kernel) type expected\n', 'rc': 1}
            check('good case refused', l.judge(go(blob(refused), ax0=False), good, reasons)['contradiction'])
            j = l.judge(go(blob({'rc': 1}), ax0=False), good, reasons)
            check('good case failing undiagnosed is undecided, not judged', j['undecided'] and not j['judged'])
            try:
                l.run(stub, blob({'mutate': True}), 5, digest)
            except ValueError as e:
                check('binary changed mid-run', 'changed during' in str(e))
            else:
                raise AssertionError('binary changed mid-run')
    with tempfile.TemporaryDirectory(prefix='lean4lean-patch-selftest-') as td:
        root = Path(td)
        directory = root / l.PATCH_DIRECTORY
        directory.mkdir(parents=True)
        source = directory / 'one.patch'
        source.write_bytes(b'original patch')
        entry = dict(file=source.relative_to(root).as_posix(), sha256=nano.digest(source))
        declared = dict(patches=[entry])
        check('source patch inventory and digest', l.patch_files(declared, root) == [entry['file']])
        def refuses(label, candidate):
            try:
                l.patch_files(candidate, root)
            except ValueError:
                check(label, True)
            else:
                raise AssertionError(label)
        refuses('changed source patch digest', dict(patches=[dict(entry, sha256='0' * 64)]))
        refuses('duplicate source patch', dict(patches=[entry, entry]))
        refuses('source patch path escape', dict(patches=[dict(entry, file='../outside.patch')]))
        refuses('source patch is missing', dict(patches=[dict(entry, file=str(l.PATCH_DIRECTORY / 'missing.patch'))]))
        extra = directory / 'extra.patch'
        extra.write_bytes(b'unlisted')
        refuses('unlisted source patch', declared)
        extra.unlink()
        original = source.read_bytes()
        source.unlink()
        target = root / 'target'
        target.write_bytes(original)
        source.symlink_to(target)
        refuses('source patch symlink', declared)
        source.unlink()
    statements = l.model((l.ROOT / nano.CONTROLS['wrong-statement-propext']['path']).read_bytes())['ax0_statements']
    check('pinned propext statement differs from the forged one', statements['propext'] != pin['ax0_statement_sha256']['propext'])
    if own:
        print(f'LEAN4LEAN_SELFTEST=ok checks={len(checks)}; no quorum vote')
    return 0
