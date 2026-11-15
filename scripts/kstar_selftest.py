#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Local controls for Q4's orchestration rules. No stub ever becomes a vote."""
import copy
import json
import tempfile
import sys
from pathlib import Path
from unittest.mock import patch
import kstar_recheck as k
import lean4lean_selftest
from kstar_subjects_selftest import restriction_controls


def selftest():
    checks = 0
    def check(name, condition):
        nonlocal checks
        assert condition, name
        checks += 1
        print('ok:', name)
    for member, obj in [
        ('lean', dict(verdict='accepted', declarations=1, axioms=['propext'])),
        ('clean-reference', dict(accepted=True, admitted=1, declarations=1,
                                axioms=['propext'], refusals=[], unpermitted_axioms=[], reader_error=None)),
        ('ck0-stock', dict(kind='coverage', accepted=1, total=1, refused={}, axioms=[[{'str':'propext'}]])),
    ]:
        raw = dict(exit_code=0, stdout=json.dumps(obj), stderr='')
        good = k.evaluate(member, raw, 1, ['propext'])
        check(member + ' honest report', good['accepted'])
        for label, bad, count, axioms in [
            ('missing report', dict(raw, stdout=''), 1, ['propext']),
            ('count drift', raw, 2, ['propext']),
            ('axiom drift', raw, 1, []),
            ('timeout', dict(raw, exit_code=None), 1, ['propext']),
            ('crash', dict(raw, exit_code=-6), 1, ['propext']),
        ]:
            check(member + ' refuses ' + label, not k.evaluate(member, bad, count, axioms)['accepted'])
        mutated = copy.deepcopy(obj)
        mutated['axioms'] = ['evil'] if member != 'ck0-stock' else [[{'str':'evil'}]]
        check(member + ' Ax0 boundary', not k.evaluate(member, dict(raw, stdout=json.dumps(mutated)), 1, ['evil'])['accepted'])
    restriction_controls(check)
    rows = {m: dict(accepted=True, axioms=['propext']) for m in k.MEMBERS}
    check('all four required', k.agreed(rows))
    for member in k.MEMBERS:
        missing = dict(rows); missing.pop(member)
        check('missing ' + member, not k.agreed(missing))
        bad = copy.deepcopy(rows); bad[member]['axioms'] = []
        check('axiom mismatch ' + member, not k.agreed(bad))
        bad[member]['accepted'] = False
        check('disagreement ' + member, not k.agreed(bad))
        for name in k.CONTROL_NAMES:
            check(member + ' control acceptance ' + name, not k.control_refused(member, name, dict(accepted=True, exit_code=0)))
            check(member + ' control timeout ' + name, not k.control_refused(member, name, dict(accepted=False, exit_code=None)))
            check(member + ' incidental failure ' + name, not k.control_refused(member, name, dict(accepted=False, exit_code=1, stderr='unrelated IO failure')))
    for name, failure in k.LEAN4LEAN_CONTROLS.items():
        row = dict(accepted=False, exit_code=0 if failure['kind'] == 'runner' else 1, failure=failure)
        check('lean4lean pinned refusal ' + name, k.control_refused('lean4lean', name, row))
        panic = dict(accepted=False, exit_code=134, verdict='panic',
                     failure=dict(kind='panic', location='x', reason=failure['reason']))
        check('lean4lean panic is no refusal ' + name, not k.control_refused('lean4lean', name, panic))
        other = dict(row, failure=dict(failure, reason='unrelated'))
        check('lean4lean other refusal ' + name, not k.control_refused('lean4lean', name, other))
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / 'record.json'
        check('missing record', k.check_record(p) == 1)
        p.write_text(json.dumps(dict(success=False, source_inputs={})))
        with patch.object(k, 'source_inputs', return_value={}):
            check('red record never green', k.check_record(p) == 1)
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / 'new-run'
        argv = ['kstar', '--members', str(Path(td) / 'absent.json'),
                '--subject', str(Path(td) / 'absent.ndjson'), '--out', str(out)]
        with patch.object(k, 'source_inputs', return_value={}), patch.object(sys, 'argv', argv):
            check('missing build receipt cannot vote', k.main() == 1)
        check('unavailable run records failure', not json.loads((out / 'replay.json').read_text())['success'])
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / 'record.json'
        candidate = dict(source_inputs={}, success=True, qualified_lean4lean=True,
                         subjects=[dict(sha256='seed', source_sha256='seed', members=rows)], controls={})
        p.write_text(json.dumps(candidate))
        with patch.object(k, 'source_inputs', return_value={}):
            check('seed cannot replace the pinned full subjects', k.check_record(p) == 1)
            candidate['subjects'] = [dict(sha256=h, source_sha256='seed', members=rows) for h in k.SUBJECT_PINS]
            candidate['identities'] = {m: {} for m in k.MEMBERS}
            p.write_text(json.dumps(candidate))
            check('an unpinned source cannot green the standing record', k.check_record(p) == 1)
            candidate['subjects'] = [dict(sha256=h, source_sha256=s, members=rows)
                                     for h, s in zip(sorted(k.SUBJECT_PINS), sorted(k.SOURCE_PINS))]
            candidate['identities'] = {}
            p.write_text(json.dumps(candidate))
            check('missing member identity cannot green the standing record', k.check_record(p) == 1)
    l4l_checks = []
    lean4lean_selftest.selftest(l4l_checks)
    checks += len(l4l_checks)
    print(f'KSTAR_SELFTEST=ok checks={checks}; no quorum vote')
    return 0
