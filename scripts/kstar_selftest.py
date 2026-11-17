#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Local controls for Q4's orchestration rules. No stub ever becomes a vote."""
import contextlib
import copy
import io
import json
import subprocess
import tempfile
import sys
from pathlib import Path
from unittest.mock import patch
import kstar_recheck as k
import lean4lean_selftest
from kstar_subjects_selftest import restriction_controls


# A tree with one file of each kind a member's build can read. `expected` must be
# inputs and `unnamed` must not; each `refusals` edit (path, text) must make the
# input rule refuse rather than name fewer files.
SOURCE_TREE = {
    'crates/m/Cargo.toml': '[package]\nname = "m"\n\n[dependencies]\nv = { path = "../../vendor/v" }\n',
    'crates/m/build.rs': 'fn main() { let _ = std::fs::read_to_string("table.tsv"); let _ = "lean-toolchain"; }\n',
    'crates/m/table.tsv': '# world\tfixture\nw\tfixtures/w.bin\n',
    'crates/m/notes.md': 'tracked under crates/ and named by nothing\n',
    'crates/m/src/lib.rs': (
        'pub const T: &str = include_str!("../../../data/t.json");\n'
        'pub const G: &[u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/g.json"));\n'
        'macro_rules! fx { ($n:literal) => { include_str!(concat!("../../../fx/", $n)) }; }\n'
        '// include_str!("../../../data/mentioned.json"), include_str!("absent.json")\n'
        'pub const S: &str = r#"include_str!("../../../data/quoted.json")"#;\n'
        '#[path = "../../../island/model.clean"]\nmod model;\n'
        'include!(concat!(env!("OUT_DIR"), "/generated.rs"));\n'),
    'data/t.json': '{}', 'data/g.json': '{}', 'data/mentioned.json': '{}', 'data/quoted.json': '{}',
    'data/unnamed.json': '{}', 'data/c.bin': 'c', 'fx/a.lean': 'a', 'fx/sub/b.lean': 'b',
    'island/model.clean': 'mod child;\n',
    'island/child.rs': 'pub const C: &[u8] = include_bytes!("../data/c.bin");\n',
    'lean-toolchain': 'leanprover/lean4:v0\n', 'fixtures/w.bin': 'w',
    'vendor/v/Cargo.toml': '[package]\nname = "v"\n', 'vendor/v/README': 'r',
    'vendor/v/src/lib.rs': 'pub const D: &str = include_str!("../data.txt");\n', 'vendor/v/data.txt': 'd',
}
EXPECTED = ['data/t.json', 'data/g.json', 'fx/a.lean', 'fx/sub/b.lean', 'data/mentioned.json',
            'data/quoted.json', 'island/model.clean', 'island/child.rs', 'data/c.bin',
            'crates/m/table.tsv', 'crates/m/notes.md', 'lean-toolchain', 'fixtures/w.bin',
            'vendor/v/Cargo.toml', 'vendor/v/README', 'vendor/v/src/lib.rs', 'vendor/v/data.txt']
REFUSALS = [
    ('an include_str! in code naming no file', 'crates/m/src/lib.rs',
     'pub const X: &str = include_str!("absent.json");\n'),
    ('a wildcard include matching no file', 'crates/m/src/lib.rs',
     'macro_rules! y { ($n:literal) => { include_str!(concat!("../../../none/", $n)) }; }\n'),
    ('a #[path] naming no file', 'crates/m/src/lib.rs', '#[path = "absent.rs"]\nmod absent;\n'),
    ('OUT_DIR without a build script', 'vendor/v/src/lib.rs',
     'include!(concat!(env!("OUT_DIR"), "/generated.rs"));\n'),
    ('a path dependency outside the repository', 'crates/m/Cargo.toml',
     'w = { path = "../../../elsewhere" }\n'),
]


def source_tree(root):
    for rel, text in [*((p, p) for p in k.FIXED_INPUTS), *SOURCE_TREE.items(),
                      ('../elsewhere/Cargo.toml', '[package]\nname = "w"\n')]:
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text)
    for argv in (['init', '-q'], ['add', '-A']):
        subprocess.run(['git', '-C', str(root), *argv], check=True, capture_output=True)


def input_controls(check):
    """The input rule: a file a member's build reads moves the record; a use it cannot name refuses."""
    def verdict(path):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = k.check_record(path)
        return code, out.getvalue()
    with tempfile.TemporaryDirectory() as td:
        root = Path(td).resolve() / 'repository'
        source_tree(root)
        record = root / 'record.json'
        with patch.object(k, 'ROOT', root):
            inputs = k.source_inputs()
            record.write_text(json.dumps(dict(source_inputs=inputs, success=False)))
            code, before = verdict(record)
            (root / 'data/t.json').write_text('{"moved": true}')
            code_after, after = verdict(record)
            check('an include_str! target outside crates/ makes the record stale',
                  'stale source inputs' not in before and code_after == 1 and 'stale source inputs' in after)
            for rel in EXPECTED:
                check('input: ' + rel, rel in inputs)
            check('a file nothing names is no input', 'data/unnamed.json' not in inputs)
            old_rule = set(k.FIXED_INPUTS) | {p.relative_to(root).as_posix() for p in (root / 'crates').rglob('*')
                                               if p.suffix in ('.rs', '.toml')}
            check('no input of the 2026-11-13 rule is dropped', old_rule <= set(inputs))
            for name, rel, text in REFUSALS:
                original = (root / rel).read_text()
                (root / rel).write_text(original + text)
                try:
                    k.source_inputs()
                    refused = False
                except ValueError:
                    refused = True
                code, out = verdict(record)
                check('refuses ' + name, refused and code == 1 and 'not knowable here' in out)
                (root / rel).write_text(original)


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
    input_controls(check)
    l4l_checks = []
    lean4lean_selftest.selftest(l4l_checks)
    checks += len(l4l_checks)
    print(f'KSTAR_SELFTEST=ok checks={checks}; no quorum vote')
    return 0
