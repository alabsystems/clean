#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
"""Run only the real substitution helper against temporary inert fixtures.

The full perturbation battery and its repository runtime inputs are never run.
The fixed relative subject prevents ambient source overrides from selecting an
older alternate script. Python optimization is propagated to the helper child.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from resource_transport import resource_fds

SOURCE = SCRIPTS / 'crystal_perturb_float_div.sh'


def book(raw, mode):
    return {'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw), 'mode': mode}


def extract_sub(raw):
    starts = list(re.finditer(rb'^sub\(\) \{ python3 - .*\n', raw, re.M))
    if len(starts) != 1:
        raise ValueError('expected exactly one real sub() definition')
    start = starts[0].start()
    if not starts[0].group().endswith(b"<<'PY'\n"):
        raise ValueError('sub() Python heredoc boundary changed')
    heredoc = re.search(rb'^PY\n', raw[starts[0].end():], re.M)
    if heredoc is None:
        raise ValueError('sub() Python heredoc terminator missing')
    after_python = starts[0].end() + heredoc.end()
    close = re.search(rb'^}\n', raw[after_python:], re.M)
    if close is None:
        raise ValueError('sub() function terminator missing')
    return raw[start:after_python + close.end()]


class AnchorGuards(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if any(name in os.environ for name in ('BASH_ENV', 'ENV')) or any(name.startswith('BASH_FUNC_') for name in os.environ):
            raise ValueError('unreviewed Bash startup/function environment')
        fd = os.open(SOURCE, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
        with os.fdopen(fd, 'rb') as stream:
            before = os.fstat(stream.fileno())
            if not stat.S_ISREG(before.st_mode) or before.st_size > 1024 * 1024:
                raise ValueError('subject must be a bounded regular script')
            raw = stream.read(1024 * 1024 + 1)
            after = os.fstat(stream.fileno())
        fields = lambda value: (value.st_dev, value.st_ino, value.st_mode,
                                value.st_size, value.st_mtime_ns, value.st_ctime_ns)
        if fields(before) != fields(after) or len(raw) != before.st_size:
            raise ValueError('subject changed during extraction')
        cls.function = extract_sub(raw)
        cls.source_book = book(raw, stat.S_IMODE(before.st_mode))

    def invoke(self, original, suffix='.rs', want=None):
        with tempfile.TemporaryDirectory(prefix='crystal-anchor-inert-') as temporary:
            root = Path(temporary)
            fixture = root / ('anchor' + suffix)
            fixture.write_bytes(original)
            fixture.chmod(0o640)
            before = book(original, stat.S_IMODE(fixture.stat().st_mode))
            # Exact extracted function bytes; neither the battery preamble nor
            # any baseline/mutation/revert call is part of the inert wrapper.
            wrapper = b'#!/bin/bash\nset -uo pipefail\n' + self.function + b'\nsub "$@"\n'
            script = root / 'only-sub.sh'
            script.write_bytes(wrapper)
            script.chmod(0o700)
            argv = ['/bin/bash', str(script), str(fixture), 'ANCHOR', 'REPLACED']
            if want is not None:
                argv.append(str(want))
            env = dict(os.environ)
            env['PYTHONOPTIMIZE'] = str(sys.flags.optimize)
            completed = subprocess.run(argv, cwd=root, env=env, stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, check=False,
                                       pass_fds=resource_fds(env))
            after_raw = fixture.read_bytes()
            after = book(after_raw, stat.S_IMODE(fixture.stat().st_mode))
            record = {'scope': 'Inert extracted-sub fixture only; no battery/compiler/native authority.',
                      'case': self.id(), 'python_optimize': sys.flags.optimize,
                      'source': self.source_book, 'function_sha256': hashlib.sha256(self.function).hexdigest(),
                      'wrapper': book(wrapper, 0o700), 'argv': argv,
                      'actual_returncode': completed.returncode,
                      'stdout': completed.stdout.decode('utf-8'), 'stderr': completed.stderr.decode('utf-8'),
                      'before': dict(before, base64=base64.b64encode(original).decode('ascii')),
                      'after': dict(after, base64=base64.b64encode(after_raw).decode('ascii'))}
            print(json.dumps(record, allow_nan=False), flush=True)
            return completed, after_raw, before, after

    def accepts(self, original, expected, suffix='.rs', want=None):
        result, after, before_book, after_book = self.invoke(original, suffix, want)
        self.assertEqual(result.returncode, 0, result.stderr.decode('utf-8'))
        self.assertEqual(result.stdout, b'')
        self.assertEqual(result.stderr, b'')
        self.assertEqual(after, expected)
        self.assertEqual(after_book['mode'], before_book['mode'])

    def refuses(self, original, reason, suffix='.rs', want=None):
        result, after, before_book, after_book = self.invoke(original, suffix, want)
        self.assertEqual(result.returncode, 9, 'real sub() unexpectedly accepted or failed for another exit status')
        self.assertIn(b'FATAL: substitution failed', result.stdout)
        self.assertIn(reason.encode(), result.stderr)
        self.assertEqual(after, original, 'refusal changed fixture bytes')
        self.assertEqual(after_book, before_book, 'refusal changed fixture bytes or mode')

    def test_one_rust_declaration_changes_exactly_once(self):
        self.accepts(b'const SRC_ONE: &str = "ANCHOR";\n', b'const SRC_ONE: &str = "REPLACED";\n')

    def test_non_declaration_lines_are_ignored(self):
        before = b'// ANCHOR\nlet other = "ANCHOR";\n const SRC_INDENTED: &str = "ANCHOR";\nconst SRC_ONE: &str = "ANCHOR";\n'
        self.accepts(before, before.rsplit(b'ANCHOR', 1)[0] + b'REPLACED";\n')

    def test_json_exact_two_lines_change(self):
        before = b'{\n  "markers_detail": "ANCHOR",\n  "markers_exact": "ANCHOR"\n}\n'
        self.accepts(before, before.replace(b'ANCHOR', b'REPLACED'), '.json', 2)

    def test_missing_anchor_refuses_without_writing(self):
        self.refuses(b'const SRC_ONE: &str = "other";\n', 'anchor must match exactly 1 line(s), matched 0')

    def test_multiple_matching_lines_refuse_without_writing(self):
        self.refuses(b'const SRC_ONE: &str = "ANCHOR";\nconst SRC_TWO: &str = "ANCHOR";\n',
                     'anchor must match exactly 1 line(s), matched 2')

    def test_wrong_explicit_count_refuses_without_writing(self):
        self.refuses(b'{"one": "ANCHOR"}\n', 'anchor must match exactly 2 line(s), matched 1', '.json', 2)

    def test_repeated_same_line_refuses_without_writing(self):
        self.refuses(b'const SRC_ONE: &str = "ANCHOR ANCHOR";\n', 'anchor not unique within its line')

    def test_later_invalid_line_refuses_without_writing(self):
        self.refuses(b'"one": "ANCHOR",\n"two": "ANCHOR ANCHOR"\n',
                     'anchor not unique within its line', '.json', 2)

    def test_non_declaration_only_refuses_without_writing(self):
        self.refuses(b'// ANCHOR\nlet other = "ANCHOR";\n', 'anchor must match exactly 1 line(s), matched 0')

    def test_empty_file_refuses_without_writing(self):
        self.refuses(b'', 'anchor must match exactly 1 line(s), matched 0')

    def test_nonpositive_expected_counts_refuse_without_writing(self):
        for want in (0, -1):
            with self.subTest(want=want):
                self.refuses(b'{"one": "ANCHOR"}\n', 'expected anchor count must be positive', '.json', want)

    def test_zero_expected_empty_file_refuses_without_writing(self):
        self.refuses(b'', 'expected anchor count must be positive', '.json', 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
