#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The committed data/crystal_freshness_scope.json is derivable, and `--emit`
refuses instead of crashing when it cannot read the tree it is asked about.

The scope file says "Derivable: `scripts/crystal_freshness_scope.py --emit`".
Until 2026-09-24 that was false: the record it binds names clean_source_rev
c46d6594b, a never-pushed lane commit, and `--emit` died in `git archive` with a
traceback. `--emit` now reads the kernel tree at `kernel_tree_read_at` -- a
pushed commit whose kernel digest must equal the record's -- and `--check`
compares the re-derivation with the committed file.
"""

from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "crystal_freshness_scope.py"
NOT_A_COMMIT = "0123456789abcdef0123456789abcdef01234567"


def emit_check(*extra):
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--emit", "--check", *extra],
        cwd=ROOT, capture_output=True, text=True, check=False,
    )


class ScopeEmitTests(unittest.TestCase):
    def test_the_committed_scope_file_is_re_derived_byte_for_byte(self):
        out = emit_check()
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertIn("SCOPE_EMIT=reproduced", out.stdout)

    def test_a_witness_whose_kernel_is_not_the_records_is_refused(self):
        # HEAD's kernel is not the record's; and once the record's rev is a
        # commit here, any --witness is refused outright.
        out = emit_check("--witness", "HEAD~0")
        self.assertEqual(out.returncode, 2, out.stdout + out.stderr)
        self.assertIn("SCOPE UNUSABLE", out.stderr)

    def test_a_rev_that_is_not_a_commit_is_refused_not_a_traceback(self):
        out = emit_check("--at", NOT_A_COMMIT)
        self.assertEqual(out.returncode, 2, out.stdout + out.stderr)
        self.assertIn("is not a commit in this repository", out.stderr)
        self.assertNotIn("Traceback", out.stderr)


if __name__ == "__main__":
    unittest.main()
