# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Self-test for scripts/tactic_parity/mint_lean_verdicts.py, on FAKE Lean executables.

The minter is the only code in the family gates that runs Lean, so what it
must refuse is pinned here without running Lean at all: a missing binary, a
binary that is the aterm reroute to Clean, a binary of the right version but
another build (`--githash`), exit 0 with no output, exit 1 with no error, a
non-JSON line, the wall cap, a message in the header, a split reading that
disagrees with the whole-file one, a stray `example`, an `unknown tactic` error
that points at no tactic, and that a refusal writes nothing (the write is
atomic). A good fake mint must pass the gate's own checks and record the
unknown tactic, `--check` must see a changed verdict or unknown tactic, and
`--file-verdict` must give 0 / 1 (an error, or a `sorry` warning) / 2. The
local_gate.sh `tactic-lean-verdicts` leg is run from its own bytes on a stub
Python: SKIPPED only for exit 2 with the minter's skip line.
"""

import contextlib
import io
import json
import os
import shlex
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.tactic_parity import mint_lean_verdicts as mint

fg, lv = mint.fg, mint.lv
ROOT = Path(__file__).resolve().parent.parent
GITHASH = lv.ORACLE_GITHASHES["v4.30.0-rc2"]
FAKE = """import json, os, re, sys, time
mode = os.environ.get("FAKE_LEAN_MODE", "good")
args = sys.argv[1:]
if args == ["--version"]:
    print("Clean 0.61.0 (the lean front door)" if mode == "reroute" else
          "Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit {gh}, Release)")
    sys.exit(0)
if args == ["--githash"]:
    print("0" * 40 if mode == "wronghash" else "{gh}")
    sys.exit(0)
path = args[1]
lines = open(path).read().splitlines()
if mode == "hang":
    time.sleep(30)
if mode == "silent":
    sys.exit(0)
if mode == "nonjson":
    print("not json")
    sys.exit(0)
msgs = []
def msg(line, sev, data, col=0):
    msgs.append({{"pos": {{"line": line, "column": col}}, "severity": sev, "data": data}})
if mode == "header":
    msg(1, "error", "unknown package 'Init'")
decl = {{}}
for i, ln in enumerate(lines, 1):
    m = re.match(r"(?:theorem|def) (\\w+)", ln)
    if m:
        decl[m.group(1)] = (i, ln)
bad = {{n for n, (_, ln) in decl.items() if "bogus_tac" in ln}}
bad |= set(filter(None, os.environ.get("FAKE_LEAN_BAD", "").split(",")))
if mode == "disagree" and os.path.basename(path).startswith("whole_"):
    bad.add("p_a")
for n in sorted(bad & set(decl)):
    ln = decl[n][1]
    # Lean points one past the unknown tactic's first character.
    col = ln.find(":=") + 1 if mode == "notoken" else ln.find("bogus_tac") + 1 if "bogus_tac" in ln else 0
    msg(decl[n][0], "error", "unknown tactic", col)
for n, (i, ln) in decl.items():
    if "sorry" in ln:
        msg(i, "warning", "declaration uses `sorry`", 8)
for i, ln in enumerate(lines, 1):
    m = re.match(r"#print axioms (\\S+)", ln)
    if m:
        n = m.group(1)
        if n not in decl:
            msg(i, "error", "Unknown constant `%s`" % n)
        else:
            msg(i, "information", "'%s' depends on axioms: [sorryAx]" % n if n in bad else
                "'%s' does not depend on any axioms" % n)
for m in msgs:
    print(json.dumps(m))
if mode == "exit1":
    sys.exit(1)
sys.exit(1 if any(m["severity"] == "error" for m in msgs) else 0)
"""
FIXTURE = """import Init

theorem canary_m (n : Nat) : n = n := rfl

/-- a docstring the span is pulled back over -/
theorem p_a (n : Nat) : n + 0 = n := rfl
theorem p_b (n : Nat) : n = n := by bogus_tac
"""
MANIFEST = {"family": "g_auto", "plan": "test", "plan_family_total": 2, "comparison_basis": "test",
            "files": [{"file": "m.lean", "label": "m", "canary": "canary_m", "helpers": [],
                       "required": [], "probes": ["p_a", "p_b"]}]}


class MintTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="mint-test-"))
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))
        self.fam = self.tmp / "fixtures" / "g_auto"
        self.fam.mkdir(parents=True)
        self.fixture(FIXTURE)
        (self.fam / "MANIFEST.json").write_text(json.dumps(MANIFEST))
        self.lean = self.tmp / "toolchain" / "bin" / "lean"
        self.lean.parent.mkdir(parents=True)
        # The fake runs through a shell exec, not a `#!{sys.executable}` line:
        # a shebang breaks when the interpreter's path holds a space (aterm's
        # is under "Application Support"), and `exec` keeps one pid for the
        # hang arm's kill.
        body = self.tmp / "fake_lean.py"
        body.write_text(FAKE.format(gh=GITHASH))
        self.lean.write_text(
            "#!/bin/sh\n"
            f'exec {shlex.quote(sys.executable)} {shlex.quote(str(body))} "$@"\n'
        )
        self.lean.chmod(0o755)
        for target, attr, val in ((fg, "FIXTURE_ROOT", self.fam.parent),):
            p = mock.patch.object(target, attr, val)
            p.start()
            self.addCleanup(p.stop)
        self.mode("good")

    def fixture(self, text):
        (self.fam / "m.lean").write_text(text)

    def mode(self, mode, bad=""):
        p = mock.patch.dict(os.environ, {"FAKE_LEAN_MODE": mode, "FAKE_LEAN_BAD": bad})
        p.start()
        self.addCleanup(p.stop)

    def main(self, *args, lean=None):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = mint.main(["--family", "g_auto", "--lean", str(lean or self.lean), *args])
        return rc, out.getvalue()

    def assertRefused(self, needle, exc=mint.Refused):
        with self.assertRaises(exc) as ctx:
            mint.mint_family("g_auto", self.lean, ROOT)
        self.assertIn(needle, str(ctx.exception))

    def test_a_good_mint_passes_the_gates_own_checks(self):
        rc, out = self.main()
        self.assertEqual(rc, 0, out)
        self.assertIn("rows=3 accept=2 reject=1", out)
        doc = lv.load_verdicts(self.fam)
        rows = doc["files"]["m.lean"]["rows"]
        self.assertEqual((rows["p_b"]["verdict"], rows["p_b"]["class"]), ("reject", "unknown-tactic"))
        self.assertEqual((rows["p_b"]["unknown_tactics"], rows["p_a"]["unknown_tactics"]), (["bogus_tac"], []))
        self.assertEqual(rows["p_a"]["axioms"], [])
        self.assertEqual(lv.verdict_problems("g_auto", MANIFEST, self.fam, ROOT), ([], []))
        self.assertEqual(self.main("--check")[0], 0)

    def test_check_sees_a_changed_verdict(self):
        self.assertEqual(self.main()[0], 0)
        self.mode("good", bad="p_a")
        rc, out = self.main("--check")
        self.assertEqual(rc, 1, out)
        self.assertIn("p_a.verdict 'accept' -> 'reject'", out)

    def test_check_sees_a_changed_unknown_tactic(self):
        self.assertEqual(self.main()[0], 0)
        doc = lv.load_verdicts(self.fam)
        doc["files"]["m.lean"]["rows"]["p_b"]["unknown_tactics"] = ["norm_num"]
        (self.fam / lv.VERDICTS_FILE).write_text(json.dumps(doc))
        rc, out = self.main("--check")
        self.assertEqual(rc, 1, out)
        self.assertIn("p_b.unknown_tactics ['norm_num'] -> ['bogus_tac']", out)

    def test_a_missing_binary_is_no_usable_lean(self):
        rc, out = self.main(lean=self.tmp / "nonexistent")
        self.assertEqual(rc, 2, out)
        self.assertIn("skipped:no-usable-lean", out)

    def test_the_aterm_reroute_to_clean_is_refused(self):
        self.mode("reroute")
        self.assertRefused("not the oracle world's Lean", mint.Unusable)

    def test_the_right_version_of_another_build_is_no_usable_lean(self):
        self.mode("wronghash")
        self.assertRefused("--githash says '0000000000", mint.Unusable)
        rc, out = self.main()
        self.assertEqual(rc, 2, out)
        self.assertIn("MINT_LEAN_VERDICTS=skipped:no-usable-lean family=g_auto", out)
        good = self.tmp / "good.lean"
        good.write_text("theorem t : True := trivial\n")
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(mint.file_verdict(good, self.lean, ROOT), 2)

    def test_an_unknown_tactic_error_pointing_at_no_tactic_is_refused(self):
        self.mode("notoken")
        self.assertRefused("an `unknown tactic` error on p_b points at no tactic token")

    def test_exit_0_with_no_output_is_refused(self):
        self.mode("silent")
        self.assertRefused("no `#print axioms` reading came back")

    def test_exit_1_with_no_error_is_refused(self):
        self.mode("exit1")
        self.assertRefused("the exit code and the messages disagree")

    def test_a_non_json_line_is_refused(self):
        self.mode("nonjson")
        self.assertRefused("is not JSON")

    def test_the_wall_cap_is_no_usable_lean(self):
        self.mode("hang")
        with mock.patch.object(mint, "WALL_S", 1.0):
            self.assertRefused("cap-wall", mint.Unusable)

    def test_a_header_message_is_refused(self):
        self.mode("header")
        self.assertRefused("a message in the header")

    def test_a_split_whole_disagreement_is_refused(self):
        self.mode("disagree")
        self.assertRefused("the rows are not independent")

    def test_a_stray_example_is_refused(self):
        self.fixture(FIXTURE + "example : True := trivial\n")
        self.assertRefused("a column-0 command no row owns")

    def test_a_refusal_writes_nothing(self):
        target = self.fam / lv.VERDICTS_FILE
        target.write_text("committed bytes\n")
        self.mode("nonjson")
        rc, out = self.main()
        self.assertEqual(rc, 1, out)
        self.assertIn("nothing written", out)
        self.assertEqual(target.read_text(), "committed bytes\n")
        self.assertEqual(sorted(p.name for p in self.fam.iterdir()), ["LEAN_VERDICTS.json", "MANIFEST.json", "m.lean"])

    def test_file_verdict_exit_codes(self):
        good, bad, sorry = self.tmp / "good.lean", self.tmp / "bad.lean", self.tmp / "sorry.lean"
        good.write_text("theorem t : True := trivial\n")
        bad.write_text("theorem t : True := by bogus_tac\n")
        sorry.write_text("theorem t : True := sorry\n")  # exit 0 with a warning: not a proof
        quiet = io.StringIO()
        with contextlib.redirect_stderr(quiet):
            self.assertEqual(mint.file_verdict(good, self.lean, ROOT), 0)
            self.assertEqual(mint.file_verdict(bad, self.lean, ROOT), 1)
            self.assertEqual(mint.file_verdict(sorry, self.lean, ROOT), 1)
            self.assertEqual(mint.file_verdict(good, self.tmp / "nonexistent", ROOT), 2)
        self.assertIn("LEAN_FILE_VERDICT=reject", quiet.getvalue())
        self.assertIn("class=sorry-warning", quiet.getvalue())

    def test_the_default_lean_is_the_oracle_toolchain_by_absolute_path(self):
        path = mint.default_lean("leanprover/lean4:v4.30.0-rc2")
        self.assertTrue(path.is_absolute())
        self.assertEqual(path.parts[-3:], ("leanprover--lean4---v4.30.0-rc2", "bin", "lean"))


LEG_MARK = "  # GATE-LEG: tactic-lean-verdicts\n"


class LocalGateLegTests(unittest.TestCase):
    """The leg's own bytes from scripts/local_gate.sh, on a stub GATE_PYTHON."""

    def run_leg(self, rc, out):
        gate = (ROOT / "scripts" / "local_gate.sh").read_text(encoding="utf-8")
        start = gate.index(LEG_MARK)
        block = gate[start:gate.index("\n  done\n", start) + len("\n  done\n")]
        tmp = Path(tempfile.mkdtemp(prefix="leg-test-"))
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        stub = tmp / "python"
        stub.write_text('#!/bin/sh\nprintf "%s\\n" "$STUB_OUT"\nexit "$STUB_RC"\n')
        stub.chmod(0o755)
        script = ('set -euo pipefail\nfail() { echo "LOCAL GATE: FAIL — $1"; exit 1; }\n'
                  f'GATE_PYTHON={stub}\n{block}echo LEG-DONE\n')
        return subprocess.run(["bash", "-c", script], capture_output=True, text=True, timeout=60,
                              env={**os.environ, "STUB_RC": str(rc), "STUB_OUT": out})

    def test_exit_2_with_the_skip_line_is_skipped(self):
        proc = self.run_leg(2, "MINT_LEAN_VERDICTS=skipped:no-usable-lean family=g_auto (no executable Lean)")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(proc.stdout.count("TACTIC-LEAN-VERDICTS=SKIPPED"), 2)
        self.assertIn("LEG-DONE", proc.stdout)

    def test_exit_2_without_it_fails(self):
        """argparse's usage error, and Python's `can't open file`, are exit 2 too."""
        for out in ("usage: mint_lean_verdicts.py [-h]\nerror: argument --family: invalid choice",
                    "python3: can't open file 'scripts/tactic_parity/mint_lean_verdicts.py'"):
            proc = self.run_leg(2, out)
            self.assertEqual(proc.returncode, 1, proc.stdout)
            self.assertIn("LOCAL GATE: FAIL — tactic family Lean verdicts g_auto", proc.stdout)
            self.assertNotIn("SKIPPED", proc.stdout)

    def test_other_exits(self):
        self.assertEqual(self.run_leg(1, "MINT_LEAN_VERDICTS=differs family=g_auto").returncode, 1)
        proc = self.run_leg(0, "MINT_LEAN_VERDICTS=same family=g_auto")
        self.assertEqual(proc.returncode, 0, proc.stdout)
        self.assertIn("LEG-DONE", proc.stdout)


if __name__ == "__main__":
    unittest.main()
