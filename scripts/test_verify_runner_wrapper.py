#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Tests for the suite runner's ENTRY: its interpreter, its board, its metadata.

Three defects, each of which made `scripts/verify_runner.sh status` -- the
command CLAUDE.md names as the answer to "is the suite green?" -- unable to
answer on this machine (2026-09-24 process audit and re-measurement):

  1. the wrapper ran `/usr/bin/env python3`, Apple's 3.9, and the runner
     imports a checker that needs `tomllib` (3.11+): ModuleNotFoundError;
  2. once past that, `targo metadata` was parsed from stdout MERGED with
     stderr, and the `cargo` on PATH announces itself on stderr: a
     JSONDecodeError at char 0 on every call;
  3. the default board held clean-verify and clean-elab only, so two of the
     three crates that went red after the wave-3 merges had no row.

Run: python3 scripts/test_verify_runner_wrapper.py
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

# Same sandboxing as test_verify_runner.py: the module resolves its writable
# locations at import, and a test must never write into the real ones.
_SANDBOX = tempfile.mkdtemp(prefix="verify_runner_wrapper_test_")
os.environ["VERIFY_RUNNER_STATE_DIR"] = os.path.join(_SANDBOX, "state")
os.environ["VERIFY_RUNNER_TARGET_DIR"] = os.path.join(_SANDBOX, "target")
os.environ["VERIFY_RUNNER_JOURNAL_DIR"] = os.path.join(_SANDBOX, "journal")

import verify_runner as vr  # noqa: E402

WRAPPER = SCRIPTS / "verify_runner.sh"
PINNED = SCRIPTS / "verify_runner_pinned.sh"


def _fake_python(path: Path, has_tomllib: bool, marker: str) -> None:
    """A stand-in interpreter: answers the tomllib probe as told, and when the
    wrapper execs it for real, prints `marker` plus its argv and exits 0."""
    probe_rc = 0 if has_tomllib else 1
    path.write_text(
        "#!/bin/sh\n"
        f'if [ "$1" = "-c" ]; then exit {probe_rc}; fi\n'
        f'echo "{marker} $*"\n'
    )
    path.chmod(0o755)


class TestWrapperInterpreter(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="vr_wrapper_py_"))

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def _run(self, env_extra: dict[str, str], path: str) -> subprocess.CompletedProcess:
        env = {k: v for k, v in os.environ.items()
               if k not in ("CLEAN_GATE_PYTHON", "VERIFY_RUNNER_SCRIPT")}
        env.update(env_extra)
        env["PATH"] = path
        return subprocess.run(["/bin/bash", str(WRAPPER), "status"], env=env,
                              capture_output=True, text=True, timeout=60, check=False)

    def test_verify_runner_wrapper_clean_gate_python_is_honoured_first(self):
        chosen = self.tmp / "chosen-python"
        _fake_python(chosen, has_tomllib=True, marker="CHOSEN")
        _fake_python(self.tmp / "python3", has_tomllib=True, marker="PATH-PYTHON3")
        proc = self._run({"CLEAN_GATE_PYTHON": str(chosen)}, f"{self.tmp}:/usr/bin:/bin")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertTrue(proc.stdout.startswith("CHOSEN "), proc.stdout)
        self.assertIn("verify_runner.py status", proc.stdout)

    def test_verify_runner_wrapper_python_without_tomllib_is_skipped(self):
        # The 2026-09-24 shape: the FIRST python3 on PATH is a 3.9 without
        # tomllib. The wrapper must walk past it, never exec it.
        _fake_python(self.tmp / "python3", has_tomllib=False, marker="OLD-PYTHON3")
        _fake_python(self.tmp / "python3.12", has_tomllib=True, marker="PY312")
        proc = self._run({}, f"{self.tmp}:/usr/bin:/bin")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertNotIn("OLD-PYTHON3", proc.stdout)
        self.assertTrue(proc.stdout.startswith("PY312 "), proc.stdout)

    def test_verify_runner_wrapper_resolver_matches_local_gate_candidates(self):
        # One resolution rule, three copies (local_gate.sh, the pre-push hook,
        # this wrapper): pin that the candidate lists have not drifted apart.
        needle = ('"${CLEAN_GATE_PYTHON:-}" python3 python3.14 python3.13 python3.12 python3.11')
        for script in (WRAPPER, SCRIPTS / "local_gate.sh"):
            self.assertIn(needle, script.read_text(), script)
        self.assertIn("/opt/homebrew/bin/python3 /usr/local/bin/python3", WRAPPER.read_text())

    def test_verify_runner_pinned_wrapper_delegates_interpreter_choice(self):
        text = PINNED.read_text()
        code = [ln for ln in text.splitlines() if ln.strip() and not ln.lstrip().startswith("#")]
        self.assertFalse(any("/usr/bin/env python3" in ln for ln in code),
                         "the pinned wrapper must not pick an interpreter of its own")
        # THIS checkout's wrapper, never the pinned worktree's: a pin older than
        # the resolver would carry the 3.9 death back with it.
        self.assertTrue(any('exec bash "$REPO_ROOT/scripts/verify_runner.sh"' in ln for ln in code), code)
        self.assertFalse(any('$WORKTREE/scripts/verify_runner.sh' in ln for ln in code), code)
        self.assertTrue(any('VERIFY_RUNNER_SCRIPT="$WORKTREE/scripts/verify_runner.py"' in ln for ln in code), code)

    def test_verify_runner_wrapper_runner_script_override_is_execed(self):
        _fake_python(self.tmp / "python3", has_tomllib=True, marker="PY")
        pinned_runner = self.tmp / "pinned" / "scripts" / "verify_runner.py"
        proc = self._run({"VERIFY_RUNNER_SCRIPT": str(pinned_runner)}, f"{self.tmp}:/usr/bin:/bin")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn(f"{pinned_runner} status", proc.stdout)
        # Control: unset, it is this checkout's own runner.
        proc = self._run({}, f"{self.tmp}:/usr/bin:/bin")
        self.assertIn(f"{SCRIPTS / 'verify_runner.py'} status", proc.stdout)


class TestCargoMetadata(unittest.TestCase):
    def test_cargo_metadata_banner_on_stderr_is_not_parsed(self):
        banner = "aterm: 'cargo' is the Rust name; on Trust the tool is 'targo'.\n"
        document = '{"packages": [], "workspace_root": "/x"}'

        def fake_run(argv, **kwargs):
            # Honour the caller's plumbing the way the OS would: a caller that
            # merges stderr into stdout gets the banner in front of the JSON.
            if kwargs.get("stderr") is subprocess.STDOUT:
                return subprocess.CompletedProcess(argv, 0, stdout=banner + document, stderr=None)
            return subprocess.CompletedProcess(argv, 0, stdout=document, stderr=banner)

        with mock.patch.object(vr.subprocess, "run", side_effect=fake_run):
            self.assertEqual(vr.cargo_metadata()["workspace_root"], "/x")

    def test_cargo_metadata_non_json_stdout_is_refused_naming_stderr(self):
        done = subprocess.CompletedProcess(args=[], returncode=0, stdout="not json",
                                           stderr="warning: something cargo said")
        with mock.patch.object(vr.subprocess, "run", return_value=done):
            with self.assertRaises(SystemExit) as ctx:
                vr.cargo_metadata()
        self.assertIn("something cargo said", str(ctx.exception))

    def test_cargo_metadata_failure_is_refused(self):
        done = subprocess.CompletedProcess(args=[], returncode=101, stdout="", stderr="error: boom")
        with mock.patch.object(vr.subprocess, "run", return_value=done):
            with self.assertRaises(SystemExit) as ctx:
                vr.cargo_metadata()
        self.assertIn("boom", str(ctx.exception))


class TestDefaultBoard(unittest.TestCase):
    def test_default_board_includes_every_frontend_crate_with_its_own_targets(self):
        for pkg in ("clean-verify", "clean-elab", "clean-parser", "clean-olean",
                    "clean-kernel", "clean-ck0"):
            self.assertIn(pkg, vr.DEFAULT_PACKAGES)

    def test_default_board_enumerates_parser_and_olean_targets(self):
        meta = {"packages": [
            {"name": "clean-parser", "targets": [
                {"name": "clean_parser", "kind": ["lib"], "test": True},
                {"name": "no_silent_trees", "kind": ["test"], "test": True}]},
        ]}
        ids = [t["id"] for t in vr.package_targets(meta, "clean-parser")]
        self.assertEqual(ids, ["clean-parser::lib", "clean-parser::test::no_silent_trees"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
