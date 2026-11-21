# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Portable neighbor selection must not weaken provenance-anchor checks."""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).with_name("check_provenance_anchors.py")
SPEC = importlib.util.spec_from_file_location("provenance_anchors", SCRIPT)
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


@contextlib.contextmanager
def working_directory(path):
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


class ProvenanceAnchorPathTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.clean = self.root / "clean"
        self.clean.mkdir()
        self.git_env = gate.repository_git_environment()
        self.trust = self.make_repo("separate Trust")
        self.ir = self.make_repo("separate TrustIR")

    def git(self, repo, *args):
        result = subprocess.run(
            ["git", "-C", str(repo), "-c", "user.name=Path Test",
             "-c", "user.email=path-test@example.invalid",
             "-c", "commit.gpgsign=false", *args],
            capture_output=True, text=True, env=self.git_env, check=True)
        return result.stdout.strip()

    def make_repo(self, name):
        repo = self.root / name
        repo.mkdir(exist_ok=True)
        self.git(repo, "init", "-q", "-b", "main")
        self.git(repo, "commit", "--allow-empty", "-qm", name)
        self.git(repo, "tag", "path-control")
        return repo

    def records(self, anchor):
        # Exercise the SAME fixed subject inventory, including its live ALLOW
        # accounting. The fixtures change records, not the production predicate.
        for name in gate.AUDITED:
            path = self.clean / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({"anchor": anchor, "allow": list(gate.ALLOW)}))

    def run_main(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with working_directory(self.clean), contextlib.redirect_stdout(out), \
                contextlib.redirect_stderr(err), mock.patch.object(gate, "selftest"):
            # The existing inline selftest runs independently in the real gate.
            # These controls execute its real main/check/ref predicate directly.
            try:
                status = gate.main([str(SCRIPT), *map(str, args)])
            except SystemExit as exc:
                status = exc.code
        return status, out.getvalue(), err.getvalue()

    def explicit_args(self):
        return ("--trust-repo", self.trust, "--trust-ir-repo", self.ir)

    def test_explicit_trust_root_resolves_real_tagged_anchor(self):
        self.records(self.git(self.trust, "rev-parse", "HEAD"))
        status, out, err = self.run_main(*self.explicit_args())
        self.assertEqual(status, 0, err)
        self.assertIn("PROVENANCE_ANCHORS=ok", out)
        self.assertIn(f"trust={self.trust.resolve()}", out)

    def test_explicit_trust_ir_root_resolves_real_tagged_anchor(self):
        self.records(self.git(self.ir, "rev-parse", "HEAD"))
        status, out, err = self.run_main(*self.explicit_args())
        self.assertEqual(status, 0, err)
        self.assertIn(f"trust-ir={self.ir.resolve()}", out)

    def test_default_paths_and_missing_default_neighbors_are_unchanged(self):
        self.make_repo("clean")
        self.records(self.git(self.clean, "rev-parse", "HEAD"))
        status, out, err = self.run_main()
        self.assertEqual(status, 0, err)
        self.assertIn("clean=. trust=../trust trust-ir=../trust-ir", out)

    def test_one_override_does_not_replace_the_other_default(self):
        self.records(self.git(self.trust, "rev-parse", "HEAD"))
        status, out, err = self.run_main("--trust-repo", self.trust)
        self.assertEqual(status, 0, err)
        self.assertIn("trust-ir=../trust-ir", out)

    def test_explicit_missing_directory_fails_before_anchor_checks(self):
        self.records(self.git(self.trust, "rev-parse", "HEAD"))
        status, out, err = self.run_main("--trust-repo", self.root / "missing")
        self.assertEqual(status, 2)
        self.assertIn("--trust-repo", err)
        self.assertNotIn("PROVENANCE_ANCHORS=ok", out)

    def test_explicit_empty_path_fails_instead_of_selecting_current_directory(self):
        status, _, err = self.run_main("--trust-ir-repo", "")
        self.assertEqual(status, 2)
        self.assertIn("nonempty Git worktree root", err)

    def test_non_repository_directory_is_rejected(self):
        status, _, err = self.run_main("--trust-repo", self.clean)
        self.assertEqual(status, 2)
        self.assertIn("not a Git worktree root", err)

    def test_regular_file_is_rejected(self):
        path = self.root / "not-a-directory"
        path.write_text("not a repository")
        status, _, err = self.run_main("--trust-repo", path)
        self.assertEqual(status, 2)
        self.assertIn("not a directory", err)

    def test_subdirectory_cannot_borrow_parent_repository_identity(self):
        child = self.trust / "child"
        child.mkdir()
        status, _, err = self.run_main("--trust-repo", child)
        self.assertEqual(status, 2)
        self.assertIn("inside another Git worktree", err)

    def test_canonical_symlink_to_exact_root_is_accepted(self):
        alias = self.root / "trust-alias"
        alias.symlink_to(self.trust, target_is_directory=True)
        self.records(self.git(self.trust, "rev-parse", "HEAD"))
        status, out, err = self.run_main("--trust-repo", alias)
        self.assertEqual(status, 0, err)
        self.assertIn(f"trust={self.trust.resolve()}", out)

    def test_option_typo_and_abbreviation_are_rejected(self):
        for option in ("--trust-reop", "--trust-rep", "--trust-ir-rep"):
            with self.subTest(option=option):
                status, _, err = self.run_main(option, self.trust)
                self.assertEqual(status, 2)
                self.assertIn("unrecognized arguments", err)

    def test_missing_option_argument_is_rejected(self):
        for option in ("--trust-repo", "--trust-ir-repo"):
            with self.subTest(option=option):
                status, _, err = self.run_main(option)
                self.assertEqual(status, 2)
                self.assertIn("expected one argument", err)

    def test_selftest_does_not_hide_invalid_explicit_path(self):
        status, _, err = self.run_main(
            "--selftest", "--trust-repo", self.root / "missing")
        self.assertEqual(status, 2)
        self.assertIn("--trust-repo", err)

    def test_overrides_do_not_make_absent_anchor_resolve(self):
        self.records("deadbeef1234")
        status, out, err = self.run_main(*self.explicit_args())
        self.assertEqual(status, 1)
        self.assertIn("deadbeef1234", err)
        self.assertNotIn("PROVENANCE_ANCHORS=ok", out)

    def test_overrides_do_not_make_local_branch_only_anchor_shareable(self):
        self.git(self.trust, "tag", "-d", "path-control")
        self.records(self.git(self.trust, "rev-parse", "HEAD"))
        status, _, err = self.run_main(*self.explicit_args())
        self.assertEqual(status, 1)
        self.assertIn("PROVENANCE ANCHORS: FAIL", err)

    def test_overrides_do_not_drop_missing_subject_file(self):
        self.records(self.git(self.trust, "rev-parse", "HEAD"))
        missing = self.clean / gate.AUDITED[-1]
        missing.unlink()
        status, _, err = self.run_main(*self.explicit_args())
        self.assertEqual(status, 1)
        self.assertIn(gate.AUDITED[-1], err)
        self.assertIn("audited record file does not exist", err)

    def test_hook_context_cannot_redirect_root_or_anchor_resolution(self):
        self.records(self.git(self.trust, "rev-parse", "HEAD"))
        with mock.patch.dict(os.environ, {
            "GIT_DIR": str(self.ir / ".git"), "GIT_WORK_TREE": str(self.ir),
            "GIT_COMMON_DIR": str(self.ir / ".git"),
        }):
            status, out, err = self.run_main(*self.explicit_args())
            self.assertEqual(status, 0, err)
            self.assertIn(f"trust={self.trust.resolve()}", out)
            # Neither a real unrelated repo nor its tag may launder a plain dir.
            status, _, err = self.run_main("--trust-repo", self.clean)
            self.assertEqual(status, 2)
            self.assertIn("not a Git worktree root", err)

    def test_reachability_selftest_at_all_digit_orphan_timestamp(self):
        # In the original fixture this date yields orphan prefix 048076796.
        date = "1700000131 +0000"
        result = subprocess.run([sys.executable, "-B", str(SCRIPT), "--selftest"],
                                cwd=SCRIPT.parent.parent, capture_output=True, text=True,
                                env={**self.git_env, "GIT_AUTHOR_DATE": date, "GIT_COMMITTER_DATE": date})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_git_inventory_is_cleared_without_dropping_global_configuration(self):
        with mock.patch.dict(os.environ, {
            "GIT_DIR": str(self.ir / ".git"),
            "GIT_OBJECT_DIRECTORY": str(self.ir / ".git" / "objects"),
            "GIT_CONFIG_GLOBAL": str(self.root / "user-git-config"),
        }):
            env = gate.repository_git_environment()
        self.assertNotIn("GIT_DIR", env)
        self.assertNotIn("GIT_OBJECT_DIRECTORY", env)
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], str(self.root / "user-git-config"))

    def test_failed_or_malformed_git_inventory_is_refused(self):
        for status, stdout in ((1, ""), (0, ""), (0, "GIT_DIR\nPATH\n")):
            with self.subTest(status=status, stdout=stdout), mock.patch.object(
                gate.subprocess, "run",
                return_value=subprocess.CompletedProcess([], status, stdout, ""),
            ):
                with self.assertRaisesRegex(ValueError, "cannot enumerate"):
                    gate.repository_git_environment()

    def test_local_gate_executes_controls_and_forwards_only_scoped_options(self):
        local_gate = SCRIPT.with_name("local_gate.sh").read_text()
        leg = local_gate.split("# GATE-LEG: provenance-anchors\n", 1)[1]
        leg = leg.split("# GATE-LEG: census-output-pin\n", 1)[0]
        self.assertIn('"$GATE_PYTHON" scripts/test_provenance_anchor_paths.py', leg)
        block = leg[leg.index("  provenance_args=("):]
        prefix = "set -eu\ncapture() { printf '%s\\n' \"$@\"; }\n"
        prefix += "GATE_PYTHON=capture\nfail() { exit 1; }\n"
        env = self.git_env.copy()
        env.pop("CLEAN_GATE_TRUST_REPO", None)
        env.pop("CLEAN_GATE_TRUST_IR_REPO", None)
        cases = (
            ({}, ["scripts/check_provenance_anchors.py"]),
            ({"CLEAN_GATE_TRUST_REPO": str(self.trust),
              "CLEAN_GATE_TRUST_IR_REPO": str(self.ir)},
             ["scripts/check_provenance_anchors.py", "--trust-repo", str(self.trust),
              "--trust-ir-repo", str(self.ir)]),
            ({"CLEAN_GATE_TRUST_REPO": ""},
             ["scripts/check_provenance_anchors.py", "--trust-repo", ""]),
        )
        for overrides, expected in cases:
            with self.subTest(overrides=overrides):
                result = subprocess.run(
                    ["/bin/bash", "--noprofile", "--norc", "-c", prefix + block],
                    capture_output=True, text=True, env={**env, **overrides})
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.splitlines(), expected)


if __name__ == "__main__":
    unittest.main()
