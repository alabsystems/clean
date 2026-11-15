#!/usr/bin/env python3
"""Tests for the honesty-critical logic in scripts/verify_runner.py.

The whole value of `data/suite_state/` is that a row cannot claim more than was
measured. Every test here pins one way that could silently break: a stored
GREEN outliving its inputs, a killed run reading as a pass, an externally
reported result being promoted without evidence.

Run: python3 scripts/test_verify_runner.py
"""

from __future__ import annotations

import atexit
import json
import math
import os
import re
import shlex
import sys
import tempfile
import subprocess
import threading
import time
import types
import unittest
from unittest import mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

# Redirect both writable locations BEFORE importing the module: it resolves
# them once at import. Without this, an end-to-end test would deposit synthetic
# records into the real data/suite_state/, where nothing downstream could tell
# them from measured ones.
_SANDBOX_OWNER = tempfile.TemporaryDirectory(prefix="verify_runner_test_")
atexit.register(_SANDBOX_OWNER.cleanup)
_SANDBOX = _SANDBOX_OWNER.name
os.environ["VERIFY_RUNNER_STATE_DIR"] = os.path.join(_SANDBOX, "state")
os.environ["VERIFY_RUNNER_TARGET_DIR"] = os.path.join(_SANDBOX, "target")
# Metadata queries invoke Cargo directly, outside run_one's environment setup.
os.environ["CARGO_TARGET_DIR"] = os.environ["VERIFY_RUNNER_TARGET_DIR"]
# THREE writable locations, not two. The journal is the third, and it was
# missed on the first pass: every `write_record` in this file appended to the
# real ~/.local/state/clean/suite-journal/ until this line existed, which is the
# same defect the two lines above exist to prevent -- synthetic entries in the
# durable artifact, indistinguishable to every later reader from measured ones.
os.environ["VERIFY_RUNNER_JOURNAL_DIR"] = os.path.join(_SANDBOX, "journal")

import verify_runner as vr  # noqa: E402
from resource_transport import resource_fds  # noqa: E402

# NO UNIT TEST MAY TOUCH THE MACHINE-WIDE ADMISSION GATE.
#
# `run_one` acquires a heavy_gate reservation for every target it runs, and the
# end-to-end classes below drive it with synthetic commands (`true`, `false`,
# a `sleep`). Unpatched, each of those blocks on a real 12 GB reservation.
#
# Measured 2026-08-23 on a busy box: this file wedged at
# `RunOne...synthetic::fail`, holding a 12 GB ticket in the real queue behind a
# fully-subscribed 96 GB budget, and was still waiting when its 300 s timeout
# expired -- so the suite could not be run at all while the machine was in use,
# and the 12 GB it reserved for a `/bin/false` starved work that needed it.
#
# The gate is a property of the RUNNER, not of these tests; the one test that is
# actually about acquisition keeps a real handle below and drives it against an
# absent gate script, which returns immediately.
_REAL_GATE_ACQUIRE = vr._gate_acquire
_REAL_GATE_RELEASE = vr._gate_release
_GATE_PATCHES: list = []


def setUpModule() -> None:
    for name, replacement in (
        # `(token, admitted, refused)` since bf96b221a gave a REFUSAL its own
        # return value; the stub is admitted-and-not-refused. A 2-tuple here
        # errored 12 tests with `not enough values to unpack` and left
        # scripts/check_script_selftests.sh -- a full-mode leg of
        # scripts/local_gate.sh -- unquarantined RED at HEAD.
        ("_gate_acquire", lambda _gb, _label: ("unit-test-token", True, False)),
        ("_gate_release", lambda _token: None),
    ):
        patcher = mock.patch.object(vr, name, replacement)
        patcher.start()
        _GATE_PATCHES.append(patcher)


def tearDownModule() -> None:
    for patcher in reversed(_GATE_PATCHES):
        patcher.stop()
    _GATE_PATCHES.clear()


ENTRY = {"id": "pkg::test::t", "package": "pkg", "kind": "test", "argv": ["targo", "--unverified", "test"]}
DIGEST = "sha256:aaaa"
OTHER = "sha256:bbbb"


def record(**overrides):
    base = {
        "target": "pkg::test::t",
        "status": vr.STATUS_GREEN,
        "input_digest": DIGEST,
        "source": "measured",
        "commit": "0123456789abcdef",
        "final_line": "test result: ok. 3 passed; 0 failed",
    }
    base.update(overrides)
    return base


class _FakePath(str):
    """A str that also answers `.exists()`, so it can stand in for the
    `pathlib.Path` HEAVY_GATE without importing pathlib into this module."""

    def exists(self) -> bool:
        return os.path.exists(str(self))


class SandboxLifetime(unittest.TestCase):
    def test_real_cargo_metadata_uses_the_owned_sandbox(self):
        script = """
from pathlib import Path
import json, os, sys
sys.path.insert(0, sys.argv[1])
import test_verify_runner as subject
meta = subject.vr.cargo_metadata()
print(json.dumps({"sandbox": subject._SANDBOX,
                  "configured_target": os.environ["CARGO_TARGET_DIR"],
                  "metadata_target": meta["target_directory"]}))
"""
        with tempfile.TemporaryDirectory(prefix="cargo_cache_probe_") as holder:
            caller = Path(holder) / "caller-cache"
            caller.mkdir()
            (caller / "keep").write_text("caller fixture")
            env = {**os.environ, "TMPDIR": holder, "CARGO_TARGET_DIR": str(caller)}
            proc = subprocess.run(
                [sys.executable, "-c", script, str(Path(__file__).resolve().parent)],
                env=env, pass_fds=resource_fds(env), capture_output=True, text=True, timeout=60)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            observed = json.loads(proc.stdout)
            sandbox = Path(observed["sandbox"])
            self.assertEqual(sandbox.parent.resolve(), Path(holder).resolve())
            wanted = sandbox / "target"
            self.assertEqual(Path(observed["configured_target"]), wanted, observed)
            self.assertEqual(Path(observed["metadata_target"]), wanted, observed)
            self.assertFalse(sandbox.exists(), "metadata output outlived its sandbox owner")
            self.assertEqual(sorted(p.name for p in caller.iterdir()), ["keep"])
            self.assertEqual((caller / "keep").read_text(), "caller fixture")

    def test_process_exit_removes_only_its_owned_sandbox(self):
        script = """
from pathlib import Path
import sys
sys.path.insert(0, sys.argv[1])
import test_verify_runner as subject
root = Path(subject._SANDBOX)
(root / "fixture-data").write_text("owned fixture")
print(root, flush=True)
if sys.argv[2] == "exception":
    raise RuntimeError("intentional sandbox cleanup control")
raise SystemExit(int(sys.argv[2]))
"""
        for mode, expected in (("0", 0), ("7", 7), ("exception", 1)):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory(prefix="runner_cleanup_probe_") as holder:
                env = {**os.environ, "TMPDIR": holder}
                proc = subprocess.run(
                    [sys.executable, "-c", script, str(Path(__file__).resolve().parent), mode],
                    env=env, pass_fds=resource_fds(env), capture_output=True, text=True, timeout=30)
                self.assertEqual(proc.returncode, expected, proc.stderr)
                root = Path(proc.stdout.strip())
                # Only this child can create paths under the parent's private
                # container; failed controls are cleaned by its context owner.
                self.assertTrue(root.is_absolute())
                self.assertEqual(root.parent.resolve(), Path(holder).resolve())
                self.assertTrue(root.name.startswith("verify_runner_test_"))
                self.assertFalse(root.exists(), "the exited test process left fixture data behind")


class TestDeriveBucket(unittest.TestCase):
    def test_derive_no_record_returns_unknown(self):
        row = vr.derive(ENTRY, None, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("never run", row["reason"])

    def test_derive_green_at_matching_digest_returns_green(self):
        row = vr.derive(ENTRY, record(), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)

    def test_derive_green_at_moved_digest_returns_unknown(self):
        row = vr.derive(ENTRY, record(), OTHER)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("stale", row["reason"])

    def test_mixed_input_record_cannot_revive_when_tree_returns_to_start(self):
        stable = record(input_digest_at_finish=DIGEST, inputs_moved_during_run=False)
        self.assertEqual(vr.derive(ENTRY, stable, DIGEST)["bucket"], vr.BUCKET_GREEN)
        evidence = [
            {"inputs_moved_during_run": True},
            {"input_digest_at_finish": OTHER},
            {"inputs_moved_during_run": False, "input_digest_at_finish": OTHER},
            {"inputs_moved_during_run": True, "input_digest_at_finish": DIGEST},
        ]
        for status in (vr.STATUS_GREEN, vr.STATUS_RED):
            for fields in evidence:
                with self.subTest(status=status, fields=fields):
                    rec = record(status=status, **fields)
                    row = vr.derive(ENTRY, rec, DIGEST)
                    self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
                    self.assertIn("during", row["reason"])
                    self.assertIn(status, row["last_known"])

    def test_derive_red_at_matching_digest_returns_red(self):
        row = vr.derive(ENTRY, record(status=vr.STATUS_RED), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_RED)

    def test_derive_stale_red_keeps_last_known_visible(self):
        """A red that goes stale must not vanish silently into UNKNOWN."""
        row = vr.derive(ENTRY, record(status=vr.STATUS_RED), OTHER)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("RED@", row["last_known"])

    def test_derive_seeded_record_returns_unknown_not_green(self):
        row = vr.derive(ENTRY, record(source="seeded", seed_note="reported by lane"), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("seeded", row["reason"])

    def test_derive_running_with_dead_pid_returns_unknown(self):
        row = vr.derive(ENTRY, record(status=vr.STATUS_RUNNING, pid=999999999), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("abandoned", row["reason"])

    def test_derive_running_with_live_pid_returns_running(self):
        import os

        row = vr.derive(ENTRY, record(status=vr.STATUS_RUNNING, pid=os.getpid()), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_RUNNING)

    def test_derive_error_status_returns_unknown(self):
        """A runner timeout is an absence of information, not a pass or a fail."""
        row = vr.derive(ENTRY, record(status=vr.STATUS_ERROR, notes="KILLED after timeout"), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_derive_unknown_status_string_returns_unknown(self):
        """Anything unrecognised must fall through to UNKNOWN, never to GREEN."""
        row = vr.derive(ENTRY, record(status="probably fine"), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_derive_green_that_ran_zero_tests_is_unknown_not_green(self):
        """THE VACUOUS GREEN. `targo --unverified test -p clean-kernel axiom_refutation_gate`
        exits 0 with "0 passed; ...; 10412 filtered out" because that gate lives
        in clean-verify. libtest calls that ok; the runner must not."""
        row = vr.derive(
            ENTRY,
            record(
                final_line="test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 10412 filtered out",
                counts={"passed": 0, "failed": 0, "ignored": 0, "result_lines": 1},
            ),
            DIGEST,
        )
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("ZERO tests", row["reason"])

    def test_ignored_tests_are_not_executed_tests(self):
        counts = {"passed": 0, "failed": 0, "ignored": 3, "result_lines": 1}
        row = vr.derive(ENTRY, record(counts=counts), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        counts["passed"] = 1
        self.assertEqual(vr.derive(ENTRY, record(counts=counts), DIGEST)["bucket"], vr.BUCKET_GREEN)

    def test_recorded_green_with_failed_tests_is_unknown(self):
        counts = {"passed": 3, "failed": 1, "ignored": 0, "result_lines": 2}
        rec = record(counts=counts, final_line="test result: ok. 3 passed; 0 failed")
        self.assertEqual(vr.derive(ENTRY, rec, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)
        counts["failed"] = 0
        self.assertEqual(vr.derive(ENTRY, rec, DIGEST)["bucket"], vr.BUCKET_GREEN)

    def test_derive_green_that_ran_tests_stays_green(self):
        """The anti-correlation arm: same shape, one test ran, still GREEN.

        Without it the arm above would pass against a rule that demoted
        everything."""
        row = vr.derive(
            ENTRY,
            record(counts={"passed": 1, "failed": 0, "ignored": 0, "result_lines": 1}),
            DIGEST,
        )
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)

    def test_derive_green_shell_gate_with_no_result_line_stays_green(self):
        """A gate row prints no `test result:` line at all -- 11 such records
        exist in data/suite_state/ -- so the zero-test rule must not fire on it."""
        row = vr.derive(
            {"id": "gate::paragon", "package": "__workspace__", "kind": "gate", "argv": ["x"]},
            record(
                target="gate::paragon",
                final_line="paragon ratchet: PASS",
                counts={"passed": 0, "failed": 0, "ignored": 0, "result_lines": 0},
            ),
            DIGEST,
        )
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)

    def test_derive_seeded_record_with_matching_digest_still_unknown(self):
        """A seeded record must not be launderable by any digest coincidence."""
        row = vr.derive(ENTRY, record(source="seeded", seed_note="n", status=vr.STATUS_GREEN), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)


class TestSummarizeOutput(unittest.TestCase):
    def test_summarize_picks_last_test_result_line_verbatim(self):
        text = "running 3 tests\ntest a ... ok\ntest result: ok. 3 passed; 0 failed; 0 ignored\n"
        final, counts = vr.summarize_output(text, 0)
        self.assertEqual(final, "test result: ok. 3 passed; 0 failed; 0 ignored")
        self.assertEqual(counts["passed"], 3)
        self.assertEqual(counts["failed"], 0)

    def test_summarize_sums_counts_across_multiple_result_lines(self):
        text = (
            "test result: ok. 3 passed; 0 failed; 0 ignored\n"
            "test result: FAILED. 1 passed; 2 failed; 0 ignored\n"
        )
        _final, counts = vr.summarize_output(text, 101)
        self.assertEqual(counts["passed"], 4)
        self.assertEqual(counts["failed"], 2)
        self.assertEqual(counts["result_lines"], 2)

    def test_summarize_empty_output_reports_absence_not_success(self):
        final, counts = vr.summarize_output("", 1)
        self.assertIn("no output", final)
        self.assertEqual(counts["passed"], 0)

    def test_summarize_falls_back_to_last_line_when_no_result_line(self):
        final, _counts = vr.summarize_output("error: could not compile `clean-verify`\n", 101)
        self.assertEqual(final, "error: could not compile `clean-verify`")


class TestInputDigest(unittest.TestCase):
    def test_digest_changes_when_argv_changes(self):
        """argv is part of the key: a green for one command is not a green for another."""
        a = dict(ENTRY, _dirs=[vr.REPO_ROOT / "scripts"])
        b = dict(ENTRY, _dirs=[vr.REPO_ROOT / "scripts"], argv=["targo", "--unverified", "test", "--release"])
        self.assertNotEqual(vr.input_digest(a), vr.input_digest(b))

    def test_argument_boundaries_cannot_reuse_a_green(self):
        pairs = [
            (["tool", "a b"], ["tool", "a", "b"]),
            (["tool", "", "x"], ["tool", " x"]),
            (["tool", "x\n y"], ["tool", "x\n", "y"]),
            (["tool", "x; y"], ["tool", "x;", "y"]),
        ]
        with tempfile.TemporaryDirectory() as tmp, \
             mock.patch.object(vr, "REPO_ROOT", Path(tmp)), \
             mock.patch.object(vr, "_dir_content_digest", return_value="unchanged-source"), \
             mock.patch.object(vr, "toolchain_id", return_value="same-compiler"):
            for left, right in pairs:
                with self.subTest(left=left, right=right):
                    self.assertEqual(" ".join(left), " ".join(right))
                    first = dict(ENTRY, argv=left, _dirs=[])
                    second = dict(ENTRY, argv=right, _dirs=[])
                    measured = vr.input_digest(first, fresh=True)
                    current = vr.input_digest(second, fresh=True)
                    self.assertNotEqual(measured, current)
                    self.assertEqual(vr.derive(second, record(input_digest=measured), current)["bucket"],
                                     vr.BUCKET_UNKNOWN)

    def test_digest_is_stable_for_identical_inputs(self):
        a = dict(ENTRY, _dirs=[vr.REPO_ROOT / "scripts"])
        self.assertEqual(vr.input_digest(a), vr.input_digest(dict(a)))

    def test_digest_scope_excludes_the_state_directory(self):
        """Writing a record must never invalidate other records."""
        self.assertFalse(str(vr.STATE_DIR).startswith(str(vr.REPO_ROOT / "crates")))


class TestLiteralPathDigests(unittest.TestCase):
    def _init(self, root, names, tracked=True):
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        for name in names:
            (root / name).write_text("initial:" + name)
        if tracked:
            subprocess.run(["git", "-C", str(root), "add", "--", "."], check=True)

    def test_quoted_source_cannot_hash_its_unquoted_neighbor(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._init(root, ["ordinary", '"ordinary"'])
            entry = dict(ENTRY, _dirs=[root])
            with mock.patch.object(vr, "REPO_ROOT", root), \
                    mock.patch.object(vr, "toolchain_id", return_value="fixed"):
                before = vr.input_digest(entry, fresh=True)
                (root / '"ordinary"').write_text("changed quoted source")
                after = vr.input_digest(entry, fresh=True)
                self.assertNotEqual(before, after)
                self.assertEqual(vr.derive(entry, record(input_digest=before), after)["bucket"],
                                 vr.BUCKET_UNKNOWN)

    def test_unusual_tracked_and_untracked_names_hash_their_own_bytes(self):
        names = ['"quoted"', "line\nname", "tab\tname", "back\\name", "λ", "control\x01"]
        for tracked in (True, False):
            for name in names:
                with self.subTest(tracked=tracked, name=name), tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    self._init(root, ["quoted", name], tracked)
                    with mock.patch.object(vr, "REPO_ROOT", root):
                        before = vr._dir_content_digest([root], fresh=True)
                        (root / name).write_text("changed:" + name)
                        after = vr._dir_content_digest([root], fresh=True)
                        self.assertNotEqual(before, after)

    def test_ordinary_paths_keep_the_existing_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._init(root, ["a", "b"])
            # Freeze the existing on-disk digest format using Git's argv path
            # boundary as an independent oracle for the content hashes.
            import hashlib
            h = hashlib.sha256()
            for name in ("a", "b"):
                blob = subprocess.check_output(["git", "hash-object", "--", name], cwd=root).strip()
                h.update(name.encode() + b"\0" + blob + b"\n")
            with mock.patch.object(vr, "REPO_ROOT", root):
                self.assertEqual(vr._dir_content_digest([root], fresh=True), h.hexdigest())


class TestCompilerEnvironmentRoutes(unittest.TestCase):
    SELECTORS = ("RUSTC", "RUSTDOC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                 "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTDOC", "CARGO_BUILD_RUSTC_WRAPPER",
                 "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER")

    def test_explicit_routes_cannot_claim_the_path_trustc_identity(self):
        for key in self.SELECTORS:
            with self.subTest(key=key), mock.patch.dict(os.environ, {key: "/unexecuted/fixture"}, clear=True), \
                    mock.patch.object(vr, "_TOOLCHAIN_CACHE", None), \
                    mock.patch.object(vr, "_dir_content_digest", return_value="source"), \
                    mock.patch.object(vr, "run_capture", return_value=(0, "rustc canonical\n")) as probe:
                entry = dict(ENTRY, _dirs=[])
                self.assertIsNone(vr.input_digest(entry, fresh=True))
                self.assertIsNone(vr.build_warm_key(entry))
                probe.assert_not_called()

    def test_explicit_route_precedes_the_status_identity_cache(self):
        with mock.patch.dict(os.environ, {"RUSTC": "/unexecuted/fixture"}, clear=True), \
                mock.patch.object(vr, "_TOOLCHAIN_CACHE", "known canonical compiler"):
            self.assertEqual(vr.toolchain_id(), "rustc-unavailable")
            self.assertEqual(vr._TOOLCHAIN_CACHE, "known canonical compiler")

    def test_explicit_route_cannot_reuse_cached_cfg_facts(self):
        with mock.patch.dict(os.environ, {"RUSTC_WRAPPER": "/unexecuted/fixture"}, clear=True), \
                mock.patch.object(vr, "_LANE_CFG_CACHE", {vr.PROFILE_DEV: {"known": True}}):
            self.assertIsNone(vr.lane_cfg_facts(vr.PROFILE_DEV))

    def test_route_refusal_names_the_variable_without_executing_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / "target-ran"
            entry = dict(ENTRY, _dirs=[], argv=["/bin/sh", "-c", "touch " + shlex.quote(str(marker))])
            with mock.patch.dict(os.environ, {"RUSTC": "/unexecuted/fixture"}, clear=True), \
                    mock.patch.object(vr, "_dir_content_digest", return_value="source"), \
                    mock.patch.object(vr, "run_capture", return_value=(0, "rustc canonical\n")), \
                    mock.patch.object(vr, "_gate_acquire", return_value=("token", True, False)) as gate:
                result = vr.run_one(entry, 10)
            self.assertFalse(marker.exists())
            gate.assert_not_called()
            self.assertEqual(result["status"], vr.STATUS_ERROR)
            self.assertIn("RUSTC", result["notes"])
            self.assertNotIn("/unexecuted/fixture", result["notes"])

    def test_empty_wrapper_reset_keeps_the_normal_identity(self):
        with mock.patch.object(vr, "_TOOLCHAIN_CACHE", None), \
                mock.patch.object(vr, "run_capture", return_value=(0, "rustc canonical\n")):
            with mock.patch.dict(os.environ, {}, clear=True):
                expected = vr.toolchain_id(fresh=True)
            with mock.patch.dict(os.environ, {"RUSTC_WRAPPER": "", "RUSTC_WORKSPACE_WRAPPER": ""}, clear=True):
                self.assertEqual(vr.toolchain_id(fresh=True), expected)


class TestBuildEnvironmentInputs(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.entry = dict(ENTRY, _dirs=[])
        for name, value in (("REPO_ROOT", Path(tmp.name)), ("_WARM_BUILDS", set())):
            patcher = mock.patch.object(vr, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        for name, value in (("toolchain_id", "fixed compiler"),
                            ("_dir_content_digest", "fixed source")):
            patcher = mock.patch.object(vr, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def keys(self, env):
        # No compiler runs under these fixture-only flags.
        with mock.patch.dict(os.environ, env, clear=True):
            return (vr.input_digest(self.entry, fresh=True), vr.build_warm_key(self.entry))

    def test_compile_settings_invalidate_evidence_and_warm_reuse(self):
        cases = {
            "RUSTFLAGS": ("-C opt-level=1", "-C opt-level=2"),
            "CARGO_ENCODED_RUSTFLAGS": ("-C\x1fopt-level=1", "-C\x1fopt-level=2"),
            "RUSTDOCFLAGS": ("--cfg doc_a", "--cfg doc_b"),
            "CARGO_ENCODED_RUSTDOCFLAGS": ("--cfg\x1fdoc_a", "--cfg\x1fdoc_b"),
            "CARGO_BUILD_RUSTFLAGS": ("-C opt-level=1", "-C opt-level=2"),
            "CARGO_BUILD_RUSTDOCFLAGS": ("--cfg doc_a", "--cfg doc_b"),
            "CARGO_INCREMENTAL": ("0", "1"),
            "CARGO_BUILD_INCREMENTAL": ("false", "true"),
            "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS": ("true", "false"),
            "CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS": ("true", "false"),
            "CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL": ("0", "1"),
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS": ("-C opt-level=1", "-C opt-level=2"),
            "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTDOCFLAGS": ("--cfg doc_a", "--cfg doc_b"),
        }
        before, warm = self.keys({})
        vr.mark_build_warm(warm)
        for key, (first, second) in cases.items():
            with self.subTest(key=key):
                after, changed_warm = self.keys({key: first})
                self.assertNotEqual(before, after)
                self.assertFalse(vr.build_is_warm(changed_warm))
                self.assertEqual(vr.derive(self.entry, record(input_digest=before), after)["bucket"],
                                 vr.BUCKET_UNKNOWN)
                self.assertNotEqual((after, changed_warm), self.keys({key: second}))

    def test_empty_encoded_override_is_not_an_absent_override(self):
        for key in ("CARGO_ENCODED_RUSTFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS"):
            with self.subTest(key=key):
                self.assertNotEqual(self.keys({"RUSTFLAGS": "-C opt-level=1"}),
                                    self.keys({"RUSTFLAGS": "-C opt-level=1", key: ""}))

    def test_target_tools_invalidate_evidence_and_warm_reuse(self):
        cases = {
            "CARGO_BUILD_TARGET": ("target-a.json", "target-b.json"),
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER": ("/unexecuted/linker a", "/unexecuted/linker b"),
            "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER": ("runner --mode a", "runner --mode b"),
            "CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER": ("link-a.exe", "link-b.exe"),
        }
        before, warm = self.keys({})
        vr.mark_build_warm(warm)
        for key, (first, second) in cases.items():
            with self.subTest(key=key):
                after, changed_warm = self.keys({key: first})
                self.assertNotEqual(before, after)
                self.assertFalse(vr.build_is_warm(changed_warm))
                self.assertEqual(vr.derive(self.entry, record(input_digest=before), after)["bucket"],
                                 vr.BUCKET_UNKNOWN)
                self.assertNotEqual((after, changed_warm), self.keys({key: second}))

    def test_empty_target_tool_value_is_not_an_absent_override(self):
        for key in ("CARGO_BUILD_TARGET", "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER",
                    "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER"):
            with self.subTest(key=key):
                self.assertNotEqual(self.keys({}), self.keys({key: ""}))

    def test_output_paths_and_job_limits_do_not_change_keys(self):
        self.assertEqual(self.keys({}), self.keys({
            "CARGO_TARGET_DIR": "/different/output",
            "CARGO_BUILD_TARGET_DIR": "/different/default-output",
            "CARGO_BUILD_JOBS": "3",
        }))

    def test_order_and_unrelated_environment_do_not_change_keys(self):
        env = {"RUSTFLAGS": "-C opt-level=1", "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS": "false"}
        self.assertEqual(self.keys(env), self.keys(dict(reversed(list(env.items())))))
        self.assertEqual(self.keys(env), self.keys(dict(env, TERM="different-terminal")))


class TestUnavailableCompilerEvidence(unittest.TestCase):
    def test_missing_identity_is_not_a_digest(self):
        for identity in ("", "rustc-unavailable"):
            with self.subTest(identity=identity), \
                    mock.patch.object(vr, "toolchain_id", return_value=identity), \
                    mock.patch.object(vr, "_dir_content_digest", return_value="source"):
                self.assertIsNone(vr.input_digest(dict(ENTRY, _dirs=[]), fresh=True))

    def test_matching_unknown_identity_cannot_reuse_a_green(self):
        with mock.patch.object(vr, "toolchain_id", return_value="rustc-unavailable"), \
                mock.patch.object(vr, "_dir_content_digest", return_value="source"):
            digest = vr.input_digest(dict(ENTRY, _dirs=[]), fresh=True)
            row = vr.derive(ENTRY, record(input_digest=digest), digest)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("compiler", row["reason"])

    def test_unknown_identity_stops_before_admission_or_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / "ran"
            entry = dict(ENTRY, _dirs=[], argv=["/bin/sh", "-c", "touch " + shlex.quote(str(marker))])
            with mock.patch.object(vr, "input_digest", return_value=None), \
                    mock.patch.object(vr, "_gate_acquire", return_value=("token", True, False)) as gate:
                result = vr.run_one(entry, 10)
            self.assertFalse(marker.exists())
            gate.assert_not_called()
            self.assertEqual(result["status"], vr.STATUS_ERROR)
            self.assertIsNone(result["exit_code"])
            self.assertIsNone(result["log"])

    def test_identity_lost_at_finish_is_not_a_green(self):
        entry = dict(ENTRY, _dirs=[], argv=["/bin/sh", "-c",
                         "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'"])
        with mock.patch.object(vr, "input_digest", side_effect=[DIGEST, None]):
            result = vr.run_one(entry, 10)
        self.assertEqual(result["status"], vr.STATUS_ERROR)
        self.assertIn("compiler", result["notes"])
        self.assertEqual(vr.derive(entry, result, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)

    def test_rollup_cannot_hide_an_unavailable_current_digest(self):
        entry = dict(ENTRY, kind=vr.KIND_ROLLUP)
        with mock.patch.object(vr, "rollup", return_value={"bucket": vr.BUCKET_GREEN}) as rollup:
            row = vr.derive(entry, None, None)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        rollup.assert_not_called()

    def test_shard_planning_stops_before_the_build(self):
        args = types.SimpleNamespace(parent="pkg::lib", action="plan")
        entry = dict(ENTRY, id=args.parent, kind="lib", _dirs=[])
        with mock.patch.object(vr, "build_inventory", return_value=[entry]), \
                mock.patch.object(vr, "input_digest", return_value=None), \
                mock.patch.object(vr, "test_binary_for", side_effect=AssertionError("build launched")):
            self.assertEqual(vr.cmd_shards(args), 2)


class TestCompilerIdentityDigest(unittest.TestCase):
    def test_fresh_digests_detect_compiler_replacement_without_poisoning_status(self):
        with tempfile.TemporaryDirectory() as tmp, \
             mock.patch.object(vr, "REPO_ROOT", Path(tmp)), \
             mock.patch.object(vr, "_dir_content_digest", return_value="unchanged-source"), \
             mock.patch.object(vr, "_TOOLCHAIN_CACHE", "rustc old|commit-hash: old"), \
             mock.patch.object(vr, "run_capture", side_effect=[
                 (0, "rustc old\ncommit-hash: old\n"),
                 (0, "rustc new\ncommit-hash: new\n"),
             ]) as capture:
            entry = dict(ENTRY, _dirs=[])
            start = vr.input_digest(entry, fresh=True)
            finish = vr.input_digest(entry, fresh=True)
            self.assertNotEqual(start, finish)
            self.assertEqual(vr.derive(entry, record(input_digest=start), finish)["bucket"],
                             vr.BUCKET_UNKNOWN)
            # A run's fresh samples must not change the memo used by an
            # already-running status table.
            self.assertEqual(vr.toolchain_id(), "rustc old|commit-hash: old")
            self.assertEqual(capture.call_count, 2)

    def test_status_compiler_identity_is_memoized(self):
        with mock.patch.object(vr, "_TOOLCHAIN_CACHE", None), \
             mock.patch.object(vr, "run_capture", return_value=(0, "rustc fixed\n")) as capture:
            self.assertEqual(vr.toolchain_id(), "rustc fixed")
            self.assertEqual(vr.toolchain_id(), "rustc fixed")
            capture.assert_called_once_with(["trustc", "-vV"])


class TestRootBuildInputDigest(unittest.TestCase):
    def test_config_and_toolchain_add_edit_remove_invalidate_green(self):
        for relative in (".cargo/config", ".cargo/config.toml",
                         "rust-toolchain", "rust-toolchain.toml"):
            with self.subTest(path=relative), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                entry = dict(ENTRY, _dirs=[])
                with mock.patch.object(vr, "REPO_ROOT", root), \
                     mock.patch.object(vr, "_dir_content_digest", return_value="unchanged-source"), \
                     mock.patch.object(vr, "toolchain_id", return_value="unchanged-compiler"):
                    digest = vr.input_digest(entry, fresh=True)
                    measured = record(input_digest=digest)
                    self.assertEqual(vr.derive(entry, measured, digest)["bucket"], vr.BUCKET_GREEN)
                    path = root / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    for content in (b"first build policy\n", b"changed build policy\n", None):
                        if content is None:
                            path.unlink()
                        else:
                            path.write_bytes(content)
                        changed = vr.input_digest(entry, fresh=True)
                        self.assertNotEqual(digest, changed)
                        self.assertEqual(vr.derive(entry, measured, changed)["bucket"], vr.BUCKET_UNKNOWN)
                        digest = changed
                        measured = record(input_digest=digest)

    def test_unrelated_root_document_does_not_invalidate_green(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = dict(ENTRY, _dirs=[])
            with mock.patch.object(vr, "REPO_ROOT", root), \
                 mock.patch.object(vr, "_dir_content_digest", return_value="unchanged-source"), \
                 mock.patch.object(vr, "toolchain_id", return_value="unchanged-compiler"):
                before = vr.input_digest(entry, fresh=True)
                (root / "README.md").write_text("unrelated documentation edit\n")
                after = vr.input_digest(entry, fresh=True)
                self.assertEqual(before, after)
                self.assertEqual(vr.derive(entry, record(input_digest=before), after)["bucket"],
                                 vr.BUCKET_GREEN)


class TestNonExecutingCommands(unittest.TestCase):
    def test_build_list_and_help_commands_cannot_be_test_rows(self):
        commands = [
            ["targo", "--unverified", "test", "--no-run"],
            ["cargo", "test", "--no-run"],
            ["targo", "trust", "test", "--", "--list"],
            ["targo", "--unverified", "test", "--help"],
            ["targo", "--unverified", "test", "--", "-h"],
        ]
        for argv in commands:
            with self.subTest(argv=argv):
                problems = vr.check_profiles([dict(ENTRY, argv=argv)])
                self.assertTrue(any("does not execute tests" in p for p in problems), problems)

    def test_executing_ignored_tests_and_shell_gates_still_work(self):
        commands = [
            ["targo", "--unverified", "test", "--", "--ignored"],
            ["targo", "--unverified", "test", "--test", "list"],
            ["scripts/probe.sh", "--list"],
        ]
        for argv in commands:
            with self.subTest(argv=argv):
                self.assertEqual(vr.check_profiles([dict(ENTRY, argv=argv)]), [])


class TestTargetFileNames(unittest.TestCase):
    def _inventory(self, ids):
        rows = {}
        for target in ids:
            package = target.split("::")[0]
            rows.setdefault(package, []).append({"id": target, "package": package,
                "kind": "test", "argv": ["true"]})
        meta = {"packages": [{"name": p, "targets": [{"kind": ["test"]}],
                "manifest_path": str(vr.REPO_ROOT / p / "Cargo.toml")} for p in rows]}
        with mock.patch.multiple(vr,
                WORKSPACE_GATES=[], RELEASE_PROFILE_TARGETS=[],
                check_crystal_extra_paths=mock.Mock(return_value=[]),
                cargo_metadata=mock.Mock(return_value=meta),
                package_targets=mock.Mock(side_effect=lambda _m, p: [dict(r) for r in rows[p]]),
                check_profiles=mock.Mock(return_value=[]),
                lib_test_coverage_problems=mock.Mock(return_value=[]),
                compiled_out_problems=mock.Mock(return_value=[]),
                path_dep_closure=mock.Mock(return_value=[]),
                closure_library_reads=mock.Mock(return_value=()),
                row_target_reads=mock.Mock(return_value=())):
            return vr.build_inventory([ids[0].split("::")[0]], with_gates=False)

    def test_a_collision_in_an_unselected_package_is_refused(self):
        pairs = [
            ["a::test::b__test__c", "a__test__b::test::c"],
            ["pkg::test::Thing", "PKG::test::thing"],
        ]
        for ids in pairs:
            with self.subTest(ids=ids):
                with self.assertRaisesRegex(SystemExit, "filename collision"):
                    self._inventory(ids)

    def test_distinct_names_keep_the_selected_inventory_unchanged(self):
        ids = ["a::test::one", "b::test::two"]
        self.assertEqual([r["id"] for r in self._inventory(ids)], ids[:1])


class TestRecordLoading(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        patcher = mock.patch.object(vr, "STATE_DIR", Path(tmp.name))
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_valid_record_round_trip_and_absent_record(self):
        self.assertIsNone(vr.load_record(ENTRY["id"]))
        expected = record()
        vr.record_path(ENTRY["id"]).write_text(json.dumps(expected))
        self.assertEqual(vr.load_record(ENTRY["id"]), expected)
        self.assertEqual(vr.derive(ENTRY, vr.load_record(ENTRY["id"]), DIGEST)["bucket"],
                         vr.BUCKET_GREEN)

    def test_foreign_or_missing_target_cannot_supply_a_green(self):
        cases = [record(target="other::test::target"), record(target=None), record()]
        del cases[-1]["target"]
        for value in cases:
            with self.subTest(target=value.get("target")):
                vr.record_path(ENTRY["id"]).write_text(json.dumps(value))
                loaded = vr.load_record(ENTRY["id"])
                row = vr.derive(ENTRY, loaded, DIGEST)
                self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
                self.assertIn("invalid record", row["reason"])
                self.assertIn("target", row["reason"])

    def test_invalid_core_fields_are_diagnostic_not_status_crashes(self):
        cases = [
            {"commit": 7}, {"started_at": []}, {"finished_at": 9},
            {"counts": []}, {"counts": {"passed": "one"}},
            {"counts": {"passed": -1}}, {"counts": {"passed": True}},
            {"counts": {"result_lines": 1.5}},
            {"status": vr.STATUS_RUNNING, "pid": "not-a-pid"},
        ]
        for fields in cases:
            with self.subTest(fields=fields):
                value = record(**fields)
                vr.record_path(ENTRY["id"]).write_text(json.dumps(value))
                row = vr.derive(ENTRY, vr.load_record(ENTRY["id"]), DIGEST)
                self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
                self.assertIn("invalid record", row["reason"])

    def test_malformed_record_is_unknown_with_a_diagnostic(self):
        for payload in (b"[]", b"null", b"true", b"5", b'"text"', b"{", b"\xff"):
            with self.subTest(payload=payload):
                vr.record_path(ENTRY["id"]).write_bytes(payload)
                loaded = vr.load_record(ENTRY["id"])
                row = vr.derive(ENTRY, loaded, DIGEST)
                self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
                self.assertIn("invalid record", row["reason"])


class TestRunOneClassification(unittest.TestCase):
    """End-to-end through run_one with synthetic commands: no cargo, real records."""

    @staticmethod
    def _entry(name: str, argv: list[str]) -> dict:
        return {"id": name, "package": "synthetic", "kind": "test", "argv": argv,
                "_dirs": [vr.REPO_ROOT / "scripts"]}

    def test_run_one_zero_exit_records_green(self):
        entry = self._entry("synthetic::ok", ["/bin/sh", "-c", "echo 'test result: ok. 1 passed; 0 failed'"])
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["status"], vr.STATUS_GREEN)
        self.assertEqual(rec["exit_code"], 0)
        self.assertEqual(rec["final_line"], "test result: ok. 1 passed; 0 failed")
        self.assertEqual(rec["counts"]["passed"], 1)

    def test_pipeline_zero_exit_does_not_hide_reported_test_failure(self):
        command = ("(echo 'test result: FAILED. 0 passed; 1 failed'; exit 1) | cat; "
                   "echo 'test result: ok. 1 passed; 0 failed'")
        entry = self._entry("synthetic::masked_failure", ["/bin/sh", "-c", command])
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["exit_code"], 0)
        self.assertEqual(rec["counts"]["failed"], 1)
        self.assertEqual(rec["counts"]["passed"], 1)
        self.assertEqual(rec["status"], vr.STATUS_ERROR)
        self.assertIn("failed tests", rec["notes"])
        self.assertEqual(vr.derive(entry, rec, rec["input_digest"])["bucket"], vr.BUCKET_UNKNOWN)

    def test_run_one_nonzero_exit_records_red_with_verbatim_line(self):
        entry = self._entry(
            "synthetic::fail",
            ["/bin/sh", "-c", "echo 'test result: FAILED. 0 passed; 2 failed; 0 ignored'; exit 101"],
        )
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["status"], vr.STATUS_RED)
        self.assertEqual(rec["exit_code"], 101)
        self.assertEqual(rec["final_line"], "test result: FAILED. 0 passed; 2 failed; 0 ignored")
        self.assertEqual(rec["counts"]["failed"], 2)

    def test_run_one_timeout_records_error_not_green_or_red(self):
        entry = self._entry("synthetic::hang", ["/bin/sh", "-c", "sleep 30"])
        rec = vr.run_one(entry, timeout=2)
        self.assertEqual(rec["status"], vr.STATUS_ERROR)
        self.assertNotIn(rec["status"], (vr.STATUS_GREEN, vr.STATUS_RED))
        self.assertIn("NOT a pass", rec["notes"])

    def test_run_one_changed_inputs_never_become_green_after_revert(self):
        entry = self._entry("pkg::test::t", ["/bin/sh", "-c", "echo 'test result: ok. 1 passed; 0 failed'"])
        with mock.patch.object(vr, "input_digest", side_effect=[DIGEST, OTHER]):
            rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["status"], vr.STATUS_GREEN)  # raw successful exit
        self.assertEqual(rec["input_digest_at_finish"], OTHER)
        self.assertTrue(rec["inputs_moved_during_run"])
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)

    def test_run_one_records_command_and_digest_provenance(self):
        entry = self._entry("synthetic::prov", ["/bin/sh", "-c", "true"])
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["command"], "/bin/sh -c true")
        self.assertTrue(rec["input_digest"].startswith("sha256:"))
        self.assertEqual(rec["source"], "measured")
        self.assertIsNotNone(rec["commit"])
        self.assertIn("inputs_moved_during_run", rec)


class TestPhaseWeightHistory(unittest.TestCase):
    def _run(self, floor, interrupted=False, changed=False):
        target = f"synthetic::phase_history_{floor}_{interrupted}_{changed}"
        prior = record(target=target, package="synthetic", counts={"passed": 1, "result_lines": 1},
                       build_peak_rss_gb=8, build_rss_samples=10,
                       run_peak_rss_gb=2, rss_samples=10,
                       peak_rss_gb=8, inputs_moved_during_run=False, timed_out=interrupted,
                       input_digest_at_finish=OTHER if changed else DIGEST)
        vr.write_record(prior)
        asked = []
        def acquire(gb, label):
            asked.append((gb, label))
            return "unit-token", True, False
        with tempfile.TemporaryDirectory() as tmp:
            fake = Path(tmp) / "targo"
            fake.write_text("#!/bin/sh\n"
                            'for a in "$@"; do [ "$a" = --no-run ] && exit 0; done\n'
                            "echo 'test result: ok. 1 passed; 0 failed'\n")
            fake.chmod(0o755)
            entry = {"id": target, "package": "synthetic", "kind": "test",
                     "argv": [str(fake), "--unverified", "test"],
                     "_dirs": [vr.REPO_ROOT / "scripts" / "verify_runner.py"]}
            with mock.patch.object(vr, "_gate_acquire", side_effect=acquire), \
                 mock.patch.object(vr, "_gate_weight_gb", return_value=20), \
                 mock.patch.object(vr, "build_is_warm", return_value=False), \
                 mock.patch.object(vr, "package_cold_build_floor_gb", return_value=(floor, "test floor")):
                result = vr.run_one(entry, timeout=60)
        self.assertEqual(result["status"], vr.STATUS_GREEN)
        self.assertEqual(result["gate_weight_gb"], asked[-1][0])
        return asked, target

    def test_prior_phase_peaks_survive_the_running_record(self):
        asked, target = self._run(0)
        self.assertEqual(asked, [(12, target + " [build]"), (3, target)])

    def test_package_cold_floor_still_raises_the_build_reservation(self):
        asked, target = self._run(18)
        self.assertEqual(asked, [(18, target + " [build]"), (3, target)])


    def test_incomplete_run_cannot_lower_phase_reservations(self):
        asked, target = self._run(0, interrupted=True)
        self.assertEqual(asked, [(20, target + " [build]"), (20, target)])


    def test_changed_input_hashes_cannot_lower_phase_reservations(self):
        asked, target = self._run(0, changed=True)
        self.assertEqual(asked, [(20, target + " [build]"), (20, target)])


class TestPhaseLogs(unittest.TestCase):
    def _run(self, build_exit):
        with tempfile.TemporaryDirectory() as tmp:
            fake = Path(tmp) / "targo"
            fake.write_text(
                "#!/bin/sh\n"
                "for a in \"$@\"; do\n"
                f"  if [ \"$a\" = --no-run ]; then echo BUILD_ONLY_DIAGNOSTIC; exit {build_exit}; fi\n"
                "done\n"
                "echo RUN_ONLY_DIAGNOSTIC\n"
                + ("echo 'test result: ok. 1 passed; 0 failed; 0 ignored'\n" if build_exit == 0
                   else "echo 'test result: FAILED. 0 passed; 1 failed; 0 ignored'\nexit 1\n"))
            fake.chmod(0o755)
            entry = {"id": f"synthetic::phase_logs_{build_exit}", "package": "synthetic",
                     "kind": "test", "argv": [str(fake), "--unverified", "test"],
                     "_dirs": [vr.REPO_ROOT / "scripts" / "verify_runner.py"]}
            return vr.run_one(entry, timeout=60)

    def _check_logs(self, rec):
        self.assertIsNotNone(rec.get("build_log"), "the build transcript was discarded")
        build = vr.REPO_ROOT / rec["build_log"]
        run = vr.REPO_ROOT / rec["log"]
        self.assertNotEqual(build, run)
        self.assertEqual(build.read_text(), "BUILD_ONLY_DIAGNOSTIC\n")
        self.assertIn("RUN_ONLY_DIAGNOSTIC", run.read_text())
        self.assertNotIn("BUILD_ONLY_DIAGNOSTIC", run.read_text())

    def test_successful_build_log_survives_the_test_phase(self):
        rec = self._run(0)
        self.assertEqual(rec["status"], vr.STATUS_GREEN)
        self._check_logs(rec)

    def test_failed_build_diagnostic_is_the_terminal_measurement(self):
        rec = self._run(1)
        self.assertEqual(rec["build_exit_code"], 1)
        self.assertEqual(rec["status"], vr.STATUS_RED)
        self.assertEqual(rec["log"], rec["build_log"])
        self.assertEqual((vr.REPO_ROOT / rec["log"]).read_text(), "BUILD_ONLY_DIAGNOSTIC\n")


class TestFailedBuildAdmission(unittest.TestCase):
    def _run(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            fake = Path(tmp) / "targo"
            marker = Path(tmp) / "run-launched"
            if mode != "missing":
                build = {"failed": "echo BUILD_FAILED; exit 7",
                         "timeout": "echo BUILD_STARTED; sleep 2; exit 0",
                         "refusal": "echo 'protected Trust toolchain directory'; exit 2",
                         "ok": "echo BUILD_OK; exit 0"}.get(mode, "exit 0")
                fake.write_text("#!/bin/sh\nfor a in \"$@\"; do\n"
                                "if [ \"$a\" = --no-run ]; then " + build + "; fi\ndone\n"
                                + "touch " + shlex.quote(str(marker)) + "\n"
                                "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'\n")
                fake.chmod(0o755)
            entry = {"id": "synthetic::build_" + mode, "package": "synthetic", "kind": "test",
                     "argv": [str(fake), "--unverified", "test"], "_dirs": []}
            asked = []
            def acquire(gb, label):
                asked.append((gb, label))
                return (None, False, True) if mode == "gate" else ("token", True, False)
            with mock.patch.object(vr, "input_digest", return_value=DIGEST), \
                    mock.patch.object(vr, "_gate_acquire", side_effect=acquire), \
                    mock.patch.object(vr, "_split_weights_gb", return_value=(19, 1)), \
                    mock.patch.object(vr, "package_cold_build_floor_gb", return_value=(19, "fixture")), \
                    mock.patch.object(vr, "_rss_profile", return_value=vr.RssProfile(2, 2, 2, 3)):
                rec = vr.run_one(entry, timeout=0.05 if mode == "timeout" else 10)
            return rec, asked, marker.exists(), entry

    def test_failed_build_cannot_retry_under_the_run_reservation(self):
        rec, asked, ran, entry = self._run("failed")
        self.assertFalse(ran)
        self.assertEqual(asked, [(19, entry["id"] + " [build]")])
        self.assertEqual(rec["status"], vr.STATUS_RED)
        self.assertEqual(rec["exit_code"], 7)
        self.assertIn("BUILD_FAILED", (vr.REPO_ROOT / rec["log"]).read_text())

    def test_timed_out_build_is_unknown_without_a_test_launch(self):
        rec, asked, ran, entry = self._run("timeout")
        self.assertFalse(ran)
        self.assertEqual(len(asked), 1)
        self.assertTrue(rec["timed_out"])
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)

    def test_refused_build_never_reaches_test_admission(self):
        for mode in ("gate", "missing", "refusal"):
            with self.subTest(mode):
                rec, asked, ran, entry = self._run(mode)
                self.assertFalse(ran)
                self.assertEqual(len(asked), 1)
                self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)

    def test_success_still_releases_build_then_uses_run_reservation(self):
        rec, asked, ran, entry = self._run("ok")
        self.assertTrue(ran)
        self.assertEqual(asked, [(19, entry["id"] + " [build]"), (1, entry["id"])])
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_GREEN)


class TestTimeoutPolicy(unittest.TestCase):
    """The per-target budget must be derived, explainable, and always finite.

    The failure this pins: on 2026-08-12 a flat 25s budget killed
    `clean-verify::test::whnf_lemma_wrapper_defs` at "running 2 tests" and
    recorded ERROR. The artifact was right to refuse to call that a pass or a
    fail; the budget was simply wrong for a target whose spec build alone runs
    into the thousands of seconds.
    """

    TEST_ENTRY = {"id": "pkg::test::t", "package": "pkg", "kind": "test", "argv": ["cargo"]}
    GATE_ENTRY = {"id": "gate::fmt", "package": "__workspace__", "kind": "gate", "argv": ["cargo"]}
    LIB_ENTRY = {"id": "pkg::lib", "package": "pkg", "kind": "lib", "argv": ["cargo"]}

    def test_never_run_target_gets_its_kind_floor(self):
        budget, basis = vr.timeout_for(self.TEST_ENTRY, None)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])
        self.assertIn("never completed here", basis)

    def test_spec_building_target_floor_is_realistic_not_seconds(self):
        """The concrete regression: a spec-building target must never get 25s."""
        budget, _ = vr.timeout_for(self.TEST_ENTRY, None)
        self.assertGreaterEqual(budget, 2500, "spec builds alone routinely take 2000-2500s")

    def test_kinds_get_different_floors(self):
        self.assertNotEqual(
            vr.timeout_for(self.GATE_ENTRY, None)[0], vr.timeout_for(self.LIB_ENTRY, None)[0]
        )

    def test_measured_duration_scales_the_budget(self):
        rec = record(status=vr.STATUS_GREEN, duration_s=5000.0, source="measured")
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, int(5000.0 * vr.TIMEOUT_HEADROOM) + 1)
        self.assertIn("5000.0s", basis)

    def test_the_budget_is_derived_from_execution_not_from_queue_wait(self):
        """`duration_s` starts when the worker picks a row up, not when it runs.

        The budget it feeds bounds `proc.wait`, which starts only AFTER
        heavy_gate admits -- so deriving it from `duration_s` pays 4x headroom
        on time the target spent QUEUEING. Measured 2026-08-28: the
        `axiom_ratchet` row reads 22444.2 s wall against a 12799 s timeout,
        because 9,645 s of it (2h41m) was the block at the gate.
        """
        rec = record(status=vr.STATUS_GREEN, source="measured",
                     duration_s=22444.2, gate_wait_s=9645.0, exec_duration_s=12799.2)
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, int(12799.2 * vr.TIMEOUT_HEADROOM) + 1)
        self.assertIn("12799.2s", basis)
        self.assertIn("queue wait excluded", basis)
        self.assertNotIn("22444.2s", basis)

    def test_a_record_without_the_new_field_keeps_its_old_basis(self):
        """No existing budget may move because a new field was added."""
        rec = record(status=vr.STATUS_GREEN, duration_s=5000.0, source="measured")
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, int(5000.0 * vr.TIMEOUT_HEADROOM) + 1)
        self.assertIn("this target last took here", basis)

    def test_short_measured_duration_does_not_shrink_below_the_floor(self):
        rec = record(status=vr.STATUS_GREEN, duration_s=3.0, source="measured")
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])

    def test_a_killed_run_doubles_the_next_budget(self):
        """A kill is evidence the budget was too small -- it must escalate."""
        rec = record(status=vr.STATUS_ERROR, timed_out=True, timeout_s=20000, source="measured")
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, 40000)
        self.assertIn("KILLED", basis)

    def test_legacy_killed_record_without_the_flag_is_still_recognised(self):
        """Records written before `timed_out` existed must not read as completed."""
        rec = record(
            status=vr.STATUS_ERROR,
            timeout_s=25,
            duration_s=25.2,
            final_line="<timed out after 25s; last line: running 2 tests>",
            source="measured",
        )
        rec.pop("timed_out", None)
        self.assertTrue(vr._record_was_killed(rec))
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertGreaterEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])

    def test_a_killed_run_duration_is_never_used_to_size_the_next_one(self):
        """25.2s of a killed run is not evidence the target needs 100s."""
        rec = record(
            status=vr.STATUS_ERROR, timed_out=True, timeout_s=25, duration_s=25.2, source="measured"
        )
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertGreater(budget, int(25.2 * vr.TIMEOUT_HEADROOM))

    def test_budget_is_always_finite_and_clamped(self):
        rec = record(status=vr.STATUS_GREEN, duration_s=10**9, source="measured")
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, vr.TIMEOUT_HARD_CEILING)

    def test_no_policy_path_yields_a_disabled_timeout(self):
        """There must be no input that turns the timeout off."""
        for rec in (
            None,
            record(status=vr.STATUS_GREEN, duration_s=0, source="measured"),
            record(status=vr.STATUS_ERROR, timed_out=True, timeout_s=10**9, source="measured"),
            record(status="weird", source="measured"),
        ):
            for entry in (self.TEST_ENTRY, self.GATE_ENTRY, self.LIB_ENTRY):
                budget, _ = vr.timeout_for(entry, rec)
                self.assertGreater(budget, 0)
                self.assertLessEqual(budget, vr.TIMEOUT_HARD_CEILING)

    def test_explicit_override_still_wins_and_says_so(self):
        budget, basis = vr.timeout_for(self.TEST_ENTRY, None, override=90)
        self.assertEqual(budget, 90)
        self.assertIn("override", basis)

    def test_seeded_record_does_not_size_a_budget(self):
        """A result this runner did not measure is not evidence of cost either."""
        rec = record(status=vr.STATUS_GREEN, duration_s=9.0, source="seeded", seed_note="lane")
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])
        self.assertIn("never completed here", basis)

    def test_timeout_record_carries_its_basis_and_the_killed_flag(self):
        entry = {"id": "synthetic::hang2", "package": "synthetic", "kind": "test",
                 "argv": ["/bin/sh", "-c", "sleep 30"], "_dirs": [vr.REPO_ROOT / "scripts"]}
        rec = vr.run_one(entry, timeout=2, timeout_basis="unit test")
        self.assertIs(rec["timed_out"], True)
        self.assertEqual(rec["timeout_basis"], "unit test")
        self.assertIn("NOT a pass", rec["notes"])

    def test_completed_record_marks_itself_not_timed_out(self):
        entry = {"id": "synthetic::quick", "package": "synthetic", "kind": "test",
                 "argv": ["/bin/sh", "-c", "true"], "_dirs": [vr.REPO_ROOT / "scripts"]}
        rec = vr.run_one(entry, timeout=60, timeout_basis="unit test")
        self.assertIs(rec["timed_out"], False)


class TestGateExitCode(unittest.TestCase):
    def test_gate_all_green_exits_zero(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 5, "RED": 0, "UNKNOWN": 0, "RUNNING": 0}), 0)

    def test_gate_any_red_exits_one(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 4, "RED": 1, "UNKNOWN": 0, "RUNNING": 0}), 1)

    def test_gate_any_unknown_exits_two(self):
        """An absence of information must not pass a gate."""
        self.assertEqual(vr.gate_exit_code({"GREEN": 4, "RED": 0, "UNKNOWN": 1, "RUNNING": 0}), 2)

    def test_gate_running_counts_as_not_green(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 4, "RED": 0, "UNKNOWN": 0, "RUNNING": 1}), 2)

    def test_gate_red_outranks_unknown(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 0, "RED": 1, "UNKNOWN": 9, "RUNNING": 0}), 1)


SAMPLE_NAMES = [
    "sat_verify::cdcl::tests::a",
    "sat_verify::cdcl::tests::b",
    "sat_verify::frontier::tests::c",
    "spec::core_spec::par_reduction::par_reduction_tests::d",
    "spec::core_spec::par_reduction::par_reduction_tests::e",
    "spec::core_spec::impl_infer::tests::f",
    "spec::tests::g",
    "eval_ir::tests::h",
    # A test sitting DIRECTLY in a module that will be split: its key is that
    # module, which is a strict prefix of its siblings' keys.
    "spec::core_spec::loose_test",
    # A test at the crate root, with no module path at all.
    "bare_root_test",
]


class TestShardKey(unittest.TestCase):
    """The key is what makes the shards a partition, so it must be a function."""

    def test_key_is_total_every_name_gets_exactly_one(self):
        splits = {"spec", "spec::core_spec"}
        keys = [vr.shard_key(n, splits) for n in SAMPLE_NAMES]
        self.assertEqual(len(keys), len(SAMPLE_NAMES))
        self.assertTrue(all(isinstance(k, str) and k for k in keys))

    def test_key_is_deterministic(self):
        splits = {"spec", "spec::core_spec"}
        self.assertEqual(
            [vr.shard_key(n, splits) for n in SAMPLE_NAMES],
            [vr.shard_key(n, splits) for n in reversed(SAMPLE_NAMES)][::-1],
        )

    def test_key_never_consumes_the_test_function_name(self):
        """`a::b::t` under split `a::b` must key on `a::b`, not on the test `t`."""
        self.assertEqual(vr.shard_key("spec::core_spec::loose_test", {"spec", "spec::core_spec"}),
                         "spec::core_spec")

    def test_key_of_a_root_test_is_itself(self):
        self.assertEqual(vr.shard_key("bare_root_test", set()), "bare_root_test")

    def test_unsplit_names_key_on_the_top_level_module(self):
        self.assertEqual(vr.shard_key("sat_verify::cdcl::tests::a", set()), "sat_verify")

    def test_classes_of_the_key_partition_the_names(self):
        """Sum of class sizes == population, and no name in two classes."""
        splits = vr.derive_splits(SAMPLE_NAMES, max_tests=2)
        buckets = {}
        for name in SAMPLE_NAMES:
            buckets.setdefault(vr.shard_key(name, splits), []).append(name)
        self.assertEqual(sum(len(v) for v in buckets.values()), len(SAMPLE_NAMES))
        flat = [n for v in buckets.values() for n in v]
        self.assertEqual(sorted(flat), sorted(SAMPLE_NAMES))
        self.assertEqual(len(flat), len(set(flat)))


class TestDeriveSplits(unittest.TestCase):
    def test_splits_reach_a_fixpoint_under_the_cap(self):
        splits = vr.derive_splits(SAMPLE_NAMES, max_tests=1)
        counts = {}
        for name in SAMPLE_NAMES:
            key = vr.shard_key(name, splits)
            counts[key] = counts.get(key, 0) + 1
        for key, count in counts.items():
            if count > 1:
                # Only an indivisible key may exceed the cap: every member must
                # already be at the module depth of the key.
                members = [n for n in SAMPLE_NAMES if vr.shard_key(n, splits) == key]
                self.assertTrue(
                    all(len(m.split("::")) - 1 <= len(key.split("::")) for m in members),
                    f"{key} exceeded the cap but was still divisible",
                )

    def test_a_cap_above_the_population_splits_nothing(self):
        self.assertEqual(vr.derive_splits(SAMPLE_NAMES, max_tests=1000), set())


class TestShardFilters(unittest.TestCase):
    def test_a_prefix_key_skips_its_sibling_keys(self):
        keys = ["spec::core_spec", "spec::core_spec::impl_infer", "spec::core_spec::par_reduction"]
        filters, skips = vr.shard_filters("spec::core_spec", keys)
        self.assertEqual(filters, ["spec::core_spec::"])
        self.assertEqual(skips, ["spec::core_spec::impl_infer::", "spec::core_spec::par_reduction::"])

    def test_a_leaf_key_needs_no_skips(self):
        keys = ["spec::core_spec", "spec::core_spec::impl_infer"]
        _filters, skips = vr.shard_filters("spec::core_spec::impl_infer", keys)
        self.assertEqual(skips, [])


class TestShardRealisation(unittest.TestCase):
    """libtest matches substrings with no anchor, so a prefix is not always safe."""

    def test_an_unambiguous_prefix_is_used_as_is(self):
        declared = ["a::x::t1", "a::x::t2", "b::y::t3"]
        mode, filters, skips = vr.shard_realisation("a", ["a", "b"], {"a::x::t1", "a::x::t2"}, declared)
        self.assertEqual(mode, "prefix")
        self.assertEqual(filters, ["a::"])
        self.assertEqual(skips, [])

    def test_an_overreaching_prefix_falls_back_to_exact_names(self):
        """The measured case: `tests::` selects 3501 of 6900 tests, not 5."""
        declared = ["tests::t1", "tests::t2", "sat::cdcl::tests::t3"]
        mode, filters, _skips = vr.shard_realisation(
            "tests", ["tests", "sat"], {"tests::t1", "tests::t2"}, declared
        )
        self.assertEqual(mode, "exact")
        self.assertEqual(filters, ["tests::t1", "tests::t2"])

    def test_exact_mode_names_every_member_and_nothing_else(self):
        declared = ["proofs::tests::a", "nn::crown_proofs::tests::b"]
        intended = {"proofs::tests::a"}
        mode, filters, _ = vr.shard_realisation("proofs", ["proofs", "nn"], intended, declared)
        self.assertEqual(mode, "exact")
        self.assertEqual(set(filters), intended)

    def test_binary_args_pass_exact_flag_only_in_exact_mode(self):
        self.assertEqual(
            vr.shard_binary_args({"mode": "exact", "filters": ["a::t"], "skip": []}),
            ["--exact", "a::t"],
        )
        self.assertEqual(
            vr.shard_binary_args({"mode": "prefix", "filters": ["a::"], "skip": ["a::b::"]}),
            ["a::", "--skip", "a::b::"],
        )


class TestShardRecordPaths(unittest.TestCase):
    def test_shard_records_live_under_their_parent(self):
        path = vr.record_path("clean-verify::lib::shard::spec::core_spec")
        self.assertIn("shards", path.parts)
        self.assertIn(vr.safe_name("clean-verify::lib"), path.parts)

    def test_plain_records_stay_at_the_top_level(self):
        self.assertEqual(vr.record_path("clean-verify::lib").parent, vr.STATE_DIR)


def _shard_entry(key, count):
    parent = "pkg::lib"
    return {
        "id": vr.shard_target_id(parent, key),
        "package": "pkg",
        "kind": vr.KIND_SHARD,
        "argv": ["cargo"],
        "_parent": parent,
        "_shard": {"key": key, "id": vr.shard_target_id(parent, key), "test_count": count},
    }


class TestShardCountGuard(unittest.TestCase):
    """A shard whose filter matches nothing exits 0. That must not read GREEN."""

    def test_shard_running_its_planned_count_is_green(self):
        entry = _shard_entry("a", 5)
        rec = record(counts={"passed": 5, "failed": 0, "ignored": 0, "result_lines": 1})
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_GREEN)

    def test_shard_that_ran_nothing_is_unknown_not_green(self):
        entry = _shard_entry("a", 5)
        rec = record(counts={"passed": 0, "failed": 0, "ignored": 0, "result_lines": 1})
        row = vr.derive(entry, rec, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("ran 0 tests", row["reason"])

    def test_shard_that_ran_too_few_is_unknown(self):
        entry = _shard_entry("a", 5)
        rec = record(counts={"passed": 4, "failed": 0, "ignored": 1, "result_lines": 1})
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_GREEN)
        rec = record(counts={"passed": 3, "failed": 0, "ignored": 0, "result_lines": 1})
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)


class TestRollup(unittest.TestCase):
    """The roll-up is GREEN only on a complete, proved, fresh set of shards."""

    PARENT = "pkg::lib"

    def _plan(self, shard_counts, verified=True, digest=DIGEST):
        return {
            "schema": vr.PLAN_SCHEMA,
            "parent": self.PARENT,
            "package": "pkg",
            "base_argv": ["targo", "--unverified", "test"],
            "commit": "0" * 40,
            "generated_at": "2026-08-13T00:00:00Z",
            "input_digest": digest,
            "max_tests_per_shard": 100,
            "split_prefixes": [],
            "partition_proof": {"verified": verified, "declared_total": sum(shard_counts.values())},
            "shards": [
                {"key": k, "id": vr.shard_target_id(self.PARENT, k), "filters": [f"{k}::"],
                 "skip": [], "test_count": c}
                for k, c in sorted(shard_counts.items())
            ],
        }

    def setUp(self):
        # A roll-up derives any shard row the caller did not supply, which means
        # computing that shard's digest. These synthetic shards have no sources,
        # so the digest is pinned instead of measured.
        self._real_digest = vr.input_digest
        vr.input_digest = lambda entry, fresh=False: DIGEST

    def tearDown(self):
        vr.input_digest = self._real_digest

    def _entry(self, plan):
        return {"id": self.PARENT, "package": "pkg", "kind": vr.KIND_ROLLUP,
                "argv": ["cargo"], "_plan": plan, "_dirs": [vr.REPO_ROOT / "scripts"]}

    @staticmethod
    def _rows(plan, buckets):
        return [{"target": s["id"], "bucket": b, "kind": vr.KIND_SHARD}
                for s, b in zip(plan["shards"], buckets)]

    def _write_shard_records(self, plan, ran):
        for shard, count in zip(plan["shards"], ran):
            vr.write_record({
                "target": shard["id"], "status": vr.STATUS_GREEN, "source": "measured",
                "input_digest": DIGEST,
                "counts": {"passed": count, "failed": 0, "ignored": 0, "result_lines": 1},
            })

    def test_no_plan_is_unknown(self):
        entry = {"id": "pkg::unplanned", "package": "pkg", "kind": vr.KIND_ROLLUP, "argv": ["c"]}
        row = vr.derive(entry, None, DIGEST, [])
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("no shard plan", row["reason"])

    def test_unproved_partition_is_unknown_even_if_every_shard_is_green(self):
        plan = self._plan({"a": 2, "b": 3}, verified=False)
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("partition proof", row["reason"])

    def test_stale_plan_is_unknown(self):
        plan = self._plan({"a": 2}, digest=OTHER)
        row = vr.derive(self._entry(plan), None, DIGEST, self._rows(plan, [vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("stale", row["reason"])

    def test_one_unknown_shard_makes_the_parent_unknown_never_green(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_UNKNOWN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_one_running_shard_makes_the_parent_unknown(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_RUNNING]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_one_red_shard_makes_the_parent_red(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_RED]))
        self.assertEqual(row["bucket"], vr.BUCKET_RED)

    def test_an_unenumerated_shard_is_derived_from_the_plan_not_assumed(self):
        """`--only <parent>` enumerates no shards; the plan still decides."""
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST, [])
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)

    def test_a_shard_with_no_record_at_all_makes_the_parent_unknown(self):
        """An incomplete measurement must never roll up to GREEN."""
        plan = self._plan({"a": 2, "b": 3})
        # Only the first shard has ever run.
        vr.write_record({
            "target": plan["shards"][0]["id"], "status": vr.STATUS_GREEN, "source": "measured",
            "input_digest": DIGEST,
            "counts": {"passed": 2, "failed": 0, "ignored": 0, "result_lines": 1},
        })
        path = vr.record_path(plan["shards"][1]["id"])
        if path.exists():
            path.unlink()
        row = vr.derive(self._entry(plan), None, DIGEST, [])
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("1 UNKNOWN", row["reason"])

    def test_all_green_and_counts_close_is_green(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)
        self.assertIn("5 tests ran", row["reason"])

    def test_all_green_but_fewer_tests_ran_than_declared_is_unknown(self):
        """The run-time half of the partition proof: the pieces must re-sum."""
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 2])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("does not close", row["reason"])


class TestPartitionVerification(unittest.TestCase):
    """`verify_partition` must fail loudly on drops, duplicates and strays."""

    @staticmethod
    def _fake_lister(mapping):
        def lister(_binary, args=None):
            return sorted(mapping[tuple(args or [])])
        return lister

    def _run(self, shards, declared, mapping):
        original = vr.list_tests
        vr.list_tests = self._fake_lister(mapping)
        try:
            return vr.verify_partition(Path("fake"), shards, declared)
        finally:
            vr.list_tests = original

    def test_clean_partition_verifies(self):
        shards = [
            {"id": "s::a", "filters": ["a::"], "skip": [], "test_count": 2, "_intended": ["a::x", "a::y"]},
            {"id": "s::b", "filters": ["b::"], "skip": [], "test_count": 1, "_intended": ["b::z"]},
        ]
        proof = self._run(shards, ["a::x", "a::y", "b::z"],
                          {("a::",): ["a::x", "a::y"], ("b::",): ["b::z"]})
        self.assertTrue(proof["verified"])
        self.assertEqual(proof["sum_of_shard_counts"], 3)
        self.assertEqual(proof["union_size"], 3)

    def test_a_dropped_test_fails_the_proof(self):
        shards = [
            {"id": "s::a", "filters": ["a::"], "skip": [], "test_count": 2, "_intended": ["a::x", "a::y"]},
        ]
        proof = self._run(shards, ["a::x", "a::y", "b::z"], {("a::",): ["a::x", "a::y"]})
        self.assertFalse(proof["verified"])
        self.assertEqual(proof["dropped_count"], 1)

    def test_a_double_counted_test_fails_the_proof(self):
        shards = [
            {"id": "s::a", "filters": ["a::"], "skip": [], "test_count": 1, "_intended": ["a::x"]},
            {"id": "s::b", "filters": ["x"], "skip": [], "test_count": 1, "_intended": ["a::x"]},
        ]
        proof = self._run(shards, ["a::x"], {("a::",): ["a::x"], ("x",): ["a::x"]})
        self.assertFalse(proof["verified"])
        self.assertEqual(proof["duplicated_count"], 1)

    def test_substring_overreach_is_caught_as_a_shard_mismatch(self):
        """The concrete hazard: `eval_ir::` also matches `spec::eval_ir::`."""
        declared = ["eval_ir::tests::a", "spec::eval_ir::tests::b"]
        shards = [
            {"id": "s::eval_ir", "filters": ["eval_ir::"], "skip": [], "test_count": 1,
             "_intended": ["eval_ir::tests::a"]},
            {"id": "s::spec", "filters": ["spec::"], "skip": [], "test_count": 1,
             "_intended": ["spec::eval_ir::tests::b"]},
        ]
        proof = self._run(shards, declared,
                          {("eval_ir::",): declared, ("spec::",): ["spec::eval_ir::tests::b"]})
        self.assertFalse(proof["verified"])
        self.assertGreaterEqual(proof["duplicated_count"], 1)
        self.assertGreaterEqual(proof["mismatched_shard_count"], 1)


class TestSpecPayingScan(unittest.TestCase):
    """The cost hint. Wrong answers cost time; they can never cost correctness."""

    def _src(self, files):
        tmp = tempfile.mkdtemp()
        root = Path(tmp) / "src"
        for rel, text in files.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return root

    def test_a_directory_module_reports_its_top_level_name(self):
        root = self._src({
            "spec/core_spec/par.rs": "fn t() { let s = build_spec_with_stack(); }",
            "nn_verify/crown.rs": "fn t() { assert!(true); }",
        })
        roots, evidence = vr.spec_paying_roots(root)
        self.assertEqual(roots, {"spec"})
        self.assertEqual(evidence, ["spec/core_spec/par.rs"])

    def test_lib_rs_maps_to_the_crate_root_tests_key(self):
        root = self._src({"lib.rs": "mod tests { fn t() { build_spec_with_stack(); } }"})
        roots, _ = vr.spec_paying_roots(root)
        self.assertEqual(roots, {"tests"})

    def test_a_top_level_file_module_drops_its_rs_suffix(self):
        root = self._src({"eval_ir.rs": "fn t() { build_eval_ir_spec_with_stack(); }"})
        roots, _ = vr.spec_paying_roots(root)
        self.assertEqual(roots, {"eval_ir"})

    def test_a_missing_source_tree_is_not_an_error(self):
        self.assertEqual(vr.spec_paying_roots(Path("/no/such/dir")), (set(), []))


class TestPackGrouping(unittest.TestCase):
    def test_a_spec_paying_root_always_lands_in_the_shared_bin(self):
        self.assertEqual(vr.pack_group_of("spec::core_spec", {"spec": 3}, {"spec"}, 100), "spec_paying")

    def test_a_big_non_spec_root_gets_its_own_group(self):
        self.assertEqual(vr.pack_group_of("sat_verify::cdcl", {"sat_verify": 2764}, set(), 100),
                         "sat_verify")

    def test_a_small_non_spec_root_is_swept_into_misc(self):
        self.assertEqual(vr.pack_group_of("ffi", {"ffi": 9}, set(), 100), "misc")


class TestPackBins(unittest.TestCase):
    def _buckets(self, sizes):
        return {key: [f"{key}::t{i}" for i in range(n)] for key, n in sizes.items()}

    def test_every_key_lands_in_exactly_one_bin(self):
        buckets = self._buckets({"a": 400, "b": 400, "c": 400, "d": 5})
        groups = {"a": "g", "b": "g", "c": "g", "d": "misc"}
        bins = vr.pack_bins(buckets, groups, 900)
        placed = [key for item in bins for key in item["keys"]]
        self.assertEqual(sorted(placed), sorted(buckets))
        self.assertEqual(len(placed), len(set(placed)))

    def test_a_bin_never_mixes_groups(self):
        buckets = self._buckets({"a": 10, "b": 10})
        bins = vr.pack_bins(buckets, {"a": "one", "b": "two"}, 1000)
        self.assertEqual(len(bins), 2)

    def test_the_cap_is_respected_except_for_an_indivisible_key(self):
        buckets = self._buckets({"a": 600, "b": 600, "huge": 5000})
        groups = dict.fromkeys(buckets, "g")
        bins = vr.pack_bins(buckets, groups, 1000)
        sizes = [sum(len(buckets[k]) for k in item["keys"]) for item in bins]
        self.assertIn(5000, sizes)  # its own bin, over the cap, undivided
        self.assertTrue(all(size <= 1000 for size in sizes if size != 5000))

    def test_a_single_bin_group_keeps_the_bare_group_name(self):
        bins = vr.pack_bins(self._buckets({"a": 3}), {"a": "solo"}, 1000)
        self.assertEqual(bins[0]["key"], "solo")

    def test_a_split_group_numbers_its_bins(self):
        bins = vr.pack_bins(self._buckets({"a": 600, "b": 600}), {"a": "g", "b": "g"}, 700)
        self.assertEqual([item["key"] for item in bins], ["g_01", "g_02"])


class TestLibtestSelect(unittest.TestCase):
    """Our mirror of libtest's own filtering. A skip beats an include."""

    def test_substring_matching_is_unanchored(self):
        declared = ["a::t", "z::a::t"]
        self.assertEqual(vr.libtest_select(declared, ["a::"], []), {"a::t", "z::a::t"})

    def test_a_skip_removes_a_test_an_include_matched(self):
        declared = ["a::t", "a::b::t"]
        self.assertEqual(vr.libtest_select(declared, ["a::"], ["a::b::"]), {"a::t"})

    def test_exact_mode_matches_whole_names_only(self):
        declared = ["a::t", "a::t2"]
        self.assertEqual(vr.libtest_select(declared, ["a::t"], [], exact=True), {"a::t"})


class TestBinRealisation(unittest.TestCase):
    def test_packing_two_keys_uses_both_prefixes(self):
        declared = ["a::x::t", "b::y::t", "c::z::t"]
        mode, filters, skips = vr.bin_realisation(
            ["a", "b"], ["a", "b", "c"], {"a::x::t", "b::y::t"}, declared
        )
        self.assertEqual((mode, filters, skips), ("prefix", ["a::", "b::"], []))

    def test_a_fence_comes_down_when_the_sibling_joins_the_bin(self):
        """`a`'s skip of `a::b::` exists to fence off `a::b`. Packed together it must go."""
        declared = ["a::t", "a::b::t"]
        keys = ["a", "a::b"]
        mode, filters, skips = vr.bin_realisation(keys, keys, {"a::t", "a::b::t"}, declared)
        self.assertEqual(mode, "prefix")
        self.assertEqual(skips, [])
        self.assertEqual(vr.libtest_select(declared, filters, skips), {"a::t", "a::b::t"})

    def test_a_fence_stays_up_when_the_sibling_is_in_another_bin(self):
        declared = ["a::t", "a::b::t"]
        keys = ["a", "a::b"]
        mode, filters, skips = vr.bin_realisation(["a"], keys, {"a::t"}, declared)
        self.assertEqual((mode, filters, skips), ("prefix", ["a::"], ["a::b::"]))

    def test_an_overreaching_prefix_in_the_bin_forces_exact(self):
        declared = ["tests::t1", "spec::t2", "sat::cdcl::tests::t3"]
        intended = {"tests::t1", "spec::t2"}
        mode, filters, _ = vr.bin_realisation(
            ["tests", "spec"], ["tests", "spec", "sat"], intended, declared
        )
        self.assertEqual(mode, "exact")
        self.assertEqual(set(filters), intended)

    def test_a_bin_too_big_to_name_exactly_is_refused_not_truncated(self):
        long = "x" * 400
        declared = [f"tests::{long}{i}" for i in range(1000)] + ["sat::tests::other"]
        intended = set(declared[:-1])
        self.assertIsNone(
            vr.bin_realisation(["tests"], ["tests", "sat"], intended, declared)
        )


class TestPackedShardBudgets(unittest.TestCase):
    """The floors must be what the measured cost model says, not round numbers."""

    def test_the_spec_shard_floor_covers_four_flavour_builds_plus_marginal(self):
        derived = vr.SPEC_FLAVOURS * vr.ONE_FLAVOUR_BUILD_S + vr.DECLARED_TESTS * vr.MARGINAL_PER_TEST_S
        floor = vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD_SPEC]
        self.assertGreaterEqual(floor, derived)
        self.assertLess(floor, derived * 1.15, "a floor well above its derivation is slack, not a derivation")

    def test_the_cheap_shard_floor_covers_the_population_plus_one_build(self):
        derived = 4.0 * vr.CHEAP_POPULATION_S + vr.ONE_FLAVOUR_BUILD_S
        floor = vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD]
        self.assertGreaterEqual(floor, derived)
        self.assertLess(floor, derived * 1.15)

    def test_a_spec_shard_gets_the_spec_floor_and_a_cheap_one_does_not(self):
        spec, _ = vr.timeout_for({"kind": vr.KIND_SHARD_SPEC}, None)
        cheap, _ = vr.timeout_for({"kind": vr.KIND_SHARD}, None)
        self.assertEqual(spec, vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD_SPEC])
        self.assertEqual(cheap, vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD])
        self.assertGreater(spec, cheap)

    def test_shard_entries_carry_the_kind_the_plan_assigned(self):
        plan = {
            "parent": "pkg::lib", "package": "pkg",
            "base_argv": ["targo", "--unverified", "test"],
            "shards": [
                {"id": "pkg::lib::shard::spec_paying", "key": "spec_paying",
                 "kind": vr.KIND_SHARD_SPEC, "mode": "prefix", "filters": ["spec::"],
                 "skip": [], "test_count": 3},
                {"id": "pkg::lib::shard::misc", "key": "misc", "mode": "prefix",
                 "filters": ["misc::"], "skip": [], "test_count": 1},
            ],
        }
        kinds = {e["id"]: e["kind"] for e in vr.shard_entries(plan)}
        self.assertEqual(kinds["pkg::lib::shard::spec_paying"], vr.KIND_SHARD_SPEC)
        # A plan written before packing has no `kind`; it must still be a shard.
        self.assertEqual(kinds["pkg::lib::shard::misc"], vr.KIND_SHARD)


class TestCommandRendering(unittest.TestCase):
    def test_a_short_command_is_stored_verbatim(self):
        argv = ["targo", "--unverified", "test", "--lib"]
        self.assertEqual(vr.render_command(argv), "targo --unverified test --lib")

    def test_rendered_command_round_trips_argument_boundaries(self):
        argv = ["/path with spaces/tool", "", "a b", "line\nbreak", "$(touch nope)",
                "semi;colon", "single'quote", 'double"quote', "back\\slash", "λ"]
        self.assertEqual(shlex.split(vr.render_command(argv)), argv)

    def test_a_huge_exact_argv_is_marked_not_silently_cut(self):
        argv = ["targo", "--unverified", "test", "--"] + [f"name_{i:06d}" * 4 for i in range(2000)]
        rendered = vr.render_command(argv)
        self.assertIn("<<TRUNCATED:", rendered)
        self.assertIn("NOT runnable", rendered)
        self.assertLess(len(rendered), 2_500)


class TestInventory(unittest.TestCase):
    def test_gates_match_the_documented_prepush_commands(self):
        by_id = {g["id"]: g["argv"] for g in vr.WORKSPACE_GATES}
        self.assertIn("--workspace", by_id["gate::check"])
        self.assertIn("--all-targets", by_id["gate::check"])
        self.assertIn("--workspace", by_id["gate::clippy"])
        self.assertIn("--all-targets", by_id["gate::clippy"])
        self.assertIn("--all", by_id["gate::fmt"])

    def test_the_paragon_ratchet_is_a_gate_row(self):
        """It was not, and that is how `files_over_500` grew 1410 -> 1416.

        `scripts/paragon_ratchet.sh` is a leg of `scripts/local_gate.sh` in both
        modes, and `scripts/hooks/pre-push` runs `local_gate.sh --fast` -- but
        that hook only exists once `just install-hooks` points `core.hooksPath`
        at it, and on the box that produced the 2026-08-16 suite pass it did
        not. This runner is what ran; the ratchet has to be one of its rows or
        nothing routine measures it.
        """
        by_id = {g["id"]: g for g in vr.WORKSPACE_GATES}
        self.assertIn("gate::paragon", by_id)
        self.assertEqual(by_id["gate::paragon"]["argv"], ["scripts/paragon_ratchet.sh"])
        self.assertEqual(by_id["gate::paragon"]["kind"], "gate")

    def test_the_paragon_row_declares_the_inputs_no_crate_dir_covers(self):
        """The ratchet MEASURES crates/ but DECIDES against files outside it.

        A row digested over the crate dirs alone would stay fresh across an edit
        to the baseline it compares against, or to the heuristics that produce
        the numbers -- a stale green in the one place the whole artifact exists
        to prevent.
        """
        entry = next(g for g in vr.WORKSPACE_GATES if g["id"] == "gate::paragon")
        extra = list(entry["_extra_paths"])
        self.assertEqual(
            extra, ["data/paragon_ratchet.json", "scripts/paragon_ratchet.sh"]
        )
        for rel in extra:
            self.assertFalse(
                rel.startswith("crates/"),
                f"{rel} is under crates/ and needs no declaration; the point of "
                f"_extra_paths is inputs the workspace dirs do NOT reach",
            )
            self.assertTrue(
                (vr.REPO_ROOT / rel).exists(),
                f"{rel} is declared as a digest input but is not in the tree",
            )

    def test_adopted_checker_edit_invalidates_source_census_digest(self):
        gate = next(g for g in vr.WORKSPACE_GATES if g["id"] == "gate::self-proof-elab")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "theories/kcheck_labelled/KCheck/Token.lean"
            source.parent.mkdir(parents=True)
            source.write_text("def token := 1\n")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            wide = dict(gate, _dirs=[root / p for p in gate["_extra_paths"]])
            narrow = dict(wide, _dirs=[p for p in wide["_dirs"] if p != root / "theories/kcheck_labelled"])
            with mock.patch.object(vr, "REPO_ROOT", root), \
                    mock.patch.object(vr, "toolchain_id", return_value="fixture-compiler"):
                before = vr.input_digest(wide, fresh=True)
                old_before = vr.input_digest(narrow, fresh=True)
                source.write_text("def token := 2\n")
                self.assertEqual(old_before, vr.input_digest(narrow, fresh=True))
                self.assertNotEqual(before, vr.input_digest(wide, fresh=True))

    def test_a_declared_file_path_really_widens_the_digest(self):
        """`_dirs` holding a FILE must be hashed, not silently ignored.

        The widening rests entirely on `git ls-files -- <path>` accepting a file
        pathspec the same way it accepts a directory. If that ever stopped being
        true the scope would narrow in silence, which is exactly the failure the
        declaration is there to prevent -- so it is measured rather than
        assumed.
        """
        narrow = {
            "id": "probe",
            "package": "__workspace__",
            "kind": "gate",
            "argv": ["scripts/paragon_ratchet.sh"],
            "_dirs": [vr.REPO_ROOT / "crates" / "clean-verify"],
        }
        wide = dict(narrow)
        wide["_dirs"] = narrow["_dirs"] + [vr.REPO_ROOT / "data" / "paragon_ratchet.json"]
        self.assertNotEqual(
            vr.input_digest(narrow, fresh=True), vr.input_digest(wide, fresh=True)
        )




class MemoryAdmissionTests(unittest.TestCase):
    """The runner's concurrency unit is memory, and it learns its own weights.

    Regression cover for reports/kernel-panic-rca-2026-08-19.md: `--jobs N`
    used to mean N targets regardless of whether each was 50 MB or 8.8 GB.
    """

    def test_unmeasured_target_gets_the_conservative_default(self):
        with mock.patch.object(vr, "load_record", return_value=None):
            self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)

    def test_default_exceeds_the_measured_spec_binary(self):
        # 8.8 GB RSS was measured for a clean-verify spec binary. A default
        # below that would under-admit the very shape that caused the panic.
        self.assertGreater(vr.DEFAULT_TARGET_GB, 8.8)

    def test_a_measured_target_admits_at_its_own_cost_plus_headroom(self):
        with mock.patch.object(vr, "load_record", return_value={"peak_rss_gb": 8.8}):
            self.assertEqual(vr._gate_weight_gb("t"), 14)   # ceil(8.8 * 1.5)

    def test_a_tiny_target_never_admits_at_zero(self):
        with mock.patch.object(vr, "load_record", return_value={"peak_rss_gb": 0.05}):
            self.assertEqual(vr._gate_weight_gb("t"), vr.MIN_TARGET_GB)

    def test_a_junk_measurement_falls_back_to_the_default(self):
        for bad in ({"peak_rss_gb": 0}, {"peak_rss_gb": -3}, {"peak_rss_gb": "big"}, {}):
            with mock.patch.object(vr, "load_record", return_value=bad):
                self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)

    def test_a_missing_gate_never_blocks_the_suite(self):
        # The gate is a safety device, not a dependency: if it is absent the
        # suite must still run, just without admission control, and the tuple
        # must preserve that fact for the row's `gate_admitted` provenance.
        with mock.patch.object(vr, "HEAVY_GATE", vr.REPO_ROOT / "no" / "such"):
            # The REAL implementation, not the module-level stub: this test is
            # the one that is about acquisition. An absent gate script makes it
            # return without ever queueing.
            token, enforced, refused = _REAL_GATE_ACQUIRE(4, "t")
            self.assertIsNone(token)
            self.assertFalse(enforced)
            # An ABSENT gate is not a REFUSAL. `refused` makes run_one record
            # STATUS_ERROR and skip the target entirely, so conflating the two
            # would turn "no gate installed" into "the whole suite is UNKNOWN".
            self.assertFalse(refused)
            _REAL_GATE_RELEASE(token)       # must not raise

    def test_small_box_refusal_exit_75_is_a_refusal_not_a_fall_through(self):
        # REGRESSION, 2026-09-17. `heavy_gate.sh` refuses an over-budget request
        # with `exit 75` (heavy_gate.sh:541, asserted by its own selftest at
        # :686). This function used to accept only returncode 2 -- a code
        # heavy_gate.sh NEVER emits (its exits are 0, 1, 3, 7, 64, 75) -- so
        # every refusal fell through the retry loop to (None, False, False),
        # which run_one reads as "gate absent" and runs the target UNGATED.
        # On an 8 GB box that is the majority of the suite, and it is precisely
        # the fail-open the 2026-08-24 kernel-panic postmortem forbids.
        import stat as _stat

        with tempfile.TemporaryDirectory() as td:
            fake = os.path.join(td, "heavy_gate.sh")
            calls = os.path.join(td, "calls")
            # Every invocation that actually RUNS appends one line, so the
            # count is the number of answers the gate gave, not a timing proxy.
            with open(fake, "w", encoding="utf-8") as fh:
                fh.write(f"#!/bin/sh\necho \"$1\" >> '{calls}'\nexit 75\n")
            os.chmod(fake, os.stat(fake).st_mode | _stat.S_IEXEC)

            def answers() -> int:
                try:
                    with open(calls, encoding="utf-8") as fh:
                        return len(fh.read().splitlines())
                except FileNotFoundError:
                    return 0

            # The backoff, observed instead of waited for: each sleep records
            # how many gate answers had arrived when it was taken.
            backoffs: list[int] = []
            with mock.patch.object(vr, "HEAVY_GATE", _FakePath(fake)), \
                    mock.patch.object(vr.time, "sleep",
                                      side_effect=lambda _s: backoffs.append(answers())):
                token, enforced, refused = _REAL_GATE_ACQUIRE(24, "t")
            self.assertIsNone(token)
            self.assertFalse(enforced)
            # The whole point: REFUSED, so run_one records STATUS_ERROR and
            # skips the target instead of running it with no reservation.
            self.assertTrue(
                refused,
                "exit 75 fell through as 'gate unavailable' -- the runner would "
                "run this target UNGATED",
            )
            # A refusal must not be retried: retrying a denial wastes the
            # backoff and muddies the record. Stated exactly, not as a
            # wall-clock bound (WS6.13 land, 2026-09-30: 5.88 s > 5.0 s on a
            # box at load 32 -- a bound on elapsed time measures the box, and
            # it also misses a retry that is merely fast): the gate answered
            # exactly once, with `acquire`, and no backoff was taken after
            # that answer. A backoff BEFORE it can only follow a spawn that
            # raised, which the malfunction path retries by design.
            self.assertEqual(
                answers(), 1,
                "a refusal was retried instead of being taken at face value",
            )
            with open(calls, encoding="utf-8") as fh:
                self.assertEqual(fh.read().splitlines(), ["acquire"])
            self.assertTrue(
                all(seen == 0 for seen in backoffs),
                f"a backoff was taken after the gate refused: {backoffs}",
            )

    def test_gate_refusal_codes_match_what_heavy_gate_actually_emits(self):
        # Pin the coupling rather than the number: if heavy_gate.sh changes its
        # refusal code, this fails instead of silently reopening the fail-open.
        gate = os.path.join(str(vr.REPO_ROOT), "scripts", "heavy_gate.sh")
        if not os.path.exists(gate):
            self.skipTest("heavy_gate.sh absent")
        with open(gate, "r", encoding="utf-8") as fh:
            body = fh.read()
        self.assertIn(
            "exit 75",
            body,
            "heavy_gate.sh no longer refuses with 75; GATE_REFUSAL_CODES is stale",
        )
        self.assertIn(75, vr.GATE_REFUSAL_CODES)

    def test_peak_rss_measures_a_real_process_group(self):
        # The child ANNOUNCES that it has allocated, and sampling starts only
        # then. Measured 2026-09-17: with the sampler started first against a
        # child that lived exactly 2.0s -- the sampler's own poll interval --
        # this failed roughly 1 run in 5 under load, because the t=0 sample
        # could land before the allocation and the next one after the child had
        # already exited. A memory gate that reds on a busy machine teaches
        # people to re-run it, so the handshake is load-bearing, not tidiness.
        proc = subprocess.Popen(
            [sys.executable, "-c",
             "import sys,time; x=bytearray(300*1024*1024); x[::4096]=b'\\1'*len(x[::4096]);"
             " sys.stdout.write('ready\\n'); sys.stdout.flush(); time.sleep(6)"],
            stdout=subprocess.PIPE, text=True, start_new_session=True,
        )
        self.assertEqual(proc.stdout.readline().strip(), "ready")
        stop = threading.Event()
        out: list[vr.RssProfile] = []
        t = threading.Thread(target=lambda: out.append(vr._rss_profile(proc.pid, stop)))
        t.start()
        proc.wait()
        stop.set()
        t.join(timeout=10)
        self.assertGreaterEqual(out[0].samples, 2, "child outlived fewer than two poll intervals")
        self.assertGreater(out[0].peak_gb, 0.2)      # saw the ~300 MB allocation
        self.assertLess(out[0].peak_gb, 4.0)         # and did not invent a number
        self.assertGreater(out[0].samples, 0)        # and says how many samples it is

    def test_a_group_sum_above_physical_ram_is_clamped_and_kept(self):
        """A resident set larger than the machine is the instrument, not the job.

        Summing `ps rss` across a process group double-counts pages shared
        between its processes. That is not theoretical: the committed record
        `clean-verify__test__kernel_core_red_env_fidelity.json` reads a 57.26 GB
        peak on a 36 GB box -- 1.59x physical RAM -- and 1.5x THAT is the weight
        it then reserved. The clamp is a bound the machine itself supplies, so
        it is not a guess; the unclamped sum is kept rather than discarded.
        """
        stop = threading.Event()
        stop.set()                          # one pass, then return

        with mock.patch.object(vr, "_phys_ram_gb", return_value=36.0), \
             mock.patch.object(vr.subprocess, "run") as run:
            run.return_value = types.SimpleNamespace(stdout="30000000\n30000000\n")
            stop2 = threading.Event()
            done = threading.Event()
            out: list[vr.RssProfile] = []

            def sample():
                out.append(vr._rss_profile(4242, stop2))
                done.set()

            t = threading.Thread(target=sample)
            t.start()
            time.sleep(0.3)
            stop2.set()
            done.wait(timeout=10)
            t.join(timeout=10)

        # 2 x 30,000,000 kB = 57.22 GB summed; the box is 36 GB.
        self.assertGreater(out[0].raw_peak_gb, 36.0)
        self.assertEqual(out[0].peak_gb, 36.0)
        self.assertLessEqual(out[0].p50_gb, 36.0)

    def test_the_budget_copy_agrees_with_heavy_gate_itself(self):
        """`weights` says which rows run ALONE; that answer is heavy_gate's.

        The threshold is duplicated here so a read-only view need not shell out
        to the gate, and a duplicated constant drifts. This compares the copy
        against `heavy_gate.sh status` on THIS machine, so the two cannot
        disagree without a test failing -- which matters because the whole
        point of the `EXCL` column is that a weight one gigabyte over the line
        stops every other lane.
        """
        gate = Path(__file__).resolve().parent / "heavy_gate.sh"
        if not gate.exists():                     # pragma: no cover
            self.skipTest("heavy_gate.sh absent")
        out = subprocess.run(["bash", str(gate), "status"],
                             capture_output=True, text=True, timeout=60).stdout
        match = re.search(r"budget (\d+) GB", out)
        self.assertIsNotNone(match, f"heavy_gate status did not state a budget: {out!r}")
        self.assertEqual(vr._gate_budget_gb(), int(match.group(1)))

    def test_over_and_under_reservation_are_stated_in_words(self):
        """The record already held both numbers and said nothing about them.

        Measured 2026-08-28: `clean-verify::test::axiom_ratchet` reserved 44 GB
        -- clamped by heavy_gate to the whole 27 GB budget, so exclusively --
        and ran at a 9.11 GB peak for 6h14m with six lanes queued behind it.
        `gate_weight_gb` and `peak_rss_gb` were both in the artifact the whole
        time. Nothing put them side by side.
        """
        big_weight_small_job = vr._reservation_verdict(
            44, vr.RssProfile(peak_gb=9.11, raw_peak_gb=9.11, p50_gb=1.02, samples=6000))
        self.assertIsNotNone(big_weight_small_job)
        self.assertIn("OVER-RESERVED", big_weight_small_job)
        self.assertIn("14 GB", big_weight_small_job)      # ceil(9.11 * 1.5)

        # The panic direction is louder, not quieter.
        under = vr._reservation_verdict(
            8, vr.RssProfile(peak_gb=23.0, raw_peak_gb=23.0, p50_gb=20.0, samples=900))
        self.assertIsNotNone(under)
        self.assertIn("UNDER-RESERVED", under)

        # A right-sized reservation, a reservation too small to matter, and a
        # run that measured nothing all say NOTHING. A verdict on every row is
        # a verdict nobody reads, and an unmeasured peak is not a small one.
        for weight, profile in (
            (14, vr.RssProfile(9.11, 9.11, 8.0, 6000)),        # 65% -- fine
            (2, vr.RssProfile(0.1, 0.1, 0.1, 40)),             # tiny reservation
            (44, vr.RssProfile(0.0, 0.0, 0.0, 0)),             # never sampled
        ):
            self.assertIsNone(vr._reservation_verdict(weight, profile),
                              f"weight {weight} / {profile} should be silent")



class ReservationReportsUseFinalizedOutcomes(unittest.TestCase):
    """Synthetic commands and sampled profiles; isolated records, no native claim."""

    def _run(self, name, script, *, finish=DIGEST, kind="test", extra=None,
             peak=9.11, timeout=60):
        entry = {"id": "synthetic::reservation::" + name, "package": "synthetic",
                 "kind": kind, "argv": ["/bin/sh", "-c", script],
                 "_dirs": [vr.REPO_ROOT / "scripts"], **(extra or {})}
        profile = vr.RssProfile(peak, peak, peak / 2, 900)
        with mock.patch.object(vr, "_gate_weight_gb", return_value=44), \
             mock.patch.object(vr, "_rss_profile", return_value=profile), \
             mock.patch.object(vr, "input_digest", side_effect=[DIGEST, finish]), \
             mock.patch.object(vr, "_compiler_identity_problem", return_value="test identity unavailable"):
            rec = vr.run_one(entry, timeout=timeout)
        # The record actually contains the observation; absence of a sampler
        # would otherwise make every negative arm pass vacuously.
        self.assertEqual(rec["rss_samples"], 900)
        self.assertEqual(rec["run_peak_rss_gb"], round(peak, 2))
        self.assertEqual(vr.load_record(entry["id"])["reservation_verdict"],
                         rec["reservation_verdict"])
        return entry, rec

    def test_completed_stable_success_still_recommends_a_lower_weight(self):
        entry, rec = self._run("success", "echo 'test result: ok. 1 passed; 0 failed'")
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_GREEN)
        self.assertIn("OVER-RESERVED", rec["reservation_verdict"])

    def test_failed_and_unknown_runs_never_recommend_downsizing(self):
        ok = "echo 'test result: ok. 1 passed; 0 failed'"
        cases = (
            ("failed", "echo 'test result: FAILED. 0 passed; 1 failed'; exit 101", {}),
            ("timeout", "sleep 5", {"timeout": 1}),
            ("moved", ok, {"finish": OTHER}),
            ("identity", ok, {"finish": None}),
            ("skipped", "echo SRCELAB_GATE=skipped:no-binary", {"kind": "gate"}),
            ("empty", "echo 'test result: ok. 0 passed; 0 failed'", {}),
            ("must_pass", ok, {"extra": {"_must_pass": ["required::test"]}}),
            ("shard", ok, {"kind": vr.KIND_SHARD,
                           "extra": {"_parent": "synthetic::parent",
                                     "_shard": {"key": "one", "test_count": 2}}}),
        )
        for name, command, kwargs in cases:
            with self.subTest(name=name):
                entry, rec = self._run(name, command, **kwargs)
                self.assertNotEqual(vr.derive(entry, rec, kwargs.get("finish", DIGEST))["bucket"],
                                    vr.BUCKET_GREEN)
                self.assertIsNone(rec["reservation_verdict"],
                                  "a failed or UNKNOWN prefix cannot size its complete retry")

    def test_partial_observation_still_warns_when_reservation_was_too_small(self):
        _, rec = self._run("under", "exit 1", peak=50.1)
        self.assertEqual(rec["status"], vr.STATUS_RED)
        self.assertIn("UNDER-RESERVED", rec["reservation_verdict"])

    def test_weights_json_filters_legacy_bad_advice_without_rewriting_history(self):
        import io
        over = "OVER-RESERVED: legacy advice to lower this weight"
        under = "UNDER-RESERVED: legacy warning"
        cases = (
            ("success", {}, {}, over),
            ("failed", {"status": vr.STATUS_RED}, {}, None),
            ("changed", {"input_digest_at_finish": OTHER}, {}, None),
            ("empty", {"counts": {"passed": 0, "failed": 0, "result_lines": 1}}, {}, None),
            ("must_pass", {}, {"_must_pass": ["required::test"]}, None),
            ("under", {"status": vr.STATUS_RED, "reservation_verdict": under}, {}, under),
        )
        for name, updates, entry_updates, expected in cases:
            with self.subTest(name=name):
                rec = record(**{"kind": "test", "counts": {"passed": 1, "failed": 0, "result_lines": 1},
                                "reservation_verdict": over, **updates})
                before = json.dumps(rec, sort_keys=True)
                output = io.StringIO()
                with mock.patch.object(vr, "build_inventory", return_value=[{**ENTRY, **entry_updates}]), \
                     mock.patch.object(vr, "load_record", return_value=rec), \
                     mock.patch.object(vr, "_gate_weight_gb", return_value=44), \
                     mock.patch.object(vr, "cold_build_floor_gb", return_value=0), \
                     mock.patch.object(vr, "package_cold_build_floor_gb", return_value=(0, None)), \
                     mock.patch("sys.stdout", output):
                    self.assertEqual(vr.cmd_weights(types.SimpleNamespace(packages=[], only=None, json=True)), 0)
                self.assertEqual(json.loads(output.getvalue())["targets"][0]["verdict"], expected)
                self.assertEqual(json.dumps(rec, sort_keys=True), before)

    def test_report_uses_full_profile_precision_until_formatting(self):
        _, rec = self._run("precision", "echo 'test result: ok. 1 passed; 0 failed'", peak=9.3334)
        self.assertEqual(rec["run_peak_rss_gb"], 9.33)
        self.assertIn("15 GB", rec["reservation_verdict"])


class ASkippedGateIsNotAPass(unittest.TestCase):
    """A gate that exits 0 without measuring anything must not read GREEN.

    Measured 2026-08-23 at 3a2aaaa2e:

        [worker] DONE (1/11) gate::srcelab -> GREEN (527.7s) SRCELAB_GATE=skipped:no-binary

    `source_elab_gate.sh` (like `kv_ratchet_gate.sh`) skip-greens when its
    prerequisite is absent, and says so in a machine-readable verdict line.
    Exiting 0 is right for the pre-push hook, which must not refuse a pusher
    over an unbuilt release binary; it is wrong for this artifact, where the row
    then asserts the source-elab ratchet held while nothing ran.
    """

    def _run(self, script: str) -> dict:
        entry = {"id": "gate::probe", "package": "__workspace__", "kind": "gate",
                 "argv": ["/bin/sh", "-c", script], "_dirs": [vr.REPO_ROOT / "scripts"]}
        return vr.run_one(entry, timeout=60, timeout_basis="test")

    def test_a_skip_verdict_on_exit_zero_is_recorded_skipped(self):
        rec = self._run("echo SRCELAB_GATE=skipped:no-binary; exit 0")
        self.assertEqual(rec["status"], vr.STATUS_SKIPPED)
        self.assertEqual(rec["final_line"], "SRCELAB_GATE=skipped:no-binary")
        self.assertIn("not a pass", rec["notes"])

    def test_a_skipped_record_derives_to_unknown_not_green(self):
        rec = self._run("echo KV_RATCHET_GATE=skipped:no-corpus; exit 0")
        entry = {"id": "gate::probe", "package": "__workspace__", "kind": "gate",
                 "argv": rec and ["/bin/sh"]}
        got = vr.derive(entry, rec, rec["input_digest"])
        self.assertEqual(got["bucket"], vr.BUCKET_UNKNOWN)

    def test_a_measured_gate_still_reads_green(self):
        rec = self._run("echo SRCELAB_GATE=measured; exit 0")
        self.assertEqual(rec["status"], vr.STATUS_GREEN)

    def test_a_failing_gate_is_still_red_not_skipped(self):
        rec = self._run("echo SRCELAB_GATE=failed:regression; exit 1")
        self.assertEqual(rec["status"], vr.STATUS_RED)

    def test_the_word_skipped_in_test_output_does_not_hijack_a_pass(self):
        # Only the gates' own verdict grammar counts. A test that prints the
        # word must not be demoted.
        rec = self._run("echo 'note: 3 cases skipped:none relevant'; exit 0")
        self.assertEqual(rec["status"], vr.STATUS_GREEN)


class AnInterruptedRunKeepsItsWeight(unittest.TestCase):
    """A killed run must not downgrade its own retry to the unmeasured default.

    Measured 2026-08-23: the worker was stopped to clear a machine-wide gate
    wedge while eight targets sat in the queue. Each left a RUNNING record with
    a blank `peak_rss_gb`, so `_gate_weight_gb` -- which read only that key --
    would have re-admitted `kernel_core_red_env_fidelity` (measured peak
    56.3 GB) at the 12 GB default. Under-reserving by 44 GB is precisely the
    unaccounted concurrency of reports/kernel-panic-rca-2026-08-19.md.
    """

    def test_a_blank_running_record_falls_back_to_the_carried_peak(self):
        killed = {"status": vr.STATUS_RUNNING, "peak_rss_gb": None,
                  "prior_peak_rss_gb": 56.3}
        with mock.patch.object(vr, "load_record", return_value=killed):
            self.assertEqual(vr._gate_weight_gb("t"), 85)      # ceil(56.3 * 1.5)

    def test_a_fresh_measurement_wins_over_the_carried_one(self):
        both = {"peak_rss_gb": 8.8, "prior_peak_rss_gb": 56.3}
        with mock.patch.object(vr, "load_record", return_value=both):
            self.assertEqual(vr._gate_weight_gb("t"), 14)      # ceil(8.8 * 1.5)

    def test_a_junk_carried_value_still_falls_back_to_the_default(self):
        for bad in ({"prior_peak_rss_gb": 0}, {"prior_peak_rss_gb": -3},
                    {"prior_peak_rss_gb": "big"}, {"prior_peak_rss_gb": True}):
            with mock.patch.object(vr, "load_record", return_value=bad):
                self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)

    def test_a_killed_run_may_raise_a_weight_but_never_cut_it(self):
        # THE SHAPE THAT WAS LIVE (2026-08-30, both rows in data/suite_state/):
        # a target measured at 28.87 GB, killed on its next run after 12799 s
        # with 9.11 GB observed, and the weight duly "learned" 44 -> 14 GB.
        # `vacuity_firewall` was worse: 28.68 -> 1.13 GB, i.e. 44 -> 2 GB, on a
        # run whose cargo leg was a 3.39 s no-op build. Under-reserving a
        # 28 GB target by 26 GB is the direction that panicked this box twice,
        # and nothing in the artifact called it anything but learning.
        for cut_short in ({"timed_out": True},
                          {"status": vr.STATUS_ERROR},
                          {"status": vr.STATUS_RUNNING}):
            killed = {"peak_rss_gb": 9.11, "prior_peak_rss_gb": 28.87}
            killed.update(cut_short)
            with mock.patch.object(vr, "load_record", return_value=killed):
                self.assertEqual(
                    vr._gate_weight_gb("t"), 44,      # ceil(28.87 * 1.5)
                    f"a run cut short by {cut_short} must not cut the weight",
                )
        # ... and the same partial observation may still RAISE it: the memory
        # was really used, whether or not the job reached its own end.
        risen = {"peak_rss_gb": 40.0, "prior_peak_rss_gb": 28.87,
                 "timed_out": True}
        with mock.patch.object(vr, "load_record", return_value=risen):
            self.assertEqual(vr._gate_weight_gb("t"), 60)   # ceil(40.0 * 1.5)

    def test_changed_inputs_may_raise_a_weight_but_never_lower_it(self):
        base = {"status": vr.STATUS_GREEN, "timed_out": False,
                "counts": {"passed": 1, "failed": 0, "result_lines": 1},
                "peak_rss_gb": 1.0, "prior_peak_rss_gb": 10.0,
                "input_digest": DIGEST, "input_digest_at_finish": DIGEST,
                "inputs_moved_during_run": False}
        for moved in ({"inputs_moved_during_run": True},
                      {"input_digest_at_finish": OTHER},
                      {"inputs_moved_during_run": True, "input_digest_at_finish": None}):
            with self.subTest(moved=moved):
                rec = dict(base, **moved)
                with mock.patch.object(vr, "load_record", return_value=rec):
                    self.assertEqual(vr._gate_weight_gb("t"), 15)
                rec["peak_rss_gb"] = 20.0
                with mock.patch.object(vr, "load_record", return_value=rec):
                    self.assertEqual(vr._gate_weight_gb("t"), 30)
        with mock.patch.object(vr, "load_record", return_value=base):
            self.assertEqual(vr._gate_weight_gb("t"), 2)

    def test_incomplete_runs_cannot_undercut_the_unmeasured_default(self):
        unfinished = [
            {"timed_out": True}, {"status": vr.STATUS_ERROR},
            {"status": vr.STATUS_RUNNING}, {"inputs_moved_during_run": True},
            {"input_digest": DIGEST, "input_digest_at_finish": OTHER},
            {"counts": {"passed": 0, "failed": 0, "result_lines": 1}},
        ]
        for fields in unfinished:
            for carried in (None, 1.0):
                with self.subTest(fields=fields, carried=carried):
                    rec = {"status": vr.STATUS_GREEN, "peak_rss_gb": 1.0,
                           "prior_peak_rss_gb": carried,
                           "counts": {"passed": 1, "result_lines": 1}, **fields}
                    with mock.patch.object(vr, "load_record", return_value=rec):
                        self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)
                    rec["peak_rss_gb"] = 20.0
                    with mock.patch.object(vr, "load_record", return_value=rec):
                        self.assertEqual(vr._gate_weight_gb("t"), 30)
        complete = {"status": vr.STATUS_GREEN, "peak_rss_gb": 1.0,
                    "counts": {"passed": 1, "result_lines": 1}}
        with mock.patch.object(vr, "load_record", return_value=complete):
            self.assertEqual(vr._gate_weight_gb("t"), 2)

    def test_completed_shell_gate_keeps_its_measured_small_weight(self):
        rec = {"status": vr.STATUS_GREEN, "kind": "gate",
               "command": "targo fmt --all -- --check", "peak_rss_gb": 1.0,
               "counts": {"passed": 0, "failed": 0, "result_lines": 0}}
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._gate_weight_gb("gate::fmt"), 2)
        rec["command"] = "targo --unverified test --lib"
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._gate_weight_gb("gate::test"), vr.DEFAULT_TARGET_GB)

    def test_a_completed_run_still_replaces_the_carried_peak(self):
        # The learning loop is the point of the measurement and must survive
        # the fix above: a run that REACHED ITS OWN END replaces the carried
        # peak outright, downwards included. Without this arm the fix could be
        # written as a plain `max` and nothing would notice.
        done = {"status": vr.STATUS_GREEN, "timed_out": False,
                "peak_rss_gb": 8.8, "prior_peak_rss_gb": 56.3}
        with mock.patch.object(vr, "load_record", return_value=done):
            self.assertEqual(vr._gate_weight_gb("t"), 14)   # ceil(8.8 * 1.5)

    def test_failed_measurements_keep_the_larger_history_and_default(self):
        # Recorded spec_paying_01 shape: the failed run observed less than
        # its predecessor despite reporting many tests, not a zero-test run.
        rec = {"status": vr.STATUS_RED, "exit_code": 101,
               "peak_rss_gb": 4.39, "prior_peak_rss_gb": 6.46,
               "counts": {"passed": 1487, "failed": 12, "result_lines": 1}}
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._prior_peak_rss_gb("t"), 6.46)
            self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)
        rec["prior_peak_rss_gb"] = 40.0
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._gate_weight_gb("t"), 60)
        rec["peak_rss_gb"] = 50.0
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._gate_weight_gb("t"), 75)
        # A successful retry can still learn a lower weight.
        rec.update(status=vr.STATUS_GREEN, exit_code=0, peak_rss_gb=4.39,
                   counts={"passed": 1499, "failed": 0, "result_lines": 1})
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._gate_weight_gb("t"), 7)

    def test_failed_phase_peaks_cannot_lower_either_reservation(self):
        rec = {"status": vr.STATUS_RED, "exit_code": 101,
               "peak_rss_gb": 4.39, "prior_peak_rss_gb": 6.46,
               "counts": {"passed": 1487, "failed": 12, "result_lines": 1},
               "build_peak_rss_gb": 2.0, "build_rss_samples": 10,
               "run_peak_rss_gb": 0.5, "rss_samples": 10}
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._split_weights_gb("t"),
                             (vr.DEFAULT_TARGET_GB, vr.DEFAULT_TARGET_GB))
            self.assertEqual(vr._split_weights_gb("t", build_floor_gb=18),
                             (18, vr.DEFAULT_TARGET_GB))
        self.assertEqual(vr.derive(ENTRY, record(status=vr.STATUS_RED), DIGEST)["bucket"],
                         vr.BUCKET_RED)

    def test_the_running_template_carries_the_peak_forward(self):
        # Ordering matters as much as the field: the carried value must be read
        # from the PREVIOUS record, before the RUNNING template overwrites it.
        src = (vr.REPO_ROOT / "scripts" / "verify_runner.py").read_text()
        read_at = src.index("prior_peak = _prior_peak_rss_gb(")
        field_at = src.index('"prior_peak_rss_gb": prior_peak,')
        template_at = src.index('"status": STATUS_RUNNING')
        self.assertLess(read_at, template_at)
        self.assertLess(template_at, field_at)


class WeightIsReadBeforeTheRecordIsOverwritten(unittest.TestCase):
    """The learning loop must not read its own blank.

    Live for one commit: the RUNNING template (peak_rss_gb=None) was written
    BEFORE the weight was computed, so `_gate_weight_gb` always read None and
    every target admitted at the default forever -- the measurement was taken
    and then ignored. Ordering is the whole fix, so it is pinned here.
    """

    def test_weight_is_computed_before_the_running_template(self):
        src = (vr.REPO_ROOT / "scripts" / "verify_runner.py").read_text()
        weight_at = src.index("gate_weight = _gate_weight_gb(")
        template_at = src.index('"status": STATUS_RUNNING')
        self.assertLess(
            weight_at, template_at,
            "the gate weight must be read before the RUNNING record overwrites "
            "peak_rss_gb, or the runner never learns",
        )

class AForegroundWorkerIsVisibleToTheGuards(unittest.TestCase):
    """A worker must announce itself however it was started.

    `run` daemonizes and `daemonize.py --pidfile` writes WORKER_PIDFILE for it;
    `run --foreground` wrote nothing, so a foreground worker was invisible to
    every reader of that file. That silently disarmed two guards: `cmd_run`'s
    "a worker is already running" check, and the refuse-to-re-pin check in
    `scripts/verify_runner_pinned.sh`, whose entire job is to stop a checkout
    moving a measurement's own sources underneath it.

    Measured 2026-08-25: a `--foreground` pinned run was in flight at dba565b24
    when a `status` call in another shell re-pinned the same worktree to
    d67054a45 and the guard said nothing, because worker.pid still held a
    long-dead pid from an earlier lane. The run's result was discarded.
    """

    def setUp(self):
        if vr.WORKER_PIDFILE.exists():
            vr.WORKER_PIDFILE.unlink()

    def tearDown(self):
        if vr.WORKER_PIDFILE.exists():
            vr.WORKER_PIDFILE.unlink()

    def test_the_pidfile_is_live_for_the_whole_worker_body(self):
        seen = {}

        def spy(_args):
            seen["content"] = vr.WORKER_PIDFILE.read_text().strip()
            return 0

        with mock.patch.object(vr, "_worker_loop", spy), \
             mock.patch.object(vr, "install_signal_handlers", lambda: None):
            rc = vr.cmd_worker(mock.Mock(queue="unused"))

        self.assertEqual(rc, 0)
        self.assertEqual(
            seen.get("content"), str(os.getpid()),
            "a foreground worker must write its own pid to WORKER_PIDFILE, or "
            "verify_runner_pinned.sh will re-pin the worktree underneath it",
        )
        self.assertFalse(
            vr.WORKER_PIDFILE.exists(),
            "the worker must drop its claim on the way out, or the next run "
            "sees a stale pid",
        )

    def test_the_claim_survives_an_exception_but_is_still_dropped(self):
        with mock.patch.object(vr, "_worker_loop", mock.Mock(side_effect=RuntimeError("boom"))), \
             mock.patch.object(vr, "install_signal_handlers", lambda: None):
            with self.assertRaises(RuntimeError):
                vr.cmd_worker(mock.Mock(queue="unused"))
        self.assertFalse(vr.WORKER_PIDFILE.exists())

    def test_a_worker_never_unlinks_a_claim_that_is_not_its_own(self):
        """`--restart` writes the new pid; the dying incumbent must not erase it.

        Otherwise the replacement worker is invisible and both guards re-open --
        the exact hole this class exists to close.
        """
        vr.WORKER_PIDFILE.parent.mkdir(parents=True, exist_ok=True)
        vr.WORKER_PIDFILE.write_text(f"{os.getpid() + 1}\n", encoding="utf-8")
        vr._release_worker_pidfile()
        self.assertTrue(
            vr.WORKER_PIDFILE.exists(),
            "releasing must compare pids: a departing worker that unlinks the "
            "live worker's claim re-opens the guard it was meant to close",
        )


class AToolchainRefusalIsNotARed(unittest.TestCase):
    """A gate the toolchain refused to RUN must not read RED.

    `ASkippedGateIsNotAPass` closes the exit-0 half of this: exiting 0 without
    measuring is UNKNOWN, not GREEN. This is the non-zero half, and it fails the
    other way -- toward a red the code did not earn.

    Measured 2026-08-25 at d67054a45, `gate::clippy`, recorded RED after 23.6s:

        error: branded Tippy driver identity changed: directory-chain identity
        changed while embedded Tippy compiler was running: selected Trust
        toolchain directory ancestor `$HOME` changed identity or contents

    The Trust frontends authenticate their own stage2 binary and every ancestor
    directory of it. One of those ancestors is the HOME DIRECTORY, and a dozen
    lanes write into it, so the check trips constantly. Nothing was tampered
    with: `targo-tippy` had not been written since Aug 8. Clippy never linted a
    line -- so the run says nothing about the workspace, and RED says it is
    dirty.
    """

    _REFUSAL = (
        "error: branded Tippy driver identity changed: directory-chain identity "
        "changed while embedded Tippy compiler was running: selected Trust toolchain "
        "directory ancestor `$HOME` changed identity or contents"
    )

    def _run(self, script: str) -> dict:
        entry = {"id": "gate::probe", "package": "__workspace__", "kind": "gate",
                 "argv": ["/bin/sh", "-c", script], "_dirs": [vr.REPO_ROOT / "scripts"]}
        return vr.run_one(entry, timeout=60, timeout_basis="test")

    def test_a_refusal_is_recorded_error_not_red(self):
        rec = self._run(f"echo '{self._REFUSAL}'; exit 1")
        self.assertEqual(rec["status"], vr.STATUS_ERROR)
        self.assertIn("REFUSED", rec["notes"])
        self.assertIn("nothing measured", rec["final_line"])

    def test_a_refusal_derives_to_unknown(self):
        rec = self._run(f"echo '{self._REFUSAL}'; exit 1")
        entry = {"id": "gate::probe", "package": "__workspace__", "kind": "gate", "argv": ["/bin/sh"]}
        got = vr.derive(entry, rec, rec["input_digest"])
        self.assertEqual(got["bucket"], vr.BUCKET_UNKNOWN)

    def test_unknown_still_fails_the_board(self):
        """The point is to relabel an unmeasurable row, never to excuse it."""
        counts = {vr.BUCKET_GREEN: 0, vr.BUCKET_RED: 0,
                  vr.BUCKET_UNKNOWN: 1, vr.BUCKET_RUNNING: 0}
        self.assertEqual(vr.gate_exit_code(counts), 2)

    def test_a_real_lint_failure_is_still_red(self):
        rec = self._run(
            "echo 'error: this expression creates a reference which is immediately dereferenced'; "
            "echo 'error: could not compile `clean-kernel` (lib) due to 1 previous error'; exit 101"
        )
        self.assertEqual(
            rec["status"], vr.STATUS_RED,
            "a genuine -D warnings failure must never be laundered into UNKNOWN",
        )

    def test_the_word_identity_in_lint_output_does_not_launder_a_red(self):
        rec = self._run("echo 'error: identity of this value changed'; exit 101")
        self.assertEqual(rec["status"], vr.STATUS_RED)



class TheCheckoutAccident(unittest.TestCase):
    """A checkout reverts data/suite_state/ under a live writer. Nothing is lost.

    This is the accident, reproduced against a real git repository rather than
    described: `data/suite_state/` is git-TRACKED and is also RUNNER OUTPUT that
    changes without a commit, so `git checkout` / `git restore` / a branch
    switch puts the committed content back -- exit 0, no warning, no error. A
    routine crash-recovery checkout destroyed a complete 14.33-hour sweep that
    way, and the results survived only because the worker's out-of-tree log
    happened to still hold them. Recovering from a log is heroics, not a design.

    Two forms, because a checkout destroys a record two different ways:

      A. REVERT-TO-STALE -- the record was tracked and the sweep overwrote it in
         place; the checkout puts the OLDER content back. Worse than deletion:
         the file exists, parses, and claims a stale input digest, so `derive`
         reports UNKNOWN and the sweep's result is gone as information.
      B. DELETION -- the record was created after the last commit and tree
         hygiene removes it.

    Both must recover, byte-identical, from one command.
    """

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="checkout_accident_")
        self.repo = Path(self.tmp) / "repo"
        self.state = self.repo / "data" / "suite_state"
        self.state.mkdir(parents=True)
        self._git("init", "-q", "-b", "main")
        self._git("config", "user.email", "t@example.com")
        self._git("config", "user.name", "t")
        self._journal_env = mock.patch.dict(
            os.environ, {"VERIFY_RUNNER_JOURNAL_DIR": str(Path(self.tmp) / "journal")})
        self._journal_env.start()
        self._state_patch = mock.patch.object(vr, "STATE_DIR", self.state)
        self._state_patch.start()

    def tearDown(self) -> None:
        self._state_patch.stop()
        self._journal_env.stop()

    def _git(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(["git", "-C", str(self.repo), *args],
                              check=True, capture_output=True, text=True)

    @staticmethod
    def _record(target: str, status: str, when: str, digest: str) -> dict:
        return {"schema": vr.SCHEMA, "target": target, "status": status,
                "source": "measured", "finished_at": when, "input_digest": digest,
                "runner_host": "simhost", "final_line": f"test result: {status}"}

    def _sweep(self) -> dict[str, dict]:
        """A committed older state, then a sweep that overwrites it in place."""
        targets = [("clean-verify::test::eval_ir", "GREEN"),
                   ("clean-verify::test::the_red_env", "RED"),
                   ("gate::srcelab", "GREEN"),
                   ("clean-verify::lib#shard#misc", "GREEN")]
        for target, _ in targets:
            vr._project_record(self._record(target, "GREEN", "2026-08-01T00:00:00Z", "sha256:STALE"))
        self._git("add", "-A")
        self._git("commit", "-qm", "state(suite): an older sweep")
        sweep = {t: self._record(t, s, f"2026-08-25T0{i}:00:00Z", "sha256:FRESH")
                 for i, (t, s) in enumerate(targets)}
        for record in sweep.values():
            vr.write_record(record)          # the shipped write-through path
        return sweep

    def test_mismatched_journal_target_cannot_overwrite_another_record(self):
        target = "pkg::test::a"
        other = "pkg::test::b"
        good = self._record(target, "GREEN", "2026-11-13T01:00:00Z", DIGEST)
        retained = self._record(other, "GREEN", "2026-11-13T01:00:00Z", DIGEST)
        vr.journal_append(good)
        vr._project_record(retained)
        bad = self._record(other, "RED", "2026-11-13T02:00:00Z", OTHER)
        envelope = {"schema": vr.JOURNAL_SCHEMA, "target": target,
                    "record": bad, "origin": "measured"}
        with vr.journal_path().open("a") as stream:
            stream.write(json.dumps(envelope) + "\n")
        report = vr.reconcile_projection(apply=True)
        self.assertEqual(vr.load_record(other), retained)
        self.assertEqual(vr.load_record(target), good)
        self.assertTrue(report["problems"])

    def test_invalid_journal_record_does_not_replace_prior_valid_entry(self):
        target = "pkg::test::a"
        good = self._record(target, "GREEN", "2026-11-13T01:00:00Z", DIGEST)
        vr.journal_append(good)
        vr.journal_append(dict(good, commit=7, finished_at=9))
        latest, problems = vr.journal_read()
        self.assertTrue(problems)
        self.assertEqual(latest[target]["record"], good)
        report = vr.reconcile_projection(apply=True)
        self.assertTrue(report["problems"])
        self.assertEqual(vr.load_record(target), good)

    def test_journal_record_must_repeat_its_envelope_target(self):
        target = "pkg::test::a"
        for nested in ({}, {"target": None}, {"target": 7}):
            with self.subTest(nested=nested):
                envelope = {"schema": vr.JOURNAL_SCHEMA, "target": target,
                            "record": nested, "origin": "measured"}
                path = vr.journal_path()
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps(envelope) + "\n")
                latest, problems = vr.journal_read()
                self.assertEqual(latest, {})
                self.assertTrue(problems)

    def test_form_a_revert_to_stale_content_is_fully_recovered(self):
        sweep = self._sweep()
        self._git("checkout", "--", "data/suite_state")

        rewound = [t for t in sweep if vr.load_record(t) != sweep[t]]
        self.assertEqual(len(rewound), len(sweep), "the accident did not reproduce")
        self.assertTrue(all(vr.load_record(t)["input_digest"] == "sha256:STALE" for t in sweep),
                        "every record should have been rewound to its committed content")

        report = vr.heal_projection(quiet=True)
        restored = sorted(a["target"] for a in report["actions"] if a["verdict"] == "restore")
        self.assertEqual(restored, sorted(sweep))
        for target, record in sweep.items():
            self.assertEqual(vr.load_record(target), record,
                             f"{target} was not restored byte-identically")

    def test_form_b_deletion_after_the_last_commit_is_fully_recovered(self):
        self._sweep()
        self._git("add", "-A")
        self._git("commit", "-qm", "state(suite): the sweep")
        fresh = self._record("clean-verify::test::brand_new", "GREEN",
                             "2026-08-25T09:00:00Z", "sha256:FRESH")
        vr.write_record(fresh)
        subprocess.run(["git", "-C", str(self.repo), "clean", "-qfd", "--", "data/suite_state"],
                       check=True, capture_output=True)
        self.assertIsNone(vr.load_record("clean-verify::test::brand_new"))

        vr.heal_projection(quiet=True)
        self.assertEqual(vr.load_record("clean-verify::test::brand_new"), fresh)

    def test_recovery_does_not_depend_on_a_pidfile(self):
        """The falsification arm option (b) would have needed, and could not pass.

        A checkout guard keyed on the worker pidfile only covers the in-flight
        case, and this runner has already shipped a pidfile that one of its two
        launch paths never wrote (`run --foreground`, fixed in edf6ec0f5) -- a
        guard on it would have been silently disarmed. So the protection must
        not read one, and that is asserted rather than assumed: no pidfile is
        written anywhere here, and the recovery still holds.
        """
        sweep = self._sweep()
        self._git("checkout", "--", "data/suite_state")
        self.assertEqual(list(Path(self.tmp).rglob("worker.pid")), [])
        vr.heal_projection(quiet=True)
        for target, record in sweep.items():
            self.assertEqual(vr.load_record(target), record)
        self.assertEqual(list(Path(self.tmp).rglob("worker.pid")), [])

    def test_a_newer_record_from_another_machine_is_never_clobbered(self):
        """The journal is local truth, not global truth.

        Records reach this directory from other machines through git. A journal
        that overwrote whatever it did not recognise would turn a data-loss bug
        into a data-corruption bug, so a projection record STRICTLY NEWER than
        anything this journal holds is reported `foreign` and left alone.
        """
        self._sweep()
        foreign = self._record("clean-verify::test::eval_ir", "RED",
                               "2026-09-01T00:00:00Z", "sha256:OTHER")
        foreign["runner_host"] = "othermachine"
        vr._project_record(foreign)
        report = vr.reconcile_projection(apply=True)
        verdicts = {a["target"]: a["verdict"] for a in report["actions"]}
        self.assertEqual(verdicts["clean-verify::test::eval_ir"], "foreign")
        self.assertEqual(vr.load_record("clean-verify::test::eval_ir"), foreign)

    @staticmethod
    def _derived_rollup(host: str, declared: int) -> dict:
        # The actual cross-host discrepancy: neither parent has a run timestamp.
        # The carried timeout is historical evidence, not the rollup's verdict.
        return {
            "schema": vr.SCHEMA, "target": "clean-verify::lib",
            "package": "clean-verify", "kind": "lib-rollup",
            "source": "derived", "status": "SUPERSEDED",
            "command": "targo --unverified test --locked -p clean-verify --lib",
            "declared_tests": declared, "shard_count": 7,
            "shard_plan": f"/Users/{host}/clean/data/suite_plans/clean-verify__lib.json",
            "superseded_run": {
                "source": "measured", "kind": "lib", "status": "ERROR",
                "started_at": "2026-08-13T03:49:38Z",
                "finished_at": "2026-08-13T15:49:39Z",
                "duration_s": 43201.6, "exit_code": -1,
                "commit": "2241f47da49fab4d5ae9027d04dcb97af8ce3347",
                "counts": {"passed": 0, "failed": 0, "ignored": 0, "result_lines": 0},
                "runner_host": "m8Macbo128GB8TB.localdomain",
            },
        }

    def test_unordered_derived_rollups_do_not_ping_pong_between_hosts(self):
        old = self._derived_rollup("ayates", 7149)
        imported = self._derived_rollup("wintergreen", 7528)
        for local, projected in ((old, imported), (imported, old)):
            with self.subTest(local=local["declared_tests"]):
                vr.write_record(local)
                vr._project_record(projected)
                journal_before = vr.journal_path().read_bytes()
                projection_before = vr.record_path("clean-verify::lib").read_bytes()
                for apply in (False, True):
                    report = vr.reconcile_projection(apply=apply)
                    self.assertEqual(report["counts"]["held"], 1)
                    self.assertEqual(report["counts"]["restore"], 0)
                    self.assertEqual(report["counts"]["foreign"], 0)
                    self.assertIn("unordered plan metadata", report["actions"][0]["reason"])
                    self.assertEqual(vr.load_record("clean-verify::lib"), projected)
                    self.assertEqual(vr.record_path("clean-verify::lib").read_bytes(),
                                     projection_before)
                    self.assertEqual(vr.journal_path().read_bytes(), journal_before)

    def test_derived_rollup_missing_from_projection_still_restores(self):
        record = self._derived_rollup("ayates", 7149)
        vr.write_record(record)
        vr.record_path(record["target"]).unlink()
        report = vr.reconcile_projection()
        self.assertEqual(report["counts"]["restore"], 1)
        self.assertIsNone(vr.load_record(record["target"]))
        vr.reconcile_projection(apply=True)
        self.assertEqual(vr.load_record(record["target"]), record)

    def test_derived_rollup_changed_historical_evidence_still_restores(self):
        original = self._derived_rollup("ayates", 7149)
        vr.write_record(original)
        for corruption in ("status", "counts", "removed"):
            with self.subTest(corruption=corruption):
                changed = self._derived_rollup("wintergreen", 7528)
                if corruption == "removed":
                    del changed["superseded_run"]
                elif corruption == "counts":
                    changed["superseded_run"]["counts"]["passed"] = 7149
                else:
                    changed["superseded_run"]["status"] = "GREEN"
                vr._project_record(changed)
                report = vr.reconcile_projection()
                self.assertEqual(report["counts"]["restore"], 1)
                vr.reconcile_projection(apply=True)
                self.assertEqual(vr.load_record(original["target"]), original)

    def test_rollup_exception_does_not_cover_measured_or_stamped_rows(self):
        for field, value in (("source", "measured"), ("kind", "lib"),
                             ("status", "GREEN"), ("schema", "unexpected"),
                             ("finished_at", "2026-08-25T00:00:00Z"),
                             ("started_at", "2026-08-25T00:00:00Z")):
            with self.subTest(field=field):
                local = self._derived_rollup("ayates", 7149)
                projected = self._derived_rollup("wintergreen", 7528)
                local[field] = projected[field] = value
                vr.write_record(local)
                vr._project_record(projected)
                report = vr.reconcile_projection(apply=True)
                self.assertEqual(report["counts"]["restore"], 1)
                self.assertEqual(vr.load_record(local["target"]), local)

    def test_derived_rollup_non_plan_metadata_changes_still_restore(self):
        local = self._derived_rollup("ayates", 7149)
        vr.write_record(local)
        for key, value in (("command", "true"), ("status", "GREEN"),
                           ("source", "measured"), ("input_digest", "sha256:FORGED")):
            with self.subTest(key=key):
                changed = self._derived_rollup("wintergreen", 7528)
                changed[key] = value
                vr._project_record(changed)
                report = vr.reconcile_projection(apply=True)
                self.assertEqual(report["counts"]["restore"], 1)
                self.assertEqual(vr.load_record(local["target"]), local)

    def test_torn_journal_remains_reported_with_held_derived_rollup(self):
        vr.write_record(self._derived_rollup("ayates", 7149))
        vr._project_record(self._derived_rollup("wintergreen", 7528))
        journal = vr.journal_path()
        journal.write_text(journal.read_text() + '{"schema":"clean.suite_journal/v1","tar\n')
        report = vr.reconcile_projection()
        self.assertEqual(report["counts"]["held"], 1)
        self.assertTrue(report["problems"])
        self.assertIn("not valid JSON", report["problems"][0])

    def test_without_the_journal_call_the_same_accident_is_unrecoverable(self):
        """The protection IS `journal_append` inside `write_record`.

        Nothing about the recovery above is a property of the runner in general;
        it is a property of that one call. Remove it -- which is what
        `_project_record` alone is -- and the identical accident is fatal. This
        is the arm that makes the four above mean something.
        """
        orphan = self._record("gate::unjournalled", "GREEN",
                              "2026-08-25T10:00:00Z", "sha256:FRESH")
        vr._project_record(orphan)                       # the pre-journal write path
        subprocess.run(["git", "-C", str(self.repo), "clean", "-qfd", "--", "data/suite_state"],
                       check=True, capture_output=True)
        report = vr.reconcile_projection(apply=True)
        self.assertIsNone(vr.load_record("gate::unjournalled"))
        self.assertEqual(report["counts"]["restore"], 0)

    def test_an_adopted_entry_never_overwrites_a_record_that_differs(self):
        """Adoption claims nothing, so it must not be able to displace anything.

        The concrete case this was written for: on 2026-08-25 the lane that lost
        the 14.33-hour sweep recovered it from `worker.log` and pushed the
        reconstructed records. A journal that had already adopted the reverted,
        STALE versions of those same targets must not re-project them over the
        recovery -- and it must not depend on the reconstructed timestamps
        happening to compare the right way for that to hold.
        """
        stale = self._record("gate::srcelab", "GREEN", "2026-09-09T00:00:00Z", "sha256:STALE")
        vr._project_record(stale)
        self.assertEqual(vr.journal_adopt()["adopted"], ["gate::srcelab"])

        recovered = self._record("gate::srcelab", "GREEN", "2026-08-01T00:00:00Z", "sha256:REAL")
        vr._project_record(recovered)                    # arrived by git, OLDER stamp
        report = vr.reconcile_projection(apply=True)
        verdicts = {a["target"]: a["verdict"] for a in report["actions"]}
        self.assertEqual(verdicts["gate::srcelab"], "held")
        self.assertEqual(vr.load_record("gate::srcelab"), recovered)

    def test_an_adopted_entry_still_restores_a_record_the_tree_lost(self):
        """The other half: `held` must not turn adoption into a no-op."""
        record = self._record("gate::srcelab", "GREEN", "2026-08-01T00:00:00Z", "sha256:REAL")
        vr._project_record(record)
        vr.journal_adopt()
        vr.record_path("gate::srcelab").unlink()
        vr.heal_projection(quiet=True)
        self.assertEqual(vr.load_record("gate::srcelab"), record)

    def test_a_torn_journal_line_is_reported_not_skipped(self):
        self._sweep()
        journal = vr.journal_path()
        journal.write_text(journal.read_text() + '{"schema":"clean.suite_journal/v1","tar\n')
        report = vr.reconcile_projection()
        self.assertTrue(report["problems"], "a truncated append must be reported")
        self.assertIn("not valid JSON", report["problems"][0])

    def test_retired_shard_records_are_never_journalled_or_projected(self):
        """The 125 retired fine-cut records stay evidence and stay inert."""
        retired = self.state / "shards" / "clean-verify__lib" / "superseded-fine-cut-9ec362dbb"
        retired.mkdir(parents=True)
        (retired / "clean-verify__lib__shard__gone.json").write_text(
            json.dumps({"schema": vr.SCHEMA, "target": "clean-verify::lib::shard::gone",
                        "status": "GREEN"}) + "\n")
        seen = {doc["target"] for _path, doc in vr.projection_records()}
        self.assertNotIn("clean-verify::lib::shard::gone", seen)
        adopted = vr.journal_adopt()["adopted"]
        self.assertNotIn("clean-verify::lib::shard::gone", adopted)


class TheJournalIsWiredIntoTheWritePath(unittest.TestCase):
    """Source-level pins, so an edit that disarms the protection cannot be quiet."""

    def test_write_record_journals_before_it_projects(self):
        src = (vr.REPO_ROOT / "scripts" / "verify_runner.py").read_text()
        body = src.split("\ndef write_record(record: dict[str, Any]) -> None:\n", 1)[1]
        body = body.split("\n\ndef ", 1)[0]
        self.assertLess(body.index("journal_append(record)"), body.index("_project_record(record)"),
                        "journal-last leaves a window where the tracked file exists and the "
                        "durable one does not, and that window is when a checkout is fatal")

    def test_status_heals_the_projection_before_deriving_from_it(self):
        src = (vr.REPO_ROOT / "scripts" / "verify_runner.py").read_text()
        body = src.split("\ndef cmd_status(args: argparse.Namespace) -> int:\n", 1)[1]
        body = body.split("\n\ndef ", 1)[0]
        self.assertLess(body.index("heal_projection()"), body.index("build_inventory("),
                        "a record the working tree lost must be re-projected before the table "
                        "is derived, or status reports UNKNOWN for a measured target")

    def test_the_journal_lives_outside_the_repository(self):
        saved = os.environ.pop("VERIFY_RUNNER_JOURNAL_DIR", None)
        try:
            path = vr.journal_path()
        finally:
            if saved is not None:
                os.environ["VERIFY_RUNNER_JOURNAL_DIR"] = saved
        self.assertNotIn(str(vr.REPO_ROOT), str(path),
                         "a journal inside the working tree is one `git clean -xdf` from "
                         "being exactly as fragile as the projection it protects")

    def test_this_test_module_never_writes_the_machine_journal(self):
        """Found by measurement, not by review, so it is pinned.

        Before the sandbox covered VERIFY_RUNNER_JOURNAL_DIR, every
        `write_record` in this file appended to the real
        ~/.local/state/clean/suite-journal/ -- synthetic entries in the durable
        artifact, indistinguishable to every later reader from measured ones,
        and re-projectable into the tracked directory by any `status`.
        """
        self.assertTrue(str(vr.journal_path()).startswith(_SANDBOX),
                        f"{vr.journal_path()} is outside the test sandbox {_SANDBOX}")

    def test_the_journal_is_keyed_on_the_projection_not_the_checkout(self):
        """One journal per projection: the pinned runner shares data/suite_state/."""
        first = vr.journal_path()
        with mock.patch.object(vr, "STATE_DIR", Path(self.__class__.__name__) / "other"):
            second = vr.journal_path()
        self.assertNotEqual(first, second)
        self.assertEqual(first, vr.journal_path())


class TestPerPackageFloors(unittest.TestCase):
    """A per-(package, kind) floor must move ONE population and say which.

    Added 2026-09-16 with the clean-elab floor. The arms are written so the
    measurement can move without the test rotting into a tautology: the floor is
    bound to its DERIVATION, and the blast radius is asserted as "clean-verify
    does not move", not as a literal budget.
    """

    def test_the_elab_test_floor_covers_the_fattest_target_at_the_worst_rate(self):
        derived = vr._ELAB_TEST_FLOOR_DERIVED_S
        floor = vr.TIMEOUT_FLOOR_BY_PACKAGE_KIND[("clean-elab", "test")]
        # Same no-slack shape the packed-shard floors use: cover the derivation
        # and do not hand out an extra 15% nobody measured.
        self.assertGreaterEqual(floor, derived)
        self.assertLess(floor, derived * 1.15)

    def test_the_derivation_is_fattest_times_worst_plus_build(self):
        self.assertAlmostEqual(
            vr._ELAB_TEST_FLOOR_DERIVED_S,
            vr._ELAB_MAX_TESTS_IN_TARGET * vr._ELAB_WORST_PER_TEST_S
            + vr._WORST_INTEGRATION_BUILD_LEG_S,
            places=6,
        )

    def test_a_clean_elab_test_target_takes_the_package_floor(self):
        entry = {"id": "clean-elab::test::x", "package": "clean-elab", "kind": "test"}
        budget, basis = vr.timeout_for(entry, None)
        self.assertEqual(budget, 2_100)
        self.assertIn("clean-elab test floor", basis)

    def test_a_clean_verify_test_target_keeps_the_kind_floor(self):
        entry = {"id": "clean-verify::test::x", "package": "clean-verify", "kind": "test"}
        budget, basis = vr.timeout_for(entry, None)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])
        self.assertIn("test floor", basis)
        # The whole point of a per-package row: the other population is untouched.
        self.assertNotIn("clean-elab", basis)

    def test_an_entry_with_no_package_falls_back_to_the_kind_floor(self):
        # `cmd_shards` builds a synthetic entry carrying only a kind. A lookup
        # that assumed a package would KeyError there.
        budget, basis = vr.timeout_for({"kind": "test"}, None)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])
        self.assertIn("test floor", basis)

    def test_a_killed_clean_elab_target_escalates_from_the_package_floor(self):
        # A floor that is too tight must self-heal rather than wedge: doubling
        # from 2100 reaches the old 7200 in two kills.
        entry = {"id": "clean-elab::test::x", "package": "clean-elab", "kind": "test"}
        killed = {"source": "measured", "status": vr.STATUS_ERROR,
                  "timed_out": True, "timeout_s": 2_100}
        budget, basis = vr.timeout_for(entry, killed)
        self.assertEqual(budget, 4_200)
        self.assertIn("KILLED", basis)


class TestBuildRunSplitApplicability(unittest.TestCase):
    """The split keys on the ARGV SHAPE, never on the row's `kind`.

    Written because the docstring of `_build_phase_argv` said "a gate row runs a
    script" as if `kind == "gate"` decided it. It does not, and the row where
    that matters is `gate::masquerade`: a `targo --unverified test` row that reserved 18 GB --
    above this box's budget, so it held the machine EXCLUSIVELY -- while its own
    last run here peaked at 10.91 GB against a 3.5 GB median. If the split is
    ever keyed on `kind`, that row silently stops splitting and nothing else
    here would notice.
    """

    def test_cargo_test_splits_whatever_the_kind_says(self):
        argv = ["targo", "--unverified", "test", "--locked", "-p", "clean-kernel", "--lib",
                "--", "masquerade"]
        self.assertIsNotNone(vr._build_phase_argv(argv))

    def test_a_script_row_does_not_split(self):
        self.assertIsNone(vr._build_phase_argv(["scripts/leancross.sh", "run"]))

    def test_a_cargo_subcommand_that_is_not_test_does_not_split(self):
        # `cargo clippy` compiles too, but it has no run phase to separate --
        # the whole invocation IS the compile, so splitting would invent a
        # boundary rather than find one.
        self.assertIsNone(vr._build_phase_argv(["targo", "tippy", "--workspace"]))

    def test_no_run_lands_before_the_separator(self):
        # Everything after `--` is the test binary's own argv. cargo would hand
        # `--no-run` straight to libtest, which does not know it.
        out = vr._build_phase_argv(["targo", "--unverified", "test", "-p", "x", "--", "filter"])
        self.assertEqual(out.index("--no-run"), out.index("--") - 1)
        self.assertEqual(out[-1], "filter")

    def test_the_documented_example_is_still_a_splitting_row(self):
        # Binds the docstring's worked example to the live registry.
        rows = {e["id"]: e for e in vr.WORKSPACE_GATES}
        self.assertIn("gate::masquerade", rows)
        self.assertIsNotNone(
            vr._build_phase_argv(rows["gate::masquerade"]["argv"]),
            "gate::masquerade no longer splits; the _build_phase_argv docstring "
            "cites it as the gate row that does -- update both together",
        )
        script_rows = [i for i, e in rows.items()
                       if e.get("kind", "").startswith("gate")
                       and vr._build_phase_argv(e["argv"]) is None]
        self.assertTrue(script_rows, "no non-splitting gate row left to contrast")



class TestPhasePeakAttribution(unittest.TestCase):
    """What may size a phase reservation, and what may not.

    The split had no unit coverage of its own weight derivation when it landed;
    these arms are that coverage, and they pin the two ways a phase figure can
    be present but meaningless.
    """

    CLEAN = {"build_peak_rss_gb": 2.0, "build_rss_samples": 40,
             "run_peak_rss_gb": 0.5, "rss_samples": 900,
             "inputs_moved_during_run": False}

    def _peak(self, rec, field="run_peak_rss_gb"):
        with mock.patch.object(vr, "load_record", return_value=rec):
            return vr._phase_peak_gb("t", field)

    def test_a_clean_record_sizes_the_phase(self):
        self.assertEqual(self._peak(dict(self.CLEAN)), 0.5)

    def test_a_thin_sample_is_not_a_measurement(self):
        rec = dict(self.CLEAN, run_peak_rss_gb=0.0, rss_samples=1)
        self.assertIsNone(self._peak(rec))

    def test_a_run_whose_inputs_moved_has_no_phase_attribution(self):
        # A run leg that recompiled puts build memory into the run phase's
        # figure, and nothing can separate them after the fact.
        #
        # These numbers are shaped like `lean4_corpus_tests`, which this guard
        # originally cited as a measured instance. It is NOT one: that shard's
        # 14.83 GB was later reproduced from the PREBUILT binary with nothing
        # compiling, so its peak is real test memory. The arm keeps the shape
        # because the shape is what the guard keys on; the attribution claim is
        # withdrawn in `_phase_peak_gb`.
        rec = dict(self.CLEAN, run_peak_rss_gb=14.83, rss_samples=1820,
                   inputs_moved_during_run=True)
        self.assertIsNone(self._peak(rec))

    def test_the_moved_guard_covers_the_build_phase_too(self):
        rec = dict(self.CLEAN, inputs_moved_during_run=True)
        self.assertIsNone(self._peak(rec, "build_peak_rss_gb"))

    def test_an_unattributable_phase_falls_back_to_the_combined_weight(self):
        # The safe direction: over-reserve rather than run a compile inside a
        # test-sized reservation.
        rec = dict(self.CLEAN, inputs_moved_during_run=True)
        with mock.patch.object(vr, "load_record", return_value=rec), \
             mock.patch.object(vr, "_gate_weight_gb", return_value=9):
            self.assertEqual(vr._split_weights_gb("t"), (9, 9))

    def test_a_clean_record_actually_moves_the_two_weights_apart(self):
        # Both directions: the guard must not simply refuse everything.
        with mock.patch.object(vr, "load_record", return_value=dict(self.CLEAN)), \
             mock.patch.object(vr, "_gate_weight_gb", return_value=9):
            build_gb, run_gb = vr._split_weights_gb("t")
        self.assertGreater(build_gb, run_gb)
        self.assertEqual(run_gb, max(vr.MIN_TARGET_GB, 1))



class FiniteMemoryHistory(unittest.TestCase):
    INVALID = [float("nan"), float("inf"), -float("inf"), True, False,
               0, -1, "4", 10 ** 400, sys.float_info.max]

    def test_invalid_combined_peaks_keep_valid_history_or_default(self):
        for value in self.INVALID:
            with self.subTest(value=value):
                rec = {"status": vr.STATUS_RUNNING, "peak_rss_gb": value,
                       "prior_peak_rss_gb": 40.0}
                with mock.patch.object(vr, "load_record", return_value=rec):
                    self.assertEqual(vr._gate_weight_gb("t"), 60)
                rec["prior_peak_rss_gb"] = value
                with mock.patch.object(vr, "load_record", return_value=rec):
                    self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)

    def test_invalid_phase_peak_uses_combined_reservation(self):
        for field in ("build_peak_rss_gb", "run_peak_rss_gb"):
            for value in self.INVALID:
                with self.subTest(field=field, value=value):
                    rec = dict(TestPhasePeakAttribution.CLEAN, **{field: value})
                    with mock.patch.object(vr, "load_record", return_value=rec), \
                         mock.patch.object(vr, "_gate_weight_gb", return_value=60):
                        weights = vr._split_weights_gb("t")
                    self.assertEqual(weights[0 if field == "build_peak_rss_gb" else 1], 60)

    def test_invalid_build_peaks_do_not_hide_valid_carried_floor(self):
        for value in self.INVALID:
            with self.subTest(value=value):
                rec = {"build_peak_rss_gb": value, "max_build_peak_rss_gb": 40.0}
                self.assertEqual(vr.recorded_build_peak_gb(rec), 40.0)
                rec["max_build_peak_rss_gb"] = value
                self.assertIsNone(vr.recorded_build_peak_gb(rec))
                self.assertEqual(vr.cold_build_floor_gb({"_cold_build_peak_gb": value}), 0)

    def test_nonstandard_json_numbers_do_not_break_record_admission(self):
        with tempfile.TemporaryDirectory() as tmp, \
             mock.patch.object(vr, "STATE_DIR", Path(tmp)):
            for value in (float("nan"), float("inf"), -float("inf")):
                with self.subTest(value=value):
                    record = {"target": "t", "status": vr.STATUS_RUNNING,
                              "peak_rss_gb": value, "prior_peak_rss_gb": 40.0,
                              "build_peak_rss_gb": value,
                              "max_build_peak_rss_gb": 40.0}
                    vr.record_path("t").write_text(json.dumps(record))
                    self.assertEqual(vr._gate_weight_gb("t"), 60)
                    self.assertEqual(vr.recorded_build_peak_gb(vr.load_record("t")), 40.0)

    def test_finite_numeric_history_keeps_fractional_headroom(self):
        for value in (4, 4.5):
            with self.subTest(value=value):
                with mock.patch.object(vr, "load_record", return_value={"peak_rss_gb": value}):
                    self.assertEqual(vr._gate_weight_gb("t"), 6 if value == 4 else 7)
                self.assertEqual(vr.recorded_build_peak_gb({"build_peak_rss_gb": value}), value)


class TestHostProvenance(unittest.TestCase):
    """`data/suite_state/` is shared between machines and the weight path never
    reads `runner_host`, so the weights table marks rows measured elsewhere.

    The marker has to be right in BOTH directions. macOS stamps this box as
    `m1AirM224GB1TB2.localdomain` and `m1-Air-M2-24GB-1TB-2.local` depending on
    whether mDNS answered, and both spellings are already committed -- comparing
    raw strings marked 6 of this box's own records foreign.
    """

    def test_the_two_spellings_of_this_box_are_the_same_box(self):
        self.assertEqual(vr._host_key("m1AirM224GB1TB2.localdomain"),
                         vr._host_key("m1-Air-M2-24GB-1TB-2.local"))

    def test_a_genuinely_different_machine_stays_different(self):
        self.assertNotEqual(vr._host_key("m1AirM224GB1TB2.localdomain"),
                            vr._host_key("m8Macbo128GB8TB.localdomain"))

    def test_a_foreign_record_is_marked(self):
        with mock.patch.object(vr, "_this_host", return_value="m1AirM224GB1TB2.localdomain"):
            self.assertTrue(vr._is_foreign_record("m8Macbo128GB8TB.localdomain"))

    def test_this_box_under_either_spelling_is_not_marked(self):
        with mock.patch.object(vr, "_this_host", return_value="m1AirM224GB1TB2.localdomain"):
            self.assertFalse(vr._is_foreign_record("m1-Air-M2-24GB-1TB-2.local"))
            self.assertFalse(vr._is_foreign_record("m1AirM224GB1TB2.localdomain"))

    def test_unknown_provenance_is_not_asserted_to_be_foreign(self):
        # A record predating the field says nothing either way; marking it would
        # put a claim on a row nobody can check.
        with mock.patch.object(vr, "_this_host", return_value="somebox"):
            self.assertFalse(vr._is_foreign_record(None))
            self.assertFalse(vr._is_foreign_record(""))



class SkippedRunsKeepReservationHistory(unittest.TestCase):
    def _record(self, **updates):
        return record(**{"status": vr.STATUS_SKIPPED, "kind": "gate",
                         "command": "/bin/sh -c partial-gate", "peak_rss_gb": 0.1,
                         "prior_peak_rss_gb": 20.0, "build_peak_rss_gb": 0.1,
                         "run_peak_rss_gb": 0.1, "build_rss_samples": 40, "rss_samples": 40,
                         "counts": {"passed": 1, "failed": 0, "result_lines": 1}, **updates})

    def test_skipped_positive_count_cannot_lower_prior_history(self):
        rec = self._record()
        entry = {**ENTRY, "kind": "gate"}
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._gate_weight_gb("t"), 30)
            self.assertEqual(vr._prior_peak_rss_gb("t"), 20.0)

    def test_skipped_without_prior_cannot_lower_the_default(self):
        rec = self._record(prior_peak_rss_gb=None)
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)

    def test_skipped_phase_peaks_cannot_replace_combined_history(self):
        with mock.patch.object(vr, "load_record", return_value=self._record()):
            self.assertEqual(vr._split_weights_gb("t"), (30, 30))
            self.assertIsNone(vr._phase_peak_gb("t", "build_peak_rss_gb"))
            self.assertIsNone(vr._phase_peak_gb("t", "run_peak_rss_gb"))

    def test_a_larger_skipped_observation_still_raises_the_weight(self):
        with mock.patch.object(vr, "load_record", return_value=self._record(peak_rss_gb=24.0)):
            self.assertEqual(vr._gate_weight_gb("t"), 36)

    def test_completed_success_still_learns_the_smaller_peak(self):
        with mock.patch.object(vr, "load_record", return_value=self._record(status=vr.STATUS_GREEN)):
            self.assertEqual(vr._gate_weight_gb("t"), vr.MIN_TARGET_GB)
            self.assertEqual(vr._split_weights_gb("t"), (vr.MIN_TARGET_GB, vr.MIN_TARGET_GB))


class TestZeroTestRunCannotLowerAWeight(unittest.TestCase):
    """A run that executed no test measured no test.

    Measured 2026-09-18 on `clean-elab::lib::shard::lean4_corpus_tests`: an
    external dependency's Cargo manifest stopped cargo before a single test ran.
    The row recorded RED, `result_lines: 0`, 51 s and a 1.53 GB peak over ONE
    sample -- the cost of a cargo invocation dying -- and that cut the weight
    from 23 GB to 3 GB against a carried 14.83 GB peak. `status` alone did not
    catch it: the run was not timed out, not ERROR and not RUNNING.
    """

    BASE = {"peak_rss_gb": 1.53, "prior_peak_rss_gb": 14.83, "timed_out": False}

    def test_a_red_run_that_printed_no_result_line_is_cut_short(self):
        rec = dict(self.BASE, status=vr.STATUS_RED,
                   counts={"passed": 0, "failed": 0, "result_lines": 0})
        self.assertTrue(vr._run_was_cut_short(rec))

    def test_a_run_that_selected_zero_tests_is_cut_short(self):
        # A filter that matched nothing still prints a result line.
        rec = dict(self.BASE, status=vr.STATUS_GREEN,
                   counts={"passed": 0, "failed": 0, "result_lines": 1})
        self.assertTrue(vr._run_was_cut_short(rec))

    def test_a_real_run_is_not_cut_short(self):
        rec = dict(self.BASE, status=vr.STATUS_GREEN,
                   counts={"passed": 596, "failed": 0, "result_lines": 1})
        self.assertFalse(vr._run_was_cut_short(rec))

    def test_a_red_run_with_results_still_preserves_the_prior_peak(self):
        # Failure observes real memory but does not establish the cost of
        # the successful path. Results alone cannot license a lower estimate.
        rec = dict(self.BASE, status=vr.STATUS_RED,
                   counts={"passed": 100, "failed": 3, "result_lines": 1})
        self.assertTrue(vr._run_was_cut_short(rec))
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._prior_peak_rss_gb("t"), 14.83)
        rec["peak_rss_gb"] = 40.0
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._prior_peak_rss_gb("t"), 40.0)

    def test_the_zero_test_peak_may_raise_but_never_lower(self):
        rec = dict(self.BASE, status=vr.STATUS_RED,
                   counts={"passed": 0, "failed": 0, "result_lines": 0})
        with mock.patch.object(vr, "load_record", return_value=rec):
            self.assertEqual(vr._prior_peak_rss_gb("t"), 14.83)
        # and it still RAISES when it is the larger number
        rec_big = dict(rec, peak_rss_gb=40.0)
        with mock.patch.object(vr, "load_record", return_value=rec_big):
            self.assertEqual(vr._prior_peak_rss_gb("t"), 40.0)

    def test_a_record_without_counts_is_unaffected(self):
        # Records predating the field must keep their old classification.
        rec = dict(self.BASE, status=vr.STATUS_GREEN)
        self.assertFalse(vr._run_was_cut_short(rec))


class ARunnerRowMeasuresOneBuildProfile(unittest.TestCase):
    """The release-profile rows (docs/DECISIONS.md R148).

    The `replay_forged` lane tests for leanprover/lean4#14807 compile only in a
    release build (`cfg(not(debug_assertions))`), and every package row is a
    debug build, so before these rows the debug `clean-olean` rows went GREEN
    without running them. Each arm here pins one way a debug result, or a run
    that never reached those tests, could stand for a release row.
    """

    RELEASE = {
        "id": "pkg::release::test::t",
        "package": "pkg",
        "kind": "test",
        "profile": "release",
        "argv": ["targo", "--unverified", "test", "--locked", "--release", "-p", "pkg",
                 "--lib", "--", "mod_a"],
        "_must_pass": ["mod_a::release_only"],
        "_cold_build_peak_gb": 8.97,
    }

    def _release_record(self, **overrides):
        base = record(
            target=self.RELEASE["id"],
            profile="release",
            counts={"passed": 2, "failed": 0, "ignored": 0, "result_lines": 1},
            passed_tests=["mod_a::debug_too", "mod_a::release_only"],
        )
        base.update(overrides)
        return base

    def test_a_debug_record_never_stands_for_a_release_row(self):
        # No `profile` field: every record written before this change, and
        # every debug row's record, is a debug measurement.
        rec = self._release_record()
        del rec["profile"]
        row = vr.derive(self.RELEASE, rec, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("dev profile", row["reason"])

    def test_a_release_record_never_stands_for_a_debug_row(self):
        row = vr.derive(ENTRY, record(profile="release"), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("release profile", row["reason"])

    def test_a_release_record_that_ran_its_must_pass_tests_is_green(self):
        # The anti-correlation arm: without it the arms below would pass
        # against a rule that demoted every release row.
        row = vr.derive(self.RELEASE, self._release_record(), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)

    def test_exit_zero_without_the_must_pass_tests_is_unknown(self):
        # The debug-build shape: the release-only test compiled out, the rest
        # ran and passed, libtest exits 0.
        rec = self._release_record(passed_tests=["mod_a::debug_too"],
                                   counts={"passed": 1, "failed": 0, "ignored": 0,
                                           "result_lines": 1})
        row = vr.derive(self.RELEASE, rec, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("mod_a::release_only", row["reason"])

    def test_a_record_with_no_passed_list_is_unknown(self):
        rec = self._release_record()
        del rec["passed_tests"]
        row = vr.derive(self.RELEASE, rec, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_a_red_release_record_stays_red(self):
        rec = self._release_record(status=vr.STATUS_RED, passed_tests=["mod_a::debug_too"])
        row = vr.derive(self.RELEASE, rec, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_RED)

    def test_the_profile_is_hashed_and_a_debug_digest_does_not_move(self):
        dev = {"id": "probe", "package": "pkg", "kind": "test",
               "argv": ["targo", "--unverified", "test"],
               "_dirs": [vr.REPO_ROOT / "scripts" / "verify_runner.sh"]}
        explicit_dev = dict(dev, profile="dev")
        release = dict(dev, profile="release")
        d = vr.input_digest(dev, fresh=True)
        self.assertEqual(d, vr.input_digest(explicit_dev, fresh=True))
        self.assertNotEqual(d, vr.input_digest(release, fresh=True))

    def test_the_real_rows_pass_their_own_consistency_check(self):
        self.assertEqual(vr.check_profiles(vr.RELEASE_PROFILE_TARGETS), [])
        for entry in vr.RELEASE_PROFILE_TARGETS:
            self.assertIn("::release::", entry["id"])
            self.assertEqual(entry["profile"], vr.PROFILE_RELEASE)

    def test_check_profiles_refuses_each_drift(self):
        cases = {
            "no --release": dict(self.RELEASE, argv=[a for a in self.RELEASE["argv"]
                                                     if a != "--release"]),
            "--release after --": dict(self.RELEASE, argv=[a for a in self.RELEASE["argv"]
                                                           if a != "--release"] + ["--release"]),
            "no must-pass": {k: v for k, v in self.RELEASE.items() if k != "_must_pass"},
            "must-pass the filter cannot select": dict(self.RELEASE, _must_pass=["mod_b::x"]),
            "must-pass the skip removes": dict(
                self.RELEASE, argv=self.RELEASE["argv"] + ["--skip", "release_only"]),
            "unknown profile": dict(self.RELEASE, profile="bench"),
            "not a cargo test": dict(self.RELEASE, argv=["scripts/x.sh", "--release"]),
            "dev that builds release": dict(self.RELEASE, profile="dev"),
            # The `--skip=X` spelling skips exactly as `--skip X` does.
            "must-pass the skip= removes": dict(
                self.RELEASE, argv=self.RELEASE["argv"] + ["--skip=release_only"]),
            # Flags that stop libtest printing `test <name> ... ok`, so the
            # must-pass parser would see nothing and the row would read UNKNOWN
            # for good -- found only after a release build of up to 24 min.
            "cargo -q": self._with_cargo_flag("-q"),
            "cargo --quiet": self._with_cargo_flag("--quiet"),
            "libtest -q": dict(self.RELEASE, argv=self.RELEASE["argv"] + ["-q"]),
            "libtest --quiet": dict(self.RELEASE, argv=self.RELEASE["argv"] + ["--quiet"]),
            "libtest --format terse": dict(
                self.RELEASE, argv=self.RELEASE["argv"] + ["--format", "terse"]),
            "libtest --format=json": dict(
                self.RELEASE, argv=self.RELEASE["argv"] + ["-Z", "unstable-options",
                                                           "--format=json"]),
            "libtest --nocapture": dict(self.RELEASE, argv=self.RELEASE["argv"] + ["--nocapture"]),
            "libtest --no-capture": dict(self.RELEASE, argv=self.RELEASE["argv"] + ["--no-capture"]),
            # A release row's learned build weight comes from whichever build
            # ran first in a shared target dir, so it must carry its highest
            # measured build peak.
            "no cold build peak": {k: v for k, v in self.RELEASE.items()
                                   if k != "_cold_build_peak_gb"},
            "cold build peak zero": dict(self.RELEASE, _cold_build_peak_gb=0),
            "cold build peak not a number": dict(self.RELEASE, _cold_build_peak_gb="9"),
            "cold build peak a bool": dict(self.RELEASE, _cold_build_peak_gb=True),
            # A row with no `profile` key is recorded as a debug one, so it may
            # not build another profile either.
            "unlabelled row with --release": dict(
                ENTRY, argv=ENTRY["argv"] + ["--release"]),
            "unlabelled row with -r": dict(ENTRY, argv=ENTRY["argv"] + ["-r"]),
            "unlabelled row with --profile": dict(
                ENTRY, argv=ENTRY["argv"] + ["--profile", "bench"]),
            "dev row with -r": dict(ENTRY, profile="dev", argv=ENTRY["argv"] + ["-r"]),
        }
        for label, entry in cases.items():
            with self.subTest(label):
                self.assertTrue(vr.check_profiles([entry]), f"{label} was accepted")
        self.assertEqual(vr.check_profiles([self.RELEASE]), [])
        # The anti-correlation arms: the pretty format spelled out, a skip that
        # misses the must-pass names, and an unlabelled debug row are accepted.
        for label, entry in {
            "--format pretty": dict(self.RELEASE, argv=self.RELEASE["argv"] + ["--format", "pretty"]),
            "--format=pretty": dict(self.RELEASE, argv=self.RELEASE["argv"] + ["--format=pretty"]),
            "--skip= another test": dict(self.RELEASE, argv=self.RELEASE["argv"] + ["--skip=debug_too"]),
            "an unlabelled debug row": ENTRY,
            "a non-cargo row with --release": dict(ENTRY, argv=["scripts/x.sh", "--release"]),
        }.items():
            with self.subTest(label):
                self.assertEqual(vr.check_profiles([entry]), [], label)

    def _with_cargo_flag(self, flag):
        argv = list(self.RELEASE["argv"])
        argv.insert(argv.index("--"), flag)
        return dict(self.RELEASE, argv=argv)

    def test_the_rows_are_on_the_board_with_no_flags(self):
        with mock.patch.object(vr, "cargo_metadata", return_value={"packages": []}), \
                mock.patch.object(vr, "path_dep_closure", return_value=[]), \
                mock.patch.object(vr, "check_crystal_extra_paths", return_value=[]):
            ids = {e["id"] for e in vr.build_inventory([])}
            refused = dict(vr.RELEASE_PROFILE_TARGETS[0])
            refused["argv"] = [a for a in refused["argv"] if a != "--release"]
            with mock.patch.object(vr, "RELEASE_PROFILE_TARGETS", [refused]):
                with self.assertRaises(SystemExit):
                    vr.build_inventory([])
        for entry in vr.RELEASE_PROFILE_TARGETS:
            self.assertIn(entry["id"], ids)

    def test_passed_test_names_reads_only_ok_lines(self):
        text = "\n".join([
            "running 4 tests",
            "test a::slow has been running for over 60 seconds",
            "test a::ok_one ... ok",
            "test a::bad ... FAILED",
            "test a::skipped ... ignored",
            "test a::ok_two ... ok",
            "test result: FAILED. 2 passed; 1 failed; 1 ignored",
        ])
        self.assertEqual(vr.passed_test_names(text), ["a::ok_one", "a::ok_two"])

    def test_run_one_records_the_profile_and_what_passed(self):
        entry = dict(self.RELEASE, id="synthetic::release",
                     argv=["/bin/sh", "-c",
                           "echo 'test mod_a::release_only ... ok'; "
                           "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'"],
                     _dirs=[vr.REPO_ROOT / "scripts"])
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["profile"], "release")
        self.assertEqual(rec["passed_tests"], ["mod_a::release_only"])
        self.assertEqual(rec["must_pass"], ["mod_a::release_only"])
        self.assertIn("profile", rec["digest_scope"])
        self.assertEqual(vr.derive(entry, rec, rec["input_digest"])["bucket"], vr.BUCKET_GREEN)

    def test_run_one_says_why_a_run_without_its_must_pass_is_not_green(self):
        entry = dict(self.RELEASE, id="synthetic::release_missing",
                     argv=["/bin/sh", "-c",
                           "echo 'test mod_a::debug_too ... ok'; "
                           "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'"],
                     _dirs=[vr.REPO_ROOT / "scripts"])
        rec = vr.run_one(entry, timeout=60)
        self.assertIn("mod_a::release_only", rec["notes"])
        self.assertEqual(vr.derive(entry, rec, rec["input_digest"])["bucket"], vr.BUCKET_UNKNOWN)

    def _worker_output(self, rec):
        import contextlib
        import io
        with tempfile.TemporaryDirectory() as tmp:
            queue = Path(tmp) / "queue.json"
            queue.write_text(json.dumps({"packages": [], "targets": [self.RELEASE["id"]], "jobs": 1}))
            out = io.StringIO()
            with mock.patch.object(vr, "build_inventory", return_value=[self.RELEASE]), \
                    mock.patch.object(vr, "input_digest", return_value=DIGEST), \
                    mock.patch.object(vr, "load_record", return_value=None), \
                    mock.patch.object(vr, "timeout_for", return_value=(60, "test floor")), \
                    mock.patch.object(vr, "run_one", return_value=rec), \
                    contextlib.redirect_stdout(out):
                vr._worker_loop(types.SimpleNamespace(queue=str(queue)))
            return out.getvalue()

    def test_the_worker_says_when_a_recorded_green_reads_unknown(self):
        # Measured 2026-10-20 on the cfg demonstration: the worker printed
        # `DONE (1/1) clean-olean::release::test::replay_forged_lanes -> GREEN`
        # for a run that `status` reads UNKNOWN, because the DONE line prints
        # the RECORDED status. A person watching the worker must see both.
        rec = self._release_record(passed_tests=["mod_a::debug_too"], duration_s=1.0)
        out = self._worker_output(rec)
        self.assertIn("-> GREEN", out)
        self.assertRegex(out, r"reads UNKNOWN, not GREEN: .*mod_a::release_only")

    def test_the_worker_adds_nothing_when_the_record_reads_as_recorded(self):
        # The anti-correlation arm: a run that ran its must-pass tests prints
        # no second verdict.
        out = self._worker_output(self._release_record(duration_s=1.0))
        self.assertIn("-> GREEN", out)
        self.assertNotIn("reads ", out)

    def test_every_must_pass_name_is_a_test_in_its_package(self):
        """A must-pass name that names no `#[test] fn` would leave its row
        UNKNOWN forever; catch the rename here, without a build. Since
        2026-11-13 (E3 fix-up) the names are those scripts/rust_modules.py
        derives the row's own build SURELY compiles -- its target's module tree,
        under the release lane's cfg facts and the features cargo resolves for
        the row -- not a file guessed from the name's module path, which missed
        a test in an inline `mod` and could not see a cfg."""
        meta = vr.cargo_metadata()
        rm = vr._rust_modules()
        for entry in vr.RELEASE_PROFILE_TARGETS:
            pkg = next(p for p in meta["packages"] if p["name"] == entry["package"])
            name = vr._test_target_name(entry["argv"])
            root = (vr.package_lib_root(meta, entry["package"]) if name is None else
                    Path(next(t["src_path"] for t in pkg["targets"]
                              if t["name"] == name and "test" in t["kind"])))
            facts = vr.row_cfg_facts(meta, pkg, entry)
            # A package with a build script may emit a cfg, so its facts are
            # undecided (`row_cfg_facts`): there the names must be tests the
            # build MAY compile under the lane's facts, every feature open.
            compiled = set(vr._crate_tests(root, rm.Reach.CERTAIN, facts) if facts is not None
                           else vr._crate_tests(root, rm.Reach.MAYBE,
                                                vr.lane_cfg_facts(vr.PROFILE_RELEASE)))
            with self.subTest(entry["id"]):
                self.assertEqual(sorted(set(entry["_must_pass"]) - compiled), [])


class AReleaseRowBuildReservesItsColdPeak(unittest.TestCase):
    """A warm build's peak may not size a release row's build reservation.

    The release rows share one target dir. Measured 2026-10-19/20: run after the
    lib row had built its dependencies, the build of
    `clean-olean::release::test::replay_forged_lanes` peaked at 4.81 GB, which
    `_split_weights_gb` turns into 8 GB; three cold builds of it peaked at 8.84,
    8.94 and 8.97 GB. `--only` one row, a fresh or pruned `release/` dir, or
    another order would run that cold build under a reservation below its own
    peak.
    """

    ROW = dict(ARunnerRowMeasuresOneBuildProfile.RELEASE, id="synthetic::release::floor")
    # Shaped like the committed clean-olean::release::test::replay_forged_lanes
    # record: a warm build, a clean split.
    WARM = {"build_peak_rss_gb": 4.81, "build_rss_samples": 117,
            "run_peak_rss_gb": 3.5, "rss_samples": 22,
            "inputs_moved_during_run": False}

    def _weights(self, entry, rec):
        with mock.patch.object(vr, "load_record", return_value=rec), \
                mock.patch.object(vr, "_gate_weight_gb", return_value=12):
            return vr._split_weights_gb(entry["id"], vr.cold_build_floor_gb(entry))

    def test_a_warm_build_record_cannot_lower_the_build_below_the_cold_floor(self):
        self.assertEqual(vr.cold_build_floor_gb(self.ROW), 14)  # ceil(1.5 x 8.97)
        self.assertEqual(self._weights(self.ROW, dict(self.WARM)), (14, 6))

    def test_without_a_floor_the_warm_record_still_sizes_the_build(self):
        # The anti-correlation arm: the floor is what raises it, nothing else.
        row = {k: v for k, v in self.ROW.items() if k != "_cold_build_peak_gb"}
        self.assertEqual(vr.cold_build_floor_gb(row), 0)
        self.assertEqual(self._weights(row, dict(self.WARM)), (8, 6))

    def test_the_floor_never_lowers_a_learned_build_weight(self):
        rec = dict(self.WARM, build_peak_rss_gb=11.77, build_rss_samples=716)
        self.assertEqual(self._weights(self.ROW, rec), (18, 6))

    def test_an_unmeasured_row_reserves_the_larger_of_default_and_floor(self):
        self.assertEqual(self._weights(self.ROW, None), (14, 12))

    def test_every_real_release_row_floors_its_build_at_or_above_its_record(self):
        # Each real row's floor is at least its committed record's build peak:
        # the floor holds the highest build peak measured for the row, so a
        # record above it is a measurement the floor has not taken in. Until
        # 2026-10-28 this read "the cold peak a floor comes from is never
        # smaller than a warm one"; the lib row's warm builds (7.74 to 7.99 GB)
        # against its cold one (5.97 GB) refuted that, and this test went red.
        # The committed records are read from the real data/suite_state/, not
        # the sandbox this module points the runner at.
        committed = vr.REPO_ROOT / "data" / "suite_state"
        for entry in vr.RELEASE_PROFILE_TARGETS:
            with self.subTest(entry["id"]):
                self.assertGreater(vr.cold_build_floor_gb(entry), 0)
                path = committed / f"{vr.safe_name(entry['id'])}.json"
                self.assertTrue(path.is_file(), f"no committed record at {path}")
                rec = json.loads(path.read_text())
                self.assertGreaterEqual(entry["_cold_build_peak_gb"], rec["build_peak_rss_gb"])

    def _fake_targo(self, tmp):
        fake = Path(tmp) / "targo"
        fake.write_text(
            "#!/bin/sh\n"
            "for a in \"$@\"; do [ \"$a\" = --no-run ] && { sleep 0.2; exit 0; }; done\n"
            "echo 'test mod_a::release_only ... ok'\n"
            "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'\n")
        fake.chmod(0o755)
        return fake

    def test_run_one_reserves_the_floor_and_records_the_build_phase(self):
        asked = []

        def acquire(gb, label):
            asked.append((gb, label))
            return ("unit-test-token", True, False)

        with tempfile.TemporaryDirectory() as tmp:
            fake = self._fake_targo(tmp)
            entry = dict(self.ROW, argv=[str(fake), "--unverified", "test", "--release",
                                         "--", "mod_a"],
                         _dirs=[vr.REPO_ROOT / "scripts"])
            with mock.patch.object(vr, "_gate_acquire", acquire), \
                    mock.patch.object(vr, "load_record", return_value=dict(self.WARM)):
                rec = vr.run_one(entry, timeout=60)
        self.assertEqual(asked[0], (14, "synthetic::release::floor [build]"))
        self.assertEqual(rec["gate_weight_build_gb"], 14)
        self.assertEqual(rec["gate_weight_build_floor_gb"], 14)
        # The build phase's own clock, which the record did not carry: the
        # durations R148 first quoted could not be re-derived from any artifact.
        self.assertIsInstance(rec.get("build_exec_duration_s"), float)
        self.assertGreaterEqual(rec["build_exec_duration_s"], 0.2)
        self.assertIsInstance(rec.get("build_gate_wait_s"), float)
        self.assertEqual(rec["passed_tests"], ["mod_a::release_only"])

    def test_the_weights_table_names_the_cold_floor(self):
        import contextlib
        import io
        out = io.StringIO()
        with mock.patch.object(vr, "build_inventory", return_value=[self.ROW]), \
                mock.patch.object(vr, "load_record", return_value=dict(self.WARM)), \
                contextlib.redirect_stdout(out):
            vr.cmd_weights(types.SimpleNamespace(packages=[], only=None, json=False))
        self.assertRegex(out.getvalue(),
                         r"synthetic::release::floor: its build reserves at least 14 GB")


class TheKernelPackagesJoinTheBoard(unittest.TestCase):
    """Self-proof unit E3 (2026-11-13): clean-kernel and clean-ck0 on the board.

    Three things had to change with them, and each arm below fails on the
    runner as it stood before: a test target's `required-features` reach its
    argv, a relative literal is RESOLVED (file- or crate-relative) before a
    digest is said to cover it, and a lib shard is digested over its parent's
    outside reads.
    """

    def test_both_packages_are_default(self):
        for package in ("clean-kernel", "clean-ck0"):
            self.assertIn(package, vr.DEFAULT_PACKAGES)

    def test_required_features_reach_the_argv_sorted(self):
        meta = {"packages": [{"name": "clean-ck0", "targets": [
            {"name": "clean_ck0", "kind": ["lib"], "test": True},
            {"name": "export_reader", "kind": ["test"], "test": True,
             "required-features": ["serde-z", "export"]},
            {"name": "plain", "kind": ["test"], "test": True},
        ]}]}
        with mock.patch.object(vr, "load_plan", return_value=None):
            argv = {t["id"]: t["argv"] for t in vr.package_targets(meta, "clean-ck0")}
        self.assertEqual(argv["clean-ck0::test::export_reader"][-2:],
                         ["--features", "export,serde-z"])
        self.assertNotIn("--features", argv["clean-ck0::test::plain"])
        self.assertNotIn("--features", argv["clean-ck0::lib"])

    def _tree(self) -> Path:
        base = Path(tempfile.mkdtemp(prefix="resolve_", dir=_SANDBOX))
        subprocess.run(["git", "init", "-q", str(base)], check=True)
        (base / ".gitignore").write_text("out/\n")
        for rel, text in {
            "data/file_rel.json": "{}",
            "data/crate_rel.json": "{}",
            "out/ignored.txt": "x",
            "crates/pk/tests/fixtures/inside.txt": "x",
            "crates/other/fixtures/table.tsv": "x",
            # The library reaches env/a.rs, so its include_str! is a derived
            # library read (`library_external_reads`); the bare literals are not.
            "crates/pk/src/lib.rs": "mod env;\n",
            "crates/pk/src/env.rs": "mod a;\n",
            # file-relative from src/env/: four levels reach the repository root
            "crates/pk/src/env/a.rs":
                'const A: &str = include_str!("../../../../data/file_rel.json");\n'
                # file-relative, and inside the crate: never owed
                'const B: &str = include_str!("../../tests/fixtures/inside.txt");\n'
                # crate-relative (CARGO_MANIFEST_DIR join): owed
                'fn c() -> &\'static str { "../../data/crate_rel.json" }\n'
                # gitignored output: never owed, whichever box holds it
                'fn d() -> &\'static str { "../../out/ignored.txt" }\n'
                '// "../../../../data/comment_only.json" is prose, never owed\n',
            "crates/pk/tests/t.rs":
                'const T: &str = include_str!("../../other/fixtures/table.tsv");\n',
        }.items():
            path = base / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        subprocess.run(["git", "-C", str(base), "add", "-A"], check=True)
        return base

    def test_relative_literals_are_resolved_not_matched(self):
        base = self._tree()
        with mock.patch.object(vr, "RESOLVED_SCAN_PACKAGES", ("pk",)), \
                mock.patch.object(vr, "_EXTRA_PATH_SOURCES", ()):
            owed = vr._crystal_extra_paths_owed(base)
        self.assertEqual(owed["pk::lib"], {"data/file_rel.json", "data/crate_rel.json"})
        self.assertEqual(owed["pk::test::t"], {"crates/other/fixtures/table.tsv"})

    def _problems(self, base):
        # The crystal row stays: the checker's own selftest re-derives it.
        with mock.patch.object(vr, "RESOLVED_SCAN_PACKAGES", ("pk",)), \
                mock.patch.object(vr, "_EXTRA_PATH_SOURCES", vr._EXTRA_PATH_SOURCES[:1]), \
                mock.patch.object(vr, "TARGET_EXTRA_PATHS",
                                  {"pk::test::t": ["crates/other/fixtures/table.tsv"]}), \
                mock.patch.object(vr, "PACKAGE_EXTRA_PATHS", {}), \
                mock.patch.object(vr, "_check_olean_world_inputs", return_value=[]):
            return vr.check_crystal_extra_paths(base)

    def test_an_unlisted_resolved_read_is_refused(self):
        # data/file_rel.json is the library's include_str!, derived (no table
        # names it); the bare crate-relative literal is no include, so nothing
        # derives it.
        problems = self._problems(self._tree())
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("pk::lib reads data/crate_rel.json", problems[0])

    def test_the_include_is_covered_by_derivation_not_by_a_table(self):
        # The anti-arm: cut env/a.rs out of the module tree and its include is
        # no library read, so the check refuses it too. Until 2026-11-13 a hand
        # table (PACKAGE_EXTRA_PATHS) covered it, and deleting its row left the
        # suite green.
        base = self._tree()
        (base / "crates/pk/src/lib.rs").write_text("")
        problems = self._problems(base)
        self.assertEqual(len(problems), 2, problems)
        self.assertTrue(any("pk::lib reads data/file_rel.json" in m for m in problems), problems)

    def test_the_real_tree_owes_nothing_unlisted(self):
        self.assertEqual(vr.check_crystal_extra_paths(), [])

    def test_a_shard_is_digested_over_its_parents_reads(self):
        plan = {"parent": "pk::lib", "package": "pk", "base_argv": ["targo", "test"],
                "shards": [{"id": "pk::lib::shard::a", "key": "a", "filters": ["a::"],
                            "skip": [], "test_count": 1}]}
        meta = {"packages": [{"name": "pk", "manifest_path": str(vr.REPO_ROOT / "Cargo.toml"),
                              "targets": [{"name": "pk", "kind": ["lib"], "test": True}]}]}
        with mock.patch.object(vr, "cargo_metadata", return_value=meta), \
                mock.patch.object(vr, "path_dep_closure", return_value=[]), \
                mock.patch.object(vr, "check_crystal_extra_paths", return_value=[]), \
                mock.patch.object(vr, "load_plan", return_value=plan), \
                mock.patch.object(vr, "TARGET_EXTRA_PATHS", {"pk::lib": ["data/x.json"]}), \
                mock.patch.object(vr, "closure_library_reads", return_value=("data/y.json",)):
            dirs = {e["id"]: e["_dirs"] for e in vr.build_inventory(["pk"], with_gates=False)}
        want = {vr.REPO_ROOT / "data/x.json", vr.REPO_ROOT / "data/y.json"}
        self.assertEqual(set(dirs["pk::lib::shard::a"]), want)
        self.assertEqual(set(dirs["pk::lib"]), want)



class ACompileTimeReadReachesEveryRowThatCompilesIt(unittest.TestCase):
    """E3 fix-up (2026-11-13): out-of-crate `include_str!`/`include_bytes!`
    reads are derived from the module tree, not listed by hand."""

    def test_the_kernel_golden_reaches_a_dependents_row(self):
        # Deleting the hand entry for data/soundness_tcb.json left the suite
        # green; now no entry exists, and a package that compiles clean-kernel
        # (clean-parser) digests it through the derivation alone.
        meta = vr.cargo_metadata()
        self.assertIn("data/soundness_tcb.json", vr.library_external_reads(
            vr.package_lib_root(meta, "clean-kernel"), False))
        reads = vr.closure_library_reads(
            meta, vr.path_dep_closure(meta, "clean-parser"), "clean-parser", False)
        self.assertIn("data/soundness_tcb.json", reads)
        self.assertNotIn("data/soundness_tcb.json", vr.TARGET_EXTRA_PATHS["clean-kernel::lib"])

    def test_an_integration_targets_own_include_is_in_its_digest(self):
        rows = {e["id"]: e for e in vr.build_inventory(["clean-ck0"], with_gates=False)}
        dirs = {str(d) for d in rows["clean-ck0::test::level_as_written"]["_dirs"]}
        self.assertIn(str(vr.REPO_ROOT / "crates/clean-kernel/src/level/fixtures/"
                          "lean_kernel_verdicts_v4.30.0-rc2.tsv"), dirs)

    def test_comments_and_strings_are_not_includes(self):
        with tempfile.TemporaryDirectory(prefix="incl_", dir=_SANDBOX) as tmp:
            root = Path(tmp)
            base = root / "crates" / "zz"
            (base / "src").mkdir(parents=True)
            (root / "data").mkdir()
            for name in ("soundness_tcb.json", "axiom_audit.json", "prelude_axiom_ratchet.json"):
                (root / "data" / name).write_text("{}\n")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (base / "Cargo.toml").write_text("[package]\nname = \"zz\"\n")
            (base / "src" / "lib.rs").write_text(
                '// include_str!("../../../data/soundness_tcb.json")\n'
                'const S: &str = "include_str!(\\"../../../data/axiom_audit.json\\")";\n'
                'const T: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), '
                '"/../../data/prelude_axiom_ratchet.json"));\n')
            lib = base / "src" / "lib.rs"
            original = lib.read_text()
            got = vr.library_external_reads(lib, False, base=root)
            self.assertEqual(got, ("data/prelude_axiom_ratchet.json",))
            # Both excluded names are real, visible inputs when used by actual
            # macros; the synthetic repository must not make negatives vacuous.
            lib.write_text(original +
                           'const U: &str = include_str!("../../../data/soundness_tcb.json");\n'
                           'const V: &str = include_str!("../../../data/axiom_audit.json");\n')
            self.assertEqual(vr.library_external_reads(lib, False, base=root),
                             ("data/axiom_audit.json", "data/prelude_axiom_ratchet.json", "data/soundness_tcb.json"))
            lib.write_text(original)
            self.assertEqual(vr.library_external_reads(lib, False, base=root), got)


class TestWarmBuildInputIdentity(unittest.TestCase):
    def test_every_root_build_input_invalidates_a_warm_key(self):
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(vr, "REPO_ROOT", Path(tmp)), \
                mock.patch.object(vr, "toolchain_id", return_value="fixed"), \
                mock.patch.object(vr, "_WARM_BUILDS", set()):
            entry = dict(ENTRY, _dirs=[])
            initial = vr.build_warm_key(entry)
            vr.mark_build_warm(initial)
            for name in vr.ROOT_BUILD_INPUTS:
                with self.subTest(name=name):
                    path = Path(tmp) / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("first")
                    first = vr.build_warm_key(entry)
                    self.assertFalse(vr.build_is_warm(first))
                    vr.mark_build_warm(first)
                    path.write_text("second")
                    self.assertFalse(vr.build_is_warm(vr.build_warm_key(entry)))
                    path.unlink()
                    self.assertEqual(vr.build_warm_key(entry), initial)

    def test_compiler_replacement_does_not_use_the_status_cache(self):
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(vr, "REPO_ROOT", Path(tmp)), \
                mock.patch.object(vr, "_TOOLCHAIN_CACHE", "status snapshot"), \
                mock.patch.object(vr, "_WARM_BUILDS", set()), \
                mock.patch.object(vr, "run_capture", side_effect=[
                    (0, "rustc old\ncommit-hash: old\n"),
                    (0, "rustc new\ncommit-hash: new\n"),
                ]) as capture:
            entry = dict(ENTRY, _dirs=[])
            vr.mark_build_warm(vr.build_warm_key(entry))
            self.assertFalse(vr.build_is_warm(vr.build_warm_key(entry)))
            self.assertEqual(capture.call_count, 2)
            self.assertEqual(vr._TOOLCHAIN_CACHE, "status snapshot")

    def test_changed_config_restores_the_cold_build_reservation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "targo"
            fake.write_text("#!/bin/sh\nfor a in \"$@\"; do [ \"$a\" = --no-run ] && exit 0; done\n"
                            "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'\n")
            fake.chmod(0o755)
            entry = dict(ENTRY, argv=[str(fake), "--unverified", "test"], _dirs=[])
            asked = []
            with mock.patch.object(vr, "REPO_ROOT", root), \
                    mock.patch.object(vr, "_WARM_BUILDS", set()), \
                    mock.patch.object(vr, "input_digest", return_value=DIGEST), \
                    mock.patch.object(vr, "toolchain_id", return_value="fixed"), \
                    mock.patch.object(vr, "_split_weights_gb", return_value=(1, 1)), \
                    mock.patch.object(vr, "package_cold_build_floor_gb", return_value=(19, "fixture")), \
                    mock.patch.object(vr, "_gate_acquire", side_effect=lambda gb, label:
                                      (asked.append(gb) or "token", True, False)):
                self.assertEqual(vr.run_one(entry, 10)["status"], vr.STATUS_GREEN)
                (root / ".cargo").mkdir()
                (root / ".cargo/config.toml").write_text("[build]\njobs = 2\n")
                self.assertEqual(vr.run_one(entry, 10)["status"], vr.STATUS_GREEN)
                self.assertEqual(vr.run_one(entry, 10)["status"], vr.STATUS_GREEN)
            self.assertEqual(asked, [19, 1, 19, 1, 1, 1])


class TestUnknownCompilerStaysCold(unittest.TestCase):
    def test_failed_or_empty_compiler_probes_produce_no_warm_key(self):
        for reply in ((1, "probe failed"), (0, "unrecognized output")):
            with self.subTest(reply=reply), tempfile.TemporaryDirectory() as tmp, \
                    mock.patch.object(vr, "REPO_ROOT", Path(tmp)), \
                    mock.patch.object(vr, "run_capture", return_value=reply), \
                    mock.patch.object(vr, "_WARM_BUILDS", set()):
                key = vr.build_warm_key(dict(ENTRY, _dirs=[]))
                self.assertIsNone(key)
                vr.mark_build_warm(key)
                self.assertFalse(vr.build_is_warm(key))

    def test_unknown_compiler_cannot_lower_the_second_build_reservation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "targo"
            fake.write_text("#!/bin/sh\nfor a in \"$@\"; do [ \"$a\" = --no-run ] && exit 0; done\n"
                            "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'\n")
            fake.chmod(0o755)
            entry = dict(ENTRY, argv=[str(fake), "--unverified", "test"], _dirs=[])
            asked = []
            with mock.patch.object(vr, "REPO_ROOT", root), \
                    mock.patch.object(vr, "_WARM_BUILDS", set()), \
                    mock.patch.object(vr, "input_digest", return_value=DIGEST), \
                    mock.patch.object(vr, "toolchain_id", return_value="rustc-unavailable"), \
                    mock.patch.object(vr, "_split_weights_gb", return_value=(1, 1)), \
                    mock.patch.object(vr, "package_cold_build_floor_gb", return_value=(19, "fixture")), \
                    mock.patch.object(vr, "_gate_acquire", side_effect=lambda gb, label:
                                      (asked.append(gb) or "token", True, False)):
                for _ in range(2):
                    self.assertEqual(vr.run_one(entry, 10)["status"], vr.STATUS_GREEN)
            self.assertEqual(asked, [19, 1, 19, 1])


class APossiblyColdBuildReservesItsPackagesPeak(unittest.TestCase):
    """E3 fix-up (2026-11-13): a warm build's learned weight may not size a
    cold rebuild. The 101 clean-kernel rows learned 1 GB from warm builds; a
    cold rebuild of their targets peaks at 10.48 to 12.57 GB."""

    LEARNED = {"build_peak_rss_gb": 0.4, "build_rss_samples": 40,
               "run_peak_rss_gb": 0.3, "rss_samples": 10, "inputs_moved_during_run": False}
    COLD = {"target": "gate::fence", "status": vr.STATUS_GREEN,
            "command": "targo --unverified test --locked -p pkx --test reference_a",
            "build_peak_rss_gb": 12.57, "finished_at": "2026-11-13T00:00:00Z"}

    def setUp(self):
        vr._WARM_BUILDS.clear()

    def _fake_targo(self, tmp):
        fake = Path(tmp) / "targo"
        fake.write_text(
            "#!/bin/sh\n"
            "for a in \"$@\"; do [ \"$a\" = --no-run ] && exit 0; done\n"
            "echo 'test a::b ... ok'\n"
            "echo 'test result: ok. 1 passed; 0 failed; 0 ignored'\n")
        fake.chmod(0o755)
        return fake

    def _run(self, fake, target, asked, records, learned):
        def acquire(gb, label):
            asked.append((gb, label))
            return ("unit-test-token", True, False)

        entry = {"id": f"pkx::test::{target}", "package": "pkx", "kind": "test",
                 "argv": [str(fake), "--unverified", "test", "--locked", "-p", "pkx",
                          "--test", target],
                 "_dirs": [vr.REPO_ROOT / "scripts"]}
        with mock.patch.object(vr, "_gate_acquire", acquire), \
                mock.patch.object(vr, "_all_records", return_value=records), \
                mock.patch.object(vr, "load_record", return_value=dict(learned)):
            return vr.run_one(entry, timeout=60)

    def test_the_first_build_of_a_shape_reserves_the_packages_cold_floor(self):
        asked: list = []
        with tempfile.TemporaryDirectory() as tmp:
            fake = self._fake_targo(tmp)
            rec = self._run(fake, "t1", asked, [self.COLD], self.LEARNED)
            # A second target of the same shape, same process, same sources:
            # what it still compiles is its own test binary.
            rec2 = self._run(fake, "t2", asked, [self.COLD], self.LEARNED)
        self.assertEqual(asked[0], (19, "pkx::test::t1 [build]"))  # ceil(1.5 x 12.57)
        self.assertIn("possibly cold", rec["build_floor_basis"])
        self.assertIn("gate::fence", rec["build_floor_basis"])
        self.assertLess(asked[2][0], 19)
        self.assertEqual(asked[2][1], "pkx::test::t2 [build]")
        self.assertIn("warm", rec2["build_floor_basis"])

    def test_without_the_floor_the_learned_weight_sizes_the_cold_build(self):
        # The anti-arm: the floor, and nothing else, raises the first build.
        asked: list = []
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(vr, "package_cold_build_floor_gb", return_value=(0, "")):
            self._run(self._fake_targo(tmp), "t1", asked, [self.COLD], self.LEARNED)
        self.assertLess(asked[0][0], 19)

    def test_an_unmeasured_package_reserves_the_default(self):
        asked: list = []
        with tempfile.TemporaryDirectory() as tmp:
            self._run(self._fake_targo(tmp), "t1", asked, [], self.LEARNED)
        self.assertEqual(asked[0][0], vr.DEFAULT_TARGET_GB)

    def test_another_shape_is_cold_again(self):
        entry = {"id": "pkx::test::t", "package": "pkx", "kind": "test",
                 "argv": ["targo", "--unverified", "test", "-p", "pkx", "--test", "t"],
                 "_dirs": [vr.REPO_ROOT / "scripts"]}
        featured = dict(entry, argv=entry["argv"] + ["--features", "x"])
        vr.mark_build_warm(vr.build_warm_key(entry))
        self.assertTrue(vr.build_is_warm(vr.build_warm_key(
            dict(entry, argv=entry["argv"][:-1] + ["u"]))))
        self.assertFalse(vr.build_is_warm(vr.build_warm_key(featured)))

    def test_a_cold_peak_is_carried_through_warm_runs(self):
        asked: list = []
        learned = dict(self.LEARNED, max_build_peak_rss_gb=12.57)
        with tempfile.TemporaryDirectory() as tmp:
            rec = self._run(self._fake_targo(tmp), "t1", asked, [], learned)
        self.assertEqual(rec["max_build_peak_rss_gb"], 12.57)
        self.assertEqual(vr.recorded_build_peak_gb(rec), 12.57)

    def test_records_raise_the_seed_and_never_lower_it(self):
        seed = {("pkx", vr.PROFILE_DEV): (10.48, "measured")}
        low = dict(self.COLD, build_peak_rss_gb=5.0)
        with mock.patch.object(vr, "PACKAGE_COLD_BUILD_SEED_GB", seed):
            with mock.patch.object(vr, "_all_records", return_value=[low]):
                self.assertEqual(vr.package_cold_build_peak_gb("pkx", vr.PROFILE_DEV)[0], 10.48)
            with mock.patch.object(vr, "_all_records", return_value=[self.COLD]):
                self.assertEqual(vr.package_cold_build_peak_gb("pkx", vr.PROFILE_DEV)[0], 12.57)
            # A release record is no dev peak.
            rel = dict(self.COLD, profile=vr.PROFILE_RELEASE, build_peak_rss_gb=30.0)
            with mock.patch.object(vr, "_all_records", return_value=[rel]):
                self.assertEqual(vr.package_cold_build_peak_gb("pkx", vr.PROFILE_DEV)[0], 10.48)

    def test_a_release_rows_peak_floors_every_release_build_of_its_package(self):
        # A row's `_cold_build_peak_gb` holds a peak no record need carry
        # (main's parity row: 31.11 GB, kept only in its report); without it
        # the kernel's release lib row reserved 23 GB on 2026-11-14.
        row = {"id": "pkx::release::test::t", "package": "pkx", "kind": "test",
               "profile": vr.PROFILE_RELEASE, "_cold_build_peak_gb": 31.11,
               "argv": ["targo", "--unverified", "test", "--release", "-p", "pkx", "--test", "t"]}
        lib = {"argv": ["targo", "--unverified", "test", "--release", "-p", "pkx", "--lib"],
               "profile": vr.PROFILE_RELEASE}
        with mock.patch.object(vr, "PACKAGE_COLD_BUILD_SEED_GB", {}), \
                mock.patch.object(vr, "_all_records", return_value=[]):
            with mock.patch.object(vr, "RELEASE_PROFILE_TARGETS", [row]):
                self.assertEqual(vr.package_cold_build_peak_gb("pkx", vr.PROFILE_RELEASE)[0], 31.11)
                self.assertEqual(vr.package_cold_build_floor_gb(lib)[0], 47)
                self.assertIsNone(vr.package_cold_build_peak_gb("pkx", vr.PROFILE_DEV)[0])
            with mock.patch.object(vr, "RELEASE_PROFILE_TARGETS", []):
                self.assertEqual(vr.package_cold_build_floor_gb(lib)[0], vr.DEFAULT_TARGET_GB)

    def test_the_real_kernel_rows_reserve_at_least_the_measured_cold_peak(self):
        # Read the committed records, not this module's sandbox.
        with mock.patch.object(vr, "STATE_DIR", vr.REPO_ROOT / "data" / "suite_state"):
            for package, peak in (("clean-kernel", 10.48), ("clean-ck0", 0.76)):
                entry = {"argv": ["targo", "--unverified", "test", "--locked", "-p", package,
                                  "--test", "any"]}
                floor, _basis = vr.package_cold_build_floor_gb(entry)
                self.assertGreaterEqual(floor, math.ceil(1.5 * peak), package)
            # Every release build of the kernel: the highest peak any release
            # row of it states, whichever row's build measured it.
            entry = {"argv": ["targo", "--unverified", "test", "--locked", "--release", "-p",
                              "clean-kernel", "--lib"], "profile": vr.PROFILE_RELEASE}
            peak = max(r["_cold_build_peak_gb"] for r in vr.RELEASE_PROFILE_TARGETS
                       if r["package"] == "clean-kernel")
            self.assertGreaterEqual(vr.package_cold_build_floor_gb(entry)[0],
                                    math.ceil(1.5 * peak))

    def test_built_packages_and_shape(self):
        argv = ["targo", "--unverified", "test", "-p", "a", "--package=b", "-pc",
                "--test", "x", "--test=y", "--no-run", "--", "-p", "z"]
        self.assertEqual(vr.built_packages(argv), ("a", "b", "c"))
        self.assertEqual(vr.build_shape(argv),
                         ("targo", "--unverified", "test", "-p", "a", "--package=b", "-pc"))
        self.assertEqual(vr.built_packages(["scripts/x.sh", "-p", "a"]), ())


class EveryLibTestCompilesInARow(unittest.TestCase):
    """E3 fix-up (2026-11-13): a lib row builds the default features, so a
    `#[test]` behind a feature or the release profile ran in no row (22 of
    clean-ck0's, 84 of clean-kernel's, and 26 release-only kernel tests)."""

    DEV = dict({n: False for n in vr.TOOL_SET_CFG_NAMES}, debug_assertions=True, unix=True)
    REL = dict({n: False for n in vr.TOOL_SET_CFG_NAMES}, unix=True)
    LIB = ("#[cfg(test)]\nmod tests {\n"
           "    #[test]\n    fn plain() {}\n"
           "    #[cfg(feature = \"x\")]\n    #[test]\n    fn gated() {}\n"
           "}\n"
           "#[cfg(all(test, not(debug_assertions)))]\nmod rel {\n"
           "    #[test]\n    fn only_release() {}\n}\n")

    def _meta(self, lib_text, test_text=None):
        base = Path(tempfile.mkdtemp(prefix="feat_", dir=_SANDBOX))
        (base / "src").mkdir()
        (base / "src" / "lib.rs").write_text(lib_text)
        targets = [{"name": "pq", "kind": ["lib"], "test": True,
                    "src_path": str(base / "src" / "lib.rs")}]
        if test_text is not None:
            (base / "tests").mkdir()
            (base / "tests" / "t.rs").write_text(test_text)
            targets.append({"name": "t", "kind": ["test"], "test": True,
                            "src_path": str(base / "tests" / "t.rs")})
        (base / "Cargo.toml").write_text("[package]\nname = \"pq\"\n")
        return {"packages": [{"name": "pq", "manifest_path": str(base / "Cargo.toml"),
                              "features": {"default": [], "x": [], "y": ["x"]},
                              "targets": targets}]}

    @staticmethod
    def _resolved(meta, package, entry):
        # The synthetic package has no dev-dependencies: cargo would resolve
        # the row's flags through the feature table, as this does.
        table = meta["packages"][0]["features"]
        feats, defaults, _every = vr.argv_features(entry.get("argv") or [])
        todo, out = feats + (["default"] if defaults else []), set()
        while todo:
            feat = todo.pop()
            if feat not in out:
                out.add(feat)
                todo.extend(table.get(feat, []))
        return frozenset(out)

    def _facts(self):
        import contextlib
        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(vr, "lane_cfg_facts", lambda profile: dict(
            self.DEV if profile == vr.PROFILE_DEV else self.REL)))
        stack.enter_context(mock.patch.object(vr, "resolved_features", self._resolved))
        return stack

    def _problems(self, meta, rows):
        with self._facts(), mock.patch.object(vr, "FEATURE_SCAN_PACKAGES", ("pq",)), \
                mock.patch.object(vr, "LIB_TESTS_NO_ROW_RUNS", {}):
            return vr.lib_test_coverage_problems(meta, rows)

    LIB_ROW = {"id": "pq::lib", "package": "pq", "kind": "lib",
               "argv": ["targo", "--unverified", "test", "--locked", "-p", "pq", "--lib"]}

    def test_a_feature_gated_and_a_release_only_test_are_refused(self):
        problems = self._problems(self._meta(self.LIB), [self.LIB_ROW])
        self.assertEqual(len(problems), 2, problems)
        self.assertIn("lib test rel::only_release is release-only", problems[0])
        self.assertIn("lib test tests::gated compiles only with a feature", problems[1])

    def test_rows_that_compile_and_select_them_cover_them(self):
        feat = {"id": "pq::lib::features::y", "package": "pq", "kind": "test",
                "argv": self.LIB_ROW["argv"] + ["--features", "y", "--", "tests::"]}
        rel = {"id": "pq::release::lib", "package": "pq", "kind": "test", "profile": "release",
               "argv": ["targo", "--unverified", "test", "--locked", "--release", "-p", "pq",
                        "--lib", "--", "rel::"]}
        self.assertEqual(self._problems(self._meta(self.LIB), [self.LIB_ROW, feat, rel]), [])
        # A row that enables the feature but does not select the test, or
        # selects it without the feature, covers nothing.
        for row in (dict(feat, argv=self.LIB_ROW["argv"] + ["--features", "y", "--", "other::"]),
                    dict(feat, argv=self.LIB_ROW["argv"] + ["--", "tests::"])):
            with self.subTest(row["argv"][-3:]):
                problems = self._problems(self._meta(self.LIB), [self.LIB_ROW, row, rel])
                self.assertEqual(len(problems), 1, problems)

    def test_an_unrun_test_must_be_accounted_exactly(self):
        meta = self._meta(self.LIB)
        feat = {"id": "f", "package": "pq", "kind": "test",
                "argv": self.LIB_ROW["argv"] + ["--features", "x"]}
        with self._facts(), mock.patch.object(vr, "FEATURE_SCAN_PACKAGES", ("pq",)):
            with mock.patch.object(vr, "LIB_TESTS_NO_ROW_RUNS",
                                   {"pq": {"rel::only_release": "why"}}):
                self.assertEqual(vr.lib_test_coverage_problems(meta, [self.LIB_ROW, feat]), [])
            with mock.patch.object(vr, "LIB_TESTS_NO_ROW_RUNS",
                                   {"pq": {"rel::only_release": "why", "rel::gone": "why"}}):
                problems = vr.lib_test_coverage_problems(meta, [self.LIB_ROW, feat])
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("rel::gone", problems[0])

    def test_the_kernel_test_build_unifies_math_overlays(self):
        # The fact the plain rows rest on, from cargo's own resolver: a target
        # behind `#![cfg(feature = "math-overlays")]` with no required-features
        # (topology_overlay_type_regressions) runs in the plain row, and the
        # one lib test behind its negation runs in none.
        meta = vr.cargo_metadata()
        entry = {"argv": ["targo", "--unverified", "test", "-p", "clean-kernel", "--lib"]}
        self.assertIn("math-overlays", vr.resolved_features(meta, "clean-kernel", entry))
        self.assertNotIn("geometry-tools", vr.resolved_features(meta, "clean-kernel", entry))
        self.assertIn("geometry-tools", vr.resolved_features(
            meta, "clean-kernel", {"argv": entry["argv"] + ["--features", "geometry-tools"]}))

    def test_a_root_compiled_out_by_its_cfg_is_refused_unless_replaced(self):
        meta = self._meta("", "#![cfg(not(debug_assertions))]\n#[test]\nfn t() {}\n")
        debug = {"id": "pq::test::t", "package": "pq", "kind": "test",
                 "argv": ["targo", "--unverified", "test", "--locked", "-p", "pq", "--test", "t"]}
        rel = {"id": "pq::release::test::t", "package": "pq", "kind": "test",
               "profile": "release", "_replaces_debug_target": "t",
               "argv": ["targo", "--unverified", "test", "--locked", "--release", "-p", "pq",
                        "--test", "t"]}
        with self._facts():
            self.assertEqual(vr.compiled_out_rows(meta, [debug, rel]),
                             {"pq::test::t": "#![cfg(not(debug_assertions))]"})
            self.assertEqual(vr.debug_test_row("pq", meta["packages"][0]["targets"][-1])["argv"],
                             debug["argv"])
            problems = vr.compiled_out_problems(meta, [debug])
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("_replaces_debug_target", problems[0])
            # Replaced, the debug row is never derived (`package_targets`).
            self.assertEqual(vr.compiled_out_problems(meta, [rel]), [])
            # The cfg gone, the replacement is stale and refused.
            live = self._meta("", "#[test]\nfn t() {}\n")
            problems = vr.compiled_out_problems(live, [rel])
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("drop the field", problems[0])
            # A replacement naming no test target is refused.
            problems = vr.compiled_out_problems(meta, [dict(rel, _replaces_debug_target="u")])
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("no test target", problems[0])

    def test_an_inventory_without_gates_still_sees_the_replacing_row(self):
        # `shards plan` builds the inventory with `with_gates=False`, which
        # leaves the release rows out; measured 2026-11-14, the check then
        # refused the kernel's release-only tests as unrun and stopped the plan.
        meta = self._meta("", "#![cfg(not(debug_assertions))]\n#[test]\nfn t() {}\n")
        rel = {"id": "pq::release::test::t", "package": "pq", "kind": "test",
               "profile": "release", "_replaces_debug_target": "t",
               "_must_pass": ["t"], "_cold_build_peak_gb": 1.0,
               "argv": ["targo", "--unverified", "test", "--locked", "--release", "-p", "pq",
                        "--test", "t"]}
        with self._facts(), mock.patch.object(vr, "cargo_metadata", return_value=meta), \
                mock.patch.object(vr, "path_dep_closure", return_value=[]), \
                mock.patch.object(vr, "check_crystal_extra_paths", return_value=[]), \
                mock.patch.object(vr, "closure_library_reads", return_value=()), \
                mock.patch.object(vr, "row_target_reads", return_value=()), \
                mock.patch.object(vr, "load_plan", return_value=None):
            with mock.patch.object(vr, "RELEASE_PROFILE_TARGETS", [rel]):
                ids = {e["id"] for e in vr.build_inventory(["pq"], with_gates=False)}
            self.assertNotIn("pq::test::t", ids)
            with mock.patch.object(vr, "RELEASE_PROFILE_TARGETS", []), \
                    self.assertRaises(SystemExit):
                vr.build_inventory(["pq"], with_gates=False)

    def test_a_feature_root_is_live_only_with_its_feature(self):
        meta = self._meta("", "#![cfg(feature = \"x\")]\n#[test]\nfn t() {}\n")
        row = {"id": "pq::test::t", "package": "pq", "kind": "test",
               "argv": ["targo", "--unverified", "test", "--locked", "-p", "pq", "--test", "t"]}
        with self._facts():
            self.assertIn("pq::test::t", vr.compiled_out_rows(meta, [row]))
            self.assertEqual(vr.compiled_out_rows(
                meta, [dict(row, argv=row["argv"] + ["--features", "y"])]), {})

    def test_the_real_ck0_feature_row_runs_every_export_test(self):
        meta = vr.cargo_metadata()
        rows = vr.package_targets(meta, "clean-ck0")
        self.assertIn("clean-ck0::lib::features::export", {r["id"] for r in rows})
        self.assertEqual(vr.lib_test_coverage_problems(meta, rows), [])
        cut = [r for r in rows if r["id"] != "clean-ck0::lib::features::export"]
        problems = vr.lib_test_coverage_problems(meta, cut)
        self.assertGreaterEqual(len(problems), 22, problems)
        self.assertTrue(all("clean-ck0: lib test export::" in m
                            or "minimal_env::overlay::tests" in m for m in problems), problems)

    def test_the_real_release_infer_parity_debug_row_is_replaced(self):
        meta = vr.cargo_metadata()
        rows = vr.package_targets(meta, "clean-kernel")
        self.assertNotIn("clean-kernel::test::release_infer_parity", {r["id"] for r in rows})
        self.assertEqual(vr.compiled_out_rows(meta, rows), {})
        pkg = next(p for p in meta["packages"] if p["name"] == "clean-kernel")
        tgt = next(t for t in pkg["targets"] if t["name"] == "release_infer_parity")
        self.assertEqual(vr.compiled_out_rows(meta, [vr.debug_test_row("clean-kernel", tgt)]),
                         {"clean-kernel::test::release_infer_parity":
                          "#![cfg(not(debug_assertions))]"})
        self.assertEqual(vr.compiled_out_problems(meta, rows + vr.RELEASE_PROFILE_TARGETS), [])

    def test_the_test_attribute_shape_is_the_selectors_gates(self):
        sys.path.insert(0, str(vr.REPO_ROOT / "scripts"))
        import check_cargo_test_selectors as sel
        self.assertEqual(vr.TEST_ATTR_BODY_RE.pattern, sel.TEST_BODY_RE.pattern)

    def test_a_rows_feature_flags_are_read_before_the_separator(self):
        self.assertEqual(vr.argv_features(["targo", "test", "--features", "a,b", "-F", "c",
                                           "--no-default-features", "--", "--features", "x"]),
                         (["a", "b", "c"], False, False))


class InheritedLibraryInputs(unittest.TestCase):
    """A dependency's embedded input must invalidate its consumers' records."""

    def setUp(self):
        self.base = Path(tempfile.mkdtemp(prefix="embedded_", dir=_SANDBOX))
        subprocess.run(["git", "init", "-q", str(self.base)], check=True)
        edges = {
            "consumer": [("direct", None), ("own_dev", "dev")],
            "direct": [("leaf", None), ("dep_dev", "dev"), ("build_support", "build")],
            "leaf": [], "own_dev": [], "dep_dev": [], "build_support": [],
            "unrelated": [],
        }
        packages = []
        self.extra = {}
        for name, deps in edges.items():
            directory = self.base / "crates" / name
            directory.mkdir(parents=True)
            (directory / "Cargo.toml").write_text("# fixture\n")
            (directory / "lib.rs").write_text("// fixture\n")
            extra = self.base / "data" / f"{name}.json"
            extra.parent.mkdir(exist_ok=True)
            extra.write_text("{}\n")
            self.extra[name] = [str(extra.relative_to(self.base))]
            packages.append({
                "name": name, "manifest_path": str(directory / "Cargo.toml"),
                "dependencies": [{"name": dep, "kind": kind} for dep, kind in deps],
                "targets": [{"name": name, "kind": ["lib"], "test": True}],
            })
        self.meta = {"packages": packages}
        subprocess.run(["git", "-C", str(self.base), "add", "."], check=True)
        for attr, value in {
            "REPO_ROOT": self.base, "PACKAGE_EXTRA_PATHS": self.extra,
            "TARGET_EXTRA_PATHS": {},
            "WORKSPACE_GATES": [{"id": "gate::fixture", "package": "__workspace__",
                                  "kind": "gate", "argv": ["fixture"]}],
            "RELEASE_PROFILE_TARGETS": [],
        }.items():
            patcher = mock.patch.object(vr, attr, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        for attr, value in {"cargo_metadata": self.meta, "load_plan": None,
                            "check_crystal_extra_paths": [], "toolchain_id": "fixture"}.items():
            patcher = mock.patch.object(vr, attr, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def inventory(self, with_gates=False):
        return {e["id"]: e for e in vr.build_inventory(
            ["consumer", "unrelated"], with_gates=with_gates)}

    def test_inherits_exact_library_closure_including_root_dev_and_build(self):
        entries = self.inventory()
        consumer = set(entries["consumer::lib"]["_dirs"])
        expected = {"consumer", "direct", "leaf", "own_dev", "build_support"}
        for name, paths in self.extra.items():
            self.assertEqual(self.base / paths[0] in consumer, name in expected, name)
        unrelated = set(entries["unrelated::lib"]["_dirs"])
        for name, paths in self.extra.items():
            self.assertEqual(self.base / paths[0] in unrelated, name == "unrelated", name)

    def test_mutating_embedded_input_invalidates_only_consuming_record(self):
        entries = self.inventory()
        consumer, unrelated = entries["consumer::lib"], entries["unrelated::lib"]
        before = vr.input_digest(consumer, fresh=True)
        untouched = vr.input_digest(unrelated, fresh=True)
        self.assertEqual(vr.derive(consumer, record(input_digest=before), before)["bucket"],
                         vr.BUCKET_GREEN)
        (self.base / self.extra["leaf"][0]).write_text('{"changed":true}\n')
        after = vr.input_digest(consumer, fresh=True)
        self.assertNotEqual(before, after)
        self.assertEqual(vr.derive(consumer, record(input_digest=before), after)["bucket"],
                         vr.BUCKET_UNKNOWN)
        self.assertEqual(untouched, vr.input_digest(unrelated, fresh=True))

    def test_workspace_gate_inherits_all_workspace_library_inputs(self):
        gate = self.inventory(with_gates=True)["gate::fixture"]
        for paths in self.extra.values():
            self.assertIn(self.base / paths[0], gate["_dirs"])



class ParserInputCoverage(unittest.TestCase):
    def test_parser_is_in_the_resolved_read_census(self):
        self.assertIn("clean-parser", vr.RESOLVED_SCAN_PACKAGES)

    def test_parser_inputs_are_attached_to_their_test_targets(self):
        expected = {
            "clean-parser::lib": {
                "crates/clean-olean/lean_worlds.tsv", "lean-toolchain",
                "reports/local-function-headers-2026-11-06/sources/let_rec_equation_class.lean",
                "tests/lean4_compat/lean4_tests", "tests/matp_bench",
            },
            "clean-parser::test::module_system_b_e2e": {
                "lean-toolchain", "tests/fixtures/module_spellings/modifier_matrix.tsv",
                "tests/fixtures/module_spellings/verdicts.tsv",
            },
            "clean-parser::test::parse_parity": {
                "tests/fixtures/parser_parity/README.md",
                "tests/fixtures/parser_parity/ground_truth.tsv",
            },
        }
        found = vr._crystal_extra_paths_owed()
        for target, paths in expected.items():
            self.assertEqual(found.get(target), paths, target)
            self.assertTrue(paths <= set(vr.TARGET_EXTRA_PATHS.get(target, ())), target)
        self.assertNotIn("clean-parser", vr.PACKAGE_EXTRA_PATHS,
                         "these cfg(test) inputs must not propagate to library consumers")

    def test_dropping_a_parser_input_is_refused(self):
        # `tests/matp_bench` is read through a path join, which only this hand
        # list covers. (Until the E3 fix-up this arm dropped `lean-toolchain`;
        # that read is an `include_str!` in `cfg(test)` code, which the
        # derivation now digests whatever the list says -- asserted below.)
        target = "clean-parser::lib"
        paths = dict(vr.TARGET_EXTRA_PATHS)
        paths[target] = [p for p in paths.get(target, ())
                         if p not in ("tests/matp_bench", "lean-toolchain")]
        with mock.patch.object(vr, "TARGET_EXTRA_PATHS", paths):
            problems = vr.check_crystal_extra_paths()
        self.assertTrue(any("clean-parser::lib reads tests/matp_bench" in p for p in problems),
                        problems)
        self.assertFalse(any("clean-parser::lib reads lean-toolchain" in p for p in problems),
                         problems)
        meta = vr.cargo_metadata()
        self.assertIn("lean-toolchain", vr.library_external_reads(
            vr.package_lib_root(meta, "clean-parser"), True))



class CheckerQualificationInputs(unittest.TestCase):
    CORE = "clean-olean::test::kcheck_core"
    SPEC = "clean-olean::test::kcheck_spec"

    def test_compiled_package_closures_are_declared(self):
        core = set(vr.TARGET_EXTRA_PATHS.get(self.CORE, ()))
        spec = set(vr.TARGET_EXTRA_PATHS.get(self.SPEC, ()))
        self.assertTrue({"lean-toolchain", "theories/cic_l", "theories/kcheck"} <= core)
        self.assertTrue({"lean-toolchain", "theories/cic_l", "theories/cic_l_model",
                         "theories/kcheck_spec"} <= spec)

    def test_fixture_order_theory_packages_are_covered(self):
        pin = (vr.REPO_ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
        fixtures = vr.REPO_ROOT / "crates/clean-olean/tests/fixtures/lean" / pin
        for target, family in [(self.CORE, "kcheck_core"), (self.SPEC, "kcheck_spec")]:
            lines = (fixtures / family / "ORDER").read_text().splitlines()
            theories = [parts[1] for line in lines
                        if (parts := line.partition("#")[0].split()) and parts[0] == "theory"]
            self.assertTrue(theories, family)
            declared = set(vr.TARGET_EXTRA_PATHS.get(target, ()))
            for theory in theories:
                self.assertIn(f"theories/{theory}", declared, (family, theory))

    def test_direct_statement_and_closure_pins_are_scanned(self):
        found = vr._crystal_extra_paths_owed()
        for target, package in [(self.CORE, "kcheck"), (self.SPEC, "kcheck_spec")]:
            pins = {f"theories/{package}/{p}" for p in
                    ("ORDER", "statement_pins.json", "axiom_closures.json")}
            self.assertTrue(pins <= found.get(target, set()), target)
            self.assertTrue(pins <= set(vr.TARGET_EXTRA_PATHS.get(target, ())), target)

    def test_theory_mutation_invalidates_exact_qualification_closure(self):
        base = Path(tempfile.mkdtemp(prefix="checker_inputs_", dir=_SANDBOX))
        subprocess.run(["git", "init", "-q", str(base)], check=True)
        crate = base / "crates/clean-olean"
        crate.mkdir(parents=True)
        (crate / "Cargo.toml").write_text("# fixture\n")
        packages = ["cic_l", "cic_l_model", "kcheck", "kcheck_spec"]
        for package in packages:
            path = base / "theories" / package / "Root.lean"
            path.parent.mkdir(parents=True)
            path.write_text("-- before\n")
        subprocess.run(["git", "-C", str(base), "add", "."], check=True)
        meta = {"packages": [{"name": "clean-olean", "manifest_path": str(crate / "Cargo.toml"),
                              "targets": [{"name": name, "kind": ["test"], "test": True}
                                          for name in ("kcheck_core", "kcheck_spec")]}]}
        with mock.patch.object(vr, "REPO_ROOT", base), \
                mock.patch.object(vr, "cargo_metadata", return_value=meta), \
                mock.patch.object(vr, "check_crystal_extra_paths", return_value=[]), \
                mock.patch.object(vr, "load_plan", return_value=None), \
                mock.patch.object(vr, "toolchain_id", return_value="fixture"):
            entries = {e["id"]: e for e in vr.build_inventory(["clean-olean"], with_gates=False)}
            expected = {"cic_l": {self.CORE, self.SPEC}, "cic_l_model": {self.SPEC},
                        "kcheck": {self.CORE}, "kcheck_spec": {self.SPEC}}
            for package, affected in expected.items():
                before = {key: vr.input_digest(entry, fresh=True) for key, entry in entries.items()}
                path = base / "theories" / package / "Root.lean"
                path.write_text("-- after\n")
                for key, entry in entries.items():
                    after = vr.input_digest(entry, fresh=True)
                    self.assertEqual(before[key] != after, key in affected, (package, key))
                    bucket = vr.derive(entry, record(target=key, input_digest=before[key]), after)["bucket"]
                    self.assertEqual(bucket, vr.BUCKET_UNKNOWN if key in affected else vr.BUCKET_GREEN)
                path.write_text("-- before\n")



class OleanBuildPinInput(unittest.TestCase):
    def test_workspace_pin_is_a_declared_library_input(self):
        self.assertIn("lean-toolchain", vr.PACKAGE_EXTRA_PATHS.get("clean-olean", ()))

    def test_pin_mutation_invalidates_library_and_consumer_but_not_unrelated(self):
        base = Path(tempfile.mkdtemp(prefix="olean_pin_", dir=_SANDBOX))
        subprocess.run(["git", "init", "-q", str(base)], check=True)
        packages = []
        for name in ("consumer", "clean-olean", "unrelated"):
            crate = base / "crates" / name
            crate.mkdir(parents=True)
            (crate / "Cargo.toml").write_text("# fixture\n")
            packages.append({
                "name": name, "manifest_path": str(crate / "Cargo.toml"),
                "dependencies": [{"name": "clean-olean", "kind": None}] if name == "consumer" else [],
                "targets": [{"name": name, "kind": ["lib"], "test": True}],
            })
        pin = base / "lean-toolchain"
        pin.write_text("leanprover/lean4:before\n")
        subprocess.run(["git", "-C", str(base), "add", "."], check=True)
        with mock.patch.object(vr, "REPO_ROOT", base), \
                mock.patch.object(vr, "cargo_metadata", return_value={"packages": packages}), \
                mock.patch.object(vr, "check_crystal_extra_paths", return_value=[]), \
                mock.patch.object(vr, "load_plan", return_value=None), \
                mock.patch.object(vr, "toolchain_id", return_value="fixture"):
            entries = vr.build_inventory(["consumer", "clean-olean", "unrelated"], with_gates=False)
            before = {e["id"]: vr.input_digest(e, fresh=True) for e in entries}
            pin.write_text("leanprover/lean4:after\n")
            for entry in entries:
                affected = entry["package"] != "unrelated"
                after = vr.input_digest(entry, fresh=True)
                self.assertEqual(before[entry["id"]] != after, affected, entry["id"])
                status = vr.derive(entry, record(target=entry["id"], input_digest=before[entry["id"]]),
                                   after)["bucket"]
                self.assertEqual(status, vr.BUCKET_UNKNOWN if affected else vr.BUCKET_GREEN)



class OleanWorldFixtureInputs(unittest.TestCase):
    def fixture_tree(self):
        root = Path(tempfile.mkdtemp(prefix="world_inputs_", dir=_SANDBOX))
        table = root / "crates/clean-olean/lean_worlds.tsv"
        table.parent.mkdir(parents=True)
        first = "tests/fixtures/olean/first.olean"
        second = "tests/fixtures/olean/second.olean"
        for name in (first, second):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"fixture")
        table.write_text(f"v1\toracle\tlean:v1\t{first}\n")
        return root, table, first, second

    def test_actual_world_fixtures_are_declared_library_inputs(self):
        table = vr.REPO_ROOT / "crates/clean-olean/lean_worlds.tsv"
        fixtures = {name for line in table.read_text().splitlines()
                    if line and not line.startswith("#")
                    for name in line.split("\t")[3].split()}
        self.assertTrue(fixtures)
        self.assertTrue(fixtures <= set(vr.PACKAGE_EXTRA_PATHS.get("clean-olean", ())))

    def test_new_table_fixture_requires_a_matching_input_declaration(self):
        root, table, first, second = self.fixture_tree()
        with mock.patch.object(vr, "PACKAGE_EXTRA_PATHS", {"clean-olean": [first]}):
            self.assertEqual(vr._check_olean_world_inputs(root), [])
            table.write_text(f"v1\toracle\tlean:v1\t{first} {second}\n")
            errors = vr._check_olean_world_inputs(root)
            self.assertTrue(any(second in error and "PACKAGE_EXTRA_PATHS" in error for error in errors), errors)
        with mock.patch.object(vr, "PACKAGE_EXTRA_PATHS", {"clean-olean": [first, second]}):
            self.assertEqual(vr._check_olean_world_inputs(root), [])
            (root / second).unlink()
            self.assertTrue(any(second in e and "missing" in e for e in vr._check_olean_world_inputs(root)))

    def test_bad_or_external_table_paths_are_refused(self):
        root, table, _, _ = self.fixture_tree()
        for content in ("invalid\n", "v1\toracle\tlean:v1\t../outside.olean\n",
                        "v1\toracle\tlean:v1\t/outside.olean\n",
                        "v1\toracle\tlean:v1\t\n"):
            table.write_text(content)
            self.assertTrue(vr._check_olean_world_inputs(root), content)

    def test_ignored_fixture_cannot_be_counted_as_a_digest_input(self):
        root, table, first, second = self.fixture_tree()
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        (root / ".gitignore").write_text(second + "\n")
        table.write_text(f"v1\toracle\tlean:v1\t{first} {second}\n")
        with mock.patch.object(vr, "PACKAGE_EXTRA_PATHS", {"clean-olean": [first, second]}):
            errors = vr._check_olean_world_inputs(root)
        self.assertTrue(any(second in e and "git-visible" in e for e in errors), errors)

    def test_world_input_failure_reaches_the_inventory_gate(self):
        with mock.patch.object(vr, "_check_olean_world_inputs", return_value=["missing world fixture"]):
            with self.assertRaisesRegex(SystemExit, "missing world fixture"):
                vr.build_inventory([], with_gates=False)



class ReleaseInferenceRow(unittest.TestCase):
    ID = "clean-kernel::release::test::release_infer_parity"

    def row(self):
        rows = [row for row in vr.RELEASE_PROFILE_TARGETS if row["id"] == self.ID]
        self.assertEqual(len(rows), 1, "the release-only parity target needs a release suite row")
        return rows[0]

    def test_release_row_requires_every_parity_test_in_the_source(self):
        import rust_modules
        row = self.row()
        source = vr.REPO_ROOT / "crates/clean-kernel/tests/release_infer_parity.rs"
        tests = {name for name, attrs in rust_modules.fn_items(
            source, "", reach=rust_modules.Reach.POSSIBLE) if "test" in attrs}
        self.assertTrue(tests)
        self.assertEqual(set(row["_must_pass"]), tests)
        self.assertEqual(row["profile"], vr.PROFILE_RELEASE)
        self.assertEqual(vr.check_profiles([row]), [])
        self.assertEqual(row["argv"][row["argv"].index("--test") + 1], "release_infer_parity")

    def test_replacement_removes_only_the_empty_debug_row_and_keeps_its_inputs(self):
        row = self.row()
        self.assertEqual(row["_replaces_debug_target"], "release_infer_parity")
        meta = {"packages": [{"name": "clean-kernel", "manifest_path": str(vr.REPO_ROOT / "crates/clean-kernel/Cargo.toml"),
                              "targets": [{"name": name, "kind": ["test"], "test": True}
                                          for name in ("release_infer_parity", "ordinary")]}]}
        # The synthetic targets have no sources, so the two coverage checks,
        # which read them (EveryLibTestCompilesInARow), have nothing to judge.
        with mock.patch.object(vr, "cargo_metadata", return_value=meta), \
                mock.patch.object(vr, "check_crystal_extra_paths", return_value=[]), \
                mock.patch.object(vr, "lib_test_coverage_problems", return_value=[]), \
                mock.patch.object(vr, "compiled_out_problems", return_value=[]), \
                mock.patch.object(vr, "RELEASE_PROFILE_TARGETS", [row]), \
                mock.patch.object(vr, "WORKSPACE_GATES", []), \
                mock.patch.object(vr, "TARGET_EXTRA_PATHS", {
                    "clean-kernel::test::release_infer_parity": ["data/probe.json"],
                    "clean-kernel::test::None": ["data/unrelated.json"]}):
            entries = {entry["id"]: entry for entry in vr.build_inventory(["clean-kernel"])}
        self.assertNotIn("clean-kernel::test::release_infer_parity", entries)
        self.assertIn("clean-kernel::test::ordinary", entries)
        self.assertIn(vr.REPO_ROOT / "data/probe.json", entries[self.ID]["_dirs"])
        self.assertNotIn(vr.REPO_ROOT / "data/unrelated.json", entries["clean-kernel::test::ordinary"]["_dirs"])
        for argv in (row["argv"] + ["--", "a_filter"], row["argv"] + ["--", "--skip", "a_test"]):
            self.assertTrue(vr.check_profiles([dict(row, argv=argv)]))
        self.assertTrue(vr.check_profiles([dict(row, _replaces_debug_target="another_target")]))
        no_profile = {key: value for key, value in row.items() if key != "profile"}
        no_profile["argv"] = [arg for arg in row["argv"] if arg != "--release"]
        self.assertTrue(vr.check_profiles([no_profile]))

    def test_a_partial_parity_run_cannot_be_green(self):
        row = self.row()
        tests = row["_must_pass"]
        complete = record(target=self.ID, input_digest="fixture", profile="release",
                          passed_tests=tests,
                          counts={"passed": len(tests), "failed": 0, "ignored": 0, "result_lines": 1})
        self.assertEqual(vr.derive(row, complete, "fixture")["bucket"], vr.BUCKET_GREEN)
        partial = dict(complete, passed_tests=tests[:-1],
                       counts={"passed": len(tests) - 1, "failed": 0, "ignored": 0, "result_lines": 1})
        self.assertEqual(vr.derive(row, partial, "fixture")["bucket"], vr.BUCKET_UNKNOWN)
        self.assertEqual(vr.derive(row, dict(complete, profile="dev"), "fixture")["bucket"],
                         vr.BUCKET_UNKNOWN)


if __name__ == "__main__":
    unittest.main(verbosity=2)
