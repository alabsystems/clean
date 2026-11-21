#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Exercise the W0 gate without Cargo using the gate's Python 3.11 or newer."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent
COMMAND = [
    "targo", "--unverified", "test", "--locked", "--offline",
    "-p", "clean-cli", "-p", "clean", "--lib", "--test", "w0_scoreboard_cli",
    "--message-format=json", "--", "cmd_evidence::",
]
FIXED_TEST = "w0_scoreboard_self_test"
SUCCESS = "SELF_PROOF_SCOREBOARD=ok the record matches its sources"
BOARD = "data/self_proof_scoreboard.json"
COVERAGE = "data/kcheck_coverage.json"
RESULT_ENV = "CLEAN_W0_GATE_RESULT"
QUALIFICATION_SCRIPTS = (
    "run_w0_scoreboard_gate.sh",
    "self_proof_fleet_w0.py",
    "kcheck_coverage_export.py",
    "cargo_test_nonvacuous.sh",
)

STUB = '''\
import json
import os
from pathlib import Path
import subprocess
import sys

role, *args = sys.argv[1:]
root = Path(os.environ["W0_TEST_ROOT"])
mode = os.environ["W0_TEST_MODE"]
with (root / "calls.jsonl").open("a") as log:
    log.write(json.dumps({
        "role": role, "args": args, "cwd": str(Path.cwd()),
        "stack": os.environ.get("RUST_MIN_STACK"),
    }) + "\\n")

def summary(count):
    print(f"running {count} tests")
    print(f"test result: ok. {count} passed; 0 failed; 0 ignored; "
          "0 measured; 0 filtered out; finished in 0.01s")

if role == "cargo":
    print((root / "cargo.jsonl").read_text(), end="")
    summary(0 if mode == "unit-empty" else 1)
    if mode == "cargo-fail":
        sys.exit(22)
    if mode == "head-moves":
        subprocess.run(["git", "update-ref", "HEAD", os.environ["W0_TEST_MOVED_HEAD"]],
                       cwd=root, check=True)
elif role == "fixed":
    if mode == "fixed-fail":
        print("fixed fixture refused", file=sys.stderr)
        sys.exit(23)
    summary(0 if mode == "fixed-empty" else 1)
elif args == ["--version"]:
    head = "0" * 40 if mode == "stale-version" else os.environ["W0_TEST_HEAD"]
    print(f"clean 0.9.4+g{head}")
elif mode == "board-fail":
    print("saved board refused", file=sys.stderr)
    sys.exit(1)
elif mode == "board-bad-output":
    print("unexpected success")
else:
    if mode == "board-dirties-source":
        (root / "tracked-evidence.txt").write_text("changed during saved-board check\\n")
    if mode == "board-moves-head":
        subprocess.run(["git", "update-ref", "HEAD", os.environ["W0_TEST_MOVED_HEAD"]],
                       cwd=root, check=True)
    if mode == "board-claims-result":
        with (root / os.environ["CLEAN_W0_GATE_RESULT"]).open("xb") as result:
            result.write(b"other writer's result\\n")
    print("SELF_PROOF_SCOREBOARD=ok the record matches its sources")
    if mode == "board-stderr":
        print("unexpected stderr", file=sys.stderr)
'''


class W0GateTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="w0-gate-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve() / "checkout with spaces"
        self.root.mkdir()
        self.result_path = self.root / "W0 gate result.json"
        self.env = {
            key: value for key, value in os.environ.items()
            if not key.startswith("GIT_") and key not in {"RUST_MIN_STACK", RESULT_ENV}
        }
        self.env.update(
            GIT_CONFIG_NOSYSTEM="1",
            GIT_CONFIG_GLOBAL=os.devnull,
            GIT_TERMINAL_PROMPT="0",
            W0_TEST_ROOT=str(self.root),
            W0_TEST_PYTHON=str(Path(sys.executable).resolve()),
        )
        self.git("init", "-q")
        self.write("Cargo.toml", '[workspace]\n[workspace.package]\nversion = "0.9.4"\n')
        self.write("crates/clean/Cargo.toml", '[package]\nname = "clean"\nversion.workspace = true\n')
        self.write("crates/clean-cli/Cargo.toml", '[package]\nname = "clean-cli"\nversion.workspace = true\n')
        self.write("crates/clean/src/bin/clean.rs", "fn main() {}\n")
        self.write("crates/clean/tests/w0_scoreboard_cli.rs", "// fixed integration harness\n")
        self.write("tracked-evidence.txt", "original\n")
        for relative in (BOARD, COVERAGE):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(SCRIPTS.parent / relative, target)
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in QUALIFICATION_SCRIPTS:
            shutil.copy2(SCRIPTS / name, scripts)
        self.git("add", ".")
        self.git(
            "-c", "user.name=W0 fixture", "-c", "user.email=w0@example.invalid",
            "-c", "commit.gpgsign=false", "-c", "core.hooksPath=" + os.devnull,
            "commit", "-qm", "Fixture inputs",
        )
        self.env["W0_TEST_HEAD"] = self.git("rev-parse", "HEAD").stdout.strip()

        self.write("stub.py", STUB)
        self.driver = self.executable("fake-targo-driver", "cargo")
        self.clean = self.executable("target/debug/clean", "clean")
        self.fixed = self.executable(
            "target/debug/build/clean/abcd/out/w0_scoreboard_cli-abcd", "fixed",
        )
        self.env.update(
            CARGO_TARGET_DIR=str(self.root / "target"),
            CARGO_BUILD_BUILD_DIR=str(self.root / "target"),
        )
        self.cargo_rows = [
            self.artifact(self.clean, "clean", "bin", "src/bin/clean.rs"),
            self.artifact(self.fixed, "w0_scoreboard_cli", "test", "tests/w0_scoreboard_cli.rs"),
        ]

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def executable(self, relative, role):
        path = self.write(
            relative,
            '#!/bin/sh\nexec "$W0_TEST_PYTHON" "$W0_TEST_ROOT/stub.py" ' + role + ' "$@"\n',
        )
        path.chmod(0o700)
        return path

    def git(self, *args):
        return subprocess.run(
            ["git", *args], cwd=self.root, env=self.env, check=True,
            capture_output=True, text=True, timeout=10,
        )

    def artifact(self, path, name, kind, source):
        package = self.root / "crates/clean"
        return {
            "reason": "compiler-artifact",
            "package_id": f"path+{package.as_uri()}#0.9.4",
            "manifest_path": str(package / "Cargo.toml"),
            "target": {
                "name": name, "kind": [kind], "crate_types": ["bin"],
                "src_path": str(package / source), "test": True,
            },
            "profile": {"test": kind == "test"},
            "executable": str(path),
            "filenames": [str(path)],
            "fresh": False,
            "trust_compile_mode": "test" if kind == "test" else "build",
            "trust_compile_kind": "host",
            "trust_executable_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        }

    def run_gate(self, mode="pass", *, rows=None, finish=True, extra="", environment=None):
        if rows is None:
            rows = self.cargo_rows
        output = "".join(json.dumps(row) + "\n" for row in rows) + extra
        if finish is not None:
            output += json.dumps({"reason": "build-finished", "success": finish}) + "\n"
        self.write("cargo.jsonl", output)
        (self.root / "calls.jsonl").unlink(missing_ok=True)
        return subprocess.run(
            [
                "/bin/bash", "scripts/run_w0_scoreboard_gate.sh",
                self.env["W0_TEST_PYTHON"], str(self.driver), *COMMAND,
            ],
            cwd=self.root, env=dict(self.env, W0_TEST_MODE=mode, **(environment or {})),
            capture_output=True, text=True, timeout=20,
        )

    def calls(self):
        path = self.root / "calls.jsonl"
        if not path.is_file():
            return []
        return [
            json.loads(line)
            for line in path.read_text(encoding="utf-8").splitlines()
        ]

    def following_commit(self):
        tree = self.git("rev-parse", "HEAD^{tree}").stdout.strip()
        return self.git(
            "-c", "user.name=W0 fixture", "-c", "user.email=w0@example.invalid",
            "commit-tree", tree, "-p", self.env["W0_TEST_HEAD"], "-m", "Move HEAD during the gate",
        ).stdout.strip()

    def assert_refusal(self, result, roles, diagnostic=None):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([call["role"] for call in self.calls()], roles)
        self.assertNotIn(SUCCESS, result.stdout)
        if diagnostic is not None:
            self.assertIn(diagnostic, result.stderr)

    def test_dirty_checkout_runs_one_cargo_command_and_both_selected_binaries(self):
        self.write("tracked-evidence.txt", "working-tree change\n")
        self.assertEqual(self.git("diff", "--name-only").stdout.strip(), "tracked-evidence.txt")
        result = self.run_gate()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = self.calls()
        self.assertEqual([call["role"] for call in calls], ["cargo", "clean", "fixed", "clean"])
        cargo, version, fixed, board = calls
        self.assertEqual(cargo["args"], COMMAND[1:])
        self.assertEqual(cargo["cwd"], str(self.root))
        self.assertEqual(fixed["args"], ["--exact", FIXED_TEST, "--color", "never"])
        self.assertEqual(fixed["cwd"], str(self.root / "crates/clean"))
        self.assertEqual(fixed["stack"], "67108864")
        self.assertEqual(version["args"], ["--version"])
        self.assertEqual(
            board["args"],
            ["evidence", "status", "--scoreboard", "--check", "--repo-root", str(self.root)],
        )
        self.assertIn(SUCCESS, result.stdout)
        self.assertFalse(self.result_path.exists())

    def test_opt_in_gate_result_binds_the_source_exact_artifact_and_cargo_log(self):
        normal, fixed = self.cargo_rows
        normal = dict(normal, fixture_metadata={"retained_cargo_field": ["original value"]})
        result = self.run_gate(rows=[normal, fixed], environment={RESULT_ENV: self.result_path.name})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([call["role"] for call in self.calls()], ["cargo", "clean", "fixed", "clean"])
        self.assertIn(SUCCESS, result.stdout)
        cargo_log = (self.root / "cargo.jsonl").read_bytes() + (
            b"running 1 tests\n"
            b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n"
            b"[w0-evidence] NONVACUOUS=ok result_lines=1 nonempty=1\n"
        )
        head = self.env["W0_TEST_HEAD"]
        self.assertEqual(json.loads(self.result_path.read_bytes()), {
            "schema": "clean.w0_gate_result.v1",
            "source_checkout": str(self.root),
            "source_commit": head,
            "source_tree": self.git("rev-parse", "HEAD^{tree}").stdout.strip(),
            "board_sha256": hashlib.sha256((self.root / BOARD).read_bytes()).hexdigest(),
            "coverage_sha256": hashlib.sha256((self.root / COVERAGE).read_bytes()).hexdigest(),
            "executable": str(self.clean),
            "executable_sha256": hashlib.sha256(self.clean.read_bytes()).hexdigest(),
            "version": f"clean 0.9.4+g{head}",
            "cargo_artifact": normal,
            "cargo_log_sha256": hashlib.sha256(cargo_log).hexdigest(),
            "qualification_sha256": {
                f"scripts/{name}": hashlib.sha256((self.root / "scripts" / name).read_bytes()).hexdigest()
                for name in QUALIFICATION_SCRIPTS
            },
        })

    def test_opt_in_gate_result_refuses_existing_destination_before_launch(self):
        original = b"preexisting gate result\n"
        self.result_path.write_bytes(original)
        result = self.run_gate(environment={RESULT_ENV: str(self.result_path)})
        self.assert_refusal(result, [], "exists")
        self.assertEqual(self.result_path.read_bytes(), original)

    def test_opt_in_gate_result_preserves_a_destination_created_during_the_check(self):
        result = self.run_gate("board-claims-result", environment={RESULT_ENV: self.result_path.name})
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([call["role"] for call in self.calls()], ["cargo", "clean", "fixed", "clean"])
        self.assertIn("W0_GATE_RESULT=invalid", result.stderr)
        self.assertEqual(self.result_path.read_bytes(), b"other writer's result\n")

    def test_opt_in_gate_result_refuses_dirty_source_before_launch(self):
        self.write("tracked-evidence.txt", "working-tree change\n")
        result = self.run_gate(environment={RESULT_ENV: str(self.result_path)})
        self.assert_refusal(result, [], "source has dirty tracked files")
        self.assertFalse(self.result_path.exists())

    def test_opt_in_gate_result_is_absent_on_board_refusal_or_late_source_movement(self):
        moved_head = self.following_commit()
        cases = (
            ("board-fail", "W0_SAVED_BOARD=invalid"),
            ("board-dirties-source", "source has dirty tracked files"),
            ("board-moves-head", "HEAD changed"),
        )
        for mode, diagnostic in cases:
            with self.subTest(mode=mode):
                try:
                    result = self.run_gate(mode, environment={
                        RESULT_ENV: str(self.result_path), "W0_TEST_MOVED_HEAD": moved_head,
                    })
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual([call["role"] for call in self.calls()], ["cargo", "clean", "fixed", "clean"])
                    self.assertIn(diagnostic, result.stderr)
                    self.assertFalse(self.result_path.exists())
                finally:
                    self.write("tracked-evidence.txt", "original\n")

    def test_failed_or_empty_evidence_tests_refuse_before_running_binaries(self):
        for mode in ("unit-empty", "cargo-fail"):
            with self.subTest(mode=mode):
                self.assert_refusal(self.run_gate(mode), ["cargo"])

    def test_malformed_or_ambiguous_cargo_stream_refuses_before_running_binaries(self):
        cases = (
            ({"extra": '{"reason":"compiler-artifact","target":\n'}, "Expecting value"),
            ({"extra": '{"reason":"compiler-artifact","reason":"build-finished","success":true}\n'},
             "a key is written twice in one object"),
            ({"extra": '{"reason":"build-finished","success":true}\n'}, "expected one successful Cargo build"),
            ({"rows": [*self.cargo_rows, self.cargo_rows[1]]}, "expected one Cargo artifact for w0_scoreboard_cli"),
            ({"finish": None}, "expected one successful Cargo build"),
            ({"finish": False}, "expected one successful Cargo build"),
        )
        for changes, diagnostic in cases:
            with self.subTest(changes=changes):
                self.assert_refusal(
                    self.run_gate(**changes), ["cargo"], f"W0_ARTIFACT=invalid {diagnostic}",
                )

    def test_wrong_artifact_binding_refuses_before_running_binaries(self):
        clean, fixed = self.cargo_rows
        replacements = (
            ({"trust_executable_sha256": "0" * 64}, "executable digest differs from Targo artifact"),
            ({"profile": {"test": False}}, "expected one Cargo artifact"),
            ({"package_id": f"path+{(self.root / 'foreign/clean').as_uri()}#0.9.4"},
             "wrong Cargo owner or source"),
            ({"target": dict(fixed["target"], src_path=str(self.root / "crates/clean/src/bin/clean.rs"))},
             "wrong Cargo owner or source"),
        )
        for change, diagnostic in replacements:
            with self.subTest(field=next(iter(change))):
                self.assert_refusal(
                    self.run_gate(rows=[clean, dict(fixed, **change)]),
                    ["cargo"], f"W0_ARTIFACT=invalid {diagnostic} for w0_scoreboard_cli",
                )

    def test_foreign_artifact_cannot_also_claim_the_fixed_executable(self):
        foreign = dict(
            self.cargo_rows[1], manifest_path=str(self.root / "foreign/Cargo.toml"),
        )
        self.assert_refusal(
            self.run_gate(rows=[*self.cargo_rows, foreign]),
            ["cargo"], "W0_ARTIFACT=invalid multiple Cargo owners for w0_scoreboard_cli",
        )

    def test_symlink_executable_refuses_even_when_its_bytes_match(self):
        original = self.fixed.with_name("original")
        self.fixed.rename(original)
        self.fixed.symlink_to(original)
        self.assert_refusal(
            self.run_gate(), ["cargo"], "W0_ARTIFACT=invalid invalid executable path for w0_scoreboard_cli",
        )

    def test_head_movement_during_cargo_refuses_before_running_binaries(self):
        next_head = self.following_commit()
        result = self.run_gate("head-moves", environment={"W0_TEST_MOVED_HEAD": next_head})
        self.assertEqual(self.git("rev-parse", "HEAD").stdout.strip(), next_head)
        self.assert_refusal(result, ["cargo"], "W0_ARTIFACT=invalid checkout HEAD changed")

    def test_fixed_test_refusal_stops_before_the_board_check(self):
        for mode in ("fixed-empty", "fixed-fail"):
            with self.subTest(mode=mode):
                self.assert_refusal(self.run_gate(mode), ["cargo", "clean", "fixed"])

    def test_stale_clean_version_stops_before_fixed_and_board_checks(self):
        self.assert_refusal(
            self.run_gate("stale-version"), ["cargo", "clean"],
            "W0_ARTIFACT=invalid Clean version differs from the checkout",
        )

    def test_board_refusal_and_unexpected_success_output_are_red(self):
        for mode in ("board-fail", "board-bad-output", "board-stderr"):
            with self.subTest(mode=mode):
                result = self.run_gate(mode)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual([call["role"] for call in self.calls()], ["cargo", "clean", "fixed", "clean"])
                self.assertIn("W0_SAVED_BOARD=invalid", result.stderr)


if __name__ == "__main__":
    unittest.main()
