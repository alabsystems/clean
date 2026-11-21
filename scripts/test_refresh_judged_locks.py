#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Self-test of scripts/refresh_judged_locks.py, the version commit's lock hook.

Run by scripts/check_script_selftests.sh (the scripts/test_* glob). The fixture
arms reuse the pin transaction's synthetic repository, its runner workspaces
and its stand-in Targo (scripts/test_bump_trust_ir_pin.py), with the REAL gate
beside the script: its lock selection and its `--locked` leg are the ones under
test. Nothing here compiles or resolves a real dependency.

  * VERSION COMMIT   the tree `pub bump` leaves before its hook: a workspace
                     crate's manifest at the next version, every lock recording
                     the last one, and a runner lock an earlier version commit
                     had already left behind (`00e83f3313`, repaired by hand in
                     `63ff84d574`). The hook rewrites every lock the gate
                     judges and no other, changes tracked files only, and a
                     second run changes nothing.
  * ALL OR NONE      a refresh that fails after earlier locks were rewritten,
                     and a refresh that exits 0 leaving a lock stale (refused
                     by the gate's own leg), each put every lock back as found,
                     an uncommitted edit included.
  * UNTRACKED LEG    a selected lock tracked under another name, whose
                     workspace `Cargo.lock` no commit carries, is refused
                     before the frontend is asked anything.
  * WIRING           publish/config.sh names the script as the flat
                     POST_BUMP_CMD_DEFAULT the publication engine reads, and on
                     the live tree the hook's locks are the gate's selection:
                     the root lock and every AY-bearing runner lock among them.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

import check_workspace_dependency_boundary as boundary  # noqa: E402
import refresh_judged_locks as hook  # noqa: E402
import test_bump_trust_ir_pin as pins  # noqa: E402

SCRIPT = SCRIPTS / "refresh_judged_locks.py"
JUDGED = ["Cargo.lock", "bench-runner/Cargo.lock", "cli-runner/Cargo.lock",
          "scripts/crystal_a2_project/Cargo.lock"]


def kernel_row(version: str) -> str:
    return f'[[package]]\nname = "clean-kernel"\nversion = "{version}"\n'


class VersionCommit(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temp = Path(tempfile.mkdtemp(prefix="clean-lock-hook-"))
        cls.tools = cls.temp / "tools"
        cls.tools.mkdir()
        cls.fake_targo = cls.tools / "targo"
        cls.fake_targo.write_text(pins.FAKE_TARGO)
        cls.fake_targo.chmod(0o755)

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.temp, ignore_errors=True)

    git = staticmethod(pins.Driver.git)

    def bumped(self) -> dict[str, str]:
        """The tree `pub bump` hands its hook: clean-kernel's manifest at 0.9.1,
        the root, cli-runner and notes locks recording 0.9.0, and bench-runner's
        still at the 0.8.0 an earlier version commit left. `notes` records no
        Git source, so the gate does not judge its lock."""
        files = pins.fixture()
        pins.satellite(files, "bench-runner", kernel="0.8.0")
        pins.satellite(files, "cli-runner")
        pins.satellite(files, "notes", pinned=False)
        kernel = "crates/clean-kernel/Cargo.toml"
        files[kernel] = files[kernel].replace('version = "0.9.0"', 'version = "0.9.1"')
        return files

    def repo(self, files: dict[str, str]) -> Path:
        root = pins.Driver.repo(self, files)  # type: ignore[arg-type]
        shutil.copy(SCRIPT, root / "scripts")
        self.git(root, "add", "-A", "scripts")
        self.git(root, "commit", "-q", "-m", "the lock hook")
        return root

    def snapshot(self, root: Path) -> dict[str, bytes]:
        out = subprocess.run(["git", "-C", str(root), "ls-files", "-z"], capture_output=True, check=True).stdout
        return {name: (root / name).read_bytes() for name in out.decode().split("\0") if name}

    def targo_log(self, root: Path) -> list[str]:
        """The stand-in's calls, as `locked=<0|1> <manifest>`."""
        log = root.with_suffix(".targo.log")
        if not log.exists():
            return []
        return [f"{call.split()[1]} {call.split()[3]}" for call in log.read_text().splitlines()]

    def run_hook(self, root: Path, mode: str = "ok", *args: str,
                 on_path: bool = False) -> subprocess.CompletedProcess:
        env = dict(os.environ, FAKE_TARGO_MODE=mode, FAKE_TARGO_LOG=str(root.with_suffix(".targo.log")))
        env.pop("CLEAN_TARGO", None)
        chosen = [] if on_path else ["--targo", str(self.fake_targo)]
        if on_path:
            env["PATH"] = f"{self.tools}{os.pathsep}{env.get('PATH', '')}"
        return subprocess.run([sys.executable, "-B", str(root / "scripts" / SCRIPT.name), *chosen, *args],
                              cwd=root, env=env, capture_output=True, text=True, check=False)

    def test_version_commit_refreshes_every_judged_lock_and_no_other(self) -> None:
        root = self.repo(self.bumped())
        before = self.snapshot(root)
        result = self.run_hook(root)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"judged locks: {' '.join(JUDGED)}\n", result.stdout)
        for name in JUDGED[:3]:
            self.assertIn(f"refreshed {name}\n", result.stdout)
        self.assertIn("refreshed scripts/crystal_a2_project/Cargo.lock (unchanged)\n", result.stdout)
        self.assertIn("every judged lock accepted under --locked", result.stdout)
        after = self.snapshot(root)
        for name in JUDGED[:3]:
            self.assertIn(kernel_row("0.9.1"), after[name].decode(), name)
        # What the version commit carries beside the manifest: tracked locks only.
        self.assertEqual(sorted(name for name in before if after[name] != before[name]), JUDGED[:3])
        self.assertEqual(self.git(root, "status", "--porcelain"),
                         "".join(f" M {name}\n" for name in JUDGED[:3]))
        # `notes` is stale too and is no lock of the gate's: never asked about.
        self.assertIn(kernel_row("0.9.0"), after["notes/Cargo.lock"].decode())
        log = self.targo_log(root)
        self.assertNotIn("notes/", "\n".join(log))
        manifests = [name.replace("Cargo.lock", "Cargo.toml") for name in JUDGED]
        self.assertEqual(log[:4], [f"locked=0 {manifest}" for manifest in manifests])
        self.assertEqual(sorted(log[4:]), [f"locked=1 {manifest}" for manifest in manifests])
        # Idempotent: nothing left to rewrite, and the gate's leg is asked again.
        result = self.run_hook(root)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in JUDGED:
            self.assertIn(f"refreshed {name} (unchanged)\n", result.stdout)
        self.assertEqual(self.snapshot(root), after)

    def test_frontend_is_the_targo_on_path_when_none_is_named(self) -> None:
        """How `pub bump` runs the hook: no option, the cycle's `targo` on PATH."""
        root = self.repo(self.bumped())
        result = self.run_hook(root, on_path=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"lock refresh frontend: {self.fake_targo}\n", result.stdout)
        self.assertEqual(self.git(root, "status", "--porcelain"),
                         "".join(f" M {name}\n" for name in JUDGED[:3]))

    def test_a_failed_refresh_puts_back_every_lock_already_rewritten(self) -> None:
        root = self.repo(self.bumped())
        edited = root / "bench-runner/Cargo.lock"
        edited.write_text(edited.read_text() + "# an uncommitted note\n")
        before = self.snapshot(root)
        result = self.run_hook(root, "fail:cli-runner")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("FAIL: cli-runner/Cargo.lock refresh failed (targo metadata exited 101)", result.stderr)
        self.assertIn("RESTORED -- every lock is as it was found.", result.stderr)
        self.assertNotIn("accepted", result.stdout)
        self.assertIn("cli-runner/Cargo.lock: not refreshed offline (fake targo: resolver refused); "
                      "asking with the network allowed", result.stderr)
        # The root and bench-runner locks were rewritten before the failure, and
        # the failing lock was asked offline, then with the network allowed.
        self.assertEqual(self.targo_log(root),
                         ["locked=0 Cargo.toml", "locked=0 bench-runner/Cargo.toml",
                          "locked=0 cli-runner/Cargo.toml", "locked=0 cli-runner/Cargo.toml"])
        self.assertEqual(self.snapshot(root), before)
        self.assertEqual(self.git(root, "status", "--porcelain"), " M bench-runner/Cargo.lock\n")

    def test_a_lock_the_refresh_leaves_stale_is_refused_by_the_gates_leg_and_restored(self) -> None:
        """A resolver that exits 0 without rewriting a stale lock: the verdict
        is the gate's own `--locked` leg, in its words, and nothing is kept."""
        root = self.repo(self.bumped())
        before = self.snapshot(root)
        result = self.run_hook(root, "leave:bench-runner")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("a Git-pinned lock does not resolve under targo metadata --locked", result.stderr)
        self.assertIn("  bench-runner/Cargo.lock: error: cannot update the lock file", result.stderr)
        self.assertIn("RESTORED -- every lock is as it was found.", result.stderr)
        self.assertNotIn("refreshed", result.stdout)
        self.assertEqual(self.snapshot(root), before)
        self.assertEqual(self.git(root, "status", "--porcelain"), "")

    def test_a_lock_no_commit_would_carry_is_refused_before_the_frontend_is_asked(self) -> None:
        files = self.bumped()
        pins.satellite(files, "odd")
        files["odd/pinned.Cargo.lock"] = files.pop("odd/Cargo.lock")
        root = self.repo(files)
        before = self.snapshot(root)
        for args in ((), ("--list",)):
            with self.subTest(args=args):
                result = self.run_hook(root, "ok", *args)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("REFUSED: odd/Cargo.lock is not a tracked file "
                              "(the lock Cargo keeps for tracked odd/pinned.Cargo.lock)", result.stderr)
                self.assertIn("Nothing was written.", result.stderr)
                self.assertEqual(self.targo_log(root), [])
                self.assertEqual(self.snapshot(root), before)
                self.assertEqual(self.git(root, "status", "--porcelain"), "")

    def test_list_names_the_locks_and_changes_nothing(self) -> None:
        root = self.repo(self.bumped())
        before = self.snapshot(root)
        result = self.run_hook(root, "ok", "--list")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines(), JUDGED)
        self.assertEqual(self.targo_log(root), [])
        self.assertEqual(self.snapshot(root), before)


class Wiring(unittest.TestCase):
    def test_publish_config_names_the_hook_as_the_engine_reads_it(self) -> None:
        """`pub bump` reads the committed file for one flat line (it does not
        source it) and runs the value with `bash -c` in the checkout's root."""
        hooks = [match[1] for line in (ROOT / "publish/config.sh").read_text().splitlines()
                 if (match := re.fullmatch(r'POST_BUMP_CMD_DEFAULT="(.*)"', line))]
        self.assertEqual(hooks, [f"python3 -B scripts/{SCRIPT.name}"])
        self.assertTrue((ROOT / "scripts" / SCRIPT.name).is_file())

    def test_live_tree_hook_locks_are_the_gates_selection(self) -> None:
        texts = hook.tracked_lock_texts()
        legs = set(hook.lock_legs(texts))
        self.assertEqual(legs, set(boundary.git_pinned_lock_paths(texts)),
                         "every selected lock is its workspace's own Cargo.lock today")
        self.assertIn("Cargo.lock", legs)
        runners = {str(path.relative_to(ROOT)) for path in boundary.REQUIRED_AY_LOCK_INVENTORIES}
        self.assertGreater(len(runners - {"Cargo.lock"}), 0, runners)
        self.assertLessEqual(runners, legs)


if __name__ == "__main__":
    unittest.main()
