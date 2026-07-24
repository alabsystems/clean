# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Regression gate for machine-portable Isabelle and Trust operations scripts."""

from __future__ import annotations

import os
from pathlib import Path
import stat
import subprocess
import tempfile
import unittest


REPO = Path(__file__).resolve().parent.parent
ISABELLE_SCRIPTS = REPO / "scripts" / "isabelle"


class IsabelleOpsPortabilityTests(unittest.TestCase):
    def test_trust_coverage_gate_never_rewrites_the_lockfile(self) -> None:
        ratchet = (REPO / "scripts" / "trust_verify_ratchet.sh").read_text(
            encoding="utf-8"
        )
        self.assertNotIn("git checkout -- Cargo.lock", ratchet)
        self.assertIn("cargo build --locked --manifest-path", ratchet)

    def test_shipped_ops_files_have_no_machine_specific_execution_paths(self) -> None:
        forbidden = (
            "$HOME",
            "$HOME",
            "sed -i ''",
            "stat -f%z",
        )
        candidates = sorted(
            path
            for path in ISABELLE_SCRIPTS.rglob("*")
            if path.is_file() and path.suffix in {".json", ".py", ".sh"}
        )
        self.assertTrue(candidates, "expected shipped Isabelle operations files")
        violations: list[str] = []
        for path in candidates:
            text = path.read_text(encoding="utf-8")
            for marker in forbidden:
                if marker in text:
                    violations.append(f"{path.relative_to(REPO)}: {marker}")
        self.assertEqual(violations, [], "\n".join(violations))

    def test_all_isabelle_shell_scripts_parse_with_bash(self) -> None:
        scripts = sorted(ISABELLE_SCRIPTS.glob("*.sh"))
        self.assertTrue(scripts, "expected Isabelle shell scripts")
        for script in scripts:
            proc = subprocess.run(
                ["bash", "-n", str(script)],
                cwd=REPO,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                proc.returncode,
                0,
                f"{script.relative_to(REPO)} failed bash -n:\n{proc.stderr}",
            )

    def test_isabelle_launchers_fail_closed_without_installation(self) -> None:
        env = os.environ.copy()
        for key in ("ISABELLE", "ISABELLE_BIN", "ISABELLE_HOME"):
            env.pop(key, None)
        launchers = (
            "export_sessions.sh",
            "zp_afp_launch.sh",
            "zp_lib3_split2_launch.sh",
            "zp_library_v3_launch.sh",
            "zp_library_v3_lib3split_launch.sh",
            "zp_library_v3_split_launch.sh",
        )
        for name in launchers:
            proc = subprocess.run(
                ["bash", str(ISABELLE_SCRIPTS / name), "--dry"],
                cwd=REPO,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(proc.returncode, 0, f"{name} guessed an Isabelle install")
            self.assertIn("ISABELLE", proc.stderr, f"{name} did not explain configuration")

    def test_trust_stage1_locator_honors_and_validates_explicit_bin(self) -> None:
        locator = REPO / "scripts" / "trust_verify_ratchet.sh"
        with tempfile.TemporaryDirectory() as tmp:
            bin_dir = Path(tmp) / "stage1" / "bin"
            bin_dir.mkdir(parents=True)
            trustc = bin_dir / "trustc"
            trustc.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
            trustc.chmod(trustc.stat().st_mode | stat.S_IXUSR)

            valid_env = os.environ.copy()
            valid_env["TRUST_STAGE1_BIN"] = str(bin_dir)
            valid = subprocess.run(
                ["bash", str(locator), "--locate-stage1"],
                cwd=REPO,
                env=valid_env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(valid.returncode, 0, valid.stderr)
            self.assertEqual(Path(valid.stdout.strip()), bin_dir.resolve())

            custom_trustc = bin_dir / "custom-trustc"
            custom_trustc.write_text(
                '#!/usr/bin/env bash\necho called >> "$TRUSTC_MARKER"\nexit 0\n',
                encoding="utf-8",
            )
            custom_trustc.chmod(custom_trustc.stat().st_mode | stat.S_IXUSR)
            custom_env = os.environ.copy()
            custom_env.pop("TRUST_STAGE1_BIN", None)
            custom_env["TRUSTC"] = str(custom_trustc)
            custom = subprocess.run(
                ["bash", str(locator), "--locate-stage1"],
                cwd=REPO,
                env=custom_env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(custom.returncode, 0, custom.stderr)
            self.assertEqual(Path(custom.stdout.strip()), bin_dir.resolve())
            marker = Path(tmp) / "custom-invoked"
            custom_env["TRUSTC_MARKER"] = str(marker)
            custom_run = subprocess.run(
                ["bash", str(locator), "--soundness"],
                cwd=REPO,
                env=custom_env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(custom_run.returncode, 0)
            self.assertTrue(marker.is_file(), "configured TRUSTC executable was not invoked")

            invalid_env = os.environ.copy()
            invalid_env["TRUST_STAGE1_BIN"] = str(Path(tmp) / "missing")
            invalid = subprocess.run(
                ["bash", str(locator), "--locate-stage1"],
                cwd=REPO,
                env=invalid_env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(invalid.returncode, 1)
            self.assertIn("has no executable trustc", invalid.stderr)

    def test_trust_stage1_locator_prefers_colocated_source_over_path(self) -> None:
        locator = REPO / "scripts" / "trust_verify_ratchet.sh"
        host_proc = subprocess.run(
            ["rustc", "-vV"],
            cwd=REPO,
            text=True,
            capture_output=True,
            check=True,
        )
        host = next(
            line.removeprefix("host: ")
            for line in host_proc.stdout.splitlines()
            if line.startswith("host: ")
        )
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            source_bin = tmp_path / "trust" / "build" / host / "stage1" / "bin"
            path_bin = tmp_path / "path-bin"
            source_bin.mkdir(parents=True)
            path_bin.mkdir()
            for trustc in (source_bin / "trustc", path_bin / "trustc"):
                trustc.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
                trustc.chmod(trustc.stat().st_mode | stat.S_IXUSR)
            env = os.environ.copy()
            env["TRUST_REPO_ROOT"] = str(tmp_path / "trust")
            env["PATH"] = os.pathsep.join((str(path_bin), env["PATH"]))
            env.pop("TRUST_STAGE1_BIN", None)
            env.pop("TRUSTC", None)
            proc = subprocess.run(
                ["bash", str(locator), "--locate-stage1"],
                cwd=REPO,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(Path(proc.stdout.strip()), source_bin.resolve())


if __name__ == "__main__":
    unittest.main()
