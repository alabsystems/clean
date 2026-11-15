#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Freshness registration for the independent R5 helper qualification target.

Uses the runner's real inventory, digest and result-derivation paths. Synthetic
records stay in a temporary sandbox and never invoke machine admission.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

_SANDBOX = tempfile.TemporaryDirectory(prefix="sort_bounds_freshness_")
for _suffix in ("STATE", "TARGET", "JOURNAL"):
    os.environ[f"VERIFY_RUNNER_{_suffix}_DIR"] = str(
        Path(_SANDBOX.name) / _suffix.lower())

import verify_runner as vr  # noqa: E402


class SortBoundsQualificationInputs(unittest.TestCase):
    TARGET = "clean-olean::test::kcheck_sort_bounds"
    PACKAGES = ("cic_l", "cic_l_model", "kcheck_spec", "kcheck_sort_bounds")

    def test_compiled_and_directly_read_inputs_are_declared(self):
        declared = set(vr.TARGET_EXTRA_PATHS.get(self.TARGET, ()))
        expected = {"lean-toolchain"} | {f"theories/{p}" for p in self.PACKAGES}
        expected |= {f"theories/kcheck_sort_bounds/{p}" for p in
                     ("ORDER", "statement_pins.json", "axiom_closures.json")}
        self.assertEqual(declared, expected)
        directly_read = vr._crystal_extra_paths_owed().get(self.TARGET, set())
        self.assertTrue({f"theories/kcheck_sort_bounds/{p}" for p in
                         ("ORDER", "statement_pins.json", "axiom_closures.json")}
                        <= directly_read)
        self.assertTrue(directly_read <= declared, directly_read - declared)
        pin = (vr.REPO_ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
        fixture = vr.REPO_ROOT / "crates/clean-olean/tests/fixtures/lean" / pin
        theories = [parts[1] for line in (fixture / "kcheck_sort_bounds/ORDER").read_text().splitlines()
                    if (parts := line.partition("#")[0].split()) and parts[0] == "theory"]
        self.assertEqual(theories, list(self.PACKAGES))

    def test_each_read_set_mutation_stales_green_and_restoration_reuses(self):
        with tempfile.TemporaryDirectory(dir=_SANDBOX.name) as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            crate = root / "crates/clean-olean"
            crate.mkdir(parents=True)
            (crate / "Cargo.toml").write_text("# fixture\n")
            inputs = ["lean-toolchain"]
            for package in self.PACKAGES:
                inputs.extend(f"theories/{package}/{name}" for name in
                              ("Root.lean", "ORDER", "statement_pins.json",
                               "axiom_closures.json", "lean-toolchain"))
            for name in inputs:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("before\n")
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            metadata = {"packages": [{"name": "clean-olean",
                        "manifest_path": str(crate / "Cargo.toml"),
                        "targets": [{"name": "kcheck_sort_bounds", "kind": ["test"],
                                     "test": True}]}]}
            with mock.patch.object(vr, "REPO_ROOT", root), \
                    mock.patch.object(vr, "cargo_metadata", return_value=metadata), \
                    mock.patch.object(vr, "check_crystal_extra_paths", return_value=[]), \
                    mock.patch.object(vr, "load_plan", return_value=None), \
                    mock.patch.object(vr, "toolchain_id", return_value="fixture"):
                entries = vr.build_inventory(["clean-olean"], with_gates=False)
                entry, = [e for e in entries if e["id"] == self.TARGET]
                baseline = vr.input_digest(entry, fresh=True)
                measured = {"target": self.TARGET, "status": vr.STATUS_GREEN,
                            "input_digest": baseline, "source": "measured",
                            "commit": "0123456789abcdef",
                            "final_line": "test result: ok. 1 passed; 0 failed"}
                self.assertEqual(vr.derive(entry, measured, baseline)["bucket"], vr.BUCKET_GREEN)
                for name in inputs:
                    with self.subTest(input=name):
                        path = root / name
                        path.write_text("after\n")
                        changed = vr.input_digest(entry, fresh=True)
                        self.assertNotEqual(changed, baseline)
                        result = vr.derive(entry, measured, changed)
                        self.assertEqual(result["bucket"], vr.BUCKET_UNKNOWN)
                        self.assertIn("stale", result["reason"])
                        path.write_text("before\n")
                        restored = vr.input_digest(entry, fresh=True)
                        self.assertEqual(restored, baseline)
                        self.assertEqual(vr.derive(entry, measured, restored)["bucket"], vr.BUCKET_GREEN)


if __name__ == "__main__":
    unittest.main()
