#!/usr/bin/env python3
"""Regression tests for the unbacked trust-ir flip census."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import trust_ir_unbacked


def _digest(n: int) -> str:
    return "sha256:" + f"{n:064x}"


def _row(
    index: int,
    name: str,
    *,
    interpreter: str,
    seam: dict | None = None,
) -> dict:
    return {
        "def_path": name,
        "def_index": index,
        "func_id": index,
        "lineage": _digest(index),
        "instr_count": 4,
        "differentials": {
            "interpreter": {
                "verdict": interpreter,
                "samples": 1 if interpreter == "agreed" else 0,
                "detail": (
                    "1 sample(s) agreed"
                    if interpreter == "agreed"
                    else "non-scalar parameter type is non-interpretable "
                    "(coverage-only skip)"
                ),
            },
            "seam": seam,
            "derived_mir": {
                "verdict": "agreed",
                "markers_exact": True,
                "markers_detail": "1 marker line(s) identical",
            },
        },
    }


class TrustIrUnbackedTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.coverage = self.root / "clean_kernel.coverage.json"
        self.log = self.root / "build.log"
        self.dump = self.root / "clean_kernel.trust-ir.txt"

        rows = [
            _row(10, "clean_kernel::backed", interpreter="agreed"),
            _row(11, "clean_kernel::unbacked", interpreter="not-run"),
            _row(
                12,
                "clean_kernel::seam_backed",
                interpreter="not-run",
                seam={"state": "resolved", "verdict": "agreed", "samples": 2},
            ),
        ]
        artifact = {
            "schema": "trust.thir-lower.crate-module.coverage.v2",
            "crate": "clean_kernel",
            "direct_obligation_capability": "structural-parity-only-v1",
            "proof_authority": "coverage-only",
            "native_verification_requests": False,
            "totals": {
                "bodies": len(rows),
                "lowered": len(rows),
                "symbolic": 0,
                "spliced": len(rows),
                "declarations": 0,
                "initializer_bodies": 0,
                "instr_count": 12,
                "unsupported": 0,
                "calls": {"resolved": 0, "extern_decls": 0, "unresolved": 0},
            },
            "bodies": rows,
        }
        self.coverage.write_text(json.dumps(artifact), encoding="utf-8")
        self.log.write_text(
            "\n".join(
                [
                    self._event(10),
                    self._event(11),
                    self._event(11),
                    self._event(12, ctfe=True),
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        self.dump.write_text(
            """functy.7 = (ptr, (ty.1, ty.2)) -> bool
rustcc fn @clean_kernel::unbacked(functy.7) {
bb0(%0: ptr, %1: (ty.1, ty.2)):
    %2 = load u8, ptr %0
    ret %2
}
""",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temp.cleanup()

    @staticmethod
    def _event(index: int, *, ctfe: bool = False) -> str:
        prefix = "CTFE " if ctfe else ""
        return (
            "INFO rustc_mir_transform::trust_ir_flip trust-ir-flip: "
            f"{prefix}compiled from trust-ir, "
            f"did=DefId(0:{index} ~ clean_kernel[abcd]::f{index}), "
            f"asserts=0, lineage={_digest(index)}, flipped_so_far=1"
        )

    def test_event_multiplicity_matches_the_authoritative_axis(self) -> None:
        data = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), str(self.dump)
        )

        self.assertEqual(data["flip_events"], 3)
        self.assertEqual(data["flip_def_ids"], 2)
        self.assertEqual(data["backed"], 1)
        self.assertEqual(data["unbacked"], 2)
        self.assertEqual(data["unbacked_def_ids"], 1)
        self.assertEqual(data["unbacked_flips"][0]["event_count"], 2)
        self.assertEqual(
            data["unbacked_flips"][0]["signature"],
            "(ptr, (ty.1, ty.2)) -> bool",
        )
        self.assertEqual(
            data["unbacked_flips"][0]["entry_params"],
            [
                {
                    "value_id": 0,
                    "type": "ptr",
                    "scalar_leaf": False,
                    "mentioned_after_entry": True,
                },
                {
                    "value_id": 1,
                    "type": "(ty.1, ty.2)",
                    "scalar_leaf": False,
                    "mentioned_after_entry": False,
                },
            ],
        )
        self.assertEqual(
            trust_ir_unbacked.check(
                data, str(self.coverage), str(self.log), str(self.dump)
            ),
            [],
        )

    def test_ctfe_channel_uses_the_same_backing_join(self) -> None:
        data = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), ctfe=True
        )
        self.assertEqual(data["flip_events"], 1)
        self.assertEqual(data["backed"], 1)
        self.assertEqual(data["unbacked"], 0)
        self.assertEqual(
            trust_ir_unbacked.check(
                data, str(self.coverage), str(self.log), None
            ),
            [],
        )

    def test_malformed_event_is_unparsed_not_foreign_and_check_refuses(self) -> None:
        with self.log.open("a", encoding="utf-8") as handle:
            handle.write("trust-ir-flip: compiled from trust-ir, malformed\n")

        data = trust_ir_unbacked.census(str(self.coverage), str(self.log))
        self.assertEqual(data["flip_events_unparsed"], 1)
        self.assertEqual(data["foreign_flip_events"], 0)
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), None
        )
        self.assertIn(
            "trust_ir_axes invariant flip_events_unparsed=1",
            errors,
        )

    def test_unjoinable_event_is_counted_per_event(self) -> None:
        with self.log.open("a", encoding="utf-8") as handle:
            handle.write(self._event(99) + "\n")
            handle.write(self._event(99) + "\n")

        data = trust_ir_unbacked.census(str(self.coverage), str(self.log))
        self.assertEqual(data["flip_events_unjoinable"], 2)
        self.assertEqual(data["flip_def_ids_unjoinable"], 1)
        self.assertEqual(
            data["backed"] + data["unbacked"] + data["flip_events_unjoinable"],
            data["flip_events"],
        )
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), None
        )
        self.assertIn(
            "trust_ir_axes invariant flip_events_unjoinable=2",
            errors,
        )

    def test_duplicate_coverage_indexes_are_refused_explicitly(self) -> None:
        artifact = json.loads(self.coverage.read_text(encoding="utf-8"))
        artifact["bodies"].append(dict(artifact["bodies"][1]))
        artifact["totals"]["bodies"] += 1
        self.coverage.write_text(json.dumps(artifact), encoding="utf-8")

        data = trust_ir_unbacked.census(str(self.coverage), str(self.log))
        self.assertEqual(data["coverage_def_index_collisions"], [11])
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), None
        )
        self.assertIn("coverage has duplicate def_index rows: 11", errors)

    def test_checked_dump_requires_every_unbacked_body_to_join(self) -> None:
        self.dump.write_text(
            """functy.7 = () -> bool
rustcc fn @clean_kernel::another_body(functy.7) {
bb0():
    ret
}
""",
            encoding="utf-8",
        )

        data = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), str(self.dump)
        )
        self.assertEqual(data["ir_dump_unjoinable"], ["clean_kernel::unbacked"])
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), str(self.dump)
        )
        self.assertIn(
            "unbacked rows absent or unparsable in IR dump: clean_kernel::unbacked",
            errors,
        )

    def test_checked_cli_writes_only_after_validation_succeeds(self) -> None:
        output = self.root / "checked.json"
        command = [
            sys.executable,
            trust_ir_unbacked.__file__,
            "--coverage",
            str(self.coverage),
            "--log",
            str(self.log),
            "--check",
            "--json",
            str(output),
        ]
        completed = subprocess.run(command, check=False, capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertTrue(output.is_file())
        self.assertEqual(json.loads(output.read_text())["schema"], trust_ir_unbacked.SCHEMA)

        with self.log.open("a", encoding="utf-8") as handle:
            handle.write("trust-ir-flip: compiled from trust-ir, malformed\n")
        refused = self.root / "refused.json"
        command[-1] = str(refused)
        completed = subprocess.run(command, check=False, capture_output=True, text=True)
        self.assertEqual(completed.returncode, 1)
        self.assertIn("flip_events_unparsed=1", completed.stderr)
        self.assertFalse(refused.exists())


if __name__ == "__main__":
    unittest.main()
