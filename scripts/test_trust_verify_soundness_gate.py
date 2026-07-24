#!/usr/bin/env python3
"""Regression tests for the per-canary Trust soundness gate."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from trust_verify_soundness_gate import EXPECTED_FALSE_KINDS, GateError, check


class SoundnessGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.source = self.root / "sentinel.rs"
        self.log = self.root / "sentinel.log"
        self.marker_lines = {name: line for line, name in enumerate(EXPECTED_FALSE_KINDS, 1)}
        self.source.write_text(
            "\n".join(
                f"pub fn {name}() {{}} // TRUST_FALSE_CANARY: {kind}"
                for name, kind in EXPECTED_FALSE_KINDS.items()
            )
            + "\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def write_rows(
        self,
        *,
        prove: str | None = None,
        omit: str | None = None,
        extra_proved: str | None = None,
    ) -> None:
        lines = []
        for name, kind in EXPECTED_FALSE_KINDS.items():
            if name == omit:
                continue
            outcome = "proved" if name == prove else "failed"
            results = [
                {
                    "kind": kind,
                    "outcome": outcome,
                    "location": {"line_start": self.marker_lines[name]},
                }
            ]
            if name == extra_proved:
                results.append(
                    {
                        "kind": kind,
                        "outcome": "proved",
                        "location": {"line_start": self.marker_lines[name] + 100},
                    }
                )
            payload = {
                "type": "function_result",
                "function": f"vacuity_sentinel::{name}",
                "results": results,
            }
            lines.append("TRUST_JSON:" + json.dumps(payload, separators=(",", ":")))
        self.log.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def test_accepts_every_individually_unproved_canary(self) -> None:
        self.write_rows()
        proved, failed, unknown, runtime_checked, total = check(self.log, self.source)
        self.assertEqual((proved, failed, unknown, runtime_checked, total), (0, 15, 0, 0, 15))

    def test_rejects_false_prove_even_when_aggregate_proved_count_is_unchanged(self) -> None:
        victim = next(iter(EXPECTED_FALSE_KINDS))
        self.write_rows(prove=victim)
        with self.assertRaisesRegex(GateError, "SOUNDNESS REGRESSION"):
            check(self.log, self.source)

    def test_unrelated_same_kind_proof_cannot_replace_the_marked_false_row(self) -> None:
        # Real div/rem transport may include a separate, legitimate same-kind
        # Proved row at the function span. Only the marked operation is the
        # canary; exact line binding avoids both a false alarm and masking.
        victim = "sentinel_div_by_zero_must_not_prove"
        self.write_rows(extra_proved=victim)
        proved, failed, unknown, runtime_checked, total = check(self.log, self.source)
        self.assertEqual((proved, failed, unknown, runtime_checked, total), (1, 15, 0, 0, 16))

    def test_rejects_missing_function_row(self) -> None:
        victim = next(iter(EXPECTED_FALSE_KINDS))
        self.write_rows(omit=victim)
        with self.assertRaisesRegex(GateError, "expected exactly one"):
            check(self.log, self.source)

    def test_rejects_unmapped_source_canary(self) -> None:
        self.write_rows()
        with self.source.open("a", encoding="utf-8") as handle:
            handle.write("pub fn sentinel_new_class_must_not_prove() {}\n")
        with self.assertRaisesRegex(GateError, "unmapped source canaries"):
            check(self.log, self.source)


if __name__ == "__main__":
    unittest.main()
