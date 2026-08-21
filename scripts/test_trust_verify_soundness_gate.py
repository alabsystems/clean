#!/usr/bin/env python3
"""Regression tests for the per-canary Trust soundness gate."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from trust_verify_soundness_gate import (
    EXPECTED_FALSE_KINDS,
    EXPECTED_FALSE_SUFFIXES,
    GateError,
    check,
)


class SoundnessGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.source = self.root / "sentinel.rs"
        self.log = self.root / "sentinel.log"
        self.marker_lines = {name: line for line, name in enumerate(EXPECTED_FALSE_KINDS, 1)}
        self.source.write_text(
            "\n".join(
                f"pub fn {name}() {{}} // TRUST_FALSE_CANARY: "
                f"{kind}#{EXPECTED_FALSE_SUFFIXES[name]}"
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
        extra_failed: str | None = None,
        omit_target: str | None = None,
        wrong_suffix: str | None = None,
    ) -> None:
        lines = []
        for name, kind in EXPECTED_FALSE_KINDS.items():
            if name == omit:
                continue
            outcome = "proved" if name == prove else "failed"
            suffix = EXPECTED_FALSE_SUFFIXES[name]
            family, ordinal_text = suffix.rsplit(":", 1)
            ordinal = int(ordinal_text)
            actual_suffix = "panic_freedom:99" if name == wrong_suffix else suffix
            results = []
            if name != omit_target:
                results.append({
                    "obligation_id": f"vc:fixture__{name}:{actual_suffix}",
                    "kind": kind,
                    "outcome": outcome,
                    "location": {"line_start": self.marker_lines[name]},
                })
            if name == extra_proved:
                results.append(
                    {
                        "obligation_id": (
                            f"vc:fixture__{name}:{family}:{ordinal + 1}"
                        ),
                        "kind": kind,
                        "outcome": "proved",
                        "location": {"line_start": self.marker_lines[name]},
                    }
                )
            if name == extra_failed:
                results.append(
                    {
                        "obligation_id": (
                            f"vc:fixture__{name}:{family}:{ordinal + 1}"
                        ),
                        "kind": kind,
                        "outcome": "failed",
                        "location": {"line_start": self.marker_lines[name]},
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

    def test_same_span_auxiliary_proof_does_not_false_alarm(self) -> None:
        # Real div/rem transport may include a separate, legitimate same-kind
        # Proved row at the exact same expression span. Only the pinned local
        # obligation ordinal is the canary.
        victim = "sentinel_div_by_zero_must_not_prove"
        self.write_rows(extra_proved=victim)
        proved, failed, unknown, runtime_checked, total = check(self.log, self.source)
        self.assertEqual((proved, failed, unknown, runtime_checked, total), (1, 15, 0, 0, 16))

    def test_auxiliary_failure_cannot_mask_a_false_prove_of_the_pinned_row(self) -> None:
        victim = "sentinel_div_by_zero_must_not_prove"
        self.write_rows(prove=victim, extra_failed=victim)
        with self.assertRaisesRegex(GateError, "SOUNDNESS REGRESSION"):
            check(self.log, self.source)

    def test_missing_target_suffix_is_rejected_even_with_same_kind_auxiliary(self) -> None:
        victim = "sentinel_div_by_zero_must_not_prove"
        self.write_rows(omit_target=victim, extra_failed=victim)
        with self.assertRaisesRegex(GateError, "expected exactly one false"):
            check(self.log, self.source)

    def test_wrong_target_suffix_is_rejected(self) -> None:
        victim = "sentinel_div_by_zero_must_not_prove"
        self.write_rows(wrong_suffix=victim)
        with self.assertRaisesRegex(GateError, "expected exactly one false"):
            check(self.log, self.source)

    def test_malformed_source_marker_is_rejected(self) -> None:
        self.write_rows()
        text = self.source.read_text(encoding="utf-8")
        self.source.write_text(text.replace("#bounds_check:0", "#0", 1), encoding="utf-8")
        with self.assertRaisesRegex(GateError, "must be `kind#family:ordinal`"):
            check(self.log, self.source)

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
