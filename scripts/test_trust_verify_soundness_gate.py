#!/usr/bin/env python3
"""Regression tests for the per-canary Trust soundness gate.

The three arms this suite exists for, in the order they were broken in
production:

1. ORDINAL SHIFT MUST NOT BREAK A PIN.  A producer that emits a new row ahead
   of a canary renumbers that canary's `obligation_id` ordinal.  Four of fifteen
   pins drifted 0 -> 1 that way on trust 9f0757334; the gate must not notice.
2. A CERTIFICATION MUST BE REPORTED EVEN WHEN SOMETHING ELSE IS ALSO FAILING.
   The old gate raised on the first failing canary in sorted order, so four
   cosmetic drifts hid a `shift:left` certification behind them.
3. A REMOVED CANARY ROW MUST STILL BE CAUGHT.  Robustness to renumbering must
   not become blindness to disappearance.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from trust_verify_soundness_gate import (
    EXIT_CERTIFIED,
    EXIT_PIN,
    EXIT_TRANSPORT,
    EXPECTED_FALSE_IDENTITY,
    EXPECTED_FALSE_KINDS,
    GateError,
    TransportIncomplete,
    check,
)


class SoundnessGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.source = self.root / "sentinel.rs"
        self.log = self.root / "sentinel.log"
        # One canary per source line, so the marker line IS the row's line.
        self.marker_lines = {name: line for line, name in enumerate(EXPECTED_FALSE_KINDS, 1)}
        self.source.write_text(
            "\n".join(
                f"pub fn {name}() {{}} // TRUST_FALSE_CANARY: "
                f"{kind}#{EXPECTED_FALSE_IDENTITY[name].family}"
                for name, kind in EXPECTED_FALSE_KINDS.items()
            )
            + "\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def row(
        self,
        name: str,
        *,
        ordinal: int = 0,
        outcome: str = "failed",
        kind: str | None = None,
        family: str | None = None,
        typed_kind: object | None = None,
        col_start: int | None = None,
        line: int | None = None,
    ) -> dict[str, object]:
        identity = EXPECTED_FALSE_IDENTITY[name]
        line_start = self.marker_lines[name] if line is None else line
        return {
            "obligation_id": f"vc:fixture__{name}:{family or identity.family}:{ordinal}",
            "kind": EXPECTED_FALSE_KINDS[name] if kind is None else kind,
            "typed_kind": (
                json.loads(identity.typed_kind) if typed_kind is None else typed_kind
            ),
            "outcome": outcome,
            "location": {
                "line_start": line_start,
                "col_start": identity.col_start if col_start is None else col_start,
                "line_end": line_start + identity.line_span,
                "col_end": 99,  # deliberately noisy: col_end is NOT part of the identity
            },
        }

    def write(self, rows_by_canary: dict[str, list[dict[str, object]]]) -> None:
        lines = [
            "TRUST_JSON:"
            + json.dumps(
                {
                    "type": "function_result",
                    "function": f"vacuity_sentinel::{name}",
                    "results": rows,
                },
                separators=(",", ":"),
            )
            for name, rows in rows_by_canary.items()
        ]
        self.log.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def baseline(self) -> dict[str, list[dict[str, object]]]:
        return {name: [self.row(name)] for name in EXPECTED_FALSE_KINDS}

    # ---------------------------------------------------------------- green

    def test_accepts_every_individually_unproved_canary(self) -> None:
        self.write(self.baseline())
        report = check(self.log, self.source)
        self.assertEqual(report.findings, [])
        self.assertEqual(
            (report.proved, report.failed, report.unknown, report.runtime_checked, report.total),
            (0, 15, 0, 0, 15),
        )
        self.assertEqual(report.exit_code(), 0)

    # --------------------------------------- (a) ordinal shift must not bite

    def test_ordinal_shift_does_not_break_the_pin(self) -> None:
        """THE MIGRATION'S REASON FOR EXISTING.

        Every canary renumbered, each behind a brand-new unrelated row — the
        exact shape of trust 9f0757334's `unreach@176` / `overflow@48` inserts.
        Nothing about the canary itself changed, so the gate must stay green.
        """
        rows = {}
        for name in EXPECTED_FALSE_KINDS:
            intruder = self.row(
                name,
                ordinal=0,
                outcome="proved",
                kind="unreach",
                typed_kind="Unreachable",
                col_start=0,
                line=self.marker_lines[name],
            )
            rows[name] = [intruder, self.row(name, ordinal=1)]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual(report.findings, [])
        self.assertEqual(report.exit_code(), 0)

    def test_large_ordinal_shift_is_still_fine(self) -> None:
        self.write({name: [self.row(name, ordinal=97)] for name in EXPECTED_FALSE_KINDS})
        self.assertEqual(check(self.log, self.source).exit_code(), 0)

    def test_col_end_drift_does_not_break_the_pin(self) -> None:
        """`col_end` moved on 7 of 15 rows between producers; it is not pinned."""
        rows = self.baseline()
        for row_list in rows.values():
            row_list[0]["location"]["col_end"] = 12345  # type: ignore[index]
        self.write(rows)
        self.assertEqual(check(self.log, self.source).exit_code(), 0)

    # --------------------------- (b) a certification is always REPORTED, and
    # --------------------------- never demoted by a co-occurring pin failure

    def test_certification_is_reported_behind_an_unrelated_pin_failure(self) -> None:
        """THE MASKING BUG.

        `sentinel_accumulator_overflow_must_not_prove` sorts FIRST and has a
        broken pin; `sentinel_shift_overflow_must_not_prove` sorts LATE and is
        certified.  The old gate raised on the first and never looked at the
        second.  Both must appear, at their own severities, and the exit code
        must be the SOUNDNESS one.
        """
        early = "sentinel_accumulator_overflow_must_not_prove"
        late = "sentinel_shift_overflow_must_not_prove"
        self.assertLess(early, late, "fixture assumes the pin failure sorts first")
        rows = self.baseline()
        rows[early] = [self.row(early, kind="something-else")]
        rows[late] = [self.row(late), self.row(late, ordinal=1, outcome="proved")]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual([f.canary for f in report.certified], [late])
        self.assertEqual([f.canary for f in report.pin_failures], [early])
        self.assertEqual(report.exit_code(), EXIT_CERTIFIED)

    def test_every_certified_canary_is_reported_not_just_the_first(self) -> None:
        victims = sorted(EXPECTED_FALSE_KINDS)[:3]
        rows = self.baseline()
        for name in victims:
            rows[name] = [self.row(name), self.row(name, ordinal=1, outcome="proved")]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual(sorted(f.canary for f in report.certified), victims)
        self.assertEqual(report.exit_code(), EXIT_CERTIFIED)

    def test_every_pin_failure_is_reported_not_just_the_first(self) -> None:
        victims = sorted(EXPECTED_FALSE_KINDS)[:4]
        rows = self.baseline()
        for name in victims:
            rows[name] = [self.row(name, kind="renamed")]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual(sorted(f.canary for f in report.pin_failures), victims)
        self.assertEqual(report.certified, [])
        self.assertEqual(report.exit_code(), EXIT_PIN)

    def test_certification_at_a_shifted_ordinal_still_blocks(self) -> None:
        """Robustness to renumbering must not become blindness to a proof."""
        victim = "sentinel_div_by_zero_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim, ordinal=7), self.row(victim, ordinal=41, outcome="proved")]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual([f.canary for f in report.certified], [victim])
        self.assertEqual(report.exit_code(), EXIT_CERTIFIED)

    def test_certification_on_the_pinned_row_itself_blocks(self) -> None:
        victim = "sentinel_div_by_zero_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim, outcome="proved")]
        self.write(rows)
        self.assertEqual(check(self.log, self.source).exit_code(), EXIT_CERTIFIED)

    def test_certification_on_a_whole_function_span_blocks(self) -> None:
        """Span CONTAINMENT, not `line_start ==`: a producer cannot dodge by
        attaching the proved row to the enclosing body."""
        victim = "sentinel_div_by_zero_must_not_prove"
        line = self.marker_lines[victim]
        rows = self.baseline()
        wide = self.row(victim, ordinal=1, outcome="proved")
        wide["location"] = {
            "line_start": line - 1,
            "col_start": 0,
            "line_end": line + 1,
            "col_end": 1,
        }
        rows[victim] = [self.row(victim), wide]
        self.write(rows)
        self.assertEqual(check(self.log, self.source).exit_code(), EXIT_CERTIFIED)

    def test_different_kind_at_the_same_line_does_not_false_alarm(self) -> None:
        """The real sentinel emits a proved `overflow:add` on the same line as
        `slice_range_oob`'s false `slice` row. Different property, stays allowed."""
        victim = "sentinel_div_by_zero_must_not_prove"
        rows = self.baseline()
        rows[victim] = [
            self.row(victim),
            self.row(victim, ordinal=1, outcome="proved", kind="overflow:sub"),
        ]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual(report.findings, [])
        self.assertEqual((report.proved, report.total), (1, 16))

    # ----------------------------------- (c) removal is still caught, exactly

    def test_removed_canary_row_is_caught_by_the_existence_pin(self) -> None:
        victim = "sentinel_div_by_zero_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim, ordinal=1, outcome="failed", kind="overflow:sub")]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual([f.canary for f in report.pin_failures], [victim])
        self.assertIn("EXISTENCE PIN", report.pin_failures[0].summary)
        self.assertEqual(report.exit_code(), EXIT_PIN)

    def test_retyped_canary_row_is_caught(self) -> None:
        victim = "sentinel_unguarded_add_overflow_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim, typed_kind={"ArithmeticOverflow": {"op": "Add"}})]
        self.write(rows)
        self.assertEqual(
            [f.canary for f in check(self.log, self.source).pin_failures], [victim]
        )

    def test_refamilied_canary_row_is_caught(self) -> None:
        victim = "sentinel_oob_index_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim, family="panic_freedom")]
        self.write(rows)
        self.assertEqual(
            [f.canary for f in check(self.log, self.source).pin_failures], [victim]
        )

    def test_moved_canary_row_is_caught(self) -> None:
        victim = "sentinel_oob_index_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim, col_start=EXPECTED_FALSE_IDENTITY[victim].col_start + 1)]
        self.write(rows)
        self.assertEqual(
            [f.canary for f in check(self.log, self.source).pin_failures], [victim]
        )

    def test_unexplained_twin_with_no_proof_is_a_pin_finding_not_a_certification(self) -> None:
        victim = "sentinel_oob_index_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim), self.row(victim, ordinal=1)]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual(report.certified, [])
        self.assertIn("DUPLICATE IDENTITY", report.pin_failures[0].summary)
        self.assertEqual(report.exit_code(), EXIT_PIN)

    def test_certified_twin_is_reported_only_as_a_certification(self) -> None:
        """A certified twin must not ALSO be filed as a pin failure — that would
        restate a soundness failure at the wrong severity."""
        victim = "sentinel_oob_index_must_not_prove"
        rows = self.baseline()
        rows[victim] = [self.row(victim), self.row(victim, ordinal=1, outcome="proved")]
        self.write(rows)
        report = check(self.log, self.source)
        self.assertEqual([f.canary for f in report.certified], [victim])
        self.assertEqual(report.pin_failures, [])

    # ------------------------------------------- transport vs pin separation

    def test_missing_function_row_is_transport_not_pin(self) -> None:
        rows = self.baseline()
        del rows[next(iter(EXPECTED_FALSE_KINDS))]
        self.write(rows)
        with self.assertRaises(TransportIncomplete):
            check(self.log, self.source)

    def test_empty_transport_is_transport_not_pin(self) -> None:
        self.log.write_text("no transport here\n", encoding="utf-8")
        with self.assertRaises(TransportIncomplete):
            check(self.log, self.source)

    def test_exit_codes_are_distinct(self) -> None:
        self.assertEqual((EXIT_PIN, EXIT_CERTIFIED, EXIT_TRANSPORT), (1, 2, 3))

    # ------------------------------------------------------ source inventory

    def test_marker_with_an_ordinal_is_rejected(self) -> None:
        """Nobody gets to re-pin the drifting field."""
        self.write(self.baseline())
        text = self.source.read_text(encoding="utf-8")
        self.source.write_text(text.replace("#bounds_check", "#bounds_check:0", 1), encoding="utf-8")
        with self.assertRaisesRegex(GateError, "still carries an ordinal"):
            check(self.log, self.source)

    def test_marker_naming_the_wrong_family_is_rejected(self) -> None:
        self.write(self.baseline())
        text = self.source.read_text(encoding="utf-8")
        self.source.write_text(text.replace("#bounds_check", "#arithmetic_safety", 1), encoding="utf-8")
        with self.assertRaisesRegex(GateError, "source marker names family"):
            check(self.log, self.source)

    def test_malformed_source_marker_is_rejected(self) -> None:
        self.write(self.baseline())
        text = self.source.read_text(encoding="utf-8")
        self.source.write_text(text.replace("slice#bounds_check", "slice", 1), encoding="utf-8")
        with self.assertRaisesRegex(GateError, "must be `kind#family`"):
            check(self.log, self.source)

    def test_rejects_unmapped_source_canary(self) -> None:
        self.write(self.baseline())
        with self.source.open("a", encoding="utf-8") as handle:
            handle.write("pub fn sentinel_new_class_must_not_prove() {}\n")
        with self.assertRaisesRegex(GateError, "unmapped source canaries"):
            check(self.log, self.source)

    def test_identity_inventory_matches_kind_inventory(self) -> None:
        self.assertEqual(set(EXPECTED_FALSE_IDENTITY), set(EXPECTED_FALSE_KINDS))


if __name__ == "__main__":
    unittest.main()
