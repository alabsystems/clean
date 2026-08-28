#!/usr/bin/env python3
"""Fail closed unless every Trust soundness canary remains individually unproved.

The aggregate proved/unproved ratchet is useful landscape telemetry, but it
cannot identify which obligation changed: one false proof can be hidden by an
unrelated obligation disappearing or becoming unknown.  This checker consumes
the compiler's structured transport and binds each canary function to the
specific VC family that is intentionally false.

Two questions, deliberately kept apart, and now a third rule about how they are
reported:

* **Does the canary still exist?**  Pinned to one exact CONTENT identity
  (`EXPECTED_FALSE_IDENTITY`), so the canary cannot vanish, move, or be renamed
  without failing the gate.
* **Was the canary certified?**  Asked of *every* transport row carrying the
  canary's VC kind whose span covers the canary's source line, because those
  rows all name the same safety property of the same operation.  Narrowing this
  second question to one obligation ordinal is how a genuinely-false `divzero`
  row rode under a green gate; do not re-narrow it.
* **Every failing canary is reported, and the two severities never merge.**  A
  certification (exit 2) and an existence-pin drift (exit 1) are different
  findings with different urgency.  Reporting only the first canary in sorted
  order is how four cosmetic ordinal drifts hid a `shift:left` certification —
  see the identity note below.

WHY THE IDENTITY IS NOT AN ORDINAL (measured 2026-08-23, four producers)
------------------------------------------------------------------------
Between 2026-07-20 (670d95890) and 2026-08-20 (35dbf2db6) the pin was
`family:ordinal`, the tail of the producer's `obligation_id`
(`vc:<crate>__<fn>:<family>:<ordinal>`).  That ordinal is a PRODUCER-LOCAL
per-function emission counter shared across the safety families, so ANY new row
emitted ahead of the canary renumbers it.

Measured by compiling this repository's `tests/trust_verify/vacuity_sentinel.rs`
with every Trust stage1 present on the build host:

    333042c50  2026-07-20      94147b34f  2026-08-11
    d28fbe4d0  2026-08-20      9f0757334  2026-08-23

Seven of fifteen pins move somewhere in that span: `accumulator_overflow`,
`loop_off_by_one`, `lossy_narrowing_cast` and `mul_overflow` drift 0 -> 1 at
9f0757334 (which emits `unreach`/`overflow` rows AHEAD of them); `div_by_zero`
and `remainder_by_zero` drift 1 -> 0 at 94147b34f; `slice_range_oob` is absent
from 333042c50 entirely.  Every one of the drifted obligations was still
correctly FAILED — an identity problem, not a soundness one.  Re-pinning
0 -> 1 drifts again on the next producer change.

Per-field agreement across those four producers, on the fourteen intended rows
all four emit:

    family       14/14      kind          14/14      typed_kind   14/14
    description  14/14      col_start     14/14      line_span    14/14
    col_end       7/14      ordinal        7/14      claim_digest  0/14

So the identity is `(family, kind, typed_kind, line_span, col_start)` — every
component of the producer's own `obligation_id` EXCEPT the ordinal, plus the
typed payload and the expression's start position.  Two fields were measured out
of the identity rather than assumed into it:

* `claim_digest_sha256` agrees on NONE of the fourteen across all four (e.g.
  `oob_index` is 3ddb7208 on 333042c50 and ce11e0c6 on the three later builds),
  and it also moved between 94147b34f and 9f0757334 on `accumulator_overflow`
  (fcf40c99 -> 01b08284), `loop_off_by_one` (303cc922 -> 86d2c1d3) and
  `mul_overflow` (42df0891 -> ef0d3cc7) while those obligations were unchanged.
* `col_end` moved on seven: 333042c50 reports the real expression end for
  arithmetic rows (`x + u32::MAX` -> col_end 16) where the three later builds
  collapse it to col_start (col_end 4).  `col_start` moved on none.

A fifth stage1, 8a5d10783 (2026-07-18), is EXCLUDED and is not counted above: it
predates the transport schema these pins read.  Its `obligation_id` carries no
crate prefix (`vc:sentinel_oob_index...` rather than
`vc:vacuity_sentinel__sentinel_oob_index...`) and every `typed_kind` is
`UnsupportedMir`.  That is a different transport era, not a producer this gate
is expected to survive; recorded here so the exclusion is a stated decision
rather than a silent one.

EXACT, BUT NOT POSITIONAL
-------------------------
The pin stays exact in content: a renamed `kind`, a changed `typed_kind`
(operator or operand widths/signedness), a changed family, or a moved start
position all fail it.  What it no longer does is require the row to sit at one
ordinal, and it no longer demands that exactly ONE row carry the identity.  That
last relaxation is deliberate and is not a loosening, because the pathology it
used to trip over is precisely a soundness finding: every time the identity
matched more than one row it was a `failed` row and a `proved` twin at the
identical kind/typed_kind/position — `div_by_zero` and `remainder_by_zero` on
94147b34f, `shift_overflow` on 9f0757334.  The soundness question is asked over
a SUPERSET of the identity, so a twin is caught as a CERTIFICATION (exit 2)
instead of being mis-reported as a broken pin (exit 1).

EXIT CODES
----------
    0  every canary exists and none is certified
    1  EXISTENCE-PIN / inventory failure — a canary row is missing, moved,
       renamed, or the source and gate inventories disagree.  Not retryable.
    2  SOUNDNESS CERTIFICATION — a genuinely-false obligation came back
       `proved`.  Blocks immediately and is never retried away.  Takes
       precedence over any concurrent pin failure, but does not suppress it:
       both sections are printed.
    3  TRANSPORT INCOMPLETE — no structured transport, or a function emitted no
       rows at all.  This is the documented cold-cache under-emission and is the
       ONLY class the caller may retry warm.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


TRANSPORT_PREFIX = "TRUST_JSON:"

EXIT_OK = 0
EXIT_PIN = 1
EXIT_CERTIFIED = 2
EXIT_TRANSPORT = 3


def _int(width: int, *, signed: bool = False) -> dict[str, Any]:
    return {"Int": {"width": width, "signed": signed}}


def _overflow(op: str, *operand_tys: dict[str, Any]) -> dict[str, Any]:
    return {"ArithmeticOverflow": {"op": op, "operand_tys": list(operand_tys)}}


def _shift(op: str, operand_ty: dict[str, Any], shift_ty: dict[str, Any]) -> dict[str, Any]:
    return {"ShiftOverflow": {"op": op, "operand_ty": operand_ty, "shift_ty": shift_ty}}


U32 = _int(32)


# Keep this inventory explicit.  Adding a `*_must_not_prove` function to the
# source without adding its expected false VC family here is a gate failure.
EXPECTED_FALSE_KINDS = {
    "sentinel_oob_index_must_not_prove": "slice",
    "sentinel_div_by_zero_must_not_prove": "divzero",
    "sentinel_lossy_narrowing_cast_must_not_prove": "bounds",
    "sentinel_unguarded_add_overflow_must_not_prove": "overflow:add",
    "sentinel_remainder_by_zero_must_not_prove": "remzero",
    "sentinel_sub_underflow_must_not_prove": "overflow:sub",
    "sentinel_mul_overflow_must_not_prove": "overflow:mul",
    "sentinel_slice_range_oob_must_not_prove": "slice",
    "sentinel_shift_overflow_must_not_prove": "shift:left",
    "sentinel_loop_off_by_one_must_not_prove": "slice",
    "sentinel_clamp_still_oob_must_not_prove": "slice",
    "sentinel_multivar_guard_lossy_must_not_prove": "bounds",
    "sentinel_stale_guard_must_not_prove": "slice",
    "sentinel_intrinsic_bound_must_not_prove": "slice",
    "sentinel_accumulator_overflow_must_not_prove": "overflow:add",
}


@dataclass(frozen=True)
class Identity:
    """The stable, producer-change-surviving identity of one canary row.

    `line_start` is NOT stored: it is derived from the position of the canary's
    `TRUST_FALSE_CANARY:` marker in the source, so editing the sentinel moves
    the pin with it.  Everything else is pinned:

    * `family`    the `obligation_id` family segment (`bounds_check`,
                  `arithmetic_safety`, ...).  Stable; the ordinal after it is not.
    * `typed_kind` the producer's typed payload, compared losslessly.
    * `line_span` `line_end - line_start` (0 for every current canary).
    * `col_start` the obligation expression's start column.  This closes the
      "two same-kind indexes on one line" substitution hole.

    `col_end` is deliberately NOT pinned: measured over four producers it moved
    on 7 of 15 canaries.  trust 333042c50 (2026-07-20) reports the real
    expression end for arithmetic rows (`x + u32::MAX` -> col_end 16) while
    94147b34f / d28fbe4d0 / 9f0757334 all collapse it to col_start (col_end 4).
    `col_start` moved on none of them.

    On mismatch the gate prints the observed rows in paste-ready form; the
    columns are producer-observed, so re-derive them, never guess them.
    """

    family: str
    typed_kind: str  # canonical sorted-key JSON
    line_span: int
    col_start: int


def _identity(family: str, typed_kind: Any, line_span: int, col_start: int) -> Identity:
    return Identity(
        family=family,
        typed_kind=json.dumps(typed_kind, sort_keys=True, separators=(",", ":")),
        line_span=line_span,
        col_start=col_start,
    )


# Measured on trust 94147b34f AND trust 9f0757334; all fifteen agree on both.
EXPECTED_FALSE_IDENTITY: dict[str, Identity] = {
    "sentinel_oob_index_must_not_prove": _identity("bounds_check", "SliceBoundsCheck", 0, 4),
    "sentinel_div_by_zero_must_not_prove": _identity("arithmetic_safety", "DivisionByZero", 0, 4),
    "sentinel_lossy_narrowing_cast_must_not_prove": _identity(
        "bounds_check", "IndexOutOfBounds", 0, 4
    ),
    "sentinel_unguarded_add_overflow_must_not_prove": _identity(
        "arithmetic_safety", _overflow("Add", U32, U32), 0, 4
    ),
    "sentinel_remainder_by_zero_must_not_prove": _identity(
        "arithmetic_safety", "RemainderByZero", 0, 4
    ),
    "sentinel_sub_underflow_must_not_prove": _identity(
        "arithmetic_safety", _overflow("Sub", U32, U32), 0, 4
    ),
    "sentinel_mul_overflow_must_not_prove": _identity(
        "arithmetic_safety", _overflow("Mul", U32, U32), 0, 4
    ),
    "sentinel_slice_range_oob_must_not_prove": _identity(
        "bounds_check", "SliceBoundsCheck", 0, 6
    ),
    "sentinel_shift_overflow_must_not_prove": _identity(
        "arithmetic_safety", _shift("Shl", U32, U32), 0, 4
    ),
    "sentinel_loop_off_by_one_must_not_prove": _identity(
        "bounds_check", "SliceBoundsCheck", 0, 31
    ),
    "sentinel_clamp_still_oob_must_not_prove": _identity(
        "bounds_check", "SliceBoundsCheck", 0, 4
    ),
    "sentinel_multivar_guard_lossy_must_not_prove": _identity(
        "bounds_check", "IndexOutOfBounds", 0, 8
    ),
    "sentinel_stale_guard_must_not_prove": _identity("bounds_check", "SliceBoundsCheck", 0, 15),
    "sentinel_intrinsic_bound_must_not_prove": _identity(
        "bounds_check", "SliceBoundsCheck", 0, 4
    ),
    "sentinel_accumulator_overflow_must_not_prove": _identity(
        "arithmetic_safety", _overflow("Add", U32, U32), 0, 8
    ),
}


class GateError(ValueError):
    """The gate cannot run, or a canary's existence pin no longer holds."""


class TransportIncomplete(GateError):
    """Structured transport is absent or empty — the one retryable class."""


@dataclass(frozen=True)
class Finding:
    """One failing canary, tagged with the severity it actually carries."""

    severity: str  # "CERTIFIED" or "PIN"
    canary: str
    summary: str
    detail: tuple[str, ...] = ()


@dataclass
class GateReport:
    proved: int = 0
    failed: int = 0
    unknown: int = 0
    runtime_checked: int = 0
    findings: list[Finding] = field(default_factory=list)

    @property
    def total(self) -> int:
        return self.proved + self.failed + self.unknown + self.runtime_checked

    @property
    def certified(self) -> list[Finding]:
        return [f for f in self.findings if f.severity == "CERTIFIED"]

    @property
    def pin_failures(self) -> list[Finding]:
        return [f for f in self.findings if f.severity == "PIN"]

    def exit_code(self) -> int:
        if self.certified:
            return EXIT_CERTIFIED
        if self.pin_failures:
            return EXIT_PIN
        return EXIT_OK


def sentinel_names_from_source(source: Path) -> set[str]:
    """Return the declared public soundness-canary function names."""
    names: set[str] = set()
    for line in source.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped.startswith("pub fn sentinel_"):
            continue
        name = stripped.removeprefix("pub fn ").split("(", 1)[0]
        if name.endswith("_must_not_prove"):
            names.add(name)
    return names


def false_markers_from_source(source: Path) -> dict[str, tuple[str, str, int]]:
    """Map each canary to its marked VC kind, obligation family, and source line.

    The marker is `TRUST_FALSE_CANARY: <kind>#<family>` — deliberately WITHOUT
    an ordinal.  The ordinal was a producer-local emission counter that drifted
    on four of fifteen canaries between two stage1 builds; nothing that renumbers
    on an unrelated new row belongs in an identity.
    """
    markers: dict[str, tuple[str, str, int]] = {}
    current: str | None = None
    for line_number, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("pub fn sentinel_"):
            current = stripped.removeprefix("pub fn ").split("(", 1)[0]
        marker = "TRUST_FALSE_CANARY:"
        if marker not in line:
            continue
        if current is None or current not in EXPECTED_FALSE_KINDS:
            raise GateError(f"false-canary marker on line {line_number} is outside a canary")
        token = line.split(marker, 1)[1].strip().split()[0]
        try:
            kind, family = token.rsplit("#", 1)
        except ValueError as error:
            raise GateError(
                f"false-canary marker on line {line_number} must be `kind#family`"
            ) from error
        if not kind or not family:
            raise GateError(
                f"false-canary marker on line {line_number} must be `kind#family`"
            )
        if ":" in family:
            raise GateError(
                f"false-canary marker on line {line_number} still carries an ordinal "
                f"(`{family}`). The ordinal is producer-local and drifts; pin `kind#family` "
                "and let scripts/trust_verify_soundness_gate.py's EXPECTED_FALSE_IDENTITY "
                "carry the rest of the identity."
            )
        if current in markers:
            raise GateError(f"{current}: multiple false-canary markers")
        markers[current] = (kind, family, line_number)
    return markers


def transport_messages(log: Path) -> list[dict[str, Any]]:
    messages: list[dict[str, Any]] = []
    for line_number, line in enumerate(log.read_text(encoding="utf-8").splitlines(), 1):
        marker = line.find(TRANSPORT_PREFIX)
        if marker < 0:
            continue
        payload = line[marker + len(TRANSPORT_PREFIX) :].strip()
        try:
            value = json.loads(payload)
        except json.JSONDecodeError as error:
            raise TransportIncomplete(
                f"malformed Trust transport on log line {line_number}: {error}"
            ) from error
        if not isinstance(value, dict):
            raise TransportIncomplete(f"non-object Trust transport on log line {line_number}")
        messages.append(value)
    if not messages:
        raise TransportIncomplete(
            "no TRUST_JSON transport found; structured verification did not run"
        )
    return messages


def row_family(row: dict[str, Any]) -> str:
    parts = str(row.get("obligation_id", "")).rsplit(":", 2)
    return parts[-2] if len(parts) >= 2 else ""


def row_span(row: dict[str, Any]) -> tuple[Any, Any, Any, Any]:
    location = row.get("location")
    if not isinstance(location, dict):
        return (None, None, None, None)
    return (
        location.get("line_start"),
        location.get("col_start"),
        location.get("line_end"),
        location.get("col_end"),
    )


def row_typed_kind(row: dict[str, Any]) -> str:
    return json.dumps(row.get("typed_kind"), sort_keys=True, separators=(",", ":"))


def row_identity_text(row: dict[str, Any]) -> str:
    """Paste-ready rendering of one row's stable identity, for failure messages."""
    line_start, col_start, line_end, col_end = row_span(row)
    span = "?" if line_start is None else f"{line_start}:{col_start}-{line_end}:{col_end}"
    ordinal = str(row.get("obligation_id", "")).rsplit(":", 1)[-1]
    return (
        f"{row.get('kind')}#{row_family(row)} @{span} "
        f"[outcome={row.get('outcome')} ordinal={ordinal} typed_kind={row_typed_kind(row)}]"
    )


def matches_identity(row: dict[str, Any], kind: str, line_start: int, identity: Identity) -> bool:
    if row.get("kind") != kind:
        return False
    if row_family(row) != identity.family:
        return False
    if row_typed_kind(row) != identity.typed_kind:
        return False
    observed_line_start, observed_col_start, observed_line_end, _ = row_span(row)
    return (observed_line_start, observed_col_start, observed_line_end) == (
        line_start,
        identity.col_start,
        line_start + identity.line_span,
    )


def names_same_property(row: dict[str, Any], kind: str, line: int) -> bool:
    """Does this row name the canary's genuinely-false property?

    Same VC kind, and a span that COVERS the canary's source line.  Span
    containment rather than `line_start == line` closes the hole where a
    producer attaches the obligation to the whole function body: measured on
    both producers this admits exactly the same rows as the old equality test,
    so it costs nothing and forecloses that dodge.

    This is deliberately BROADER than `matches_identity`.  The existence pin
    says which row must be there; the soundness verdict is taken over every row
    naming the property, whatever ordinal it carries.
    """
    if row.get("kind") != kind:
        return False
    line_start, _, line_end, _ = row_span(row)
    if not isinstance(line_start, int):
        return False
    if not isinstance(line_end, int):
        line_end = line_start
    return line_start <= line <= line_end


def check(log: Path, source: Path) -> GateReport:
    declared = sentinel_names_from_source(source)
    expected = set(EXPECTED_FALSE_KINDS)
    if set(EXPECTED_FALSE_IDENTITY) != expected:
        raise GateError("false-canary identity inventory does not match kind inventory")
    if declared != expected:
        missing = sorted(declared - expected)
        stale = sorted(expected - declared)
        detail = []
        if missing:
            detail.append(f"unmapped source canaries: {', '.join(missing)}")
        if stale:
            detail.append(f"mapped canaries absent from source: {', '.join(stale)}")
        raise GateError("canary inventory mismatch (" + "; ".join(detail) + ")")

    markers = false_markers_from_source(source)
    if set(markers) != expected:
        missing = sorted(expected - set(markers))
        raise GateError("canaries missing an exact false-obligation marker: " + ", ".join(missing))
    for name, expected_kind in EXPECTED_FALSE_KINDS.items():
        marker_kind, marker_family, _ = markers[name]
        if marker_kind != expected_kind:
            raise GateError(
                f"{name}: source marker names `{marker_kind}`, expected `{expected_kind}`"
            )
        expected_family = EXPECTED_FALSE_IDENTITY[name].family
        if marker_family != expected_family:
            raise GateError(
                f"{name}: source marker names family `{marker_family}`, "
                f"expected `{expected_family}`"
            )

    rows: dict[str, list[dict[str, Any]]] = {name: [] for name in expected}
    seen_function_rows: dict[str, int] = {name: 0 for name in expected}
    for message in transport_messages(log):
        if message.get("type") != "function_result":
            continue
        function = message.get("function")
        if not isinstance(function, str):
            raise GateError("function_result transport has no string function identity")
        short_name = function.rsplit("::", 1)[-1]
        if short_name in rows:
            seen_function_rows[short_name] += 1
            results = message.get("results")
            if not isinstance(results, list):
                raise GateError(f"{short_name}: obligation result inventory is not a list")
            rows[short_name].extend(results)

    report = GateReport()

    # EVERY canary is evaluated. Raising on the first failure is how four
    # cosmetic ordinal drifts hid a `shift:left` certification behind them.
    for name in sorted(expected):
        count = seen_function_rows[name]
        if count == 0:
            raise TransportIncomplete(
                f"{name}: no function_result row in the transport (under-emission)"
            )
        if count != 1:
            raise GateError(
                f"{name}: expected exactly one function_result row, found {count}"
            )
        results = [row for row in rows[name] if isinstance(row, dict)]
        if len(results) != len(rows[name]):
            raise GateError(f"{name}: non-object obligation result")
        if not results:
            raise TransportIncomplete(f"{name}: empty obligation result inventory")

        expected_kind = EXPECTED_FALSE_KINDS[name]
        identity = EXPECTED_FALSE_IDENTITY[name]
        _, _, expected_line = markers[name]

        same_property = [
            row for row in results if names_same_property(row, expected_kind, expected_line)
        ]
        pinned = [
            row for row in results if matches_identity(row, expected_kind, expected_line, identity)
        ]

        # SOUNDNESS FIRST: asked of the PROPERTY, not of one ordinal and not of
        # the pinned row alone. Measured: `x / (n - n)` emitted
        # `divzero#arithmetic_safety:0` (failed) and `:1` (proved) at the same
        # line:col, the second one's SMT-LIB body `n != 0 AND n == 0` — the same
        # zero-divisor question re-asked under its own assert-passed guard, UNSAT
        # by construction for every program. It is not an independent auxiliary
        # row and it proves nothing.
        proved = [row for row in same_property if row.get("outcome") == "proved"]
        if proved:
            report.findings.append(
                Finding(
                    severity="CERTIFIED",
                    canary=name,
                    summary=(
                        f"genuinely-false `{expected_kind}` obligation at source line "
                        f"{expected_line} was CERTIFIED ({len(proved)} proved row(s))"
                    ),
                    detail=tuple(
                        f"proved: {row.get('obligation_id', '<no id>')} "
                        f"solver={row.get('solver')} "
                        f"proof_evidence.status="
                        f"{(row.get('proof_evidence') or {}).get('status')} "
                        f"[{row_identity_text(row)}]"
                        for row in proved
                    ),
                )
            )

        # EXISTENCE PIN: the canary row must still be there, under this exact
        # content identity. `>= 1`, not `== 1`: a same-identity twin is the
        # soundness pathology above, not a broken pin, and must not be reported
        # as one — when a twin IS certified the CERTIFIED finding already owns
        # it, and duplicating it here would restate a soundness failure at the
        # wrong severity. Zero matches is a vanished/moved/renamed/retyped canary
        # and is a hard failure.
        if not pinned:
            report.findings.append(
                Finding(
                    severity="PIN",
                    canary=name,
                    summary=(
                        f"EXISTENCE PIN — no row matches the pinned identity "
                        f"`{expected_kind}#{identity.family}` at "
                        f"{expected_line}:{identity.col_start}"
                        f"(+{identity.line_span} lines) "
                        f"typed_kind={identity.typed_kind}"
                    ),
                    detail=tuple(
                        f"observed: {row_identity_text(row)}" for row in results
                    )
                    or ("observed: <no rows>",),
                )
            )
        elif len(pinned) > 1 and not proved:
            report.findings.append(
                Finding(
                    severity="PIN",
                    canary=name,
                    summary=(
                        f"DUPLICATE IDENTITY — {len(pinned)} rows share the pinned identity "
                        f"`{expected_kind}#{identity.family}`, none of them proved; the "
                        "producer emitted an unexplained twin"
                    ),
                    detail=tuple(f"twin: {row_identity_text(row)}" for row in pinned),
                )
            )

        for result in results:
            outcome = result.get("outcome")
            if outcome == "proved":
                report.proved += 1
            elif outcome == "failed":
                report.failed += 1
            elif outcome in {"unknown", "timeout", "timed_out", "skipped"}:
                report.unknown += 1
            elif outcome == "runtime_checked":
                report.runtime_checked += 1
            else:
                raise GateError(f"{name}: unrecognized obligation outcome {outcome!r}")

    return report


def render_findings(report: GateReport, stream: Any) -> None:
    """Print ALL findings, grouped by severity, worst first. Never truncated."""
    certified = report.certified
    pins = report.pin_failures
    print(
        f"SOUNDNESS GATE FAIL: {len(certified)} certification(s), "
        f"{len(pins)} existence-pin failure(s) across "
        f"{len({f.canary for f in report.findings})} canary(ies)",
        file=stream,
    )
    if certified:
        print(
            f"  [2] SOUNDNESS CERTIFICATION — {len(certified)} canary(ies). "
            "The verifier proved a genuinely-false safety obligation; the SMT "
            "context is vacuously UNSAT for that property. Blocks unconditionally.",
            file=stream,
        )
        for finding in certified:
            print(f"    - {finding.canary}: {finding.summary}", file=stream)
            for line in finding.detail:
                print(f"        {line}", file=stream)
    if pins:
        print(
            f"  [1] EXISTENCE-PIN DRIFT — {len(pins)} canary(ies). The canary row "
            "no longer matches its pinned identity (vanished, moved, renamed, or "
            "retyped). NOT a soundness verdict; do not report it as one.",
            file=stream,
        )
        for finding in pins:
            print(f"    - {finding.canary}: {finding.summary}", file=stream)
            for line in finding.detail:
                print(f"        {line}", file=stream)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    args = parser.parse_args()
    try:
        report = check(args.log, args.source)
    except TransportIncomplete as error:
        print(f"SOUNDNESS GATE TRANSPORT INCOMPLETE: {error}", file=sys.stderr)
        return EXIT_TRANSPORT
    except (GateError, OSError) as error:
        print(f"SOUNDNESS GATE FAIL: {error}", file=sys.stderr)
        return EXIT_PIN
    if report.findings:
        render_findings(report, sys.stderr)
        return report.exit_code()
    print(
        f"{report.proved} {report.failed} {report.unknown} "
        f"{report.runtime_checked} {report.total}"
    )
    return EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
