#!/usr/bin/env python3
"""Fail closed unless every Trust soundness canary remains individually unproved.

The aggregate proved/unproved ratchet is useful landscape telemetry, but it
cannot identify which obligation changed: one false proof can be hidden by an
unrelated obligation disappearing or becoming unknown.  This checker consumes
the compiler's structured transport and binds each canary function to the
specific VC family that is intentionally false.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


TRANSPORT_PREFIX = "TRUST_JSON:"

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

# A source span is not a unique obligation identity. In particular, rustc's
# division/remainder lowering has long emitted two same-kind transport rows at
# the same expression span: the genuinely false zero-divisor row and an
# independently provable auxiliary row. Pin the full producer-owned obligation
# suffix (family plus local ordinal), as well as kind and line, so an auxiliary
# proof neither false-alarms nor masks a proof of the actual canary.
EXPECTED_FALSE_SUFFIXES = {
    "sentinel_oob_index_must_not_prove": "bounds_check:0",
    "sentinel_div_by_zero_must_not_prove": "arithmetic_safety:0",
    "sentinel_lossy_narrowing_cast_must_not_prove": "bounds_check:0",
    "sentinel_unguarded_add_overflow_must_not_prove": "arithmetic_safety:0",
    "sentinel_remainder_by_zero_must_not_prove": "arithmetic_safety:0",
    "sentinel_sub_underflow_must_not_prove": "arithmetic_safety:0",
    "sentinel_mul_overflow_must_not_prove": "arithmetic_safety:0",
    "sentinel_slice_range_oob_must_not_prove": "bounds_check:0",
    "sentinel_shift_overflow_must_not_prove": "arithmetic_safety:0",
    "sentinel_loop_off_by_one_must_not_prove": "bounds_check:0",
    "sentinel_clamp_still_oob_must_not_prove": "bounds_check:0",
    "sentinel_multivar_guard_lossy_must_not_prove": "bounds_check:1",
    "sentinel_stale_guard_must_not_prove": "bounds_check:0",
    "sentinel_intrinsic_bound_must_not_prove": "bounds_check:0",
    "sentinel_accumulator_overflow_must_not_prove": "arithmetic_safety:0",
}


class GateError(ValueError):
    """The transport is incomplete, malformed, or falsely proves a canary."""


class SoundnessRegression(GateError):
    """A genuinely-false canary obligation was reported as proved."""


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
    """Map each canary to its marked VC kind, exact suffix, and source line."""
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
            kind, suffix = token.rsplit("#", 1)
            family, ordinal_text = suffix.rsplit(":", 1)
            ordinal = int(ordinal_text)
        except (ValueError, IndexError) as error:
            raise GateError(
                f"false-canary marker on line {line_number} must be "
                "`kind#family:ordinal`"
            ) from error
        if not kind or not family or ordinal < 0:
            raise GateError(
                f"false-canary marker on line {line_number} has an invalid kind or suffix"
            )
        if current in markers:
            raise GateError(f"{current}: multiple false-canary markers")
        markers[current] = (kind, suffix, line_number)
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
            raise GateError(
                f"malformed Trust transport on log line {line_number}: {error}"
            ) from error
        if not isinstance(value, dict):
            raise GateError(f"non-object Trust transport on log line {line_number}")
        messages.append(value)
    if not messages:
        raise GateError("no TRUST_JSON transport found; structured verification did not run")
    return messages


def check(log: Path, source: Path) -> tuple[int, int, int, int, int]:
    declared = sentinel_names_from_source(source)
    expected = set(EXPECTED_FALSE_KINDS)
    if set(EXPECTED_FALSE_SUFFIXES) != expected:
        raise GateError("false-canary suffix inventory does not match kind inventory")
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
        marker_kind, marker_suffix, _ = markers[name]
        if marker_kind != expected_kind:
            raise GateError(
                f"{name}: source marker names `{marker_kind}`, expected `{expected_kind}`"
            )
        expected_suffix = EXPECTED_FALSE_SUFFIXES[name]
        if marker_suffix != expected_suffix:
            raise GateError(
                f"{name}: source marker names suffix `{marker_suffix}`, "
                f"expected `{expected_suffix}`"
            )

    rows: dict[str, list[dict[str, Any]]] = {name: [] for name in expected}
    for message in transport_messages(log):
        if message.get("type") != "function_result":
            continue
        function = message.get("function")
        if not isinstance(function, str):
            raise GateError("function_result transport has no string function identity")
        short_name = function.rsplit("::", 1)[-1]
        if short_name in rows:
            rows[short_name].append(message)

    totals = {"proved": 0, "failed": 0, "unknown": 0, "runtime_checked": 0, "other": 0}
    for name in sorted(expected):
        function_rows = rows[name]
        if len(function_rows) != 1:
            raise GateError(
                f"{name}: expected exactly one function_result row, found {len(function_rows)}"
            )
        results = function_rows[0].get("results")
        if not isinstance(results, list) or not results:
            raise GateError(f"{name}: missing non-empty obligation result inventory")

        expected_kind = EXPECTED_FALSE_KINDS[name]
        expected_suffix = EXPECTED_FALSE_SUFFIXES[name]
        _, _, expected_line = markers[name]
        matching = [
            row
            for row in results
            if isinstance(row, dict)
            and row.get("kind") == expected_kind
            and isinstance(row.get("location"), dict)
            and row["location"].get("line_start") == expected_line
            and isinstance(row.get("obligation_id"), str)
            and row["obligation_id"].endswith(f":{expected_suffix}")
        ]
        if len(matching) != 1:
            observed = sorted(
                {
                    f"{row.get('kind')}@{(row.get('location') or {}).get('line_start')}"
                    f"#{':'.join(str(row.get('obligation_id', '')).rsplit(':', 2)[-2:])}"
                    for row in results
                    if isinstance(row, dict)
                }
            )
            raise GateError(
                f"{name}: expected exactly one false `{expected_kind}#{expected_suffix}` "
                f"obligation at source line {expected_line}, found {len(matching)} "
                f"(observed kind@line#suffix: {', '.join(observed) or '<none>'})"
            )
        proved = [row for row in matching if row.get("outcome") == "proved"]
        if proved:
            raise SoundnessRegression(
                f"SOUNDNESS REGRESSION — {name}: genuinely-false `{expected_kind}` "
                f"obligation was CERTIFIED ({len(proved)} proved row(s))"
            )

        for result in results:
            if not isinstance(result, dict):
                raise GateError(f"{name}: non-object obligation result")
            outcome = result.get("outcome")
            if outcome == "proved":
                totals["proved"] += 1
            elif outcome == "failed":
                totals["failed"] += 1
            elif outcome in {"unknown", "timeout", "timed_out", "skipped"}:
                totals["unknown"] += 1
            elif outcome == "runtime_checked":
                totals["runtime_checked"] += 1
            else:
                totals["other"] += 1

    if totals["other"]:
        raise GateError(f"encountered {totals['other']} unrecognized obligation outcome(s)")
    total = totals["proved"] + totals["failed"] + totals["unknown"] + totals["runtime_checked"]
    return (
        totals["proved"],
        totals["failed"],
        totals["unknown"],
        totals["runtime_checked"],
        total,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    args = parser.parse_args()
    try:
        proved, failed, unknown, runtime_checked, total = check(args.log, args.source)
    except SoundnessRegression as error:
        print(f"SOUNDNESS GATE FAIL: {error}", file=sys.stderr)
        return 2
    except (GateError, OSError) as error:
        print(f"SOUNDNESS GATE FAIL: {error}", file=sys.stderr)
        return 1
    print(f"{proved} {failed} {unknown} {runtime_checked} {total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
