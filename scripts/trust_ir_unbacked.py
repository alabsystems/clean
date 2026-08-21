#!/usr/bin/env python3
"""Explain which trust-ir flip events lack an interpreter or seam agreement.

scripts/trust_ir_axes.py owns the gated flip_backed metrics.  This script is a
diagnostic view of the same population: it names each unbacked DefId, preserves
the exact event multiplicity, and groups the producer's refusal details.

The optional trust-ir dump adds signatures and syntactic entry-parameter
observations.  Those observations are deliberately not called blockers.  The
admission policy is two-sided and evolves in Trust; one emitted module cannot
prove that a parameter would be refused by the current differential.

Use --check when the result will be cited.  It re-runs trust_ir_axes.measure,
requires exact event/backing parity, and refuses every fatal axis invariant.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trust_ir_axes  # noqa: E402  (the sibling import is intentional)


SCHEMA = "clean.trust_ir_unbacked.census.v2"
SUBJECT_CRATE = "clean_kernel"

# This mirrors differential.rs::is_interpretable_scalar at the time this tool
# landed.  It is used only to annotate the producer dump, never to decide
# whether a body is backed or admissible.
_SCALAR_LEAVES = {
    "bool",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "f32",
    "f64",
    "isize",
    "usize",
    "char",
}


def _read_flip_events(log_path: str) -> dict[str, Any]:
    """Parse the same complete flip-event language as trust_ir_axes.measure."""
    codegen: list[int] = []
    ctfe: list[int] = []
    foreign = 0
    unparsed: list[str] = []

    with open(log_path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if "compiled from trust-ir" not in line:
                continue
            match = trust_ir_axes.FLIP_RE.search(line)
            if match is None:
                # A malformed event has unknown artifact identity.  Keep it
                # distinct from a well-formed event for another crate.
                unparsed.append(line.strip()[:200])
                continue
            if SUBJECT_CRATE not in line:
                foreign += 1
                continue
            target = ctfe if match.group("ctfe") else codegen
            target.append(int(match.group("index")))

    return {
        "codegen": codegen,
        "ctfe": ctfe,
        "foreign_flip_events": foreign,
        "flip_events_unparsed": len(unparsed),
        "unparsed_examples": unparsed[:20],
    }


def _read_dump(dump_path: str) -> tuple[dict[str, str], dict[str, str]]:
    """Return def-path to signature and body maps from a trust-ir text dump."""
    with open(dump_path, encoding="utf-8", errors="replace") as handle:
        text = handle.read()

    functy = dict(re.findall(r"^functy\.(\d+) = (.*)$", text, re.M))
    signatures: dict[str, str] = {}
    for name, type_id in re.findall(
        r"^rustcc fn @([^\n]+)\(functy\.(\d+)\) \{$", text, re.M
    ):
        signatures.setdefault(name, functy.get(type_id, "<unresolved functy>"))

    bodies: dict[str, str] = {}
    for match in re.finditer(
        r"^rustcc fn @([^\n]+)\(functy\.\d+\) \{\n(.*?)^\}",
        text,
        re.M | re.S,
    ):
        bodies.setdefault(match.group(1), match.group(2))
    return signatures, bodies


def _split_top_level(text: str) -> list[str]:
    """Split comma-separated block parameters without splitting nested types."""
    pieces: list[str] = []
    start = 0
    depth = 0
    pairs = {"(": ")", "[": "]", "<": ">"}
    closers = set(pairs.values())
    stack: list[str] = []

    for index, char in enumerate(text):
        if char in pairs:
            stack.append(pairs[char])
            depth += 1
        elif char in closers and stack and char == stack[-1]:
            stack.pop()
            depth -= 1
        elif char == "," and depth == 0:
            pieces.append(text[start:index].strip())
            start = index + 1
    tail = text[start:].strip()
    if tail:
        pieces.append(tail)
    return pieces


def _entry_params(body: str) -> list[dict[str, Any]] | None:
    """Describe entry parameters syntactically; make no admission claim."""
    head = re.search(r"^bb0\((.*)\):", body, re.M)
    if head is None:
        return None
    rest = body[head.end() :]
    params: list[dict[str, Any]] = []
    for piece in _split_top_level(head.group(1)):
        match = re.fullmatch(r"%(\d+):\s*(.+)", piece)
        if match is None:
            return None
        value_id = int(match.group(1))
        ty = match.group(2).strip()
        params.append(
            {
                "value_id": value_id,
                "type": ty,
                "scalar_leaf": ty in _SCALAR_LEAVES,
                "mentioned_after_entry": bool(
                    re.search(rf"%{value_id}\b", rest)
                ),
            }
        )
    return params


def _coverage_index(
    coverage: dict[str, Any],
) -> tuple[dict[int, dict[str, Any]], list[int]]:
    by_index: dict[int, dict[str, Any]] = {}
    counts: collections.Counter[int] = collections.Counter()
    for row in coverage["bodies"]:
        index = int(row["def_index"])
        counts[index] += 1
        by_index[index] = row
    collisions = sorted(index for index, count in counts.items() if count != 1)
    return by_index, collisions


def census(
    coverage_path: str,
    log_path: str,
    dump_path: str | None = None,
    *,
    ctfe: bool = False,
) -> dict[str, Any]:
    with open(coverage_path, encoding="utf-8") as handle:
        coverage = json.load(handle)

    by_index, index_collisions = _coverage_index(coverage)
    parsed = _read_flip_events(log_path)
    channel = "ctfe" if ctfe else "codegen"
    events: list[int] = parsed[channel]
    event_counts = collections.Counter(events)
    signatures, dump_bodies = _read_dump(dump_path) if dump_path else ({}, {})

    rows: list[dict[str, Any]] = []
    backed_events = 0
    backed_def_ids = 0
    unjoinable_events = 0
    unjoinable_def_ids = 0

    for index, event_count in sorted(event_counts.items()):
        row = by_index.get(index)
        if row is None:
            unjoinable_events += event_count
            unjoinable_def_ids += 1
            continue

        interpreter = trust_ir_axes._verdict(row, "interpreter")
        seam = trust_ir_axes._verdict(row, "seam")
        if interpreter == "agreed" or seam == "agreed":
            backed_events += event_count
            backed_def_ids += 1
            continue

        differentials = row["differentials"]
        body = dump_bodies.get(row["def_path"])
        rows.append(
            {
                "def_path": row["def_path"],
                "def_index": index,
                "event_count": event_count,
                "signature": signatures.get(row["def_path"], ""),
                "entry_params": _entry_params(body) if body is not None else None,
                "instr_count": row.get("instr_count"),
                "interpreter_verdict": interpreter,
                "interpreter_detail": differentials["interpreter"].get("detail", ""),
                "seam_state": (differentials.get("seam") or {}).get("state"),
                "seam_verdict": seam,
                "derived_mir_verdict": trust_ir_axes._verdict(row, "derived_mir"),
            }
        )

    unbacked_events = sum(row["event_count"] for row in rows)
    dump_missing = (
        sorted(row["def_path"] for row in rows if row["entry_params"] is None)
        if dump_path
        else []
    )
    return {
        "schema": SCHEMA,
        "crate": coverage.get("crate"),
        "channel": channel,
        "flip_events": len(events),
        "flip_def_ids": len(event_counts),
        "backed": backed_events,
        "backed_def_ids": backed_def_ids,
        "unbacked": unbacked_events,
        "unbacked_def_ids": len(rows),
        "flip_events_unjoinable": unjoinable_events,
        "flip_def_ids_unjoinable": unjoinable_def_ids,
        "foreign_flip_events": parsed["foreign_flip_events"],
        "flip_events_unparsed": parsed["flip_events_unparsed"],
        "coverage_def_index_collisions": index_collisions,
        "ir_dump_unjoinable": dump_missing,
        "unparsed_examples": parsed["unparsed_examples"],
        "unbacked_flips": rows,
    }


def _axis_parity(
    data: dict[str, Any], coverage_path: str, log_path: str
) -> tuple[list[str], dict[str, Any]]:
    """Compare this diagnostic with the authoritative axis implementation."""
    axis = trust_ir_axes.measure(coverage_path, log_path)
    measured = axis["measured"]
    suffix = "ctfe" if data["channel"] == "ctfe" else "codegen"
    expected = {
        "flip_events": measured[f"flip_events_{suffix}"],
        "backed": measured[f"flip_backed_{suffix}"],
        "foreign_flip_events": axis["invariants"]["foreign_flip_events"],
        "flip_events_unparsed": axis["invariants"]["flip_events_unparsed"],
    }
    mismatches = [
        f"{key}: census={data[key]!r}, trust_ir_axes={value!r}"
        for key, value in expected.items()
        if data[key] != value
    ]

    # The selected channel must partition into backed, unbacked, and rows that
    # could not be joined.  This catches event-vs-DefId count mixing locally.
    partition = (
        data["backed"] + data["unbacked"] + data["flip_events_unjoinable"]
    )
    if partition != data["flip_events"]:
        mismatches.append(
            "event partition: "
            f"{data['backed']} + {data['unbacked']} + "
            f"{data['flip_events_unjoinable']} != {data['flip_events']}"
        )
    return mismatches, axis


def check(
    data: dict[str, Any], coverage_path: str, log_path: str, dump_path: str | None
) -> list[str]:
    """Return every reproducibility failure; an empty result is a checked census."""
    errors, axis = _axis_parity(data, coverage_path, log_path)
    if data["crate"] != SUBJECT_CRATE:
        errors.append(
            f"coverage crate is {data['crate']!r}, expected {SUBJECT_CRATE!r}"
        )
    if data["coverage_def_index_collisions"]:
        errors.append(
            "coverage has duplicate def_index rows: "
            + ", ".join(map(str, data["coverage_def_index_collisions"]))
        )
    if dump_path and data["ir_dump_unjoinable"]:
        errors.append(
            "unbacked rows absent or unparsable in IR dump: "
            + ", ".join(data["ir_dump_unjoinable"][:20])
        )
    for key, _why in trust_ir_axes.FATAL_INVARIANTS:
        value = axis["invariants"][key]
        if value:
            errors.append(f"trust_ir_axes invariant {key}={value}")
    return errors


def report(data: dict[str, Any]) -> None:
    print(f"crate {data['crate']}  channel {data['channel']}")
    print(
        f"  flip events {data['flip_events']} ({data['flip_def_ids']} DefIds)"
        f"   backed {data['backed']} ({data['backed_def_ids']} DefIds)"
        f"   UNBACKED {data['unbacked']} ({data['unbacked_def_ids']} DefIds)"
    )
    if (
        data["flip_events_unjoinable"]
        or data["foreign_flip_events"]
        or data["flip_events_unparsed"]
        or data["coverage_def_index_collisions"]
    ):
        print(
            "  !! "
            f"unjoinable {data['flip_events_unjoinable']}, "
            f"foreign {data['foreign_flip_events']}, "
            f"unparsed {data['flip_events_unparsed']}, "
            f"duplicate coverage indexes "
            f"{len(data['coverage_def_index_collisions'])}"
        )
    if not data["unbacked_flips"]:
        return

    buckets: dict[tuple[str, str], list[dict[str, Any]]] = (
        collections.OrderedDict()
    )
    for row in data["unbacked_flips"]:
        reason = row["interpreter_detail"].split(":")[0].split(";")[0].strip()
        buckets.setdefault((row["interpreter_verdict"], reason), []).append(row)

    print()
    for (verdict, reason), group in sorted(
        buckets.items(), key=lambda item: -sum(r["event_count"] for r in item[1])
    ):
        event_count = sum(row["event_count"] for row in group)
        print(
            f"=== [{event_count:3d} event(s), {len(group):3d} DefId(s)] "
            f"interpreter={verdict} :: {reason}"
        )
        details = collections.Counter(
            row["interpreter_detail"] for row in group
        )
        if len(details) > 1:
            for detail, count in details.most_common():
                print(f"      [{count} DefId(s)] {detail}")
        for row in group:
            signature = f"  {row['signature']}" if row["signature"] else ""
            multiplicity = (
                f" [events={row['event_count']}]" if row["event_count"] != 1 else ""
            )
            print(f"      - {row['def_path']}{multiplicity}{signature}")
        print()

    observations: collections.Counter[str] = collections.Counter()
    for row in data["unbacked_flips"]:
        for param in row["entry_params"] or []:
            if param["scalar_leaf"]:
                continue
            use = "mentioned" if param["mentioned_after_entry"] else "unmentioned"
            observations[f"{use} {param['type']}"] += 1
    if observations:
        print("ENTRY-PARAM OBSERVATIONS (producer IR only; not admission verdicts):")
        for observation, count in observations.most_common():
            print(f"  {count:3d}  {observation}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--coverage", required=True)
    parser.add_argument("--log", required=True)
    parser.add_argument(
        "--ir-dump",
        default=None,
        help="trust-ir text dump, used only for signatures and parameter observations",
    )
    parser.add_argument("--ctfe", action="store_true", help="census the CTFE channel")
    parser.add_argument("--json", default=None)
    parser.add_argument(
        "--check",
        action="store_true",
        help="require exact trust_ir_axes parity and all fatal invariants to be zero",
    )
    args = parser.parse_args()

    data = census(args.coverage, args.log, args.ir_dump, ctfe=args.ctfe)
    report(data)

    if args.check:
        errors = check(data, args.coverage, args.log, args.ir_dump)
        if errors:
            for error in errors:
                print(f"CHECK FAIL: {error}", file=sys.stderr)
            return 1
        print("CHECK PASS: exact trust_ir_axes parity; all fatal invariants are zero")

    # In checked mode, never publish a JSON artifact before the parity and
    # invariant checks succeed.  A failed command may report diagnostics to the
    # terminal, but it must not mint a file that looks authoritative.
    if args.json:
        with open(args.json, "w", encoding="utf-8") as handle:
            handle.write(json.dumps(data, indent=1) + "\n")
        print(f"wrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
