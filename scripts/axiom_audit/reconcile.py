#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Reconcile per-conjecture rows in `data/axiom_audit.json` (#3640).

CANONICAL SOURCE: alabsystems/clean

This module compares the stored per-conjecture counters against live
`verify_gamma_crown --json` output and either checks or rewrites the
stored rows.

Usage:
  python3 -m scripts.axiom_audit.reconcile
  python3 -m scripts.axiom_audit.reconcile --check --snapshot /tmp/verify_gc.json
"""

from __future__ import annotations

__all__ = [
    "ReconcileResult",
    "RowDrift",
    "check_drift",
    "load_live_snapshot",
    "main",
    "reconcile_rows",
    "run_verify_gamma_crown",
]

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from scripts.axiom_audit.aggregates import load_audit, write_aggregates

FieldKind = Literal["int", "bool"]

_LIVE_TO_STORED_FIELDS: tuple[tuple[str, str, FieldKind], ...] = (
    ("domain_axioms", "axioms", "int"),
    ("theorems", "theorems", "int"),
    ("definitions", "definitions", "int"),
    ("opaques", "opaques", "int"),
    ("tc_verified", "tc_verified", "bool"),
    # This is the live kernel bit from `verify_gamma_crown`, not the
    # audit-semantic `proof_mechanism` label stored in axiom_audit.json.
    ("constructive", "constructive", "bool"),
)


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class RowDrift:
    """One conjecture row whose stored counters differ from live."""

    conjecture: str
    deltas: tuple[tuple[str, Any, Any], ...]

    def format(self) -> str:
        parts = [f"{field}: {stored}->{live}" for (field, stored, live) in self.deltas]
        return f"  {self.conjecture}: " + ", ".join(parts)


@dataclass(frozen=True)
class ReconcileResult:
    """Summary of a reconcile pass."""

    drift_rows: tuple[RowDrift, ...]
    missing_from_live: tuple[str, ...]
    missing_from_audit: tuple[str, ...]

    @property
    def is_clean(self) -> bool:
        return (
            not self.drift_rows
            and not self.missing_from_live
            and not self.missing_from_audit
        )


def run_verify_gamma_crown(
    *, repo_root: Path, verbose: bool = False
) -> dict[str, Any]:
    """Invoke the live kernel pipeline and return the parsed JSON."""
    cmd = [
        "cargo",
        "run",
        "--locked",
        "--quiet",
        "--message-format=short",
        "-j",
        os.environ.get("CARGO_BUILD_JOBS", "1"),
        "-p",
        "clean-kernel",
        "--bin",
        "verify_gamma_crown",
        "--features",
        "test-utils math-overlays",
        "--",
        "--json",
    ]
    if verbose:
        print(f"[reconcile_conjecture_axioms] $ {' '.join(cmd)}", file=sys.stderr)
    proc = subprocess.run(
        cmd,
        cwd=str(repo_root),
        capture_output=True,
        text=True,
        check=False,
    )
    if not proc.stdout.strip():
        raise ValueError(
            "verify_gamma_crown produced no stdout\n"
            f"exit={proc.returncode}\nstderr:\n{proc.stderr}"
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"verify_gamma_crown stdout not JSON: {exc}\n"
            f"stdout (first 500 chars):\n{proc.stdout[:500]}"
        ) from exc


def load_live_snapshot(path: Path) -> dict[str, Any]:
    """Load a pre-captured `verify_gamma_crown --json` snapshot."""
    if not path.exists():
        raise FileNotFoundError(f"live snapshot not found: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _live_rows_by_id(live: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = live.get("conjectures")
    if not isinstance(rows, list):
        raise ValueError(
            "live snapshot: missing or non-list 'conjectures' field "
            f"(got {type(rows).__name__})"
        )
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict) or "id" not in row:
            raise ValueError(f"live snapshot: malformed conjecture row {row!r}")
        cid = str(row["id"])
        if cid in out:
            raise ValueError(
                f"live snapshot: duplicate conjecture id {cid!r} in 'conjectures'"
            )
        missing_fields = [
            live_field
            for (live_field, _stored_field, _kind) in _LIVE_TO_STORED_FIELDS
            if live_field not in row
        ]
        if missing_fields:
            raise ValueError(
                f"live snapshot: conjecture {cid} missing required field(s): "
                + ", ".join(missing_fields)
            )
        out[cid] = row
    return out


def _as_int(value: Any, *, field: str, cid: str, source: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(
            f"{source} {cid}.{field}: expected int, got "
            f"{type(value).__name__} ({value!r})"
        )
    return value


def _as_bool(value: Any, *, field: str, cid: str, source: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(
            f"{source} {cid}.{field}: expected bool, got "
            f"{type(value).__name__} ({value!r})"
        )
    return value


def _coerce_field(
    value: Any, *, kind: FieldKind, field: str, cid: str, source: str
) -> int | bool:
    if kind == "int":
        return _as_int(value, field=field, cid=cid, source=source)
    return _as_bool(value, field=field, cid=cid, source=source)


def check_drift(audit: dict[str, Any], live: dict[str, Any]) -> ReconcileResult:
    """Compare stored per-conjecture rows against live."""
    conjectures = audit.get("conjectures")
    if not isinstance(conjectures, dict):
        raise ValueError("axiom_audit.json: missing or non-object 'conjectures'")
    live_by_id = _live_rows_by_id(live)

    drifts: list[RowDrift] = []
    missing_live: list[str] = []
    for cid, entry in conjectures.items():
        if not isinstance(entry, dict):
            raise ValueError(
                f"conjectures.{cid}: expected object, got {type(entry).__name__}"
            )
        if cid not in live_by_id:
            missing_live.append(cid)
            continue
        live_row = live_by_id[cid]
        deltas: list[tuple[str, Any, Any]] = []
        for live_field, stored_field, kind in _LIVE_TO_STORED_FIELDS:
            stored = _coerce_field(
                entry.get(stored_field, 0),
                kind=kind,
                field=stored_field,
                cid=cid,
                source="axiom_audit.json",
            )
            live_val = _coerce_field(
                live_row[live_field],
                kind=kind,
                field=live_field,
                cid=cid,
                source="verify_gamma_crown",
            )
            if stored != live_val:
                deltas.append((stored_field, stored, live_val))
        if deltas:
            drifts.append(RowDrift(conjecture=cid, deltas=tuple(deltas)))

    missing_audit = [cid for cid in live_by_id.keys() if cid not in conjectures]
    return ReconcileResult(
        drift_rows=tuple(drifts),
        missing_from_live=tuple(missing_live),
        missing_from_audit=tuple(missing_audit),
    )


def reconcile_rows(
    audit_path: Path, live: dict[str, Any]
) -> tuple[ReconcileResult, bool]:
    """Apply live counters to the audit file and refresh aggregates."""
    audit = load_audit(audit_path)
    before = check_drift(audit, live)
    live_by_id = _live_rows_by_id(live)
    for cid, entry in audit["conjectures"].items():
        if cid not in live_by_id:
            continue
        live_row = live_by_id[cid]
        for live_field, stored_field, kind in _LIVE_TO_STORED_FIELDS:
            entry[stored_field] = _coerce_field(
                live_row[live_field],
                kind=kind,
                field=live_field,
                cid=cid,
                source="verify_gamma_crown",
            )
    _agg, changed = write_aggregates(audit_path, audit=audit)
    return before, changed


def _format_drift_report(result: ReconcileResult) -> str:
    lines: list[str] = []
    if result.drift_rows:
        lines.append(f"Per-conjecture drift ({len(result.drift_rows)} rows):")
        for row in result.drift_rows:
            lines.append(row.format())
    if result.missing_from_live:
        lines.append("Conjectures in audit but NOT in live (kernel inventory shrank?):")
        for cid in result.missing_from_live:
            lines.append(f"  {cid}")
    if result.missing_from_audit:
        lines.append("Conjectures in live but NOT in audit (new rows needed):")
        for cid in result.missing_from_audit:
            lines.append(f"  {cid}")
    return "\n".join(lines) if lines else "(no drift)"


def _load_live(args: argparse.Namespace, repo_root: Path) -> dict[str, Any]:
    if args.snapshot is not None:
        return load_live_snapshot(args.snapshot)
    return run_verify_gamma_crown(repo_root=repo_root, verbose=args.verbose)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="reconcile_conjecture_axioms",
        description=(
            "Reconcile per-conjecture counters in data/axiom_audit.json "
            "against live `verify_gamma_crown --json` output."
        ),
    )
    parser.add_argument(
        "--audit",
        type=Path,
        default=None,
        help="Path to axiom_audit.json (default: <repo>/data/axiom_audit.json)",
    )
    parser.add_argument(
        "--snapshot",
        type=Path,
        default=None,
        help=(
            "Path to a pre-captured verify_gamma_crown --json file. "
            "When omitted, a locked short-diagnostic single-job `cargo run` "
            "is invoked to produce one live."
        ),
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Echo cargo invocations to stderr.",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write",
        dest="mode",
        action="store_const",
        const="write",
        help="(default) Reconcile rows from live and write aggregates.",
    )
    mode.add_argument(
        "--check",
        dest="mode",
        action="store_const",
        const="check",
        help="Verify stored rows match live. Exit 1 on drift. Does NOT mutate.",
    )
    parser.set_defaults(mode="write")
    return parser


def _run_check_mode(audit_path: Path, live: dict[str, Any]) -> int:
    audit = load_audit(audit_path)
    result = check_drift(audit, live)
    if not result.is_clean:
        sys.stderr.write("reconcile_conjecture_axioms: drift detected.\n")
        sys.stderr.write(_format_drift_report(result) + "\n")
        sys.stderr.write(
            "\nFix: run `python3 -m scripts.axiom_audit.reconcile` "
            "to refresh rows from live, then re-stage.\n"
        )
        return 1
    sys.stdout.write(
        "reconcile_conjecture_axioms: OK — "
        f"all {len(audit['conjectures'])} rows match live.\n"
    )
    return 0


def _run_write_mode(audit_path: Path, live: dict[str, Any]) -> int:
    before, changed = reconcile_rows(audit_path, live)
    if before.is_clean and not changed:
        sys.stdout.write(
            "reconcile_conjecture_axioms: unchanged — rows already match live.\n"
        )
        return 0
    sys.stdout.write(
        f"reconcile_conjecture_axioms: UPDATED {audit_path}.\n"
        f"{_format_drift_report(before)}\n"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    repo_root = _repo_root()
    audit_path = args.audit or (repo_root / "data" / "axiom_audit.json")

    try:
        live = _load_live(args, repo_root)
        if args.mode == "check":
            return _run_check_mode(audit_path, live)
        return _run_write_mode(audit_path, live)
    except FileNotFoundError as exc:
        sys.stderr.write(f"reconcile_conjecture_axioms: {exc}\n")
        return 2
    except ValueError as exc:
        sys.stderr.write(f"reconcile_conjecture_axioms: {exc}\n")
        return 2
    except subprocess.CalledProcessError as exc:
        sys.stderr.write(
            f"reconcile_conjecture_axioms: cargo invocation failed: {exc}\n"
        )
        return 2


if __name__ == "__main__":
    sys.exit(main())
