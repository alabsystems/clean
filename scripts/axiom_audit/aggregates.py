#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Maintain top-level aggregates in `data/axiom_audit.json` (#3613, #3641).

CANONICAL SOURCE: alabsystems/clean

`data/axiom_audit.json` stores, at the top level, four aggregate metrics
computed from the per-conjecture `.conjectures.{C001-C030}` sub-trees
and (if present) the `.non_conjecture_axioms.per_prefix` block:

  * `total_domain_axioms`   = sum of `.axioms`   across all conjectures
  * `total_theorems`        = sum of `.theorems` across all conjectures
  * `constructive_theorems` = sum of `.theorems` across conjectures whose
                              `constructive` flag is `true`
  * `total_all_axioms`      = `total_domain_axioms`
                              + sum of `.non_conjecture_axioms.per_prefix.*.count`
                              (reconciles per-conjecture-prefix tally with
                              kernel-wide domain-axiom footprint)

Per `design doc` §"Proof Soundness Rules" `total_domain_axioms` is a
ratcheting metric: it must decrease or stay flat across commits, never
increase without a justifying issue. A `null` or stale aggregate violates
the ratchet invariant because there is no trustworthy baseline to compare
against. `total_all_axioms` is an informational companion — it makes the
structural gap between per-conjecture rows and broader kernel axiom tally
visible and auditable (#3641).

Usage:
  python3 -m scripts.axiom_audit.aggregates            # writes
  python3 -m scripts.axiom_audit.aggregates --check    # verify
  python3 -m scripts.axiom_audit.aggregates \
      --audit path/to/axiom_audit.json --check
"""

from __future__ import annotations

__all__ = [
    "AGGREGATE_KEYS",
    "NON_CONJECTURE_AXIOMS_KEY",
    "Aggregates",
    "AggregateMismatch",
    "compute_aggregates",
    "compute_non_conjecture_axiom_total",
    "load_audit",
    "write_aggregates",
    "verify_aggregates",
    "main",
]

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


AGGREGATE_KEYS: tuple[str, ...] = (
    "total_domain_axioms",
    "total_theorems",
    "constructive_theorems",
    "total_all_axioms",
)

NON_CONJECTURE_AXIOMS_KEY = "non_conjecture_axioms"


def _repo_root() -> Path:
    """Resolve the repo root by walking up from this file."""
    return Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class Aggregates:
    """Computed top-level aggregates."""

    total_domain_axioms: int
    total_theorems: int
    constructive_theorems: int
    total_all_axioms: int

    def as_dict(self) -> dict[str, int]:
        return {
            "total_domain_axioms": self.total_domain_axioms,
            "total_theorems": self.total_theorems,
            "constructive_theorems": self.constructive_theorems,
            "total_all_axioms": self.total_all_axioms,
        }


class AggregateMismatch(Exception):
    """Raised when stored aggregates disagree with the recomputed values."""


def _as_int_count(value: Any, field: str, cid: str) -> int:
    """Interpret a per-conjecture `axioms` / `theorems` field as an int."""
    if isinstance(value, bool):
        raise ValueError(
            f"conjectures.{cid}.{field}: unexpected bool; want int or list[str]"
        )
    if isinstance(value, int):
        if value < 0:
            raise ValueError(
                f"conjectures.{cid}.{field}: negative count {value!r}"
            )
        return value
    if isinstance(value, list):
        return len(value)
    raise ValueError(
        f"conjectures.{cid}.{field}: expected int or list, got "
        f"{type(value).__name__} ({value!r})"
    )


def compute_non_conjecture_axiom_total(audit: dict[str, Any]) -> int:
    """Sum the `non_conjecture_axioms.per_prefix.*.count` block."""
    block = audit.get(NON_CONJECTURE_AXIOMS_KEY)
    if block is None:
        return 0
    if not isinstance(block, dict):
        raise ValueError(
            f"{NON_CONJECTURE_AXIOMS_KEY}: expected object, got {type(block).__name__}"
        )
    per_prefix = block.get("per_prefix", {})
    if not isinstance(per_prefix, dict):
        raise ValueError(
            f"{NON_CONJECTURE_AXIOMS_KEY}.per_prefix: expected object, got "
            f"{type(per_prefix).__name__}"
        )
    total = 0
    for prefix, entry in per_prefix.items():
        if not isinstance(entry, dict):
            raise ValueError(
                f"{NON_CONJECTURE_AXIOMS_KEY}.per_prefix.{prefix}: "
                f"expected object, got {type(entry).__name__}"
            )
        count = entry.get("count")
        if isinstance(count, bool) or not isinstance(count, int):
            raise ValueError(
                f"{NON_CONJECTURE_AXIOMS_KEY}.per_prefix.{prefix}.count: "
                f"expected int, got {type(count).__name__} ({count!r})"
            )
        if count < 0:
            raise ValueError(
                f"{NON_CONJECTURE_AXIOMS_KEY}.per_prefix.{prefix}.count: "
                f"negative value {count}"
            )
        total += count
    return total


def compute_aggregates(audit: dict[str, Any]) -> Aggregates:
    """Recompute the four top-level aggregates from `.conjectures`."""
    conjectures = audit.get("conjectures")
    if not isinstance(conjectures, dict):
        raise ValueError("axiom_audit.json: missing or non-object 'conjectures' field")

    total_axioms = 0
    total_theorems = 0
    constructive_theorems = 0
    for cid, entry in conjectures.items():
        if not isinstance(entry, dict):
            raise ValueError(
                f"conjectures.{cid}: expected object, got {type(entry).__name__}"
            )
        n_axioms = _as_int_count(entry.get("axioms", 0), "axioms", cid)
        n_theorems = _as_int_count(entry.get("theorems", 0), "theorems", cid)
        total_axioms += n_axioms
        total_theorems += n_theorems
        if entry.get("constructive") is True:
            constructive_theorems += n_theorems

    non_conjecture = compute_non_conjecture_axiom_total(audit)
    return Aggregates(
        total_domain_axioms=total_axioms,
        total_theorems=total_theorems,
        constructive_theorems=constructive_theorems,
        total_all_axioms=total_axioms + non_conjecture,
    )


def load_audit(path: Path) -> dict[str, Any]:
    """Load and minimally validate the audit file."""
    if not path.exists():
        raise FileNotFoundError(f"axiom audit file not found: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _apply_aggregates(
    audit: dict[str, Any], new_values: Aggregates
) -> dict[str, Any]:
    """Return a new dict with aggregate fields updated in place."""
    new_dict = new_values.as_dict()
    existing_agg_keys = [k for k in audit.keys() if k in AGGREGATE_KEYS]
    missing_agg_keys = [k for k in AGGREGATE_KEYS if k not in audit]

    if existing_agg_keys:
        anchor: str | None = existing_agg_keys[-1]
    elif "last_updated" in audit:
        anchor = "last_updated"
    else:
        anchor = None

    out: dict[str, Any] = {}
    if anchor is None and missing_agg_keys:
        for agg_key in missing_agg_keys:
            out[agg_key] = new_dict[agg_key]

    for key, value in audit.items():
        out[key] = new_dict[key] if key in AGGREGATE_KEYS else value
        if key == anchor and missing_agg_keys:
            for agg_key in missing_agg_keys:
                out[agg_key] = new_dict[agg_key]

    return out


def _serialize(audit: dict[str, Any]) -> str:
    """Serialize with the file's canonical format."""
    return json.dumps(audit, indent=2, sort_keys=False, ensure_ascii=True) + "\n"


def write_aggregates(
    path: Path, *, audit: dict[str, Any] | None = None
) -> tuple[Aggregates, bool]:
    """Recompute aggregates and write them back. Idempotent."""
    if audit is None:
        audit = load_audit(path)
    aggregates = compute_aggregates(audit)
    updated = _apply_aggregates(audit, aggregates)
    new_text = _serialize(updated)
    old_text = path.read_text(encoding="utf-8") if path.exists() else ""
    if new_text == old_text:
        return aggregates, False
    path.write_text(new_text, encoding="utf-8")
    return aggregates, True


def verify_aggregates(path: Path) -> Aggregates:
    """Raise AggregateMismatch if the stored values are stale or invalid."""
    audit = load_audit(path)
    recomputed = compute_aggregates(audit)
    recomputed_dict = recomputed.as_dict()

    errs: list[str] = []
    for key in AGGREGATE_KEYS:
        if key not in audit:
            errs.append(f"  {key}: missing (want {recomputed_dict[key]})")
            continue
        stored = audit[key]
        if stored is None:
            errs.append(
                f"  {key}: null — violates ratchet invariant "
                f"(want {recomputed_dict[key]})"
            )
            continue
        if isinstance(stored, bool) or not isinstance(stored, int):
            errs.append(
                f"  {key}: non-integer {stored!r} "
                f"(want int {recomputed_dict[key]})"
            )
            continue
        if stored < 0:
            errs.append(
                f"  {key}: negative {stored} (want {recomputed_dict[key]})"
            )
            continue
        if stored != recomputed_dict[key]:
            errs.append(
                f"  {key}: stored {stored}, recomputed {recomputed_dict[key]}"
            )
    if errs:
        raise AggregateMismatch(
            "axiom_audit.json aggregates are stale or invalid:\n"
            + "\n".join(errs)
            + "\n\nRun: python3 -m scripts.axiom_audit.aggregates\n"
            "to refresh the aggregates from .conjectures, then re-stage."
        )
    return recomputed


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="recompute_axiom_audit_aggregates",
        description=(
            "Recompute and maintain the top-level aggregate fields "
            "(total_domain_axioms, total_theorems, constructive_theorems) "
            "in data/axiom_audit.json."
        ),
    )
    parser.add_argument(
        "--audit",
        type=Path,
        default=None,
        help="Path to axiom_audit.json (default: <repo>/data/axiom_audit.json)",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write",
        dest="mode",
        action="store_const",
        const="write",
        help="(default) Recompute and write aggregates back to the file.",
    )
    mode.add_argument(
        "--check",
        dest="mode",
        action="store_const",
        const="check",
        help=(
            "Verify stored aggregates match the live recomputation. "
            "Exit 1 on mismatch (null, stale, wrong type). Does NOT mutate."
        ),
    )
    parser.set_defaults(mode="write")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    repo_root = _repo_root()
    audit_path = args.audit or (repo_root / "data" / "axiom_audit.json")

    try:
        if args.mode == "check":
            aggregates = verify_aggregates(audit_path)
            sys.stdout.write(
                "recompute_axiom_audit_aggregates: OK — "
                f"total_domain_axioms={aggregates.total_domain_axioms}, "
                f"total_theorems={aggregates.total_theorems}, "
                f"constructive_theorems={aggregates.constructive_theorems}, "
                f"total_all_axioms={aggregates.total_all_axioms}\n"
            )
            return 0

        aggregates, changed = write_aggregates(audit_path)
        if changed:
            sys.stdout.write(
                f"recompute_axiom_audit_aggregates: UPDATED {audit_path} — "
                f"total_domain_axioms={aggregates.total_domain_axioms}, "
                f"total_theorems={aggregates.total_theorems}, "
                f"constructive_theorems={aggregates.constructive_theorems}, "
                f"total_all_axioms={aggregates.total_all_axioms}\n"
            )
        else:
            sys.stdout.write(
                "recompute_axiom_audit_aggregates: unchanged — "
                f"total_domain_axioms={aggregates.total_domain_axioms}, "
                f"total_theorems={aggregates.total_theorems}, "
                f"constructive_theorems={aggregates.constructive_theorems}, "
                f"total_all_axioms={aggregates.total_all_axioms}\n"
            )
        return 0
    except FileNotFoundError as exc:
        sys.stderr.write(f"recompute_axiom_audit_aggregates: {exc}\n")
        return 2
    except ValueError as exc:
        sys.stderr.write(f"recompute_axiom_audit_aggregates: {exc}\n")
        return 2
    except AggregateMismatch as exc:
        sys.stderr.write(f"recompute_axiom_audit_aggregates: {exc}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())

