#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""
Compute specification status metrics for Phase 4 tracking.

This script parses the spec definition files and counts:
- Total definitions
- Definitions by ProofStatus (Axiom, DerivedPending, DerivedProved)
- Definitions by AxiomCategory (FoundationalRule, DerivedLemma, HelperAxiom)
- Derivability percentage

Usage:
    python3 scripts/spec_metrics.py              # Print JSON to stdout
    python3 scripts/spec_metrics.py --summary    # Print summary table
    python3 scripts/spec_metrics.py --file FILE  # Write to file

Output fields:
    - total_definitions: count of add_definition() calls
    - total_inductives: count of add_inductive() calls (each creates type+recursor+ctors)
    - total_recursive: count of add_recursive_def() calls
    - total: sum of above (source calls, not runtime definitions)
    - by_proof_status: counts from explicit ProofStatus:: assignments in source
    - by_category: counts from AxiomCategory:: assignments in source
    - derivability_pct: (proved + 0.5*pending) / total, with partial credit
    - strict_derivability_pct: proved / total, no partial credit

Note: Counts are from source pattern matching. add_inductive creates multiple
runtime definitions (type + recursor + constructors + aliases), so actual
definition count is higher. proof_status counts only apply to add_definition
calls that have explicit ProofStatus assignments.
"""

import argparse
import json
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import NamedTuple

DETERMINISTIC_TIMESTAMP = "1970-01-01T00:00:00"


class SpecCounts(NamedTuple):
    """Specification definition counts."""

    add_definition: int
    add_inductive: int
    add_recursive: int
    proof_status: dict[str, int]
    category: dict[str, int]


def count_spec_definitions(repo_root: Path | None = None) -> SpecCounts:
    """Count spec definitions from source files.

    Parses:
    - self.add_definition calls
    - self.add_inductive calls
    - self.add_recursive calls
    - proof_status: ProofStatus::* assignments
    - category: AxiomCategory::* assignments
    """
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[1]

    spec_dir = repo_root / "crates" / "clean-verify" / "src" / "spec"
    if not spec_dir.exists():
        return SpecCounts(0, 0, 0, {}, {})

    add_definition_count = 0
    add_inductive_count = 0
    add_recursive_count = 0
    proof_status: dict[str, int] = {
        "Axiom": 0,
        "DerivedPending": 0,
        "DerivedProved": 0,
    }
    category: dict[str, int] = {
        "FoundationalRule": 0,
        "DerivedLemma": 0,
        "HelperAxiom": 0,
    }

    # Patterns to match
    add_def_pattern = re.compile(r"self\.add_definition\s*\(")
    add_ind_pattern = re.compile(r"self\.add_inductive\s*\(")
    add_rec_pattern = re.compile(r"self\.add_recursive_def\s*\(")
    # Match explicit ProofStatus assignments (not default())
    proof_status_explicit = re.compile(
        r"proof_status:\s*ProofStatus::(Axiom|DerivedPending|DerivedProved)"
    )
    # Match default() assignments (count as Axiom)
    proof_status_default = re.compile(r"proof_status:\s*ProofStatus::default\(\)")
    category_pattern = re.compile(r"category:\s*AxiomCategory::(\w+)")

    for rs_file in sorted(spec_dir.glob("*.rs")):
        try:
            content = rs_file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue

        # Count add_* calls
        add_definition_count += len(add_def_pattern.findall(content))
        add_inductive_count += len(add_ind_pattern.findall(content))
        add_recursive_count += len(add_rec_pattern.findall(content))

        # Count proof_status assignments
        # Explicit status assignments
        for match in proof_status_explicit.findall(content):
            if match in proof_status:
                proof_status[match] += 1
        # Default assignments count as Axiom
        default_count = len(proof_status_default.findall(content))
        proof_status["Axiom"] += default_count

        # Count category assignments
        for match in category_pattern.findall(content):
            if match in category:
                category[match] += 1

    return SpecCounts(
        add_definition=add_definition_count,
        add_inductive=add_inductive_count,
        add_recursive=add_recursive_count,
        proof_status=proof_status,
        category=category,
    )


def compute_derivability(counts: SpecCounts) -> float:
    """Compute derivability percentage.

    This measures how many definitions have constructive proofs vs axioms.

    - DerivedProved: Has constructive proof (goal state)
    - DerivedPending: Has proof but depends on helper axioms (partial credit)
    - Axiom: No proof yet (needs work)

    Derivability = (DerivedProved + 0.5*DerivedPending) / (DerivedProved + DerivedPending + Axiom)

    This gives partial credit for DerivedPending since they have proofs,
    just not fully constructive from the trusted base.
    """
    proved = counts.proof_status.get("DerivedProved", 0)
    pending = counts.proof_status.get("DerivedPending", 0)
    axiom = counts.proof_status.get("Axiom", 0)

    # Total that could potentially be derived
    total = proved + pending + axiom
    if total == 0:
        return 0.0

    # Full credit for DerivedProved, half credit for DerivedPending
    score = proved + 0.5 * pending
    return round(100.0 * score / total, 1)


def get_spec_metrics(
    repo_root: Path | None = None,
    *,
    timestamp: str | None = None,
) -> dict:
    """Get spec metrics as a dictionary.

    Returns:
        Dictionary with spec status metrics suitable for JSON output.
    """
    counts = count_spec_definitions(repo_root)

    total = counts.add_definition + counts.add_inductive + counts.add_recursive
    derivability = compute_derivability(counts)

    # Strict derivability: only fully proven definitions count
    proved = counts.proof_status.get("DerivedProved", 0)
    pending = counts.proof_status.get("DerivedPending", 0)
    axiom = counts.proof_status.get("Axiom", 0)
    proof_total = proved + pending + axiom
    strict_derivability = (
        round(100.0 * proved / proof_total, 1) if proof_total > 0 else 0.0
    )

    return {
        "timestamp": timestamp or datetime.now().isoformat(timespec="seconds"),
        "total_definitions": counts.add_definition,
        "total_inductives": counts.add_inductive,
        "total_recursive": counts.add_recursive,
        "total": total,
        "by_proof_status": counts.proof_status,
        "by_category": counts.category,
        "derivability_pct": derivability,
        "strict_derivability_pct": strict_derivability,
    }


def print_summary(metrics: dict) -> None:
    """Print a human-readable summary table."""
    print("Spec Definition Metrics (source call counts)")
    print("=" * 40)
    print(f"add_definition calls:  {metrics['total_definitions']}")
    print(
        f"add_inductive calls:   {metrics['total_inductives']} (each creates type+rec+ctors)"
    )
    print(f"add_recursive calls:   {metrics['total_recursive']}")
    print(f"Total source calls:    {metrics['total']}")
    print()
    print("By Proof Status (from add_definition only):")
    for status, count in metrics["by_proof_status"].items():
        print(f"  {status:20} {count:5}")
    print()
    print("By Category (from add_definition only):")
    for cat, count in metrics["by_category"].items():
        print(f"  {cat:20} {count:5}")
    print()
    print(f"Derivability:          {metrics['derivability_pct']:.1f}%")
    print(f"Strict derivability:   {metrics['strict_derivability_pct']:.1f}%")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Compute spec definition metrics for Phase 4 tracking"
    )
    parser.add_argument(
        "--summary", action="store_true", help="Print human-readable summary"
    )
    parser.add_argument("--file", type=Path, help="Write JSON output to file")
    parser.add_argument(
        "--repo-root", type=Path, help="Repository root (default: auto-detect)"
    )
    parser.add_argument(
        "--timestamp",
        help="override timestamp in JSON output for reproducible evidence",
    )
    parser.add_argument(
        "--deterministic",
        action="store_true",
        help="use a stable timestamp when --timestamp is omitted",
    )
    args = parser.parse_args(argv)

    timestamp = args.timestamp
    if timestamp is None and args.deterministic:
        timestamp = DETERMINISTIC_TIMESTAMP

    metrics = get_spec_metrics(args.repo_root, timestamp=timestamp)

    if args.summary:
        print_summary(metrics)
        return 0

    output = json.dumps(metrics, indent=2, sort_keys=True)

    if args.file:
        args.file.write_text(output + "\n", encoding="utf-8")
        print(f"Wrote metrics to {args.file}", file=sys.stderr)
    else:
        print(output)

    return 0


if __name__ == "__main__":
    sys.exit(main())
