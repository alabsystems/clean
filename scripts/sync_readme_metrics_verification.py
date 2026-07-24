#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Verification metrics helpers for sync_readme_metrics.py."""

from __future__ import annotations

import logging
import re
from dataclasses import dataclass
from pathlib import Path


def _count_matching_lines(root: Path, *patterns: str) -> int:
    """Count lines matching any literal substring under a root directory."""
    if not root.exists():
        return 0

    total = 0
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        try:
            total += sum(
                1
                for line in path.read_text(encoding="utf-8").splitlines()
                if any(pattern in line for pattern in patterns)
            )
        except (OSError, UnicodeDecodeError):
            pass
    return total


def count_proof_contracts(crates_dir: Path) -> int:
    """Count REQUIRES/ENSURES contract lines under crate src trees."""
    total = 0
    for src_dir in crates_dir.glob("*/src"):
        total += _count_matching_lines(src_dir, "REQUIRES", "ENSURES")
    return total


def count_verus_proofs(root: Path) -> int:
    """Count archived Verus proof fn lines."""
    return _count_matching_lines(root / "archive" / "verus" / "verus-proofs", "proof fn")


def count_property_tests(crates_dir: Path) -> int:
    """Count proptest! lines under crates/."""
    return _count_matching_lines(crates_dir, "proptest!")


def format_number(n: int) -> str:
    """Format a metric count with commas."""
    return f"{n:,}"


@dataclass(frozen=True)
class VerificationMetricsSnapshot:
    """Counts published in docs/VERIFICATION_METRICS.md."""

    proof_contracts: int
    verus_proofs: int
    property_tests: int
    unit_tests: int


def build_verification_metrics_snapshot(
    root: Path,
    crates_dir: Path,
    unit_tests: int,
) -> VerificationMetricsSnapshot:
    """Collect the counts published by docs/VERIFICATION_METRICS.md."""
    return VerificationMetricsSnapshot(
        proof_contracts=count_proof_contracts(crates_dir),
        verus_proofs=count_verus_proofs(root),
        property_tests=count_property_tests(crates_dir),
        unit_tests=unit_tests,
    )


def update_verification_metrics_overview(
    content: str,
    snapshot: VerificationMetricsSnapshot,
    today: str,
    logger: logging.Logger,
) -> str:
    """Update only the overview table in docs/VERIFICATION_METRICS.md."""
    row_specs = [
        (r"Proof Contracts", "Proof Contracts", snapshot.proof_contracts),
        (r"Verus Proofs(?: \(archived\))?", "Verus Proofs (archived)", snapshot.verus_proofs),
        (r"Property Tests", "Property Tests", snapshot.property_tests),
        (r"Unit Tests", "Unit Tests", snapshot.unit_tests),
    ]

    updated = content
    for label_pattern, label, count in row_specs:
        row_pattern = rf"\| {label_pattern} \| [^|]+ \| \d{{4}}-\d{{2}}-\d{{2}} \|"
        replacement = f"| {label} | {format_number(count)} | {today} |"
        updated, replacements = re.subn(row_pattern, replacement, updated, count=1)
        if replacements == 0:
            logger.warning("Verification metrics row not found: %s", label)
    return updated


def sync_verification_metrics_md(
    doc_path: Path,
    snapshot: VerificationMetricsSnapshot,
    today: str,
    dry_run: bool,
    logger: logging.Logger,
) -> bool:
    """Update docs/VERIFICATION_METRICS.md overview counts and dates."""
    if not doc_path.exists():
        return False

    with open(doc_path, encoding="utf-8") as f:
        content = f.read()

    original = content
    content = update_verification_metrics_overview(content, snapshot, today, logger)

    if content == original:
        logger.info("docs/VERIFICATION_METRICS.md is already up-to-date")
        return False

    if dry_run:
        logger.info("Would also update docs/VERIFICATION_METRICS.md:")
    else:
        with open(doc_path, "w", encoding="utf-8") as f:
            f.write(content)
        logger.info("Updated docs/VERIFICATION_METRICS.md:")

    logger.info("  Proof Contracts: %s", format_number(snapshot.proof_contracts))
    logger.info("  Verus Proofs (archived): %s", format_number(snapshot.verus_proofs))
    logger.info("  Property Tests: %s", format_number(snapshot.property_tests))
    logger.info("  Unit Tests: %s", format_number(snapshot.unit_tests))
    logger.info("  Date: %s", today)
    return True
