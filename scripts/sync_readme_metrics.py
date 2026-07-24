#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Sync repo metric docs from live analysis.

Updates README.md, docs/DESIGN.md, and docs/VERIFICATION_METRICS.md.
Prevents recurring staleness issues (#669, #823, #1017, #1118, #2438).
Fixed KeyError: 'loc' by deriving LOC/test data from the repo instead of
metrics/latest.json.

Usage:
    python3 scripts/sync_readme_metrics.py [--dry-run]
    python3 scripts/sync_readme_metrics.py --check
"""

from __future__ import annotations

import argparse
import logging
import re
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path

from sync_readme_metrics_verification import (
    VerificationMetricsSnapshot,
    count_property_tests as count_property_tests_impl,
    count_proof_contracts as count_proof_contracts_impl,
    count_verus_proofs as count_verus_proofs_impl,
    sync_verification_metrics_md as sync_verification_metrics_md_impl,
    update_verification_metrics_overview as update_verification_metrics_overview_impl,
)

log = logging.getLogger(__name__)

ROOT = Path(__file__).resolve().parents[1]
README = ROOT / "README.md"
DESIGN_MD = ROOT / "docs" / "DESIGN.md"
VERIFICATION_METRICS_MD = ROOT / "docs" / "VERIFICATION_METRICS.md"
CRATES_DIR = ROOT / "crates"
# Map README component names to crate directories
COMPONENT_CRATES: dict[str, str] = {
    "Kernel (type checker)": "clean-kernel",
    "Parser (Lean 4 syntax)": "clean-parser",
    "Elaborator": "clean-elab",
    "Compiler": "clean-compiler",
    "Automation (SMT/ATP)": "clean-auto",
    "Server (JSON-RPC)": "clean-server",
    "C Verification": "clean-c-sem",
    "Rust Semantics": "clean-rust-sem",
    "Self-Verification": "clean-verify",
    ".olean Import": "clean-olean",
}

# Crates in DESIGN.md crate table (preserves doc row order)
DESIGN_TABLE_CRATES: list[str] = [
    "clean-kernel",
    "clean-elab",
    "clean-auto",
    "clean-compiler",
    "clean-olean",
    "clean-parser",
    "clean-server",
    "clean-c-sem",
    "clean-rust-sem",
    "clean-tla",
    "clean-verify",
    "clean-runtime",
    "clean-lsp",
    "clean-macro",
    "clean-cli",
    "clean-lake",
    "clean-fold",
    "clean-sys",
]


@dataclass(frozen=True)
class RepoLayout:
    """Filesystem layout for doc-metrics sync."""

    root: Path
    readme: Path
    design_md: Path
    verification_metrics_md: Path
    crates_dir: Path


def build_layout(root: Path | None = None) -> RepoLayout:
    """Build a repo layout from an explicit root or the default module paths."""
    if root is None:
        return RepoLayout(
            root=ROOT,
            readme=README,
            design_md=DESIGN_MD,
            verification_metrics_md=VERIFICATION_METRICS_MD,
            crates_dir=CRATES_DIR,
        )
    resolved_root = Path(root).resolve()
    return RepoLayout(
        root=resolved_root,
        readme=resolved_root / "README.md",
        design_md=resolved_root / "docs" / "DESIGN.md",
        verification_metrics_md=resolved_root / "docs" / "VERIFICATION_METRICS.md",
        crates_dir=resolved_root / "crates",
    )


def _resolve_layout(layout: RepoLayout | None = None) -> RepoLayout:
    """Resolve the active repo layout, honoring patched module globals in tests."""
    return build_layout() if layout is None else layout

def count_total_loc(layout: RepoLayout | None = None) -> int:
    """Count total lines of Rust code across all crates."""
    active_layout = _resolve_layout(layout)
    total = 0
    for rs_file in active_layout.crates_dir.rglob("*.rs"):
        try:
            total += len(rs_file.read_text(encoding="utf-8").splitlines())
        except (OSError, UnicodeDecodeError):
            pass
    return total


def count_total_tests(layout: RepoLayout | None = None) -> int:
    """Count total #[test] annotations across all crates."""
    active_layout = _resolve_layout(layout)
    total = 0
    for rs_file in active_layout.crates_dir.rglob("*.rs"):
        try:
            total += rs_file.read_text(encoding="utf-8").count("#[test]")
        except (OSError, UnicodeDecodeError):
            pass
    return total


def count_proof_contracts(layout: RepoLayout | None = None) -> int:
    """Count REQUIRES/ENSURES contract lines under crate src trees."""
    active_layout = _resolve_layout(layout)
    return count_proof_contracts_impl(active_layout.crates_dir)


def count_verus_proofs(layout: RepoLayout | None = None) -> int:
    """Count archived Verus proof fn lines."""
    active_layout = _resolve_layout(layout)
    return count_verus_proofs_impl(active_layout.root)


def count_property_tests(layout: RepoLayout | None = None) -> int:
    """Count proptest! lines under crates/."""
    active_layout = _resolve_layout(layout)
    return count_property_tests_impl(active_layout.crates_dir)


def format_number(n: int) -> str:
    """Format number with commas: 457093 -> '457,093'."""
    return f"{n:,}"


def format_loc(loc: int) -> str:
    """Format LOC for README table, rounded to the nearest thousand."""
    if loc >= 1000:
        return f"{(loc + 500) // 1000}K"
    return str(loc)


def count_crate_loc(crate_name: str, layout: RepoLayout | None = None) -> int:
    """Count lines of Rust code in a crate directory."""
    active_layout = _resolve_layout(layout)
    crate_dir = active_layout.crates_dir / crate_name
    if not crate_dir.exists():
        return 0

    total = 0
    for f in crate_dir.rglob("*.rs"):
        try:
            total += len(f.read_text(encoding="utf-8").splitlines())
        except (OSError, UnicodeDecodeError):
            pass
    return total


def count_crate_tests(crate_name: str, layout: RepoLayout | None = None) -> int:
    """Count #[test] annotations in a crate directory."""
    active_layout = _resolve_layout(layout)
    crate_dir = active_layout.crates_dir / crate_name
    if not crate_dir.exists():
        return 0

    total = 0
    for f in crate_dir.rglob("*.rs"):
        try:
            total += f.read_text(encoding="utf-8").count("#[test]")
        except (OSError, UnicodeDecodeError):
            pass
    return total


def get_crate_metrics(layout: RepoLayout | None = None) -> dict[str, tuple[int, int]]:
    """Get LOC and test counts for all mapped components."""
    active_layout = _resolve_layout(layout)
    results = {}
    for component, crate in COMPONENT_CRATES.items():
        loc = count_crate_loc(crate, active_layout)
        tests = count_crate_tests(crate, active_layout)
        results[component] = (loc, tests)
    return results


def update_component_row(content: str, component: str, loc: int, tests: int) -> str:
    """Update a single row in the component table.

    Table format:
    | Component | Lines | Tests | Status |
    | Kernel (type checker) | 224K | 3,748 | V1 |
    """
    loc_str = format_loc(loc)

    # Escape special regex chars in component name
    escaped = re.escape(component)

    # Match: | Component | LOC | Tests | Status |
    # The LOC and Tests columns can have various formats (200K, 3,748, etc.)
    pattern = rf'(\| {escaped} \|) [^|]+ \| [^|]+ (\|[^|]+\|)'
    replacement = rf'\1 {loc_str} | {tests} \2'

    return re.sub(pattern, replacement, content)


def update_readme_date(content: str, today: str) -> str:
    """Update the snapshot date in the README footer."""
    # Match: updated 2026-02-08 or updated 2026-03-02
    return re.sub(
        r'updated \d{4}-\d{2}-\d{2}',
        f'updated {today}',
        content,
    )


def update_design_crate_row(content: str, crate_name: str, loc: int, tests: int) -> str:
    """Update a single crate row in the DESIGN.md crate table.

    Table format:
    | clean-kernel | 246K | 4,285 |
    """
    loc_str = format_loc(loc)
    escaped = re.escape(crate_name)
    pattern = rf'(\| {escaped} \|) [^|]+ \| [^|]+ \|'
    replacement = rf'\1 {loc_str} | {format_number(tests)} |'
    return re.sub(pattern, replacement, content)


def build_verification_metrics_snapshot(
    unit_tests: int,
    layout: RepoLayout | None = None,
) -> VerificationMetricsSnapshot:
    """Collect the counts published by docs/VERIFICATION_METRICS.md."""
    active_layout = _resolve_layout(layout)
    return VerificationMetricsSnapshot(
        proof_contracts=count_proof_contracts(active_layout),
        verus_proofs=count_verus_proofs(active_layout),
        property_tests=count_property_tests(active_layout),
        unit_tests=unit_tests,
    )


def update_verification_metrics_overview(
    content: str,
    snapshot: VerificationMetricsSnapshot,
    today: str,
) -> str:
    """Update only the overview table in docs/VERIFICATION_METRICS.md."""
    return update_verification_metrics_overview_impl(content, snapshot, today, log)


def sync_verification_metrics_md(
    snapshot: VerificationMetricsSnapshot,
    today: str,
    dry_run: bool,
    layout: RepoLayout | None = None,
) -> bool:
    """Update docs/VERIFICATION_METRICS.md overview counts and dates."""
    active_layout = _resolve_layout(layout)
    return sync_verification_metrics_md_impl(
        active_layout.verification_metrics_md,
        snapshot,
        today,
        dry_run,
        log,
    )


def sync_design_md(
    rust_loc: int,
    test_count: int,
    today: str,
    dry_run: bool,
    layout: RepoLayout | None = None,
) -> bool:
    """Update DESIGN.md total LOC, test count, and per-crate table.

    Returns True if changes were made, False if already up-to-date.
    """
    active_layout = _resolve_layout(layout)
    with open(active_layout.design_md, encoding="utf-8") as f:
        content = f.read()

    original = content
    crate_updates: list[str] = []

    # Update "Total Lines of Code" row
    content = re.sub(
        r'(\| Total Lines of Code \|) [^|]+ \|',
        rf'\1 ~{format_number(rust_loc // 1000 * 1000)} (Rust: {format_number(rust_loc)}) |',
        content,
    )

    # Update "Total Tests" row
    content = re.sub(
        r'(\| Total Tests \|) [^|]+ \|',
        rf'\1 {format_number(test_count)} passing |',
        content,
    )

    # Update "Last Updated" date
    content = re.sub(
        r'\*\*Last Updated\*\*: \d{4}-\d{2}-\d{2}',
        f'**Last Updated**: {today}',
        content,
    )

    # Update per-crate table rows
    for crate_name in DESIGN_TABLE_CRATES:
        loc = count_crate_loc(crate_name, active_layout)
        tests = count_crate_tests(crate_name, active_layout)
        new_content = update_design_crate_row(content, crate_name, loc, tests)
        if new_content != content:
            crate_updates.append(f"  {crate_name}: {format_loc(loc)} LOC, {format_number(tests)} tests")
        content = new_content

    if content == original:
        log.info("DESIGN.md is already up-to-date")
        return False

    if dry_run:
        log.info("Would also update docs/DESIGN.md:")
    else:
        with open(active_layout.design_md, "w", encoding="utf-8") as f:
            f.write(content)
        log.info("Updated docs/DESIGN.md:")

    if crate_updates:
        log.info("  Crate table updates:")
        for upd in crate_updates:
            log.info("    %s", upd)

    return True


def sync_all(dry_run: bool = False, layout: RepoLayout | None = None) -> bool:
    """Sync repo docs that publish live metrics. Returns True if any file changed."""
    active_layout = _resolve_layout(layout)
    log.info("Computing metrics from crate directories...")
    rust_loc = count_total_loc(active_layout)
    test_count = count_total_tests(active_layout)
    today = date.today().isoformat()
    verification_snapshot = build_verification_metrics_snapshot(test_count, active_layout)

    readme_changed = _sync_readme_content(
        rust_loc,
        test_count,
        today,
        dry_run,
        active_layout,
    )
    design_changed = False
    if active_layout.design_md.exists():
        design_changed = sync_design_md(
            rust_loc,
            test_count,
            today,
            dry_run,
            active_layout,
        )
    verification_metrics_changed = sync_verification_metrics_md(
        verification_snapshot,
        today,
        dry_run,
        active_layout,
    )

    return readme_changed or design_changed or verification_metrics_changed


def _sync_readme_content(
    rust_loc: int,
    test_count: int,
    today: str,
    dry_run: bool,
    layout: RepoLayout | None = None,
) -> bool:
    """Internal: update README.md content. Returns True if changed."""
    active_layout = _resolve_layout(layout)
    with open(active_layout.readme, encoding="utf-8") as f:
        content = f.read()

    original = content
    component_updates: list[str] = []

    # Pattern 1: "X lines of Rust. Y tests."
    loc_test_pattern = r'\*\*[\d,]+ lines of Rust\. [\d,]+ tests\.'
    loc_test_replacement = f'**{format_number(rust_loc)} lines of Rust. {format_number(test_count)} tests.'
    if not re.search(loc_test_pattern, content):
        log.warning("LOC/test pattern not found in README.md")
    content = re.sub(loc_test_pattern, loc_test_replacement, content)

    # Pattern 2: Update snapshot date in footer
    content = update_readme_date(content, today)

    # Pattern 3: Update per-component LOC and test counts in the table
    crate_metrics = get_crate_metrics(active_layout)
    for component, (loc, tests) in crate_metrics.items():
        new_content = update_component_row(content, component, loc, tests)
        if new_content != content:
            component_updates.append(f"  {component}: {format_loc(loc)} LOC, {tests} tests")
        content = new_content

    if content == original:
        log.info("README.md is already up-to-date")
        return False

    if dry_run:
        log.info("Would update README.md:")
    else:
        with open(active_layout.readme, "w", encoding="utf-8") as f:
            f.write(content)
        log.info("Updated README.md:")

    log.info("  Rust LOC: %s", format_number(rust_loc))
    log.info("  Tests: %s", format_number(test_count))
    log.info("  Date: %s", today)
    if component_updates:
        log.info("  Component updates:")
        for upd in component_updates:
            log.info("    %s", upd)

    return True


def sync_readme(dry_run: bool = False, layout: RepoLayout | None = None) -> bool:
    """Update README.md with current metrics (backward-compatible entry point).

    Returns True if changes were made, False if already up-to-date.
    """
    return sync_all(dry_run=dry_run, layout=layout)


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    parser = argparse.ArgumentParser(
        description="Sync repo doc metrics from live repo analysis"
    )
    parser.add_argument(
        "--root",
        type=Path,
        help="Operate on an alternate repo root instead of this script's parent repo",
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be changed without modifying files",
    )
    group.add_argument(
        "--check",
        action="store_true",
        help="Exit 1 if docs are stale, 0 if synchronized (never writes files)",
    )
    args = parser.parse_args()
    layout = build_layout(args.root)

    if args.check:
        changed = sync_all(dry_run=True, layout=layout)
        if changed:
            log.info("STALE: docs would be updated by sync")
            return 1
        log.info("CLEAN: docs are synchronized")
        return 0

    sync_all(dry_run=args.dry_run, layout=layout)
    return 0


if __name__ == "__main__":
    sys.exit(main())
