#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Synchronize the dedicated static Rust source inventory.

``docs/SOURCE_INVENTORY.md`` is a source-shape diagnostic, not verification
evidence. Its test number counts line-leading ``#[test]`` attributes; this
script never builds or executes tests.

Usage:
    python3 scripts/sync_readme_metrics.py [--dry-run]
    python3 scripts/sync_readme_metrics.py --check
"""

from __future__ import annotations

import argparse
import logging
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

log = logging.getLogger(__name__)

ROOT = Path(__file__).resolve().parents[1]

# Selected-crate table order. The total inventory still covers every Rust file
# under crates/.
INVENTORY_TABLE_CRATES: tuple[str, ...] = (
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
)

TEST_ATTRIBUTE = re.compile(r"(?m)^\s*#\[test\]\s*$")


@dataclass(frozen=True)
class RepoLayout:
    """Filesystem layout for source-inventory synchronization."""

    root: Path
    source_inventory_md: Path
    crates_dir: Path


def build_layout(root: Path | None = None) -> RepoLayout:
    """Build a repo layout from an explicit root or this checkout."""
    resolved_root = ROOT if root is None else Path(root).resolve()
    return RepoLayout(
        root=resolved_root,
        source_inventory_md=resolved_root / "docs" / "SOURCE_INVENTORY.md",
        crates_dir=resolved_root / "crates",
    )


def tracked_rust_files(layout: RepoLayout) -> list[Path]:
    """Return the deterministic Rust inventory under ``crates/``.

    A checkout uses Git as the tracked-file authority. A source snapshot such
    as the one produced by ``git archive`` has no ``.git`` metadata, so its
    filesystem contents are already the complete tracked-file set and are
    walked directly. This keeps the post-commit archive gate executable without
    weakening normal-checkout handling of untracked files.
    """
    if (layout.root / ".git").exists():
        result = subprocess.run(
            ["git", "-C", str(layout.root), "ls-files", "-z", "--", "crates"],
            check=True,
            capture_output=True,
        )
        paths = result.stdout.decode("utf-8").split("\0")
        return sorted(
            layout.root / path for path in paths if path and path.endswith(".rs")
        )

    if not layout.crates_dir.is_dir():
        raise FileNotFoundError(
            f"source snapshot has no crates directory: {layout.crates_dir}"
        )
    return sorted(layout.crates_dir.rglob("*.rs"))


def read_source(path: Path) -> str:
    """Read one inventory source file."""
    return path.read_text(encoding="utf-8")


def count_loc(files: list[Path]) -> int:
    """Count physical Rust source lines."""
    return sum(len(read_source(path).splitlines()) for path in files)


def count_test_attributes(files: list[Path]) -> int:
    """Count line-leading ``#[test]`` attributes without claiming execution."""
    return sum(len(TEST_ATTRIBUTE.findall(read_source(path))) for path in files)


def format_number(value: int) -> str:
    """Format an integer with thousands separators."""
    return f"{value:,}"


def replace_exactly_once(
    content: str, pattern: str, replacement: str, label: str
) -> str:
    """Replace one required inventory marker and reject missing/duplicate rows."""
    updated, count = re.subn(pattern, replacement, content)
    if count != 1:
        raise ValueError(
            "docs/SOURCE_INVENTORY.md must contain exactly one "
            f"{label}; found {count}"
        )
    return updated


def render_inventory(content: str, layout: RepoLayout) -> str:
    """Render live totals into an existing, structurally validated template."""
    all_files = tracked_rust_files(layout)
    total_loc = count_loc(all_files)
    total_tests = count_test_attributes(all_files)

    content = replace_exactly_once(
        content,
        r"(\| Total Lines of Code \|) [^|]+ \|",
        rf"\1 {format_number(total_loc)} Rust lines |",
        "total-lines row",
    )
    content = replace_exactly_once(
        content,
        r"(\| Total Tests \|) [^|]+ \|",
        rf"\1 {format_number(total_tests)} source `#[test]` attributes "
        r"(not execution evidence) |",
        "total-tests row",
    )

    for crate_name in INVENTORY_TABLE_CRATES:
        crate_root = layout.crates_dir / crate_name
        files = [path for path in all_files if path.is_relative_to(crate_root)]
        crate_loc = count_loc(files)
        crate_tests = count_test_attributes(files)
        escaped = re.escape(crate_name)
        content = replace_exactly_once(
            content,
            rf"(\| {escaped} \|) [^|]+ \| [^|]+ \|",
            rf"\1 {format_number(crate_loc)} | {format_number(crate_tests)} |",
            f"{crate_name!r} crate row",
        )
    return content


def sync_all(*, dry_run: bool, layout: RepoLayout) -> bool:
    """Synchronize the inventory; return whether it differs from disk."""
    if not layout.source_inventory_md.is_file():
        raise ValueError(f"missing inventory owner: {layout.source_inventory_md}")
    original = layout.source_inventory_md.read_text(encoding="utf-8")
    rendered = render_inventory(original, layout)
    if rendered == original:
        log.info("SOURCE_INVENTORY.md is already up-to-date")
        return False
    if dry_run:
        log.info("Would update docs/SOURCE_INVENTORY.md")
    else:
        layout.source_inventory_md.write_text(rendered, encoding="utf-8")
        log.info("Updated docs/SOURCE_INVENTORY.md")
    return True


def main() -> int:
    """CLI entry point."""
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    parser = argparse.ArgumentParser(
        description="Sync the static Rust source inventory from the live checkout"
    )
    parser.add_argument(
        "--root",
        type=Path,
        help="operate on an alternate repository root",
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--dry-run",
        action="store_true",
        help="show whether the inventory would change without writing",
    )
    group.add_argument(
        "--check",
        action="store_true",
        help="exit 1 if the inventory is stale or malformed",
    )
    args = parser.parse_args()

    try:
        changed = sync_all(
            dry_run=args.dry_run or args.check,
            layout=build_layout(args.root),
        )
    except (OSError, UnicodeError, ValueError, subprocess.SubprocessError) as error:
        log.error("source inventory check failed: %s", error)
        return 1

    if args.check and changed:
        log.error("STALE: docs/SOURCE_INVENTORY.md would be updated")
        return 1
    if args.check:
        log.info("CLEAN: source inventory is synchronized")
    return 0


if __name__ == "__main__":
    sys.exit(main())
