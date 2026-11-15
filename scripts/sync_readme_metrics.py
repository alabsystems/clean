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


# ── WHOSE BYTES ARE COUNTED ──────────────────────────────────────────────────
#
# The INDEX's, not the working tree's, whenever this is a git checkout.
#
# This artifact is a PUBLISHED number about the repository, and until 2026-09-14
# it counted whatever happened to be on disk. That made it a function of every
# lane's scratch state: in a tree with 61 worktrees and concurrent writers, any
# uncommitted `.rs` edit moved the total, so a freshness gate over it would have
# gone red for a reason the pusher did not cause and could not fix without
# committing -- the exact shape scripts/githooks/gate-legs.txt exists to keep out
# of the hook. Measured that day: a two-line plant left in
# crates/kernel/src/env/snapshot.rs by a racing self-test flipped the leg red.
#
# Counting the index fixes both halves at once. Unstaged work is invisible, so
# there is no false red; and the workflow that keeps the page true is the one
# every other derived artifact here already uses -- stage your change,
# regenerate, stage the page, commit -- so the number lands in the same commit
# as the code it describes rather than one push behind it.
#
# A source snapshot (`git archive`, no `.git`) has no index and its filesystem
# IS the tracked set, so it reads from disk. That path is unchanged.
_INDEX_CACHE: dict[Path, dict[Path, str]] = {}


def _index_sources(layout: RepoLayout, files: list[Path]) -> dict[Path, str]:
    """path -> the file's content AS STAGED, for a git checkout."""
    cached = _INDEX_CACHE.get(layout.root)
    if cached is not None:
        return cached
    listing = subprocess.run(
        ["git", "-C", str(layout.root), "ls-files", "-s", "-z", "--", "crates"],
        check=True, capture_output=True,
    ).stdout.decode("utf-8").split("\0")
    sha_of: dict[Path, str] = {}
    for entry in listing:
        if not entry:
            continue
        meta, _, rel = entry.partition("\t")
        parts = meta.split()
        if len(parts) < 3 or not rel.endswith(".rs"):
            continue
        sha_of[layout.root / rel] = parts[1]
    wanted = [(path, sha_of[path]) for path in files if path in sha_of]
    out: dict[Path, str] = {}
    if wanted:
        batch = subprocess.run(
            ["git", "-C", str(layout.root), "cat-file", "--batch"],
            input="\n".join(sha for _, sha in wanted).encode() + b"\n",
            check=True, capture_output=True,
        ).stdout
        pos = 0
        for path, _sha in wanted:
            nl = batch.index(b"\n", pos)
            size = int(batch[pos:nl].split()[2])
            body = batch[nl + 1: nl + 1 + size]
            out[path] = body.decode("utf-8", errors="replace")
            pos = nl + 1 + size + 1
    _INDEX_CACHE[layout.root] = out
    return out


def read_source(path: Path, sources: dict[Path, str] | None = None) -> str:
    """Read one inventory source file -- from the index when one was captured."""
    if sources is not None and path in sources:
        return sources[path]
    return path.read_text(encoding="utf-8")


def count_loc(files: list[Path], sources: dict[Path, str] | None = None) -> int:
    """Count physical Rust source lines."""
    return sum(len(read_source(path, sources).splitlines()) for path in files)


def count_test_attributes(files: list[Path], sources: dict[Path, str] | None = None) -> int:
    """Count line-leading ``#[test]`` attributes without claiming execution."""
    return sum(len(TEST_ATTRIBUTE.findall(read_source(path, sources))) for path in files)


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
    sources = _index_sources(layout, all_files) if (layout.root / ".git").exists() else None
    total_loc = count_loc(all_files, sources)
    total_tests = count_test_attributes(all_files, sources)

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
        crate_loc = count_loc(files, sources)
        crate_tests = count_test_attributes(files, sources)
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


def self_test() -> int:
    """Two-way arms for WHOSE BYTES ARE COUNTED, on a synthetic git repo.

    The property that matters is a pair, and only the pair is worth anything:
    an UNSTAGED edit must NOT move the number (or this cannot sit in the hook
    without red-lighting every lane mid-edit), and the SAME edit STAGED MUST
    move it (or the check is inert and the published number is decorative).
    """
    import shutil
    import tempfile

    failures: list[str] = []

    def arm(name: str, ok: bool, detail: str = "") -> None:
        print(f"  self-test ARM {'ok' if ok else 'FAILED'}: {name}"
              + (f" -> {detail}" if detail else ""))
        if not ok:
            failures.append(name)

    tmp = Path(tempfile.mkdtemp(prefix="source_inventory_selftest_"))
    try:
        crate = INVENTORY_TABLE_CRATES[0]
        src = tmp / "crates" / crate / "src"
        src.mkdir(parents=True)
        (src / "lib.rs").write_text("pub fn a() {}\n#[test]\nfn t() {}\n", encoding="utf-8")
        (tmp / "docs").mkdir()
        rows = "\n".join(f"| {c} | 0 | 0 |" for c in INVENTORY_TABLE_CRATES)
        (tmp / "docs" / "SOURCE_INVENTORY.md").write_text(
            "| Measure | Static source count |\n|---|---:|\n"
            "| Total Lines of Code | 0 Rust lines |\n"
            "| Total Tests | 0 source `#[test]` attributes (not execution evidence) |\n\n"
            "| Crate | Rust LOC | Source `#[test]` attributes |\n|---|---:|---:|\n"
            + rows + "\n",
            encoding="utf-8")
        for c in INVENTORY_TABLE_CRATES[1:]:
            d = tmp / "crates" / c / "src"
            d.mkdir(parents=True)
            (d / "lib.rs").write_text("pub fn b() {}\n", encoding="utf-8")

        def git(*a):
            return subprocess.run(["git", "-C", str(tmp), "-c", "user.name=selftest",
                                   "-c", "user.email=selftest@example.invalid", *a],
                                  capture_output=True, check=False)
        git("init", "-q")
        git("add", "-A")
        git("commit", "-q", "-m", "base")

        layout = build_layout(tmp)
        _INDEX_CACHE.clear()
        sync_all(dry_run=False, layout=layout)
        git("add", "-A")
        git("commit", "-q", "-m", "inventory")

        _INDEX_CACHE.clear()
        arm("a freshly minted inventory is not stale",
            sync_all(dry_run=True, layout=layout) is False)

        (src / "lib.rs").write_text(
            "pub fn a() {}\n#[test]\nfn t() {}\n// one\n// two\n// three\n",
            encoding="utf-8")
        _INDEX_CACHE.clear()
        arm("an UNSTAGED Rust edit does not move the published number",
            sync_all(dry_run=True, layout=layout) is False,
            "three lines added on disk, nothing staged")

        git("add", "crates")
        _INDEX_CACHE.clear()
        arm("the SAME edit, STAGED, does move it",
            sync_all(dry_run=True, layout=layout) is True,
            "the number lands in the commit that changes the code")

        _INDEX_CACHE.clear()
        sync_all(dry_run=False, layout=layout)
        _INDEX_CACHE.clear()
        arm("re-minting against the staged tree clears it",
            sync_all(dry_run=True, layout=layout) is False)

        blob = git("show", f":crates/{crate}/src/lib.rs").stdout.decode()
        _INDEX_CACHE.clear()
        files = tracked_rust_files(layout)
        sources = _index_sources(layout, files)
        # layout.root is RESOLVED (build_layout resolves it) and tmp may be a
        # symlinked /var/folders path on macOS -- key off the layout, not tmp.
        target = layout.root / "crates" / crate / "src" / "lib.rs"
        arm("the bytes counted ARE the index blob, verbatim",
            sources.get(target) == blob,
            f"{len(blob)} bytes")
    finally:
        _INDEX_CACHE.clear()
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        print(f"self-test: {len(failures)} arm(s) FAILED: {', '.join(failures)}")
        return 1
    print("self-test: all arms green")
    return 0


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
    group.add_argument(
        "--self-test",
        action="store_true",
        help="two-way arms on a synthetic git repo: an unstaged edit must not "
             "move the number, the same edit staged must",
    )
    args = parser.parse_args()

    if args.self_test:
        return self_test()

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
