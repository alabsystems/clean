#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Fail closed when a tracked crate or target escapes the documented lint gate.

`Cargo.toml` narrows `default-members` to the publish smoke surface on purpose
(see the rationale at `Cargo.toml:33-37`), so the bare `cargo check --locked` /
`cargo clippy --locked --all-targets` inner loop compiles only a fraction of the
workspace. That is a deliberate speed trade, not a coverage claim — the coverage
claim belongs to the pre-push gate, which must select **every** member and
**every** target kind.

This script checks the two ways that guarantee silently rots. It does not wrap a
cargo command; it compares the live workspace shape against the gate text:

  1. Orphan crates — a git-tracked `crates/*/Cargo.toml` that is not a workspace
     member is compiled, linted, and tested by *no* command in this repo, not
     even `--workspace`. Known orphans live in `KNOWN_ORPHANS` below; that map
     is shrink-only (a stale entry fails too).
  2. Gate narrowing — the documented full gate must appear verbatim in the
     places that are supposed to run it (`CLAUDE.md`, `Justfile`,
     `scripts/local_gate.sh`), so dropping `--workspace` or `--all-targets` from
     any one of them breaks the gate instead of quietly shrinking it.

It also prints the live coverage delta (crates and targets selected by the fast
inner loop vs. the full gate) so the numbers quoted in CLAUDE.md can be
re-derived on demand rather than trusted.

Usage:  python3 scripts/check_lint_coverage.py [--quiet]
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOP_LEVEL_MANIFEST = re.compile(r"crates/[^/]+/Cargo\.toml")

# Tracked crates that are deliberately (or, historically, accidentally) outside
# `[workspace] members`. SHRINK-ONLY: a stale entry — one that has become a
# member, or whose manifest is gone — fails this check, so the list cannot
# outlive the deviation it records.
KNOWN_ORPHANS: dict[str, str] = {
    "crates/clean-mathverse-server": (
        "tracked but not a workspace member and not in Cargo.lock; no cargo "
        "command in this repo builds or lints it. Keep-or-kill decision is "
        "open — docs/AUDIT_2026-07_DISPOSITIONS.md rows 19, 31, 132."
    ),
}

# The pre-push gate. Every site listed below must contain this string verbatim.
FULL_GATE = "cargo clippy --locked --workspace --all-targets"
GATE_SITES = ("CLAUDE.md", "Justfile", "scripts/local_gate.sh")


class CoverageFailure(RuntimeError):
    """A tracked crate or a gate site no longer matches the documented gate."""


def cargo_metadata() -> dict:
    """Workspace shape from cargo itself (authoritative, ~0.04s, no build)."""
    proc = subprocess.run(
        ["cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise CoverageFailure(f"cargo metadata failed: {proc.stderr.strip()}")
    return json.loads(proc.stdout)


def tracked_crate_manifests() -> list[str]:
    """Top-level `crates/<name>/Cargo.toml` only.

    Nested manifests (e.g. `crates/clean-rust-sem/tests/source_macro_ingestion/`)
    are compile-env fixtures whose sources are `#[path]`-included into a real
    test target, so the full gate already lints them through their owning crate.
    """
    proc = subprocess.run(
        ["git", "ls-files", "--", "crates"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise CoverageFailure(f"git ls-files failed: {proc.stderr.strip()}")
    return sorted(
        line
        for line in proc.stdout.splitlines()
        if TOP_LEVEL_MANIFEST.fullmatch(line)
    )


def member_dirs(metadata: dict, key: str) -> set[str]:
    ids = set(metadata[key])
    dirs: set[str] = set()
    for package in metadata["packages"]:
        if package["id"] in ids:
            manifest = Path(package["manifest_path"]).resolve().parent
            dirs.add(manifest.relative_to(ROOT).as_posix())
    return dirs


def check_orphans(metadata: dict) -> list[str]:
    members = member_dirs(metadata, "workspace_members")
    failures: list[str] = []
    tracked = {Path(m).parent.as_posix() for m in tracked_crate_manifests()}

    for crate_dir in sorted(tracked - members):
        if crate_dir in KNOWN_ORPHANS:
            continue
        failures.append(
            f"{crate_dir} is git-tracked but is not a workspace member: no "
            f"cargo command in this repo compiles or lints it. Add it to "
            f"[workspace] members in Cargo.toml, or record it in KNOWN_ORPHANS "
            f"with the disposition that keeps it out."
        )

    for crate_dir, reason in sorted(KNOWN_ORPHANS.items()):
        if not (ROOT / crate_dir / "Cargo.toml").exists():
            failures.append(
                f"KNOWN_ORPHANS lists {crate_dir}, which no longer exists — "
                f"delete the entry (the list is shrink-only). Recorded reason: "
                f"{reason}"
            )
        elif crate_dir in members:
            failures.append(
                f"KNOWN_ORPHANS lists {crate_dir}, which is now a workspace "
                f"member — delete the entry (the list is shrink-only)."
            )
    return failures


def check_gate_sites() -> list[str]:
    failures: list[str] = []
    for site in GATE_SITES:
        path = ROOT / site
        if not path.exists():
            failures.append(f"gate site {site} is missing")
            continue
        if FULL_GATE not in path.read_text(encoding="utf-8"):
            failures.append(
                f"{site} no longer contains the full gate `{FULL_GATE}`. The "
                f"pre-push gate must select every workspace member and every "
                f"target kind; narrowing it re-opens the blind spot where "
                f"non-default members' test targets are never linted."
            )
    return failures


def coverage_summary(metadata: dict) -> str:
    """Live crate/target counts for both gates (build scripts excluded)."""
    members = set(metadata["workspace_members"])
    defaults = set(metadata["workspace_default_members"])
    fast_crates = fast_targets = full_crates = full_targets = 0
    for package in metadata["packages"]:
        if package["id"] not in members:
            continue
        targets = sum(
            1 for t in package["targets"] if t["kind"] != ["custom-build"]
        )
        full_crates += 1
        full_targets += targets
        if package["id"] in defaults:
            fast_crates += 1
            fast_targets += targets
    return (
        f"  fast inner loop (default-members, --all-targets): "
        f"{fast_crates}/{full_crates} crates, {fast_targets}/{full_targets} targets\n"
        f"  full gate (--workspace --all-targets):            "
        f"{full_crates}/{full_crates} crates, {full_targets}/{full_targets} targets"
    )


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv[1:]
    try:
        metadata = cargo_metadata()
        failures = check_orphans(metadata) + check_gate_sites()
    except CoverageFailure as exc:
        print(f"lint-coverage check FAILED: {exc}", file=sys.stderr)
        return 1

    if failures:
        print("lint-coverage check FAILED:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1

    if not quiet:
        print(coverage_summary(metadata))
        for crate_dir, reason in sorted(KNOWN_ORPHANS.items()):
            print(f"  known orphan (tracked, unbuilt): {crate_dir} — {reason}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
