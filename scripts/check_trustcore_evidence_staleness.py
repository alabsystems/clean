#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Trust-core evidence staleness tripwire (loud version of the silent treadmill).

The three trust-core launch-evidence artifacts pin the gate logic that minted
them: all three pin the sha256 of crates/clean-cli/src/cmd_replacement.rs, and
kernel-soundness + deny-sorry additionally pin a module-tree digest of every
non-test `.rs` file under crates/clean-cli/src/cmd_replacement/ (computed by
`sha256_repo_module_tree`, crates/clean-cli/src/cmd_replacement/artifact_io.rs).
Any edit under cmd_replacement/ therefore SILENTLY stales the artifacts: the
in-binary validators reject them at read time, but nothing at push time says
so. This tripwire recomputes the identical digests and fails the local gate
loudly whenever a checked-in artifact pins a different digest than the working
tree hashes to right now.

Byte-identity of the replication was proven against a Rust-minted pin: at the
evidence-mint commit 93670bb91 this implementation reproduces the recorded
module-tree digest 1959edbf... exactly. If `sha256_repo_module_tree` ever
changes its hashing (file set, ordering, or delimiting), this script must be
updated in the same commit — divergence fails LOUD (a spurious `stale`), never
silently `fresh`, because `fresh` requires the pinned digest to equal the
digest computed here.

Prints exactly one machine-readable verdict line on exit:

    TRUSTCORE_STALENESS=fresh|stale|skipped:<reason>

`skipped:<reason>` is reserved for implementations that need an external
binary; this pure-stdlib replication never skips — a missing or unreadable
artifact or source tree is `stale` (fail-closed).

Wired into scripts/local_gate.sh. Pure-stdlib; no cargo build required.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Mirrors cmd_replacement/consts.rs (TRUST_CORE_RUST_SOURCE_PATH,
# TRUST_CORE_RUST_MODULE_DIR, TRUST_CORE_RUST_MODULE_TREE_KEY).
MODULE_FILE = "crates/clean-cli/src/cmd_replacement.rs"
MODULE_DIR = "crates/clean-cli/src/cmd_replacement"
MODULE_TREE_KEY = "crates/clean-cli/src/cmd_replacement/**/*.rs"

# artifact path -> whether its in-binary validator REQUIRES the module-tree pin.
# kernel-soundness + deny-sorry do (launch_validation.rs calls
# validate_trust_core_module_tree_sha); axiom-audit currently pins only the
# `cmd_replacement.rs` file sha (gate_checks.rs, exactly 2 source entries) —
# if it ever gains the module-tree key, the comparison below picks it up.
ARTIFACTS: dict[str, bool] = {
    "reports/kernel-soundness-launch-evidence.json": True,
    "reports/deny-sorry-launch-evidence.json": True,
    "reports/axiom-audit-launch-evidence.json": False,
}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_tree_digest(root: Path) -> str:
    """Byte-identical replication of `sha256_repo_module_tree` (artifact_io.rs).

    Rust: walk `root` (no symlink following), keep regular files whose
    `Path::extension()` is exactly `rs`, take the `/`-separated path relative
    to `root`, drop anything under `tests/`, sort by relative path (byte
    order), then sha256 over `rel-bytes 0x00 u64-LE-content-length content`
    per file.
    """
    entries: list[tuple[bytes, bytes]] = []
    for path in root.rglob("*"):
        if path.is_symlink() or not path.is_file():
            continue
        # Path::extension() == Some("rs"): last-dot split, non-empty stem
        # (".rs" has NO extension in Rust and is excluded).
        stem, dot, ext = path.name.rpartition(".")
        if dot != "." or stem == "" or ext != "rs":
            continue
        rel = path.relative_to(root).as_posix()
        if rel.startswith("tests/"):
            continue
        data = path.read_bytes()
        entries.append((rel.encode("utf-8"), data))
    entries.sort(key=lambda entry: entry[0])
    hasher = hashlib.sha256()
    for rel_bytes, data in entries:
        # Length-delimit so no rename/content shuffle can collide.
        hasher.update(rel_bytes)
        hasher.update(b"\x00")
        hasher.update(len(data).to_bytes(8, "little"))
        hasher.update(data)
    return hasher.hexdigest()


def check_artifact(
    rel_path: str,
    tree_pin_required: bool,
    current_file_sha: str,
    current_tree_digest: str,
) -> list[str]:
    """Return the list of staleness findings for one evidence artifact."""
    path = REPO_ROOT / rel_path
    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return [f"{rel_path}: unreadable ({exc})"]
    source_sha256 = artifact.get("source_sha256")
    if not isinstance(source_sha256, dict):
        return [f"{rel_path}: missing source_sha256 map"]

    findings: list[str] = []
    pinned_file_sha = source_sha256.get(MODULE_FILE)
    if pinned_file_sha is None:
        findings.append(f"{rel_path}: source_sha256 is missing {MODULE_FILE}")
    elif pinned_file_sha != current_file_sha:
        findings.append(
            f"{rel_path}: pins {MODULE_FILE} {pinned_file_sha} "
            f"but the working tree hashes to {current_file_sha}"
        )

    pinned_tree = source_sha256.get(MODULE_TREE_KEY)
    if pinned_tree is None:
        if tree_pin_required:
            findings.append(
                f"{rel_path}: source_sha256 is missing the module-tree pin "
                f"{MODULE_TREE_KEY} (predates the pin; the in-binary "
                f"validator rejects it)"
            )
    elif pinned_tree != current_tree_digest:
        findings.append(
            f"{rel_path}: pins module-tree digest {pinned_tree} "
            f"but the working tree hashes to {current_tree_digest}"
        )
    return findings


def main() -> int:
    module_file = REPO_ROOT / MODULE_FILE
    module_dir = REPO_ROOT / MODULE_DIR
    try:
        current_file_sha = sha256_file(module_file)
        if not module_dir.is_dir():
            raise OSError(f"{module_dir} is not a directory")
        current_tree_digest = module_tree_digest(module_dir)
    except OSError as exc:
        print(f"FAIL: cannot hash the trust-core gate sources: {exc}")
        print("TRUSTCORE_STALENESS=stale")
        return 1

    findings: list[str] = []
    for rel_path, tree_pin_required in ARTIFACTS.items():
        findings.extend(
            check_artifact(
                rel_path, tree_pin_required, current_file_sha, current_tree_digest
            )
        )

    print(f"  current {MODULE_FILE} sha256: {current_file_sha}")
    print(f"  current module-tree digest ({MODULE_TREE_KEY}): {current_tree_digest}")
    if findings:
        for finding in findings:
            print(f"  STALE: {finding}")
        print(
            "  A cmd_replacement/ gate-logic edit outdated the checked-in "
            "trust-core evidence. Regenerate with a HEAD-built clean binary —\n"
            "    clean replacement trust-core-evidence --kernel-soundness\n"
            "    clean replacement trust-core-evidence --deny-sorry\n"
            "    clean replacement axiom-audit --verify data/axiom_audit.json "
            "--evidence reports/axiom-audit-launch-evidence.json --json\n"
            "  — and commit the refreshed artifacts in the SAME change as the "
            "gate edit."
        )
        print("TRUSTCORE_STALENESS=stale")
        return 1
    print("TRUSTCORE_STALENESS=fresh")
    return 0


if __name__ == "__main__":
    sys.exit(main())
