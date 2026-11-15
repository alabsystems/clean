#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Derive the vendored Kernel Arena round table from the round's Zenodo files.

The arena battery (crates/clean-olean/tests/kernel_arena_battery.rs) reads two
vendored files under crates/clean-olean/tests/fixtures/kernel_arena/round-2026-09/:
the round's test archive, byte for byte, and `round-2026-09.table.json`, which
this script derives from the round's `results.json` (4.2 MB, mostly checker
stdout/stderr, not vendored). The table keeps, per archived test, what the
battery needs: the expected outcome, the timeout of the test's YAML at the
round's arena commit, the file's sha256, and the verdicts of the kernels
`lake check --paranoid` bundles at v4.35.0 (Lake/CLI/Check.lean `bundledKernels`:
leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron; the round ran the
official kernel as `official`, v4.34.0, and has no `leanchecker-paranoid` row).

Both inputs are untrusted downloads: each must match its pinned sha256 before
anything is read, the archive is read with `tarfile` without extracting, and
this script executes nothing from either. Run it with `python3 -I`.

    python3 -I scripts/kernel_arena_round.py \\
        --results <dir>/lean-arena-round-2026-09-results.json \\
        --archive crates/clean-olean/tests/fixtures/kernel_arena/round-2026-09/lean-arena-round-2026-09-tests.tar.gz \\
        --out crates/clean-olean/tests/fixtures/kernel_arena/round-2026-09/round-2026-09.table.json

Fetch the results with
`curl -o results.json https://zenodo.org/api/records/22944094/files/lean-arena-round-2026-09-results.json/content`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import tarfile
from pathlib import Path

ARCHIVE_SHA256 = "98a69742b538296c5f413d0527dfeef8c4d1815fe64b12c8623cd33de63bee0d"
RESULTS_SHA256 = "c48cab650e1bcfbb4231221d0b68820880a077ac67b37e435bf1a4aa9caff9f7"
ARCHIVE_FILES = 193
PARANOID = ("official", "lean4lean", "nanoda", "con-leche", "con-ron")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def consensus(verdicts: dict[str, dict]) -> str:
    """The common verdict of the paranoid kernels that judged the test."""
    judged = {v["status"] for v in verdicts.values() if v["status"] in ("accepted", "rejected")}
    if not judged:
        return "none"
    if len(judged) > 1:
        return "split"
    return "accept" if judged == {"accepted"} else "reject"


def derive(results_path: Path, archive_path: Path) -> dict:
    for path, pinned in ((results_path, RESULTS_SHA256), (archive_path, ARCHIVE_SHA256)):
        found = sha256(path)
        if found != pinned:
            raise SystemExit(f"{path}: sha256 {found}, pinned {pinned}; refusing to read it")
    results = json.loads(results_path.read_text(encoding="utf-8"))
    with tarfile.open(archive_path, "r:gz") as archive:
        members = [m for m in archive.getmembers() if m.isfile()]
        digests = {}
        for member in members:
            handle = archive.extractfile(member)
            if handle is None:
                raise SystemExit(f"{member.name}: unreadable archive member")
            digests[member.name] = hashlib.sha256(handle.read()).hexdigest()
    if len(members) != ARCHIVE_FILES:
        raise SystemExit(f"archive has {len(members)} files, pinned {ARCHIVE_FILES}")
    tests = {t["name"]: t for t in results["tests"]}
    by_test: dict[str, dict[str, dict]] = {}
    for row in results["results"]:
        if row["checker"] in PARANOID:
            by_test.setdefault(row["test"], {})[row["checker"]] = {
                "status": row["status"],
                "exit_code": row["exit_code"],
            }
    rows = []
    for path in sorted(digests):
        if not path.endswith(".ndjson"):
            raise SystemExit(f"{path}: not an .ndjson test")
        group, _, rest = path.partition("/")
        arena_name = rest[: -len(".ndjson")]
        test = tests.get(arena_name)
        if test is None:
            raise SystemExit(f"{path}: no test {arena_name!r} in results.json")
        expected = {"good": "accept", "bad": "reject"}.get(group)
        if expected != test["outcome"]:
            raise SystemExit(f"{path}: archive group {group!r}, results outcome {test['outcome']!r}")
        if test["sha256"] != digests[path]:
            raise SystemExit(f"{path}: sha256 differs from results.json")
        verdicts = {k: by_test.get(arena_name, {}).get(k, {"status": "missing", "exit_code": None})
                    for k in PARANOID}
        rows.append({
            "path": path,
            "arena_name": arena_name,
            "outcome": test["outcome"],
            "timeout_s": test.get("timeout"),
            "sha256": digests[path],
            "lean_version": test["lean_version"],
            "paranoid": verdicts,
            "consensus": consensus(verdicts),
        })
    meta = results["meta"]
    return {
        "schema": "clean.kernel-arena-round-table.v1",
        "round": meta["round"],
        "doi": meta["doi"],
        "arena_commit": meta["git_revision"],
        "archive": {"file": archive_path.name, "sha256": ARCHIVE_SHA256, "files": ARCHIVE_FILES},
        "results_json_sha256": RESULTS_SHA256,
        "license": "Apache-2.0 (The Lean Kernel Arena contributors, Zenodo record 22944094)",
        "paranoid_kernels": list(PARANOID),
        "consensus_rule": (
            "the common verdict of the paranoid kernels that accepted or rejected the test "
            "(a decline, error or timeout is no verdict); 'split' when they disagree, 'none' "
            "when none judged it"
        ),
        "tests": rows,
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    table = derive(args.results, args.archive)
    args.out.write_text(json.dumps(table, indent=1, sort_keys=False) + "\n", encoding="utf-8")
    counts = {}
    for row in table["tests"]:
        counts[(row["outcome"], row["consensus"])] = counts.get((row["outcome"], row["consensus"]), 0) + 1
    print(f"wrote {args.out}: {len(table['tests'])} tests; (outcome, consensus) counts {sorted(counts.items())}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
