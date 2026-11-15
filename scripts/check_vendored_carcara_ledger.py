#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Hold third-party/carcara/UPSTREAM.json to the files it describes.

The vendored Carcara is Clean's Alethe checker, so a defect in it is a defect
in Clean's trust root (third-party/carcara/DOWNSTREAM.md). Its ledger,
UPSTREAM.json, gives one row per file:

* ``files[]`` -- an upstream file: ``bytes``/``sha256`` are the UPSTREAM file at
  the pinned revision and are never rewritten; a file changed here also
  carries ``local``, the digest of the file as committed. A row without
  ``local`` must be byte-identical to upstream.
* ``local_files[]`` -- a Clean-authored file, with its digest.

DOWNSTREAM.md and UPSTREAM.json themselves are the only tracked files under
third-party/carcara/ with no row.

Until 2026-09-30 nothing recomputed any of it: ``git grep UPSTREAM.json`` found
only prose. A vendored edit could land with a stale digest, or with no row at
all, and the import would stop being checkable against upstream without anyone
being told. This script is the check.

WHOSE BYTES ARE CHECKED: the INDEX's, whenever this is a git checkout (the same
rule as scripts/sync_readme_metrics.py, for the same reason: an unstaged edit
in a shared tree must not red-light another lane's push, and the same edit
staged must be held to the ledger, so the digest lands in the commit that
changes the file). A source snapshot with no ``.git`` reads from disk.

Usage:
    python3 scripts/check_vendored_carcara_ledger.py [--check]
    python3 scripts/check_vendored_carcara_ledger.py --write
    python3 scripts/check_vendored_carcara_ledger.py --self-test

``--write`` refreshes the ``local`` digest of every EXISTING row from the
staged bytes (and drops ``local`` from a ``files[]`` row whose bytes are
upstream's again). It never adds a row: a file with no row is a decision --
upstream file or Clean's own -- that a person makes in UPSTREAM.json.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VENDORED = "third-party/carcara"
LEDGER = f"{VENDORED}/UPSTREAM.json"
UNLISTED = {f"{VENDORED}/DOWNSTREAM.md", LEDGER}


def _git(root: Path, *args: str, stdin: bytes | None = None) -> bytes:
    return subprocess.run(
        ["git", "-C", str(root), *args],
        input=stdin, check=True, capture_output=True,
    ).stdout


def tracked_contents(root: Path) -> dict[str, bytes]:
    """Repo-relative path -> content of every tracked file under VENDORED.

    From the index in a git checkout; from disk in a snapshot without one.
    """
    if not (root / ".git").exists():
        base = root / VENDORED
        return {
            str(p.relative_to(root)): p.read_bytes()
            for p in sorted(base.rglob("*")) if p.is_file()
        }
    listing = _git(root, "ls-files", "-s", "-z", "--", VENDORED).decode("utf-8")
    entries = []
    for entry in listing.split("\0"):
        if not entry:
            continue
        meta, _, rel = entry.partition("\t")
        entries.append((rel, meta.split()[1]))
    if not entries:
        return {}
    batch = _git(root, "cat-file", "--batch",
                 stdin="\n".join(sha for _, sha in entries).encode() + b"\n")
    out: dict[str, bytes] = {}
    pos = 0
    for rel, _sha in entries:
        nl = batch.index(b"\n", pos)
        size = int(batch[pos:nl].split()[2])
        out[rel] = batch[nl + 1: nl + 1 + size]
        pos = nl + 1 + size + 1
    return out


def digest(content: bytes) -> dict[str, object]:
    return {"bytes": len(content), "sha256": hashlib.sha256(content).hexdigest()}


def check(root: Path) -> list[str]:
    """Every way the ledger and the tracked files disagree, one line each."""
    contents = tracked_contents(root)
    ledger_bytes = contents.get(LEDGER)
    if ledger_bytes is None:
        return [f"{LEDGER} is not tracked"]
    ledger = json.loads(ledger_bytes)
    problems: list[str] = []
    seen: set[str] = set()

    def row_path(row: dict) -> str:
        path = f"{VENDORED}/{row['path']}"
        if path in seen:
            problems.append(f"{row['path']}: listed twice")
        seen.add(path)
        return path

    for row in ledger["files"]:
        path = row_path(row)
        upstream = {"bytes": row["bytes"], "sha256": row["sha256"]}
        local = row.get("local")
        if local is not None and local == upstream:
            problems.append(f"{row['path']}: `local` equals the upstream digest; "
                            "an unmodified file carries no `local`")
        content = contents.get(path)
        if content is None:
            problems.append(f"{row['path']}: has a row but is not tracked")
            continue
        want = local if local is not None else upstream
        got = digest(content)
        if got != want:
            which = "local" if local is not None else "upstream (no `local`)"
            problems.append(
                f"{row['path']}: is {got['bytes']} bytes, sha256 {got['sha256']}; "
                f"the {which} row says {want['bytes']} bytes, sha256 {want['sha256']}")
    for row in ledger["local_files"]:
        path = row_path(row)
        content = contents.get(path)
        if content is None:
            problems.append(f"{row['path']}: has a local_files row but is not tracked")
            continue
        want = {"bytes": row["bytes"], "sha256": row["sha256"]}
        got = digest(content)
        if got != want:
            problems.append(
                f"{row['path']}: is {got['bytes']} bytes, sha256 {got['sha256']}; "
                f"its local_files row says {want['bytes']} bytes, sha256 {want['sha256']}")
    for path in sorted(set(contents) - seen - UNLISTED):
        problems.append(f"{path[len(VENDORED) + 1:]}: is tracked but has no row "
                        "(an upstream file goes in files[], a Clean-authored one in local_files[])")
    return problems


def write(root: Path) -> bool:
    """Refresh the digests of existing rows from the staged bytes. True if changed."""
    contents = tracked_contents(root)
    path = root / LEDGER
    before = path.read_bytes()
    ledger = json.loads(before)
    for row in ledger["files"]:
        content = contents.get(f"{VENDORED}/{row['path']}")
        if content is None:
            continue
        got = digest(content)
        if got == {"bytes": row["bytes"], "sha256": row["sha256"]}:
            row.pop("local", None)
        else:
            row["local"] = got
    for row in ledger["local_files"]:
        content = contents.get(f"{VENDORED}/{row['path']}")
        if content is not None:
            row.update(digest(content))
    after = (json.dumps(ledger, indent=2) + "\n").encode()
    if after != before:
        path.write_bytes(after)
        return True
    return False


def self_test() -> int:
    """Arms on a synthetic git repo; each must turn the check red for its reason."""
    import shutil
    import tempfile

    failures: list[str] = []

    def arm(name: str, ok: bool, detail: str = "") -> None:
        print(f"  self-test ARM {'ok' if ok else 'FAILED'}: {name}"
              + (f" -> {detail}" if detail else ""))
        if not ok:
            failures.append(name)

    tmp = Path(tempfile.mkdtemp(prefix="carcara_ledger_selftest_")).resolve()
    try:
        def git(*a: str) -> None:
            subprocess.run(["git", "-C", str(tmp), "-c", "user.name=selftest",
                            "-c", "user.email=selftest@example.invalid", *a],
                           capture_output=True, check=True)

        base = tmp / VENDORED
        (base / "src").mkdir(parents=True)
        upstream = b"fn upstream() {}\n"
        modified_upstream = b"fn changed() {}\n"
        (base / "src" / "kept.rs").write_bytes(upstream)
        (base / "src" / "changed.rs").write_bytes(b"fn changed() { /* Modified in Clean */ }\n")
        (base / "own.rs").write_bytes(b"fn clean() {}\n")
        (base / "DOWNSTREAM.md").write_bytes(b"notes\n")
        ledger = {
            "files": [
                {"path": "src/changed.rs", **digest(modified_upstream)},
                {"path": "src/kept.rs", **digest(upstream)},
            ],
            "local_files": [{"path": "own.rs", "bytes": 0, "sha256": "0" * 64}],
        }
        (tmp / LEDGER).write_text(json.dumps(ledger, indent=2) + "\n", encoding="utf-8")
        git("init", "-q")
        git("add", "-A")
        git("commit", "-q", "-m", "base")

        problems = check(tmp)
        arm("stale digests are found before --write",
            len(problems) == 2 and all("row says" in p for p in problems), "; ".join(problems))
        arm("--write refreshes them", write(tmp) is True)
        git("add", "-A")
        arm("a refreshed ledger is clean", check(tmp) == [], "; ".join(check(tmp)))
        refreshed = json.loads((tmp / LEDGER).read_text(encoding="utf-8"))
        arm("--write keeps the upstream digest and records `local` beside it",
            refreshed["files"][0]["sha256"] == digest(modified_upstream)["sha256"]
            and refreshed["files"][0]["local"] == digest(
                (base / "src" / "changed.rs").read_bytes())
            and "local" not in refreshed["files"][1])
        arm("--write on a clean ledger changes nothing", write(tmp) is False)

        (base / "src" / "kept.rs").write_bytes(upstream.replace(b"{}", b"{ }"))
        arm("an UNSTAGED one-byte edit does not move the verdict", check(tmp) == [])
        git("add", "-A")
        problems = check(tmp)
        arm("the SAME edit, STAGED, is refused against the upstream digest",
            len(problems) == 1 and problems[0].startswith("src/kept.rs: ")
            and "upstream (no `local`)" in problems[0], "; ".join(problems))
        (base / "src" / "kept.rs").write_bytes(upstream)
        git("add", "-A")

        (base / "own.rs").write_bytes(b"fn clean() { }\n")
        git("add", "-A")
        problems = check(tmp)
        arm("an edit to a Clean-authored file is refused against its row",
            len(problems) == 1 and "local_files row says" in problems[0], "; ".join(problems))
        write(tmp)
        git("add", "-A")

        (base / "src" / "new.rs").write_bytes(b"fn new() {}\n")
        git("add", "-A")
        problems = check(tmp)
        arm("a tracked file with no row is refused",
            len(problems) == 1 and problems[0].startswith("src/new.rs: is tracked but has no row"),
            "; ".join(problems))
        arm("--write never adds a row", write(tmp) is False and check(tmp) == problems)
        git("rm", "-q", "-f", f"{VENDORED}/src/new.rs")

        git("rm", "-q", "--cached", f"{VENDORED}/src/kept.rs")
        problems = check(tmp)
        arm("a row for a file that is not tracked is refused",
            len(problems) == 1 and "has a row but is not tracked" in problems[0],
            "; ".join(problems))
        git("add", "-A")

        doubled = json.loads((tmp / LEDGER).read_text(encoding="utf-8"))
        doubled["files"].append(dict(doubled["files"][1]))
        (tmp / LEDGER).write_text(json.dumps(doubled, indent=2) + "\n", encoding="utf-8")
        git("add", "-A")
        problems = check(tmp)
        arm("a path listed twice is refused",
            any("listed twice" in p for p in problems), "; ".join(problems))

        doubled["files"].pop()
        doubled["files"][1]["local"] = {k: doubled["files"][1][k] for k in ("bytes", "sha256")}
        (tmp / LEDGER).write_text(json.dumps(doubled, indent=2) + "\n", encoding="utf-8")
        git("add", "-A")
        problems = check(tmp)
        arm("a `local` that equals upstream is refused",
            len(problems) == 1 and "`local` equals the upstream digest" in problems[0],
            "; ".join(problems))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        print(f"self-test: {len(failures)} arm(s) FAILED: {', '.join(failures)}")
        return 1
    print("self-test: all arms green")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", type=Path, default=ROOT,
                        help="operate on an alternate repository root")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true",
                       help="exit 1 when the ledger and the staged files disagree (default)")
    group.add_argument("--write", action="store_true",
                       help="refresh the digests of existing rows from the staged files")
    group.add_argument("--self-test", action="store_true",
                       help="arms on a synthetic git repo")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    root = args.root.resolve()
    if args.write:
        changed = write(root)
        print(f"{LEDGER}: {'refreshed' if changed else 'already current'}")
    problems = check(root)
    for problem in problems:
        print(f"LEDGER: {problem}")
    if problems:
        print(f"STALE: {LEDGER} disagrees with {len(problems)} tracked file(s) "
              f"(refresh digests with --write, after staging; add a row by hand)")
        return 1
    print(f"CLEAN: {LEDGER} matches every tracked file under {VENDORED}/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
