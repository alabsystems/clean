#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Every committed chain fixture, and every committed reader-A provenance file, still equals the digest its run recorded.

THE HOLE THIS FILLS, stated as it was found (2026-08-27, lane REV).

`crystal_fixture_freshness.py` closed the gap between the fixtures and a
LIVE trustc dump, and its module doc says exactly why that mattered: *"The gate
reads the FIXTURE. It has never read a dump."*  One level DOWN there was a
second copy of the same gap, and nothing had looked at it.

`crystal_fixture_rebaseline.py` writes, for every fixture it mints, the
sha256 and byte length of the text it wrote --- `new_sha256` / `new_bytes` in
`data/crystal_fixture_rebaseline_<...>.json`.  Measured 2026-08-27: those fields
are read by the minter itself and **by nothing else in either tree**.  No gate,
no suite row, no script.

So the arrangement was: twenty-one `*.trust-ir.txt` files pin the emitted IR that
every link-2a lane compares its spec module against; a committed record states
what those files contained when a real compiler produced them; and the two were
never compared.  Editing a fixture leaves every link-2a gate green, because every
link-2a gate reads the fixture --- the record sitting beside it in `data/`, which
would have said no, is not consulted by anything.

This script is that comparison.  Unlike `crystal_fixture_freshness.py` it needs
no compiler and no dump, so unlike that script it can be, and is, a GATE LEG that
runs on every invocation of `scripts/local_gate.sh`.

WHAT IT DECIDES, AND WHAT IT DOES NOT

It decides ONE question: are the committed fixtures byte-identical to what the
newest rebaseline recorded writing?  Three ways to fail, all RED:

  * a fixture's bytes differ from its recorded `new_sha256` / `new_bytes`;
  * a committed `*.trust-ir.txt` has no row in the record (arrived uncompared);
  * a recorded fixture is not committed (vanished).

It does NOT decide whether the fixtures still match what the compiler emits
TODAY.  Nothing here can: that needs a dump, it is
`crystal_fixture_freshness.py`, and it remains a manual duty with a
producer requirement.  A green here means "nobody has edited a fixture since the
last real measurement", never "the chains are revalidated".  Those are different
sentences and this file will not let them be confused.

The record is not named here.  It is read out of `CURRENT_REBASELINE` in
`crates/clean-verify/tests/crystal_a1_lineage/freshness.rs`, which is the same
const the Rust suite decides against, so this gate and that suite cannot come to
disagree about which record is current --- and a rename fails loudly instead of
silently checking a stale file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NoReturn

REPO = Path(__file__).resolve().parent.parent
FRESHNESS_RS = REPO / "crates/clean-verify/tests/crystal_a1_lineage/freshness.rs"
FIXTURE_DIR = REPO / "crates/clean-verify/tests/fixtures"
SUFFIX = ".trust-ir.txt"


def fail(message: str) -> NoReturn:
    raise SystemExit(f"CRYSTAL FIXTURE PINS: {message}")


def current_rebaseline(freshness_rs: Path) -> str:
    """Read the record path out of the suite's own const, never a second copy."""
    try:
        text = freshness_rs.read_text(encoding="utf-8")
    except OSError as exc:
        fail(f"cannot read {freshness_rs}: {exc}")
    match = re.search(
        r'const\s+CURRENT_REBASELINE\s*:\s*&str\s*=\s*"([^"]+)"\s*;', text, re.S
    )
    if not match:
        fail(
            f"{freshness_rs.relative_to(REPO) if freshness_rs.is_relative_to(REPO) else freshness_rs}"
            " no longer declares `const CURRENT_REBASELINE: &str = \"...\";` -- this gate"
            " reads that const so it cannot drift from the suite; re-point it, do not"
            " hard-code a record here"
        )
    return match.group(1)


def check(root: Path | None = None) -> list[str]:
    """Return one message per disagreement; empty means the pins hold."""
    base = root or REPO
    freshness_rs = base / "crates/clean-verify/tests/crystal_a1_lineage/freshness.rs"
    fixtures = base / "crates/clean-verify/tests/fixtures"
    rel = current_rebaseline(freshness_rs)
    record_path = base / rel
    if not record_path.is_file():
        fail(f"{rel} is named by CURRENT_REBASELINE but is not a file")
    try:
        record = json.loads(record_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"{rel} is unreadable or not JSON: {exc}")
    recorded = record.get("fixtures")
    if not isinstance(recorded, dict) or not recorded:
        fail(f"{rel} carries no `fixtures` object -- nothing to check against")

    problems: list[str] = []
    committed = {p.name[: -len(SUFFIX)] for p in fixtures.glob(f"*{SUFFIX}")}

    for stem in sorted(set(recorded) - committed):
        problems.append(
            f"{stem}{SUFFIX} is recorded by {rel} but is NOT committed -- a pinned "
            f"emitted body vanished from the tree"
        )
    for stem in sorted(committed - set(recorded)):
        problems.append(
            f"{stem}{SUFFIX} is committed but has no row in {rel} -- a fixture "
            f"arrived without ever being compared to a live dump"
        )
    for stem in sorted(set(recorded) & committed):
        entry = recorded[stem]
        expected = entry.get("new_sha256")
        expected_bytes = entry.get("new_bytes")
        if not isinstance(expected, str):
            problems.append(f"{rel} row {stem} carries no `new_sha256`")
            continue
        raw = (fixtures / f"{stem}{SUFFIX}").read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        if actual != expected:
            problems.append(
                f"{stem}{SUFFIX} DRIFTED from its pin: {actual[:16]} != recorded "
                f"{expected[:16]} ({len(raw)} bytes vs recorded {expected_bytes}). "
                f"The spec modules are compared against this text, so a theorem now "
                f"describes a body no measurement ever saw. Re-derive with a dump "
                f"(crystal_fixture_freshness.py), never by editing the pin"
            )
        elif isinstance(expected_bytes, int) and len(raw) != expected_bytes:
            problems.append(
                f"{stem}{SUFFIX} matches `new_sha256` but is {len(raw)} bytes where "
                f"{rel} records {expected_bytes} -- the record is internally inconsistent"
            )
    return problems


# ── reader A's provenance, pinned to the run that wrote it ──────────────────
#
# The same question one directory over: every committed
# `generated/*.prov.json` is the output of ONE run of the crystal-A2 projector
# over dumps that are not on this machine, so it cannot be regenerated here --
# and until verifier r7 (2026-09-24) nothing noticed when one was edited by
# hand (54861cbce rewrote a refusal literal in ir_lzd.core.prov.json to match
# the projector it had just fixed; no run produced those bytes). Each file is
# pinned in PROJECTOR_RECORD to the bytes its run wrote; a change is a real run
# (re-pin the row with that run's commit) or a hand edit, RED until the row
# says which.
#
# `committed_at` IS CHECKED AGAINST GIT, not read as a label (verifier r8,
# 2026-09-25). Until then only its TYPE was checked, so a hand edit re-pinned
# by sha256 and byte count alone -- `committed_at` left at the old run's
# commit, or set to `not-a-commit` -- printed OK, and the self-test pinned a
# commit id that exists nowhere. Now the row's commit must be (1) a commit
# reachable from HEAD, (2) one whose tree holds EXACTLY the pinned bytes at
# that path, and (3) the commit those bytes ARRIVED in: none of its parents
# holds them there. So `git show <committed_at> -- <path>` is always the diff
# that wrote the pinned bytes, which is the change a reviewer must be able to
# read as a projector run. What this cannot decide: whether that commit WAS a
# run -- a hand edit committed on its own is also a commit where its bytes
# arrived. Only the dumps can say, and they are not on this machine.
PROJECTOR_RECORD = "data/projector_output_record.json"
GENERATED = "crates/clean-verify/src/spec/core_spec/generated"
PROV_SUFFIX = ".prov.json"


def check_projector_outputs(root: Path | None = None) -> list[str]:
    """One message per committed provenance file that is not its run's bytes."""
    base = root or REPO
    try:
        record = json.loads((base / PROJECTOR_RECORD).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"{PROJECTOR_RECORD} is unreadable or not JSON: {exc}"]
    rows = record.get("files")
    if not isinstance(rows, dict) or not rows:
        return [f"{PROJECTOR_RECORD} carries no `files` object -- nothing to check against"]
    committed = {
        f"{GENERATED}/{p.name}" for p in (base / GENERATED).glob(f"*{PROV_SUFFIX}")
    }
    problems = [
        f"{rel} is committed but has no row in {PROJECTOR_RECORD} -- reader A's "
        f"provenance arrived without the run that wrote it being recorded"
        for rel in sorted(committed - set(rows))
    ] + [
        f"{rel} is recorded by {PROJECTOR_RECORD} but is NOT committed"
        for rel in sorted(set(rows) - committed)
    ]
    for rel in sorted(committed & set(rows)):
        row = rows[rel]
        if not isinstance(row.get("committed_at"), str) or not isinstance(
            row.get("inputs_on_this_machine"), bool
        ):
            problems.append(
                f"{PROJECTOR_RECORD} row {rel} must say which commit holds the run's bytes "
                f"(`committed_at`) and whether its dumps are on this machine "
                f"(`inputs_on_this_machine`)"
            )
            continue
        raw = (base / rel).read_bytes()
        if hashlib.sha256(raw).hexdigest() != row.get("sha256") or len(raw) != row.get("bytes"):
            problems.append(
                f"{rel} is not the bytes the projector run recorded at "
                f"{row.get('committed_at')} ({hashlib.sha256(raw).hexdigest()[:16]} != "
                f"{str(row.get('sha256'))[:16]}). Projector output is regenerated by a real "
                f"run over the dumps it names, never edited; after a run, re-pin this row "
                f"with the run's commit"
            )
            continue
        why = arrival_problem(base, row["committed_at"], rel, row["sha256"])
        if why:
            problems.append(
                f"{PROJECTOR_RECORD} row {rel} names commit {row['committed_at']!r} as the "
                f"run that wrote its bytes, and {why}. The row must name the commit, "
                f"reachable from HEAD, in which exactly the pinned bytes arrived at {rel}"
            )
    return problems


# git's repository-location variables, scrubbed from every git call here. A
# pre-push hook run from a LINKED worktree inherits an absolute GIT_DIR, and
# with GIT_DIR set `git -C <dir>` answers from THAT repository: the real
# check would read the wrong history, and the self-test's `git init` / `commit`
# in its temporary tree would write into the pushing repository (the hazard
# scripts/check_doc_claims.py records as GIT_LOCATION_VARS, measured
# 2026-09-15).
GIT_LOCATION_VARS = (
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_COMMON_DIR",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_NAMESPACE",
    "GIT_CEILING_DIRECTORIES",
)


def _git(base: Path, *args: str) -> subprocess.CompletedProcess:
    env = {k: v for k, v in os.environ.items() if k not in GIT_LOCATION_VARS}
    return subprocess.run(
        ["git", "-C", str(base), *args], capture_output=True, check=False, env=env
    )


def _blob_sha256(base: Path, rev: str, rel: str) -> str | None:
    """sha256 of `rel` in `rev`'s tree, or None when `rev` has no such path."""
    shown = _git(base, "cat-file", "blob", f"{rev}:{rel}")
    return hashlib.sha256(shown.stdout).hexdigest() if shown.returncode == 0 else None


def arrival_problem(base: Path, at: str, rel: str, sha256: str) -> str | None:
    """Why commit `at` is not where `sha256`'s bytes arrived at `rel`, or None."""
    if not re.fullmatch(r"[0-9a-f]{7,40}", at):
        return "that is not a commit id (7-40 lowercase hex digits)"
    resolved = _git(base, "rev-parse", "--verify", "--quiet", f"{at}^{{commit}}")
    if resolved.returncode != 0:
        return "this repository has no such commit"
    commit = resolved.stdout.decode().strip()
    if _git(base, "merge-base", "--is-ancestor", commit, "HEAD").returncode != 0:
        return "that commit is not reachable from HEAD"
    held = _blob_sha256(base, commit, rel)
    if held != sha256:
        return (
            "that commit's tree has no such path"
            if held is None
            else f"that commit's tree holds other bytes there ({held[:16]} != {sha256[:16]})"
        )
    parents = _git(base, "rev-list", "--parents", "-n", "1", commit).stdout.decode().split()[1:]
    carried = [p[:11] for p in parents if _blob_sha256(base, p, rel) == sha256]
    if carried:
        return (
            f"the bytes did not arrive there: its parent {carried[0]} already holds them "
            f"(`git log --format=%h -- {rel}` lists the commits that changed the file)"
        )
    return None


def selftest() -> None:
    """Arms on a synthetic tree: prove it can say no before it says yes."""
    good = "rustcc fn @lvl.is_zero() -> bool {\n  ret [bool true]\n}\n"
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        rs = base / "crates/clean-verify/tests/crystal_a1_lineage"
        fx = base / "crates/clean-verify/tests/fixtures"
        rs.mkdir(parents=True)
        fx.mkdir(parents=True)
        (base / "data").mkdir()
        rec = base / "data/rb.json"

        def write_all(body: str, extra: dict | None = None) -> None:
            (fx / f"a{SUFFIX}").write_text(body)
            fixtures = {
                "a": {
                    "new_sha256": hashlib.sha256(good.encode()).hexdigest(),
                    "new_bytes": len(good.encode()),
                }
            }
            fixtures.update(extra or {})
            rec.write_text(json.dumps({"fixtures": fixtures}))

        (rs / "freshness.rs").write_text(
            'pub(crate) const CURRENT_REBASELINE: &str =\n    "data/rb.json";\n'
        )

        arms: list[tuple[str, bool]] = []
        write_all(good)
        arms.append(("pins hold", not check(base)))
        write_all(good.replace("true", "false"))  # one token: STRUCTURAL drift
        arms.append(("edited fixture", bool(check(base))))
        write_all(good, {"b": {"new_sha256": "0" * 64, "new_bytes": 1}})
        arms.append(("recorded but absent", bool(check(base))))
        write_all(good)
        (fx / f"c{SUFFIX}").write_text(good)
        arms.append(("committed but unrecorded", bool(check(base))))

        # The provenance arms run in a REAL repository: `committed_at` is
        # checked against git, so a fake commit id cannot stand in for one
        # (until verifier r8 this self-test pinned "0123456789a", which exists
        # nowhere, and passed). HOME and the config are the fixture's, so the
        # box's git configuration cannot shape the history.
        gen = base / GENERATED
        gen.mkdir(parents=True)
        rel = f"{GENERATED}/ir_x{PROV_SUFFIX}"
        env = {k: v for k, v in os.environ.items() if k not in GIT_LOCATION_VARS}
        env.update({
            "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
            "GIT_COMMITTER_EMAIL": "t@t", "GIT_CONFIG_NOSYSTEM": "1", "HOME": str(base),
        })

        def commit(message: str) -> str:
            for argv in (["add", "-A"], ["commit", "-q", "--allow-empty", "-m", message]):
                subprocess.run(["git", "-C", str(base), *argv], env=env, check=True)
            return subprocess.run(
                ["git", "-C", str(base), "rev-parse", "--short=11", "HEAD"], env=env,
                check=True, capture_output=True, text=True,
            ).stdout.strip()

        subprocess.run(["git", "-C", str(base), "init", "-q", "-b", "main"], env=env, check=True)
        commit("before the run")
        prov = b'{\n "reader": "A"\n}\n'
        edited = prov.replace(b"A", b"a")
        (gen / f"ir_x{PROV_SUFFIX}").write_bytes(prov)
        run = commit("the run")
        later = commit("a later commit that carries the run's bytes")

        def pin(body: bytes = prov, at: str = run) -> None:
            (base / PROJECTOR_RECORD).write_text(json.dumps({"files": {rel: {
                "sha256": hashlib.sha256(body).hexdigest(),
                "bytes": len(body),
                "committed_at": at,
                "inputs_on_this_machine": False,
            }}}))

        pin()
        arms.append(("provenance pins hold", not check_projector_outputs(base)))
        pin(at="0123456789a")
        arms.append(("provenance row names a commit this repo lacks",
                     bool(check_projector_outputs(base))))
        pin(at="not-a-commit")
        arms.append(("provenance row names no commit at all", bool(check_projector_outputs(base))))
        pin(at=later)
        arms.append(("provenance row names a commit that carries the bytes but did not write "
                     "them", bool(check_projector_outputs(base))))
        pin()
        (gen / f"ir_x{PROV_SUFFIX}").write_bytes(edited)
        arms.append(("provenance edited by hand", bool(check_projector_outputs(base))))
        pin(body=edited)
        arms.append(("provenance edited by hand, the row re-pinned by digest with its commit "
                     "unchanged (verifier r8 S1)", bool(check_projector_outputs(base))))
        subprocess.run(["git", "-C", str(base), "switch", "-q", "-c", "side"], env=env, check=True)
        side = commit("the hand edit, on a branch HEAD does not reach")
        subprocess.run(["git", "-C", str(base), "switch", "-q", "main"], env=env, check=True)
        (gen / f"ir_x{PROV_SUFFIX}").write_bytes(edited)
        pin(body=edited, at=side)
        arms.append(("provenance row names a commit HEAD does not reach",
                     bool(check_projector_outputs(base))))
        (gen / f"ir_x{PROV_SUFFIX}").write_bytes(prov)
        pin()
        (gen / f"ir_y{PROV_SUFFIX}").write_bytes(prov)
        arms.append(("provenance committed but unrecorded", bool(check_projector_outputs(base))))

        bad = [name for name, ok in arms if not ok]
        if bad:
            fail(f"SELFTEST FAILED -- these arms did not behave: {bad}")
        print(f"crystal fixture pins selftest: {len(arms)}/{len(arms)} arms behave")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--selftest", action="store_true", help="run the mutation arms only")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    if args.selftest:
        selftest()
        return 0

    selftest()
    problems = check() + check_projector_outputs()
    rel = current_rebaseline(FRESHNESS_RS)
    if problems:
        print(
            f"CRYSTAL FIXTURE PINS: {len(problems)} disagreement(s) with {rel} or "
            f"{PROJECTOR_RECORD}",
            file=sys.stderr,
        )
        for message in problems:
            print(f"  - {message}", file=sys.stderr)
        return 1
    count = len(json.loads((REPO / rel).read_text())["fixtures"])
    if not args.quiet:
        print(
            f"OK: crystal fixture pins — {count} committed fixture(s) byte-identical to "
            f"{rel}; set matches exactly. (This is NOT a live-dump revalidation: see "
            f"crystal_fixture_freshness.py.)"
        )
        print(
            f"OK: projector provenance — every {GENERATED}/*{PROV_SUFFIX} is the bytes "
            f"its run recorded in {PROJECTOR_RECORD}."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
