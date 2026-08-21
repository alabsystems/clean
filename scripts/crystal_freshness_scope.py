#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Bind the crystal revalidation records to a clean-kernel SOURCE REV, and say
what HEAD's distance from it does and does not invalidate.

THE HOLE THIS FILLS (found 2026-08-19, at clean 891b7d153).

`scripts/crystal_fixture_freshness.py` compares a chain fixture to a LIVE
trustc dump.  It is the only thing that ever has.  But it needs the Trust
compiler, so it cannot run in the Rust suite, and its answer is therefore a
DATED RECORD -- `data/crystal_chain_revalidation_*.json` -- not a standing
claim.  Nothing bound those records to the clean-kernel source they were taken
from, so nothing could tell whether they still describe HEAD.

They did not.  Both committed records were measured with clean-kernel source
tree `214f8ffd0d` (clean revs f99b94e21 / f0846ade2).  At 891b7d153 the kernel
source tree is `a3ae6c21fc`: three files moved (+37 lines) in
`crates/clean-kernel/src/env/`, adding a field to `Environment`, three methods,
and a `Reducibility` match arm.  Every link-2a gate kept passing, because every
one of them reads a fixture.

WHAT THIS DECIDES, AND -- MORE IMPORTANTLY -- WHAT IT REFUSES TO DECIDE

Whether a chained BODY drifted is a question only trustc can answer.  This
script does not pretend otherwise.  What it can decide, with no compiler, is
the SCOPE the record's answer still covers:

  FRESH           the kernel source is byte-identical to the tree the record
                  was measured at.  The record's per-body answer covers HEAD.

  NUMBERING-SCOPE the kernel source moved, but NO chained body's own defining
                  source file moved.  Whole-crate `functy.N` / `enum.N` /
                  `struct.N` / `@func.N` indices have certainly renumbered --
                  adding one item to the crate does that with zero
                  instructions changed.  AMBER: printed, ledgered, and NOT a
                  failure.

  CONTENT-SCOPE   a chained body's own defining source file moved.  The body
                  the spec module transcribes may no longer be the body the
                  producer emits, and no fixture can tell you.  RED: re-derive
                  with `scripts/crystal_fixture_freshness.py` against a fresh
                  dump before trusting any link-2a verdict.

That split is the same one `crystal_fixture_freshness.py` makes between its
AMBER token classes and STRUCTURAL, lifted one level up -- from "which tokens
moved in the emitted text" to "which source could have moved them".  It is the
reason this gate is survivable: a gate that goes red every time an unrelated
crate item is added gets switched off inside a week, and then the CONTENT case
goes unnoticed with it.

It is NOT a claim that numbering-scope drift is harmless to the bodies.  It is
a claim that it is not evidence of body drift, and that the honest response is
a printed, ledgered revalidation DEBT rather than either a silent green or a
red nobody can act on.

WHAT CONTENT-SCOPE CAN MISS, STATED RATHER THAN LEFT TO BE DISCOVERED

A body's emitted instructions depend on its own MIR and on the LAYOUT of the
types it touches -- not only on the bytes of the file it is written in.  This
check pins the defining file and nothing else, so a layout change to a type
defined elsewhere, or an inlined callee moving, would read NUMBERING-SCOPE.

The gap is bounded here rather than open, and the bound is read from the record
rather than asserted: ten of the eleven chained bodies carry
`calls: {resolved: 0, extern_decls: 0, unresolved: 0}` -- nothing is inlined
into them because nothing is called -- and each one's own types (`CleanMode`,
`Level`, `FlatFlags`, `ExprPathStep`, `Expr`) are defined in the very file this
check pins.  The eleventh, `level_is_zero`, makes 6 calls, all into
`<LevelArc as Deref>::deref`, and `LevelArc` lives in the pinned
`src/level/mod.rs`.  The live census is printed with every AMBER verdict, so if
a chained body ever gains a call the approximation's weakening is visible
rather than assumed away.

It is still an approximation.  That is exactly why the non-chained case is
AMBER and not green: the only thing that settles it is a dump.

THE MAPPING IS SELF-CHECKING.  Each chained def_path is mapped to one source
file AND to a pattern that must occur in it.  A mapping that no longer resolves
is a hard failure, not a skip -- otherwise a file rename would silently empty
the content-scope check and leave a green that checks nothing.

Usage:

    scripts/crystal_freshness_scope.py                 # check HEAD's tree
    scripts/crystal_freshness_scope.py --strict        # AMBER fails too
    scripts/crystal_freshness_scope.py --emit          # (re)write the scope file
    scripts/crystal_freshness_scope.py --json OUT

Exit codes: 0 fresh or amber, 1 CONTENT-SCOPE drift (or amber under --strict),
2 the scope file or a mapping is unusable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
KERNEL = Path("crates/clean-kernel")
SCOPE_FILE = REPO / "data" / "crystal_freshness_scope.json"
FIXTURE_SCRIPT = "scripts/crystal_fixture_freshness.py"

# The record whose scope this file binds. Dated records are never rewritten;
# this is a separate, derivable statement ABOUT the newest one.
RECORD = "data/crystal_chain_revalidation_2026-08-19_28fb5dd812.json"

# chain stem -> (defining source file, a pattern that must occur in it).
#
# The pattern is what makes the mapping self-checking. `; #loc:` in the fixture
# carries only a whole-crate FILE INDEX, which is meaningless without the dump,
# so the mapping cannot be read off the artifact -- it is stated here and
# verified against the tree on every run.
BODY_SOURCES: dict[str, tuple[str, str]] = {
    "has_cubical_layer": ("src/mode.rs", "fn has_cubical_layer"),
    "from_source_system": ("src/mode.rs", "fn from_source_system"),
    "level_kind_ord": ("src/level/mod.rs", "fn kind_ord"),
    "level_is_zero": ("src/level/mod.rs", "fn is_zero"),
    "flat_flags_contains": ("src/flat/types.rs", "fn contains"),
    "bvar_in_range": ("src/expr/mod.rs", "fn bvar_in_range"),
    "is_valid_char": ("src/env/native_reducers_char.rs", "fn is_valid_char"),
    "expr_path_step_clone": ("src/tc/expr_location.rs", "ExprPathStep"),
    "float_div": ("src/env/native_reducers_float.rs", "fn reduce_float_div"),
    "get_char_val_trunc": (
        "src/env/native_reducers_beq_shortcircuit.rs",
        "fn get_char_val",
    ),
    "meta_tag_shl": ("src/tc/local_context.rs", "META_TAG"),
    "simp_priority_value": ("src/env/types.rs", "fn value"),
    # Chains 12-14, the 2026-08-20 float tranche: three closures inside
    # float_binary_op's callers, one source line each.
    "float_add": ("src/env/native_reducers_float.rs", "fn reduce_float_add"),
    "float_sub": ("src/env/native_reducers_float.rs", "fn reduce_float_sub"),
    "float_mul": ("src/env/native_reducers_float.rs", "fn reduce_float_mul"),
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def kernel_files(root: Path) -> list[Path]:
    """The kernel source set, walked from the FILESYSTEM.

    Filesystem rather than git on purpose: the verdict must be the same in a
    detached worktree, in a pinned suite-runner checkout and in a tree with
    uncommitted edits, and it must not need git history at all. An untracked
    `.rs` under `src/` is therefore included -- conservative in the fail-closed
    direction, since a file that is present but unreferenced can only make the
    digest move earlier, never later.
    """
    base = root / KERNEL
    out = sorted(p for p in (base / "src").rglob("*.rs") if p.is_file())
    manifest = base / "Cargo.toml"
    if manifest.is_file():
        out.append(manifest)
    return out


def kernel_digest(root: Path) -> tuple[str, dict[str, str]]:
    """(aggregate digest, per-file digest) over the kernel source set."""
    per: dict[str, str] = {}
    agg = hashlib.sha256()
    for path in kernel_files(root):
        rel = path.relative_to(root).as_posix()
        digest = sha256_bytes(path.read_bytes())
        per[rel] = digest
        agg.update(rel.encode("utf-8"))
        agg.update(b"\0")
        agg.update(digest.encode("ascii"))
        agg.update(b"\n")
    return agg.hexdigest(), per


def check_mapping(root: Path) -> list[str]:
    """Every mapped file exists and still contains its item. Fail closed."""
    problems: list[str] = []
    for stem, (rel, pattern) in sorted(BODY_SOURCES.items()):
        path = root / KERNEL / rel
        if not path.is_file():
            problems.append(f"{stem}: {KERNEL / rel} does not exist")
            continue
        if pattern not in path.read_text(encoding="utf-8", errors="replace"):
            problems.append(
                f"{stem}: {KERNEL / rel} no longer contains `{pattern}` — the mapping is "
                "stale, so the content-scope check would silently cover nothing"
            )
    return problems



def call_census(record_rel: str) -> tuple[int, list[str]]:
    """(bodies making no calls, names of those that do) from the record.

    The content-scope check pins a body's DEFINING file, which is exact only
    while nothing is inlined into that body. A zero-call body settles that
    directly, so the census is the honest measure of how much of the closure
    the pin actually covers -- and it is read live, so it cannot rot into a
    claim about a record that has moved on.
    """
    chains = json.loads((REPO / record_rel).read_text(encoding="utf-8"))["chains"]
    zero, called = 0, []
    for stem in sorted(BODY_SOURCES):
        row = chains.get(stem) or {}
        calls = (row.get("links_at_head") or {}).get("calls") or {}
        if calls.get("resolved") == 0:
            zero += 1
        else:
            called.append(stem)
    return zero, called


def tree_at(rev: str) -> Path:
    """Extract `crates/clean-kernel` at `rev` into a temp dir and return it."""
    out = Path(tempfile.mkdtemp(prefix="crystal-scope-")) / "t"
    out.mkdir()
    archive = subprocess.run(
        ["git", "-C", str(REPO), "archive", rev, str(KERNEL)],
        stdout=subprocess.PIPE,
        check=True,
    ).stdout
    subprocess.run(["tar", "-x", "-C", str(out)], input=archive, check=True)
    return out


def moved_kernel_files(rev: str) -> list[str] | None:
    """Best-effort listing of which kernel files moved since `rev`.

    Compared against the WORKING TREE rather than against HEAD, so it agrees
    with the digest walk above on a tree with uncommitted edits. Reported for
    the operator, never for the verdict: the verdict is decided by the digests
    in the scope file, which need no git at all. A tree without git history
    still gets a correct verdict and loses only this listing.
    """
    try:
        done = subprocess.run(
            ["git", "-C", str(REPO), "diff", "--name-only", rev, "--", str(KERNEL)],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return sorted(line for line in done.stdout.splitlines() if line.strip())


def emit(rev: str) -> int:
    root = tree_at(rev)
    try:
        problems = check_mapping(root)
        if problems:
            for p in problems:
                print("MAPPING UNUSABLE AT %s: %s" % (rev, p), file=sys.stderr)
            return 2
        agg, per = kernel_digest(root)
    finally:
        shutil.rmtree(root.parent, ignore_errors=True)
    doc = {
        "schema": "clean.crystal.freshness_scope/v1",
        "what_this_is": (
            "The clean-kernel SOURCE the newest crystal revalidation record was measured "
            "at. Whether a chained BODY drifted is a question only trustc can answer, and "
            "the record is its DATED answer; this pins the tree that answer covers, so a "
            "pre-push gate and a suite row can decide -- with no Trust compiler and no "
            "dump -- whether it still covers the tree in front of them. Derivable: "
            "`scripts/crystal_freshness_scope.py --emit`."
        ),
        "record": RECORD,
        "covered_clean_rev": rev,
        "clean_kernel_src_sha256": agg,
        "clean_kernel_src_file_count": len(per),
        "digest_definition": (
            "sha256 over, in sorted path order, `<repo-relative path>\\0<sha256 of file "
            "bytes>\\n` for every crates/clean-kernel/src/**/*.rs plus "
            "crates/clean-kernel/Cargo.toml, walked from the filesystem."
        ),
        "chained_body_sources": {
            stem: {
                "file": (KERNEL / rel).as_posix(),
                "sha256": per[(KERNEL / rel).as_posix()],
                "must_contain": pattern,
            }
            for stem, (rel, pattern) in sorted(BODY_SOURCES.items())
        },
        "how_to_re_derive": (
            "A CONTENT-SCOPE failure is not refreshed by re-emitting this file. Produce a "
            "fresh dump and run " + FIXTURE_SCRIPT + ", commit the new revalidation "
            "record, point `record` at it, then --emit."
        ),
    }
    SCOPE_FILE.write_text(json.dumps(doc, indent=1) + "\n", encoding="utf-8")
    print("wrote %s" % SCOPE_FILE)
    print("  covered_clean_rev        %s" % rev)
    print("  clean_kernel_src_sha256  %s" % agg)
    print("  files                    %d" % len(per))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--emit", action="store_true", help="(re)write the scope file")
    ap.add_argument(
        "--at",
        default=None,
        help="with --emit, the clean rev to pin (default: the record's clean_worktree_rev)",
    )
    ap.add_argument(
        "--strict", action="store_true", help="NUMBERING-SCOPE drift fails too"
    )
    ap.add_argument("--json", type=Path, default=None, help="write the verdict here")
    args = ap.parse_args()

    if args.emit:
        rev = args.at
        if rev is None:
            record = json.loads((REPO / RECORD).read_text(encoding="utf-8"))
            rev = record["provenance"]["clean_worktree_rev"]
        return emit(rev)

    if not SCOPE_FILE.is_file():
        print("SCOPE UNUSABLE: %s is missing." % SCOPE_FILE, file=sys.stderr)
        print("  Re-derive it: scripts/crystal_freshness_scope.py --emit", file=sys.stderr)
        return 2
    scope = json.loads(SCOPE_FILE.read_text(encoding="utf-8"))
    if not (REPO / scope["record"]).is_file():
        print(
            "SCOPE UNUSABLE: it names %s, which is not in the tree." % scope["record"],
            file=sys.stderr,
        )
        return 2

    problems = check_mapping(REPO)
    if problems:
        for p in problems:
            print("MAPPING UNUSABLE: %s" % p, file=sys.stderr)
        return 2

    agg, per = kernel_digest(REPO)
    moved_bodies: list[str] = []
    for stem, entry in sorted(scope["chained_body_sources"].items()):
        live = per.get(entry["file"])
        if live != entry["sha256"]:
            moved_bodies.append(
                "%s: %s moved (%s -> %s)"
                % (stem, entry["file"], entry["sha256"][:12], (live or "ABSENT")[:12])
            )

    verdict = (
        "CONTENT-SCOPE"
        if moved_bodies
        else ("FRESH" if agg == scope["clean_kernel_src_sha256"] else "NUMBERING-SCOPE")
    )

    print("== crystal revalidation scope ==")
    print("record                 %s" % scope["record"])
    print("covered_clean_rev      %s" % scope["covered_clean_rev"])
    print("covered kernel digest  %s" % scope["clean_kernel_src_sha256"][:24])
    print("live kernel digest     %s" % agg[:24])
    print("verdict                %s" % verdict)

    if args.json:
        args.json.write_text(
            json.dumps(
                {
                    "schema": "clean.crystal.freshness_scope_verdict/v1",
                    "verdict": verdict,
                    "record": scope["record"],
                    "covered_clean_rev": scope["covered_clean_rev"],
                    "covered_kernel_src_sha256": scope["clean_kernel_src_sha256"],
                    "live_kernel_src_sha256": agg,
                    "chained_body_sources_moved": moved_bodies,
                },
                indent=1,
            )
            + "\n",
            encoding="utf-8",
        )
        print("verdict written to %s" % args.json)

    if verdict == "CONTENT-SCOPE":
        print("\nRED — a chained body's own source moved:")
        for m in moved_bodies:
            print("  %s" % m)
        print(
            "\nThe body the spec module transcribes may no longer be the body the producer\n"
            "emits, and NO fixture in this tree can tell you: every link-2a gate reads the\n"
            "fixture. Re-DERIVE against a live dump (%s) and commit a\n"
            "new revalidation record. Do not re-emit the scope file to clear this." % FIXTURE_SCRIPT
        )
        return 1

    if verdict == "NUMBERING-SCOPE":
        print(
            "\nAMBER — the kernel source moved, but no chained body's own source did.\n"
            "  Whole-crate functy.N / enum.N / struct.N / @func.N indices have renumbered:\n"
            "  adding one crate item does that with zero instructions changed. That is NOT\n"
            "  evidence a body drifted, and it is NOT a claim that none did — only a fresh\n"
            "  dump can say. It is a revalidation DEBT, and it is printed rather than\n"
            "  smoothed."
        )
        zero, called = call_census(scope["record"])
        print(
            "  closure note: %d of %d chained bodies make ZERO calls in the record, so nothing\n"
            "  can be inlined into them and the pin on their defining file is exact. %s"
            % (
                zero,
                zero + len(called),
                (
                    "Covered only approximately: "
                    + ", ".join(called)
                    + " (calls, so an inlined callee could move instructions with the pinned "
                    "file unchanged)."
                    if called
                    else "No calling body is left, so the pin is exact throughout."
                ),
            )
        )
        listing = moved_kernel_files(scope["covered_clean_rev"])
        if listing is None:
            print("  (which files moved is unavailable here — no usable git history)")
        else:
            print("  kernel files moved since %s: %d" % (scope["covered_clean_rev"][:9], len(listing)))
            for rel in listing[:12]:
                print("    %s" % rel)
            if len(listing) > 12:
                print("    ... and %d more" % (len(listing) - 12))
        print("  Re-derive: %s <dump-dir>, then --emit." % FIXTURE_SCRIPT)
        if args.strict:
            print("\n--strict: a revalidation debt is a failure in this mode.")
            return 1
        return 0

    print("\nFRESH: the record's per-body answer covers this tree byte-for-byte.")
    return 0



if __name__ == "__main__":
    sys.exit(main())
