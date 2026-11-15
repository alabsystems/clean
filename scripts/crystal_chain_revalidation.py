#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint an append-only Crystal chain record from a live Trust dump.

`crystal_fixture_freshness.py` is the authority for comparing committed
fixtures with a live dump.  Its JSON is intentionally close to that comparison,
whereas the committed `clean.crystal.chain_revalidation/v3` record also binds
the compiler, source tree, whole-crate invariants, and every executable link.
The first v3 record was assembled by hand and later grew out of sync with the
set of chained bodies.  This script makes that conversion reproducible and
fails closed before it writes anything.

Usage:

    scripts/crystal_fixture_freshness.py DUMP --json RAW
    scripts/crystal_chain_revalidation.py DUMP --freshness-report RAW \
      --trustc SEALED/bin/trustc --driver SEALED/lib/librustc_driver-....dylib \
      --supersedes data/crystal_chain_revalidation_<previous>.json \
      --out data/crystal_chain_revalidation_YYYY-MM-DD_<clean>.json

The output is opened with exclusive creation.  Revalidation records describe
one measured build and are append-only; this tool never overwrites one.

AT-HEAD MODE (2026-09-20, `--at-head --control-record REC`).  The strict v3
record above exists only AFTER a fixture rebaseline: every row must be
IDENTICAL, the rebaseline record must cover the very rev and dump being minted,
and the trustc/driver bytes must be the rebaseline's own.  That is the right
bar for a record that says "the fixtures ARE this dump".  It is the wrong bar
for the other question the freshness comparator answers -- "do the fixtures cut
at rev X still describe the bodies the producer emits at HEAD?" -- because a
NUMBERING-ONLY answer (whole-crate indices renumbered, zero instructions moved)
is exactly the survivable verdict every link-2a gate accepts, and it is the
verdict that clears `crystal_freshness_scope.py`'s CONTENT-SCOPE red, whose own
docstring names "a fresh dump and a NEW record" as the remedy.  Until today no
record kind could carry that answer: the strict minter refused it and the scope
file could not advance, so a red raised by a `mod` line or a new struct field
(2026-09-20: `b1f2e3a89`, `pub struct Environment`) stayed red -- or was
`--no-verify`'d -- with the measurement in hand.

In this mode the record's schema is `clean.crystal.chain_revalidation_at_head/v1`,
rows admit IDENTICAL and NUMBERING-ONLY (never STRUCTURAL; `instructions_moved`
is 0 or the tool refuses), and the provenance says explicitly which rebaseline
the fixtures were CUT at and which CONTROL record proves the producer: the
control record must show this driver reproducing the rebaseline's own
`trust-ir.bin` and `trust-ir.txt` digests BYTE FOR BYTE at the rebaseline's rev
(that is what makes a HEAD dump attributable to clean-side movement rather than
to producer drift), and must name this trustc's and driver's exact bytes.  The
`-vV` stamp is NOT the trust rev in this mode -- every crystal driver on this box
carries the 2026-08-11 seed stamp deliberately (CLAUDE.md, "the stamp lies") --
so the trust rev is the control record's `rebuilt_from_trust_rev`, and the stamp
is recorded beside it as what it is.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, NoReturn

from crystal_fixture_freshness import BODIES, EXTRA_BODIES


REPO = Path(__file__).resolve().parent.parent
KERNEL = REPO / "crates" / "clean-kernel"
ARTIFACTS = (
    "clean_kernel.trust-ir.bin",
    "clean_kernel.trust-ir.txt",
    "clean_kernel.coverage.json",
    "clean_kernel.build.log",
    "clean_kernel.axes.json",
    "clean_kernel.argv",
)


def fail(message: str) -> NoReturn:
    raise SystemExit(f"REVALIDATION REFUSED: {message}")


def run(*argv: str) -> str:
    try:
        done = subprocess.run(
            argv,
            cwd=REPO,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        fail(f"command failed: {' '.join(argv)} ({exc})")
    return done.stdout.strip()


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as src:
        for chunk in iter(lambda: src.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def kernel_digest() -> str:
    files = sorted(p for p in (KERNEL / "src").rglob("*.rs") if p.is_file())
    manifest = KERNEL / "Cargo.toml"
    if manifest.is_file():
        files.append(manifest)
    h = hashlib.sha256()
    for path in files:
        rel = path.relative_to(REPO).as_posix()
        h.update(rel.encode())
        h.update(b"\0")
        h.update(sha256(path).encode("ascii"))
        h.update(b"\n")
    return h.hexdigest()


def artifact(path: Path) -> dict[str, Any]:
    if not path.is_file():
        fail(f"required artifact is missing: {path}")
    return {"sha256": sha256(path), "bytes": path.stat().st_size}


# The drift classes `crystal_fixture_freshness.py` assigns to a NUMBERING-ONLY row.
# Mirrored (not imported) so a class the comparator grows is refused here rather
# than admitted unread; `crystal_a1_lineage/freshness.rs` pins the same five.
NUMBERING_CLASSES = frozenset(
    {"functy-index", "type-table-index", "callee-index", "global-index", "loc-file-index"}
)

# Set by main() under --at-head; read by the row builders.
AT_HEAD = False


def _admit_verdict(stem: str, verdict: Any, classes: Any, what: str) -> None:
    if AT_HEAD:
        if verdict == "IDENTICAL" and classes == []:
            return
        if (
            verdict == "NUMBERING-ONLY"
            and isinstance(classes, list)
            and classes
            and all(c in NUMBERING_CLASSES for c in classes)
        ):
            return
        fail(
            f"{stem}: an at-head revalidation admits IDENTICAL/[] or NUMBERING-ONLY over the "
            f"known index classes only, found {verdict!r}/{classes!r} -- a STRUCTURAL verdict "
            f"is a re-derivation of the {what}, never a record"
        )
    if verdict != "IDENTICAL" or classes != []:
        fail(
            f"{stem}: strict current-source revalidation requires IDENTICAL/[] after the "
            f"source-bound fixture rebaseline, found {verdict!r}/{classes!r}"
        )


def primary_row(stem: str, raw: dict[str, Any]) -> dict[str, Any]:
    verdict = raw.get("verdict")
    classes = raw.get("classes")
    head = raw.get("at_head")
    pinned = raw.get("pinned")
    _admit_verdict(stem, verdict, classes, "chain's spec module and refinement theorem")
    if not isinstance(head, dict) or not isinstance(pinned, dict):
        fail(f"{stem}: missing live or pinned lineage data")
    lineage = head.get("lineage")
    flip = head.get("flip_event")
    checks = {
        "lowered": head.get("lowered") is True,
        "spliced": head.get("spliced") is True,
        "unsupported-empty": head.get("unsupported") == [],
        "derived-mir-agreed": head.get("derived_mir_verdict") == "agreed",
        "markers-exact": head.get("markers_exact") is True,
        "flip-fired": isinstance(flip, str)
        and "compiled from trust-ir" in flip
        and isinstance(lineage, str)
        and lineage in flip,
        "instruction-count-pinned": head.get("instr_count") == pinned.get("instr_count"),
    }
    bad = [name for name, ok in checks.items() if not ok]
    if bad:
        fail(f"{stem}: executable-link checks failed: {', '.join(bad)}")
    pinned_lineage = pinned.get("lineage")
    if not (
        isinstance(lineage, str)
        and lineage.startswith("sha256:")
        and isinstance(pinned_lineage, str)
        and pinned_lineage.startswith("sha256:")
    ):
        fail(f"{stem}: lineage values are not sha256 identities")
    return {
        "def_path": raw.get("def_path"),
        "emitted_body_vs_committed_fixture": {
            "verdict": verdict,
            "drift_classes": classes,
            "instructions_moved": 0,
        },
        "links_at_head": {
            "instr_count": head.get("instr_count"),
            "lowered": head.get("lowered"),
            "spliced": head.get("spliced"),
            "unsupported": head.get("unsupported"),
            "calls": head.get("calls"),
            "derived_mir": {
                "verdict": head.get("derived_mir_verdict"),
                "markers_exact": head.get("markers_exact"),
            },
            "flip_fired": True,
        },
        "lineage": {
            "pinned_in_fixture": pinned_lineage,
            "pinned_def_index": pinned.get("def_index"),
            "at_head": lineage,
            "def_index_at_head": head.get("def_index"),
            "func_id_at_head": head.get("func_id"),
            "moved": pinned_lineage != lineage,
        },
    }


def extra_row(stem: str, raw: dict[str, Any]) -> dict[str, Any]:
    verdict = raw.get("verdict")
    classes = raw.get("classes")
    head = raw.get("at_head")
    _admit_verdict(stem, verdict, classes, "helper's model")
    if not isinstance(head, dict):
        fail(f"{stem}: missing live link data")
    checks = {
        "lowered": head.get("lowered") is True,
        "spliced": head.get("spliced") is True,
        "unsupported-empty": head.get("unsupported") == [],
        "derived-mir-unsupported": head.get("derived_mir_verdict") == "unsupported",
        "markers-not-exact": head.get("markers_exact") is False,
        "flip-absent": head.get("flip_event") is None,
    }
    bad = [name for name, ok in checks.items() if not ok]
    if bad:
        fail(f"{stem}: helper fail-closed checks failed: {', '.join(bad)}")
    return {
        "def_path": raw.get("def_path"),
        "emitted_body_vs_committed_fixture": {
            "verdict": verdict,
            "drift_classes": classes,
            "instructions_moved": 0,
        },
        "links_at_head": {
            "instr_count": head.get("instr_count"),
            "lowered": head.get("lowered"),
            "spliced": head.get("spliced"),
            "unsupported": head.get("unsupported"),
            "calls": head.get("calls"),
            "derived_mir": {
                "verdict": head.get("derived_mir_verdict"),
                "markers_exact": head.get("markers_exact"),
            },
            "flip_fired": isinstance(head.get("flip_event"), str),
        },
        "lineage": {
            "at_head": head.get("lineage"),
            "def_index_at_head": head.get("def_index"),
            "func_id_at_head": head.get("func_id"),
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("dump", type=Path)
    ap.add_argument("--freshness-report", type=Path, required=True)
    ap.add_argument("--trustc", type=Path, required=True)
    ap.add_argument("--driver", type=Path, required=True)
    ap.add_argument("--rebaseline-record", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument(
        "--supersedes",
        required=True,
        help="repo-relative current-source chain record this append-only record supersedes",
    )
    ap.add_argument("--clean-rev", default="HEAD")
    ap.add_argument(
        "--at-head",
        action="store_true",
        help="mint an AT-HEAD record: NUMBERING-ONLY rows admitted, fixtures cut at the "
        "rebaseline record's rev, producer proved by --control-record (see module doc)",
    )
    ap.add_argument(
        "--control-record",
        type=Path,
        default=None,
        help="with --at-head: the data/crystal_revalidation_at_head_*.json whose control "
        "dump reproduced the rebaseline's trust-ir digests byte for byte with THIS driver",
    )
    ap.add_argument("--measured-utc", default=None)
    # Build-provenance prose. The defaults describe the sealed stage-1 snapshot
    # every record before 2026-10-07 was measured with; a run on another
    # toolchain states its own rather than inheriting a sentence not about it.
    ap.add_argument(
        "--toolchain-pairing",
        default=(
            "The installed Stage-1 trustc and its Stage-1 sysroot were copied as one "
            "read-only snapshot. Trust's seal_driver guard resolved the driver inside "
            "that snapshot, and sysrootcheck reported matching metadata v12 and a "
            "successful std compile."
        ),
    )
    ap.add_argument(
        "--recipe",
        default=(
            "TRUSTC=<sealed stage1>/bin/trustc TRUST_IR_BUILD_DUMP=<dump> "
            "TRUST_IR_BUILD_TARGET_DIR=<exact-driver prewarm> "
            "scripts/trust_ir_build.sh --print-only; "
            "scripts/crystal_fixture_freshness.py <dump> --json <raw>"
        ),
    )
    args = ap.parse_args()

    try:
        raw = json.loads(args.freshness_report.read_text())
        axes = json.loads((args.dump / "clean_kernel.axes.json").read_text())
        rebaseline = json.loads(args.rebaseline_record.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read generator input: {exc}")
    if raw.get("schema") != "clean.crystal.fixture_freshness/v1":
        fail(f"unexpected freshness schema: {raw.get('schema')!r}")
    if axes.get("schema_self") != "clean.trust_ir_build.measured.v1":
        fail(f"unexpected axes schema: {axes.get('schema_self')!r}")
    if rebaseline.get("schema") != "clean.crystal.fixture_rebaseline/v1":
        fail(f"unexpected rebaseline schema: {rebaseline.get('schema')!r}")
    superseded_path = REPO / args.supersedes
    if (
        superseded_path.parent != REPO / "data"
        or not superseded_path.name.startswith("crystal_chain_revalidation_")
        or not superseded_path.is_file()
    ):
        fail(f"superseded current-source record is missing or outside data/: {args.supersedes}")
    try:
        superseded = json.loads(superseded_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read superseded current-source record: {exc}")
    if not isinstance(superseded, dict) or superseded.get("schema") != "clean.crystal.chain_revalidation/v3":
        fail("superseded current-source record is not a v3 chain revalidation")

    bodies = raw.get("bodies")
    if not isinstance(bodies, dict):
        fail("freshness report carries no bodies object")
    expected = set(BODIES) | set(EXTRA_BODIES)
    if set(bodies) != expected:
        fail(
            "freshness body set differs from the live comparator: "
            f"missing={sorted(expected - set(bodies))}, extra={sorted(set(bodies) - expected)}"
        )

    invariants = axes.get("invariants")
    if not isinstance(invariants, dict) or not invariants:
        fail("axes report carries no fatal invariants")
    nonzero = {k: v for k, v in invariants.items() if v != 0}
    if nonzero:
        fail(f"whole-crate fatal invariants are non-zero: {nonzero}")

    clean_rev = run("git", "rev-parse", args.clean_rev)
    if run(
        "git",
        "status",
        "--porcelain",
        "--untracked-files=all",
        "--",
        "crates/clean-kernel",
    ):
        fail("clean-kernel has tracked or untracked changes outside the requested revision")
    clean_tree = run("git", "rev-parse", f"{clean_rev}^{{tree}}")
    rebaseline_provenance = rebaseline.get("provenance")
    if not isinstance(rebaseline_provenance, dict):
        fail("fixture rebaseline record has no provenance object")
    if rebaseline.get("append_only") is not True:
        fail("fixture rebaseline record is not marked append-only")
    current_kernel_sha = kernel_digest()
    if set(rebaseline.get("complete_body_set") or []) != expected:
        fail("fixture rebaseline record does not cover the exact comparator body set")

    if not args.trustc.is_file() or not args.driver.is_file():
        fail("trustc and driver must both be regular files")
    version = run(str(args.trustc), "-vV").splitlines()
    stamp_rev = next(
        (line.split(":", 1)[1].strip() for line in version if line.startswith("commit-hash:")),
        "",
    )
    if len(stamp_rev) != 40:
        fail("trustc -vV did not report a full commit hash")
    trustc_sha = sha256(args.trustc)
    driver_sha = sha256(args.driver)
    at_head: dict[str, Any] | None = None
    if args.at_head:
        # Fixtures were CUT at the rebaseline's rev; this dump is at `clean_rev`. The
        # producer is proved by the control record, never by the stamp.
        if args.control_record is None:
            fail("--at-head requires --control-record")
        try:
            control = json.loads(args.control_record.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            fail(f"cannot read control record: {exc}")
        if control.get("schema") != "clean.crystal.revalidation_at_head/v1":
            fail(f"control record has an unexpected schema: {control.get('schema')!r}")
        producer = control.get("producer") or {}
        ctrl = control.get("control") or {}
        if producer.get("trustc_sha256") != trustc_sha:
            fail("control record names different trustc bytes than --trustc")
        if producer.get("librustc_driver_sha256") != driver_sha:
            fail("control record names different driver bytes than --driver")
        control_rev = producer.get("rebuilt_from_trust_rev")
        if control_rev != rebaseline_provenance.get("trust_worktree_rev"):
            fail("control record's producer is not the rebaseline's Trust compiler revision")
        for name, key in (
            ("clean_kernel.trust-ir.bin", "dump_binary_sha256"),
            ("clean_kernel.trust-ir.txt", "dump_ir_sha256"),
        ):
            row = ctrl.get(name) or {}
            if row.get("verdict") != "MATCH":
                fail(f"control record does not show {name} reproduced: {row.get('verdict')!r}")
            if row.get("got") != rebaseline_provenance.get(key) or row.get(
                "lane18_recorded"
            ) != rebaseline_provenance.get(key):
                fail(f"control record's {name} digest is not the rebaseline's {key}")
        try:
            control_rel = args.control_record.resolve().relative_to(REPO).as_posix()
        except ValueError:
            fail("control record must live inside this Clean repository")
        fixtures_rev = rebaseline_provenance.get("clean_source_rev")
        if not isinstance(fixtures_rev, str) or len(fixtures_rev) != 40:
            fail("fixture rebaseline record carries no full clean_source_rev")
        if fixtures_rev == clean_rev:
            fail(
                "--at-head at the rebaseline's own rev is the strict record's job; drop --at-head"
            )
        at_head = {
            "fixtures_cut_at_clean_rev": fixtures_rev,
            "fixtures_cut_at_kernel_src_sha256": rebaseline_provenance.get(
                "clean_kernel_src_sha256"
            ),
            "fixtures_rebaseline_record": args.rebaseline_record.resolve()
            .relative_to(REPO)
            .as_posix(),
            "control_record": control_rel,
            "control_verdict": "MATCH on clean_kernel.trust-ir.bin and clean_kernel.trust-ir.txt "
            "at the rebaseline's rev -- this driver reproduces the rebaseline's producer",
            # A package-store toolchain (trust/9192, 2026-10-18) stamps its own
            # commit, so the seed-stamp sentence is said only when it is true.
            "trust_worktree_rev_source": "control record `producer.rebuilt_from_trust_rev`; "
            + (
                "the -vV stamp below names the same commit"
                if stamp_rev == control_rev
                else "the -vV stamp below is the 2026-08-11 seed stamp every crystal driver "
                "carries"
            ),
        }
        trust_rev = control_rev
    else:
        trust_rev = stamp_rev
        if rebaseline_provenance.get("clean_source_rev") != clean_rev:
            fail("fixture rebaseline record covers a different Clean source revision")
        if rebaseline_provenance.get("clean_kernel_src_sha256") != current_kernel_sha:
            fail("fixture rebaseline record covers a different clean-kernel source tree")
        for key, name in (
            ("dump_binary_sha256", "clean_kernel.trust-ir.bin"),
            ("dump_ir_sha256", "clean_kernel.trust-ir.txt"),
            ("coverage_sha256", "clean_kernel.coverage.json"),
        ):
            if rebaseline_provenance.get(key) != sha256(args.dump / name):
                fail(f"fixture rebaseline record covers a different {name} artifact")
        if rebaseline_provenance.get("trust_worktree_rev") != trust_rev:
            fail("fixture rebaseline record names a different Trust compiler revision")
        if rebaseline_provenance.get("trustc_sha256") != trustc_sha:
            fail("fixture rebaseline record names different trustc bytes")
        if rebaseline_provenance.get("librustc_driver_sha256") != driver_sha:
            fail("fixture rebaseline record names different driver bytes")

    artifacts = {name: artifact(args.dump / name) for name in ARTIFACTS}
    artifacts[args.freshness_report.name] = artifact(args.freshness_report)
    artifacts[args.rebaseline_record.name] = artifact(args.rebaseline_record)
    try:
        rebaseline_rel = args.rebaseline_record.resolve().relative_to(REPO).as_posix()
    except ValueError:
        fail("fixture rebaseline record must live inside this Clean repository")
    measured = axes.get("measured") or {}
    measurement = {
        "bodies": measured.get("bodies"),
        "lowered": measured.get("lowered"),
        "spliced": measured.get("spliced"),
        "derived_mir_agreed": measured.get("derived_mir_agreed"),
        "derived_mir_mismatch": measured.get("mismatch"),
        "interpreter_agreed": measured.get("interpreter_agreed"),
        "interpreter_mismatch": measured.get("interpreter_mismatch"),
        "seam_agreed": measured.get("seam_agreed"),
        "seam_mismatch": measured.get("seam_mismatch"),
        "lineage_rows": measured.get("lineage_rows"),
        "flip_events_total": measured.get("flip_events_total"),
        "flip_events_codegen": measured.get("flip_events_codegen"),
        "flip_events_ctfe": measured.get("flip_events_ctfe"),
        "flip_backed_total": measured.get("flip_backed_total"),
        "mode": "print-only; pre-existing whole-crate axis reds are recorded, not re-baselined",
    }
    if measurement["derived_mir_mismatch"] != 0:
        fail("whole-crate derived-MIR mismatch count is non-zero")

    global AT_HEAD
    AT_HEAD = bool(args.at_head)
    chains = {stem: primary_row(stem, bodies[stem]) for stem in BODIES}
    extras = {stem: extra_row(stem, bodies[stem]) for stem in EXTRA_BODIES}
    counts: dict[str, int] = {}
    for row in chains.values():
        verdict = row["emitted_body_vs_committed_fixture"]["verdict"]
        counts[verdict] = counts.get(verdict, 0) + 1

    measured_utc = args.measured_utc or dt.datetime.now(dt.timezone.utc).replace(
        microsecond=0
    ).isoformat().replace("+00:00", "Z")
    record = {
        "schema": (
            "clean.crystal.chain_revalidation_at_head/v1"
            if at_head
            else "clean.crystal.chain_revalidation/v3"
        ),
        "measured_utc": measured_utc,
        "what_this_is": (
            "A mechanically generated live-trustc revalidation of every committed Crystal "
            "chain AT HEAD against fixtures cut at an earlier rev: the exact Clean source "
            "measured, the producer proved by a byte-for-byte control, the per-body verdict "
            "(IDENTICAL or NUMBERING-ONLY, zero instructions moved), whole-crate invariants, "
            "and all executable links. It rewrites no fixture and no historical record."
            if at_head
            else "A mechanically generated live-trustc revalidation of every committed Crystal "
            "chain. It binds the exact Clean source, paired Trust driver/sysroot identity, "
            "fixture comparison, whole-crate invariants, and all executable links without "
            "rewriting any historical record."
        ),
        "supersedes_for_current_source_scope": args.supersedes,
        "provenance": {
            "clean_source_rev": clean_rev,
            "clean_source_tree": clean_tree,
            "clean_kernel_src_sha256": current_kernel_sha,
            "trust_worktree_rev": trust_rev,
            "trustc_version": version[0],
            "trustc_sha256": trustc_sha,
            "librustc_driver_sha256": driver_sha,
            "toolchain_pairing": args.toolchain_pairing,
            "recipe": args.recipe,
            "dependency_prewarm": (
                "The target dependency graph was built by this exact trustc/sysroot pair "
                "with in-compilation verification disabled before the measurement. "
                "trust_ir_build.sh then used that same compiler to cargo-clean clean-kernel "
                "and recompiled the subject non-incrementally with lowering and flip enabled."
            ),
            "profile": (
                "release, -Cdebuginfo=0, -Cdebug-assertions=off; release-only inference "
                "spine present 6/6"
            ),
            "measurement_driver": "scripts/trust_ir_build.sh",
            "measurement_driver_sha256": sha256(REPO / "scripts" / "trust_ir_build.sh"),
            **({"at_head": at_head} if at_head else {}),
        },
        "artifacts": artifacts,
        "generator": {
            "script": "scripts/crystal_chain_revalidation.py",
            "append_only": True,
            "freshness_schema": raw["schema"],
            "axes_schema": axes["schema_self"],
            "fixture_rebaseline_record": rebaseline_rel,
            "fixture_rebaseline_schema": rebaseline["schema"],
        },
        "measurement": measurement,
        "fatal_invariants": invariants,
        "chains": chains,
        "extra_fixtures": extras,
        "finding": (
            f"All {len(chains)} primary Crystal bodies retain their exact instruction "
            f"graphs: {counts.get('IDENTICAL', 0)} identical and "
            f"{counts.get('NUMBERING-ONLY', 0)} numbering-only"
            + (
                f" against fixtures cut at {at_head['fixtures_cut_at_clean_rev'][:9]}; "
                "zero structural"
                if at_head
                else ""
            )
            + ". Every primary remains lowered, spliced, derived-MIR agreed, marker-exact, "
            "and flipped."
        ),
    }

    out = args.out if args.out.is_absolute() else REPO / args.out
    if out.parent != REPO / "data" or not out.name.startswith(
        "crystal_chain_revalidation_"
    ):
        fail("output must be a new data/crystal_chain_revalidation_*.json path")
    try:
        with out.open("x", encoding="utf-8") as dst:
            json.dump(record, dst, indent=1)
            dst.write("\n")
    except FileExistsError:
        fail(f"append-only output already exists: {out}")
    print(f"wrote {out}")
    print(f"  clean {clean_rev}")
    print(f"  trust {trust_rev}")
    print(f"  chains {len(chains)} ({counts})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
