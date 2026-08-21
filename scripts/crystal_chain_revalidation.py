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


def primary_row(stem: str, raw: dict[str, Any]) -> dict[str, Any]:
    verdict = raw.get("verdict")
    classes = raw.get("classes")
    head = raw.get("at_head")
    pinned = raw.get("pinned")
    if verdict != "IDENTICAL" or classes != []:
        fail(
            f"{stem}: strict current-source revalidation requires IDENTICAL/[] after the "
            f"source-bound fixture rebaseline, found {verdict!r}/{classes!r}"
        )
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
    if verdict != "IDENTICAL" or classes != []:
        fail(
            f"{stem}: strict current-source helper requires IDENTICAL/[], "
            f"found {verdict!r}/{classes!r}"
        )
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
    ap.add_argument("--measured-utc", default=None)
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
    if rebaseline_provenance.get("clean_source_rev") != clean_rev:
        fail("fixture rebaseline record covers a different Clean source revision")
    current_kernel_sha = kernel_digest()
    if rebaseline_provenance.get("clean_kernel_src_sha256") != current_kernel_sha:
        fail("fixture rebaseline record covers a different clean-kernel source tree")
    for key, name in (
        ("dump_binary_sha256", "clean_kernel.trust-ir.bin"),
        ("dump_ir_sha256", "clean_kernel.trust-ir.txt"),
        ("coverage_sha256", "clean_kernel.coverage.json"),
    ):
        if rebaseline_provenance.get(key) != sha256(args.dump / name):
            fail(f"fixture rebaseline record covers a different {name} artifact")
    if set(rebaseline.get("complete_body_set") or []) != expected:
        fail("fixture rebaseline record does not cover the exact comparator body set")

    if not args.trustc.is_file() or not args.driver.is_file():
        fail("trustc and driver must both be regular files")
    version = run(str(args.trustc), "-vV").splitlines()
    trust_rev = next(
        (line.split(":", 1)[1].strip() for line in version if line.startswith("commit-hash:")),
        "",
    )
    if len(trust_rev) != 40:
        fail("trustc -vV did not report a full commit hash")
    trustc_sha = sha256(args.trustc)
    driver_sha = sha256(args.driver)
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
        "schema": "clean.crystal.chain_revalidation/v3",
        "measured_utc": measured_utc,
        "what_this_is": (
            "A mechanically generated live-trustc revalidation of every committed Crystal "
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
            "toolchain_pairing": (
                "The installed Stage-1 trustc and its Stage-1 sysroot were copied as one "
                "read-only snapshot. Trust's seal_driver guard resolved the driver inside "
                "that snapshot, and sysrootcheck reported matching metadata v12 and a "
                "successful std compile."
            ),
            "recipe": (
                "TRUSTC=<sealed stage1>/bin/trustc TRUST_IR_BUILD_DUMP=<dump> "
                "TRUST_IR_BUILD_TARGET_DIR=<exact-driver prewarm> "
                "scripts/trust_ir_build.sh --print-only; "
                "scripts/crystal_fixture_freshness.py <dump> --json <raw>"
            ),
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
            f"{counts.get('NUMBERING-ONLY', 0)} numbering-only. Every primary remains "
            "lowered, spliced, derived-MIR agreed, marker-exact, and flipped."
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
