#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Source-bound, fail-closed Crystal fixture rebaseline.

This is the WRITE half of ``crystal_fixture_freshness.py``.  It is deliberately
separate because a live comparison is safe to run routinely, while replacing a
committed artifact pin is a reviewed operation.  A rebaseline is permitted only
when all of the following agree exactly:

* the requested Clean revision and clean-kernel source digest;
* the live binary/text IR, coverage report, pre-rebaseline freshness report,
  trustc, and rustc-driver hashes supplied by the reviewer;
* the complete primary/helper body set in the freshness comparator;
* a unique live body for every fixture and an exact reproduction of every
  verdict, class list, and unified diff in the pre-rebaseline report;
* NUMBERING-ONLY (or already IDENTICAL) drift, never STRUCTURAL drift; and
* the source-bound proof/spec/tag bindings listed in a reviewed manifest.

The binding check is load-bearing.  A historical attempt to refresh every
fixture made strict freshness green while breaking the registered
ExprPathStep type and Level::is_zero callee identities.  This tool refuses that
partial state before writing anything.

On success it atomically replaces the fixture texts with the exact bodies from
the live dump and exclusively creates an append-only old->new identity ledger.
It never edits proof/spec/tag bindings itself.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, NoReturn

from crystal_fixture_freshness import (
    BODIES,
    EXTRA_BODIES,
    classify,
    extract,
    signature_of,
)


REPO = Path(__file__).resolve().parent.parent
FIXTURES = REPO / "crates" / "clean-verify" / "tests" / "fixtures"
KERNEL = REPO / "crates" / "clean-kernel"
EVIDENCE: dict[str, str] = {
    "has_cubical_layer": "has_cubical_layer.lineage.json",
    "level_kind_ord": "level_kind_ord.lineage.json",
    "from_source_system": "from_source_system.lineage.json",
    "flat_flags_contains": "flat_flags_contains.lineage.json",
    "bvar_in_range": "bvar_in_range.lineage.json",
    "is_valid_char": "is_valid_char.lineage.json",
    "expr_path_step_clone": "expr_path_step_clone.lineage.json",
    "float_div": "float_div.lineage.json",
    "get_char_val_trunc": "get_char_val_trunc.lineage.json",
    "meta_tag_shl": "meta_tag_shl.lineage.json",
    "level_is_zero": "level_is_zero.a0.json",
    "float_add": "float_add.lineage.json",
    "float_sub": "float_sub.lineage.json",
    "float_mul": "float_mul.lineage.json",
    "strict_monads": "strict_monads.lineage.json",
    "flat_flags_with": "flat_flags_with.lineage.json",
    "node_id_index": "node_id_index.lineage.json",
    "simp_priority_value": "simp_priority_value.lineage.json",
}

# These are the numbering tokens whose concrete identity is consumed outside
# the fixture parser.  Their new values must be bound by the reviewed manifest
# before fixture replacement.  Other moved tokens are debug/file coordinates
# or indices the corresponding lane deliberately treats as a moving artifact
# pin; the append-only ledger still records every one of them.
REQUIRED_BINDINGS: dict[str, set[tuple[str, str, str]]] = {
    "from_source_system": {("type-table-index", "enum.175", "enum.178")},
    "flat_flags_contains": {("type-table-index", "struct.1012", "struct.1017")},
    "expr_path_step_clone": {("type-table-index", "enum.181", "enum.184")},
    "level_is_zero": {
        ("callee-index", "@func.4914", "@func.3894"),
        ("callee-index", "@func.4925", "@func.3905"),
    },
    "strict_monads": {("type-table-index", "struct.433", "struct.441")},
    "flat_flags_with": {("type-table-index", "struct.1012", "struct.1017")},
    "node_id_index": {("type-table-index", "struct.317", "struct.323")},
}


class Refusal(RuntimeError):
    """A checked precondition failed; no output is authorized."""


def refuse(message: str) -> NoReturn:
    raise Refusal(message)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as src:
        for chunk in iter(lambda: src.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def text_sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


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
        refuse(f"command failed: {' '.join(argv)} ({exc})")
    return done.stdout.strip()


def git_text(rev: str, rel: str) -> str:
    """Read the committed pre-rebaseline fixture without trusting the worktree."""
    try:
        done = subprocess.run(
            ("git", "show", f"{rev}:{rel}"),
            cwd=REPO,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        refuse(f"cannot read committed fixture {rev}:{rel} ({exc})")
    try:
        return done.stdout.decode("utf-8")
    except UnicodeDecodeError as exc:
        refuse(f"committed fixture {rev}:{rel} is not UTF-8 ({exc})")


def validate_existing_pin_set(
    existing: dict[Path, object],
    expected_paths: set[Path],
    new_record_rel: str,
    committed_rev: str,
) -> tuple[str | None, dict[str, Any] | None]:
    """Authenticate the complete current pin generation before replacing it.

    The first rebaseline had no predecessor.  Every later rebaseline replaces
    the *current* nested pin while retaining the predecessor's append-only
    ledger.  Accepting an arbitrary nested object here would let a hand edit
    become the alleged predecessor, so the complete file bytes must match the
    predecessor ledger's recorded post-write hash and its duplicated identity
    fields must match the pin itself.

    A pin set naming ``new_record_rel`` is the one permitted interrupted-write
    replay: all pins were installed, but exclusive creation of the new ledger
    had not happened yet.  There can be no predecessor ledger in that case.
    """
    if not existing:
        return None, None
    if set(existing) != expected_paths:
        refuse(
            "an interrupted or successor rebaseline has an incomplete or expanded evidence set: "
            f"missing={sorted(str(p.relative_to(REPO)) for p in expected_paths - set(existing))}, "
            f"extra={sorted(str(p.relative_to(REPO)) for p in set(existing) - expected_paths)}"
        )

    records: set[str] = set()
    for path, pin in existing.items():
        if not isinstance(pin, dict):
            refuse(f"current-source evidence pin is not an object: {path.relative_to(REPO)}")
        record = pin.get("record")
        if not isinstance(record, str) or not record:
            refuse(f"current-source evidence pin has no record: {path.relative_to(REPO)}")
        records.add(record)
    if len(records) != 1:
        refuse(f"current-source evidence pins name mixed predecessor records: {sorted(records)}")
    prior_rel = next(iter(records))
    if prior_rel == new_record_rel:
        return prior_rel, None

    prior_path = REPO / prior_rel
    if (
        prior_path.parent != REPO / "data"
        or not prior_path.name.startswith("crystal_fixture_rebaseline_")
        or not prior_path.is_file()
    ):
        refuse(f"current-source predecessor is not a committed rebaseline ledger: {prior_rel}")
    try:
        prior_text = prior_path.read_text()
        exact(
            "predecessor committed identity",
            text_sha256(prior_text),
            text_sha256(git_text(committed_rev, prior_rel)),
        )
        prior = json.loads(prior_text)
    except (OSError, json.JSONDecodeError) as exc:
        refuse(f"cannot read current-source predecessor {prior_rel}: {exc}")
    if not isinstance(prior, dict):
        refuse(f"current-source predecessor is not an object: {prior_rel}")
    exact("predecessor schema", str(prior.get("schema")), "clean.crystal.fixture_rebaseline/v1")
    if prior.get("append_only") is not True:
        refuse(f"current-source predecessor is not append-only: {prior_rel}")
    if set(prior.get("complete_body_set") or []) != set(BODIES) | set(EXTRA_BODIES):
        refuse(f"current-source predecessor has a stale body set: {prior_rel}")
    ledger = prior.get("lineage_evidence")
    if not isinstance(ledger, dict) or set(ledger) != set(EVIDENCE):
        refuse(f"current-source predecessor has an incomplete lineage ledger: {prior_rel}")
    provenance = prior.get("provenance")
    if not isinstance(provenance, dict):
        refuse(f"current-source predecessor has no provenance: {prior_rel}")
    for key in (
        "clean_source_rev",
        "clean_source_tree",
        "clean_kernel_src_sha256",
        "trust_worktree_rev",
        "trustc_sha256",
        "librustc_driver_sha256",
        "dump_binary_sha256",
        "dump_ir_sha256",
        "coverage_sha256",
        "binding_manifest",
        "binding_manifest_sha256",
    ):
        if not isinstance(provenance.get(key), str) or not provenance[key]:
            refuse(f"current-source predecessor has no provenance.{key}: {prior_rel}")

    for stem, filename in EVIDENCE.items():
        path = FIXTURES / filename
        pin = existing[path]
        assert isinstance(pin, dict)
        entry = ledger.get(stem)
        if not isinstance(entry, dict):
            refuse(f"{prior_rel}: predecessor row {stem} is not an object")
        rel = path.relative_to(REPO).as_posix()
        exact(
            f"{stem} committed predecessor pin",
            sha256(path),
            text_sha256(git_text(committed_rev, rel)),
        )
        exact(
            f"{stem} predecessor pin schema",
            str(pin.get("schema")),
            "clean.crystal.current_source_bound_pin/v1",
        )
        exact(f"{stem} predecessor pin record", str(pin.get("record")), prior_rel)
        exact(f"{stem} predecessor file", str(entry.get("file")), rel)
        exact(f"{stem} predecessor post-write hash", sha256(path), str(entry.get("new_sha256")))
        exact(f"{stem} predecessor lineage", str(pin.get("lineage")), str(entry.get("current_lineage")))
        exact(f"{stem} predecessor def_index", str(pin.get("def_index")), str(entry.get("current_def_index")))
        exact(f"{stem} predecessor func_id", str(pin.get("func_id")), str(entry.get("current_func_id")))
        build = pin.get("build")
        artifacts = build.get("artifacts") if isinstance(build, dict) else None
        if not isinstance(build, dict) or not isinstance(artifacts, dict):
            refuse(f"{stem}: predecessor pin has no source-bound build/artifact object")
        for pin_key, provenance_key in (
            ("clean_source_rev", "clean_source_rev"),
            ("clean_source_tree", "clean_source_tree"),
            ("clean_kernel_src_sha256", "clean_kernel_src_sha256"),
            ("trust_worktree_rev", "trust_worktree_rev"),
            ("trustc_sha256", "trustc_sha256"),
            ("librustc_driver_sha256", "librustc_driver_sha256"),
        ):
            exact(
                f"{stem} predecessor {pin_key}",
                str(build.get(pin_key)),
                str(provenance.get(provenance_key)),
            )
        for artifact_name, provenance_key in (
            ("clean_kernel.trust-ir.bin", "dump_binary_sha256"),
            ("clean_kernel.trust-ir.txt", "dump_ir_sha256"),
            ("clean_kernel.coverage.json", "coverage_sha256"),
        ):
            row = artifacts.get(artifact_name)
            if not isinstance(row, dict):
                refuse(f"{stem}: predecessor pin has no {artifact_name} row")
            exact(
                f"{stem} predecessor {artifact_name}",
                str(row.get("sha256")),
                str(provenance.get(provenance_key)),
            )
        exact(
            f"{stem} predecessor binding manifest",
            Path(str(pin.get("binding_manifest"))).name,
            str(provenance.get("binding_manifest")),
        )
    return prior_rel, prior


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


def exact(label: str, actual: str, expected: str) -> None:
    if actual != expected:
        refuse(f"{label} mismatch: expected {expected}, found {actual}")


def validate_body_set(bodies: object) -> dict[str, Any]:
    if not isinstance(bodies, dict):
        refuse("freshness report carries no bodies object")
    expected = set(BODIES) | set(EXTRA_BODIES)
    actual = set(bodies)
    if actual != expected:
        refuse(
            "freshness report body set is incomplete or expanded: "
            f"missing={sorted(expected - actual)}, extra={sorted(actual - expected)}"
        )
    return bodies


def changed_token_pairs(old: str, new: str, classes: tuple[str, ...]) -> list[dict[str, str]]:
    patterns = {
        "functy-index": r"functy\.\d+",
        "type-table-index": r"\b(?:enum|struct|tuple|array)\.\d+",
        "callee-index": r"@func\.\d+",
        "global-index": r"@global\.\d+",
        "loc-file-index": r"#loc:\s+\d+(?:\s+\d+\s+\d+)?",
    }
    pairs: list[dict[str, str]] = []
    for cls in classes:
        pattern = patterns.get(cls)
        if pattern is None:
            refuse(f"unknown drift class {cls!r}")
        left = re.findall(pattern, old)
        right = re.findall(pattern, new)
        if len(left) != len(right):
            refuse(f"{cls}: token arity changed on {old!r} -> {new!r}")
        for before, after in zip(left, right):
            if before != after:
                pairs.append({"class": cls, "old": before, "new": after})
    return pairs


def plan_body(stem: str, row: dict[str, Any], dump_text: str, fixture_text: str) -> dict[str, Any]:
    found = extract(dump_text, signature_of(fixture_text))
    if len(found) != 1:
        refuse(f"{stem}: live body binding is ambiguous ({len(found)} matches)")
    live = found[0]
    if len(fixture_text.splitlines()) != len(live.splitlines()):
        classes: dict[str, list[str]] = {
            "STRUCTURAL": [
                f"line count {len(fixture_text.splitlines())} -> {len(live.splitlines())}"
            ]
        }
    else:
        classes = {}
        for before, after in zip(fixture_text.splitlines(), live.splitlines()):
            if before != after:
                for cls in classify(before, after):
                    classes.setdefault(cls, []).append(
                        f"{before.strip()}  ->  {after.strip()}"
                    )
    verdict = "IDENTICAL" if fixture_text == live else (
        "STRUCTURAL" if "STRUCTURAL" in classes else "NUMBERING-ONLY"
    )
    class_names = sorted(classes)
    report_verdict = row.get("verdict")
    report_classes = row.get("classes")
    if verdict != report_verdict or class_names != report_classes:
        refuse(
            f"{stem}: pre-report does not reproduce: "
            f"report=({report_verdict!r}, {report_classes!r}), "
            f"actual=({verdict!r}, {class_names!r})"
        )
    if verdict not in ("IDENTICAL", "NUMBERING-ONLY"):
        refuse(f"{stem}: {verdict} drift is a re-derivation, not a rebaseline")
    expected_diff = "" if verdict == "IDENTICAL" else "".join(
        difflib.unified_diff(
            fixture_text.splitlines(keepends=True),
            live.splitlines(keepends=True),
            fromfile=f"fixture {stem}.trust-ir.txt",
            tofile="live dump",
        )
    )
    if (row.get("diff") or "") != expected_diff:
        refuse(f"{stem}: pre-report unified diff does not bind these exact texts")

    changed_lines: list[dict[str, Any]] = []
    token_pairs: list[dict[str, str]] = []
    for line_no, (before, after) in enumerate(
        zip(fixture_text.splitlines(), live.splitlines()), start=1
    ):
        if before == after:
            continue
        line_classes = classify(before, after)
        if "STRUCTURAL" in line_classes:
            refuse(f"{stem}:{line_no}: structural line reached numbering rebaseline")
        pairs = changed_token_pairs(before, after, line_classes)
        token_pairs.extend(pairs)
        changed_lines.append(
            {
                "line": line_no,
                "classes": list(line_classes),
                "old": before,
                "new": after,
                "token_pairs": pairs,
            }
        )
    return {
        "def_path": row.get("def_path"),
        "verdict_before": verdict,
        "verdict_after_expected": "IDENTICAL",
        "classes": class_names,
        "changed_line_count": len(changed_lines),
        "changed_lines": changed_lines,
        "token_pairs": token_pairs,
        "old_sha256": text_sha256(fixture_text),
        "new_sha256": text_sha256(live),
        "old_bytes": len(fixture_text.encode()),
        "new_bytes": len(live.encode()),
        "live_text": live,
    }


def manifest_binding_set(manifest: dict[str, Any]) -> set[tuple[str, str, str, str]]:
    bindings = manifest.get("bindings")
    if not isinstance(bindings, list):
        refuse("binding manifest carries no bindings list")
    out: set[tuple[str, str, str, str]] = set()
    for i, binding in enumerate(bindings):
        if not isinstance(binding, dict):
            refuse(f"binding {i} is not an object")
        stem = binding.get("stem")
        cls = binding.get("class")
        old = binding.get("old")
        new = binding.get("new")
        if not all(isinstance(x, str) and x for x in (stem, cls, old, new)):
            refuse(f"binding {i} has incomplete identity fields")
        key = (stem, cls, old, new)
        if key in out:
            refuse(f"binding {i} duplicates {key}")
        out.add(key)
        anchors = binding.get("anchors")
        if not isinstance(anchors, list) or not anchors:
            refuse(f"binding {i} has no proof/spec/tag anchors")
        for j, anchor in enumerate(anchors):
            if not isinstance(anchor, dict):
                refuse(f"binding {i} anchor {j} is not an object")
            rel = anchor.get("file")
            needle = anchor.get("must_contain")
            count = anchor.get("count")
            if not isinstance(rel, str) or not isinstance(needle, str) or not isinstance(count, int):
                refuse(f"binding {i} anchor {j} is incomplete")
            path = REPO / rel
            try:
                text = path.read_text()
            except OSError as exc:
                refuse(f"binding {i} anchor {j} is unreadable: {path} ({exc})")
            actual = text.count(needle)
            if actual != count:
                refuse(
                    f"binding {i} anchor {j} is stale: {rel} contains the required "
                    f"new binding {actual} times, expected {count}"
                )
    return out


def require_identical_successor(plans: dict[str, dict[str, Any]]) -> None:
    nonidentical = sorted(
        stem
        for stem, plan in plans.items()
        if plan["verdict_before"] != "IDENTICAL"
        or plan["classes"]
        or plan["token_pairs"]
    )
    if nonidentical:
        refuse(
            "identical-fixtures successor mode cannot authorize fixture numbering drift: "
            f"{nonidentical}"
        )


def verify_required_bindings(
    plans: dict[str, dict[str, Any]],
    manifest: dict[str, Any],
    prior_record_rel: str | None,
    prior_record: dict[str, Any] | None,
) -> None:
    supplied = manifest_binding_set(manifest)
    required = {
        (stem, cls, old, new)
        for stem, rows in REQUIRED_BINDINGS.items()
        for cls, old, new in rows
    }

    mode = manifest.get("binding_mode", "numbering-repin")
    if mode == "identical-fixtures-successor":
        if prior_record_rel is None or prior_record is None:
            refuse("an identical-fixtures successor has no authenticated predecessor record")
        exact(
            "successor predecessor record",
            str(manifest.get("prior_rebaseline_record")),
            prior_record_rel,
        )
        prior_provenance = prior_record.get("provenance")
        if not isinstance(prior_provenance, dict):
            refuse("authenticated predecessor has no provenance object")
        prior_manifest_name = prior_provenance.get("binding_manifest")
        if not isinstance(prior_manifest_name, str) or not prior_manifest_name:
            refuse("authenticated predecessor has no binding manifest")
        prior_manifest_rel = f"data/{prior_manifest_name}"
        exact(
            "successor predecessor binding manifest",
            str(manifest.get("prior_binding_manifest")),
            prior_manifest_rel,
        )
        prior_manifest_path = REPO / prior_manifest_rel
        if not prior_manifest_path.is_file():
            refuse(f"successor predecessor binding manifest is missing: {prior_manifest_rel}")
        exact(
            "successor predecessor binding manifest hash",
            sha256(prior_manifest_path),
            str(prior_provenance.get("binding_manifest_sha256")),
        )
        try:
            prior_manifest = json.loads(prior_manifest_path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            refuse(f"cannot read successor predecessor binding manifest: {exc}")
        if not isinstance(prior_manifest, dict):
            refuse("successor predecessor binding manifest is not an object")
        inherited = manifest_binding_set(prior_manifest)
        if inherited != required:
            refuse(
                "successor predecessor no longer covers the complete load-bearing mapping set: "
                f"missing={sorted(required - inherited)}, extra={sorted(inherited - required)}"
            )
        require_identical_successor(plans)
        if supplied:
            refuse("identical-fixtures successor must inherit bindings, not restate new deltas")
        return
    if mode != "numbering-repin":
        refuse(f"unknown binding mode: {mode!r}")
    if supplied != required:
        refuse(
            "binding manifest does not cover exactly the load-bearing mappings: "
            f"missing={sorted(required - supplied)}, extra={sorted(supplied - required)}"
        )
    for stem, cls, old, new in required:
        actual = {
            (pair["class"], pair["old"], pair["new"])
            for pair in plans[stem]["token_pairs"]
        }
        if (cls, old, new) not in actual:
            refuse(f"binding {stem} {old}->{new} is not present in the exact live delta")


def current_evidence_pin(
    *,
    stem: str,
    report_row: dict[str, Any],
    coverage_row: dict[str, Any],
    axes: dict[str, Any],
    record_rel: str,
    bindings_rel: str,
    measured_utc: str,
    clean_rev: str,
    clean_tree: str,
    kernel_sha: str,
    trust_rev: str,
    trustc_sha: str,
    driver_sha: str,
    dump: Path,
    emitted_sha: str,
) -> dict[str, Any]:
    head = report_row.get("at_head")
    if not isinstance(head, dict):
        refuse(f"{stem}: freshness report has no live evidence row")
    dm = (coverage_row.get("differentials") or {}).get("derived_mir")
    if not isinstance(dm, dict):
        refuse(f"{stem}: coverage row has no derived-MIR differential")
    flip = head.get("flip_event")
    if not isinstance(flip, str) or "compiled from trust-ir" not in flip:
        refuse(f"{stem}: current primary body has no codegen flip event")
    for key in (
        "def_index",
        "func_id",
        "instr_count",
        "lineage",
        "lowered",
        "spliced",
        "unsupported",
        "calls",
    ):
        if head.get(key) != coverage_row.get(key):
            refuse(f"{stem}: freshness and coverage disagree on {key}")
    if dm.get("verdict") != "agreed" or dm.get("markers_exact") is not True:
        refuse(f"{stem}: current proof-authority links are not agreed/marker-exact")
    lineage = coverage_row.get("lineage")
    if not isinstance(lineage, str) or lineage not in flip:
        refuse(f"{stem}: flip event is not bound to the coverage lineage")
    measured = axes.get("measured")
    invariants = axes.get("invariants")
    if not isinstance(measured, dict) or not isinstance(invariants, dict):
        refuse("axes report is missing measurements or fatal invariants")
    if any(value != 0 for value in invariants.values()):
        refuse(f"whole-crate fatal invariants are non-zero: {invariants}")
    artifacts = {}
    for name in (
        "clean_kernel.trust-ir.bin",
        "clean_kernel.trust-ir.txt",
        "clean_kernel.coverage.json",
        "clean_kernel.build.log",
        "clean_kernel.axes.json",
        "clean_kernel.argv",
    ):
        path = dump / name
        if not path.is_file():
            refuse(f"current evidence artifact is missing: {path}")
        artifacts[name] = {"sha256": sha256(path), "bytes": path.stat().st_size}
    return {
        "schema": "clean.crystal.current_source_bound_pin/v1",
        "record": record_rel,
        "binding_manifest": bindings_rel,
        "measured_utc": measured_utc,
        "def_path": report_row.get("def_path"),
        "def_index": coverage_row.get("def_index"),
        "func_id": coverage_row.get("func_id"),
        "instr_count": coverage_row.get("instr_count"),
        "lineage": lineage,
        "lowered": coverage_row.get("lowered"),
        "spliced": coverage_row.get("spliced"),
        "unsupported": coverage_row.get("unsupported"),
        "calls": coverage_row.get("calls"),
        "derived_mir": dm,
        "interpreter": (coverage_row.get("differentials") or {}).get("interpreter"),
        "flip_event": {
            "fired": True,
            "seam": "codegen",
            "lineage": lineage,
            "matches_artifact_lineage": True,
            "raw": flip,
        },
        "emitted_body": {
            "verdict": "IDENTICAL",
            "classes": [],
            "sha256": emitted_sha,
        },
        "build": {
            "clean_source_rev": clean_rev,
            "clean_source_tree": clean_tree,
            "clean_kernel_src_sha256": kernel_sha,
            "trust_worktree_rev": trust_rev,
            "trustc_sha256": trustc_sha,
            "librustc_driver_sha256": driver_sha,
            "profile": "release, -Cdebuginfo=0, -Cdebug-assertions=off",
            "recipe": (
                "TRUSTC=<sealed stage1>/bin/trustc TRUST_IR_BUILD_DUMP=<dump> "
                "TRUST_IR_BUILD_TARGET_DIR=<exact-driver prewarm> "
                "scripts/trust_ir_build.sh --print-only"
            ),
            "driver_seal": (
                "Trust seal_driver guard passed with the sole resolved driver inside the "
                "read-only snapshot; sysrootcheck reported metadata v12/v12 and compiled std."
            ),
            "artifacts": artifacts,
            "whole_crate_measurement": measured,
            "fatal_invariants": invariants,
        },
        "historical_top_level_preserved": True,
        "how_to_re_derive": (
            "Run the exact live dump recipe in build.recipe, then "
            "scripts/crystal_fixture_freshness.py <dump> --strict and the source-bound "
            "scripts/crystal_fixture_rebaseline.py workflow."
        ),
    }


def selftest() -> None:
    # Stale-source control: exact means exact.
    try:
        exact("clean source", "stale", "current")
    except Refusal:
        pass
    else:
        raise AssertionError("stale source was accepted")

    # Missing-chain control.
    complete = {stem: {} for stem in set(BODIES) | set(EXTRA_BODIES)}
    missing = dict(complete)
    missing.pop(next(iter(BODIES)))
    try:
        validate_body_set(missing)
    except Refusal:
        pass
    else:
        raise AssertionError("missing chain was accepted")

    fixture = "rustcc fn @m::f(functy.1) {\nbb0:\n    ret\n}\n"
    live = "rustcc fn @m::f(functy.2) {\nbb0:\n    ret\n}\n"
    row = {
        "verdict": "NUMBERING-ONLY",
        "classes": ["functy-index"],
        "diff": "".join(
            difflib.unified_diff(
                fixture.splitlines(keepends=True),
                live.splitlines(keepends=True),
                fromfile="fixture x.trust-ir.txt",
                tofile="live dump",
            )
        ),
    }
    # Ambiguous live binding control.
    try:
        plan_body("x", row, live + live, fixture)
    except Refusal:
        pass
    else:
        raise AssertionError("ambiguous body was accepted")

    # Falsified report control.
    bad = dict(row)
    bad["classes"] = ["loc-file-index"]
    try:
        plan_body("x", bad, live, fixture)
    except Refusal:
        pass
    else:
        raise AssertionError("mismatched report was accepted")

    # A successor may inherit the reviewed numeric bindings only when every
    # fixture body is byte-identical.  A numbering move must return to the
    # explicit proof/spec/tag binding lane.
    try:
        require_identical_successor(
            {
                "x": {
                    "verdict_before": "NUMBERING-ONLY",
                    "classes": ["callee-index"],
                    "token_pairs": [{"old": "@func.1", "new": "@func.2"}],
                }
            }
        )
    except Refusal:
        pass
    else:
        raise AssertionError("successor binding inheritance accepted numbering drift")

    print("crystal fixture rebaseline selftest: PASS (5 fail-closed controls)")


def main() -> int:
    if sys.argv[1:] == ["--selftest"]:
        selftest()
        return 0

    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("dump", type=Path)
    ap.add_argument("--pre-report", type=Path, required=True)
    ap.add_argument("--bindings", type=Path, required=True)
    ap.add_argument("--trustc", type=Path, required=True)
    ap.add_argument("--driver", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--expect-clean-rev", required=True)
    ap.add_argument("--expect-kernel-sha256", required=True)
    ap.add_argument("--expect-bin-sha256", required=True)
    ap.add_argument("--expect-ir-sha256", required=True)
    ap.add_argument("--expect-coverage-sha256", required=True)
    ap.add_argument("--expect-pre-report-sha256", required=True)
    ap.add_argument("--expect-trustc-sha256", required=True)
    ap.add_argument("--expect-driver-sha256", required=True)
    ap.add_argument("--measured-utc", required=True)
    ap.add_argument(
        "--reason",
        required=True,
        help="reviewed explanation recorded verbatim in the append-only ledger",
    )
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    if not args.apply:
        refuse("fixture replacement requires the explicit --apply authorization")

    out = args.out if args.out.is_absolute() else REPO / args.out
    if out.parent != REPO / "data" or not out.name.startswith("crystal_fixture_rebaseline_"):
        refuse("output must be a new data/crystal_fixture_rebaseline_*.json path")
    if out.exists():
        refuse(f"append-only ledger already exists: {out}")
    record_rel = out.relative_to(REPO).as_posix()

    clean_rev = run("git", "rev-parse", "HEAD")
    exact("Clean revision", clean_rev, args.expect_clean_rev)
    if run("git", "status", "--porcelain", "--untracked-files=all", "--", str(KERNEL)):
        refuse("clean-kernel has tracked or untracked changes")
    kernel_sha = kernel_digest()
    exact("clean-kernel source digest", kernel_sha, args.expect_kernel_sha256)

    binary_path = args.dump / "clean_kernel.trust-ir.bin"
    ir_path = args.dump / "clean_kernel.trust-ir.txt"
    coverage_path = args.dump / "clean_kernel.coverage.json"
    axes_path = args.dump / "clean_kernel.axes.json"
    log_path = args.dump / "clean_kernel.build.log"
    argv_path = args.dump / "clean_kernel.argv"
    for path in (
        binary_path,
        ir_path,
        coverage_path,
        axes_path,
        log_path,
        argv_path,
        args.pre_report,
        args.bindings,
        args.trustc,
        args.driver,
    ):
        if not path.is_file():
            refuse(f"required input is missing: {path}")
    exact("live binary IR digest", sha256(binary_path), args.expect_bin_sha256)
    exact("live text IR digest", sha256(ir_path), args.expect_ir_sha256)
    exact("coverage digest", sha256(coverage_path), args.expect_coverage_sha256)
    exact("pre-report digest", sha256(args.pre_report), args.expect_pre_report_sha256)
    exact("trustc digest", sha256(args.trustc), args.expect_trustc_sha256)
    exact("driver digest", sha256(args.driver), args.expect_driver_sha256)

    try:
        report = json.loads(args.pre_report.read_text())
        manifest = json.loads(args.bindings.read_text())
        coverage = json.loads(coverage_path.read_text())
        axes = json.loads(axes_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        refuse(f"cannot read JSON input: {exc}")
    exact("freshness schema", str(report.get("schema")), "clean.crystal.fixture_freshness/v1")
    exact("binding schema", str(manifest.get("schema")), "clean.crystal.fixture_rebaseline_bindings/v1")
    exact("manifest source rev", str(manifest.get("clean_source_rev")), clean_rev)
    exact("manifest kernel digest", str(manifest.get("clean_kernel_src_sha256")), kernel_sha)
    exact("manifest binary IR digest", str(manifest.get("dump_bin_sha256")), args.expect_bin_sha256)
    exact("manifest IR digest", str(manifest.get("dump_ir_sha256")), args.expect_ir_sha256)
    exact("manifest pre-report digest", str(manifest.get("pre_report_sha256")), args.expect_pre_report_sha256)
    exact("axes schema", str(axes.get("schema_self")), "clean.trust_ir_build.measured.v1")

    bodies = validate_body_set(report.get("bodies"))
    if set(EVIDENCE) != set(BODIES) or len(set(EVIDENCE.values())) != len(EVIDENCE):
        refuse("lineage evidence mapping is not one-to-one with all primary chains")
    coverage_rows: dict[str, dict[str, Any]] = {}
    required_def_paths = set(BODIES.values())
    for row in coverage.get("bodies") or []:
        if not isinstance(row, dict):
            refuse("coverage bodies contains a non-object row")
        def_path = row.get("def_path")
        if not isinstance(def_path, str) or def_path not in required_def_paths:
            continue
        if def_path in coverage_rows:
            refuse(f"coverage contains duplicate def_path {def_path}")
        coverage_rows[def_path] = row
    missing_rows = sorted(set(BODIES.values()) - set(coverage_rows))
    if missing_rows:
        refuse(f"coverage is missing primary definitions: {missing_rows}")

    expected_evidence_paths = {FIXTURES / name for name in EVIDENCE.values()}
    existing_current_pins: dict[Path, object] = {}
    for path in FIXTURES.glob("*.json"):
        try:
            value = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            refuse(f"cannot audit current-source evidence pins in {path}: {exc}")
        if isinstance(value, dict) and "current_source_bound_pin" in value:
            existing_current_pins[path] = value["current_source_bound_pin"]
    prior_record_rel, prior_record = validate_existing_pin_set(
        existing_current_pins, expected_evidence_paths, record_rel, clean_rev
    )

    dump_text = ir_path.read_text(encoding="utf-8", errors="replace")
    plans: dict[str, dict[str, Any]] = {}
    for stem in {**BODIES, **EXTRA_BODIES}:
        fixture = FIXTURES / f"{stem}.trust-ir.txt"
        if not fixture.is_file():
            refuse(f"{stem}: fixture is missing: {fixture}")
        rel = fixture.relative_to(REPO).as_posix()
        before = git_text(clean_rev, rel)
        plans[stem] = plan_body(stem, bodies[stem], dump_text, before)
        worktree_text = fixture.read_text()
        if worktree_text not in (before, plans[stem]["live_text"]):
            refuse(f"{stem}: worktree fixture is neither the committed old pin nor exact live body")
    verify_required_bindings(plans, manifest, prior_record_rel, prior_record)

    trust_version = run(str(args.trustc), "-vV").splitlines()
    trust_rev = next(
        (line.split(":", 1)[1].strip() for line in trust_version if line.startswith("commit-hash:")),
        "",
    )
    if len(trust_rev) != 40:
        refuse("trustc -vV did not report a full commit hash")
    clean_tree = run("git", "rev-parse", f"{clean_rev}^{{tree}}")
    bindings_rel = args.bindings.resolve().relative_to(REPO).as_posix()
    evidence_plans: dict[str, dict[str, Any]] = {}
    evidence_ledger: dict[str, Any] = {}
    for stem, filename in EVIDENCE.items():
        path = FIXTURES / filename
        if path not in expected_evidence_paths or not path.is_file():
            refuse(f"{stem}: lineage evidence file is missing: {path}")
        try:
            worktree_value = json.loads(path.read_text())
            rel = path.relative_to(REPO).as_posix()
            old_text = git_text(clean_rev, rel)
            old_value = json.loads(old_text)
        except (OSError, json.JSONDecodeError) as exc:
            refuse(f"{stem}: cannot read lineage evidence {path}: {exc}")
        if not isinstance(worktree_value, dict) or not isinstance(old_value, dict):
            refuse(f"{stem}: lineage evidence is not an object")
        # Compare the immutable historical part independently from the nested
        # current generation.  On the first run HEAD has no nested pin.  On a
        # successor HEAD carries the authenticated predecessor generation, and
        # that generation is replaced only after validate_existing_pin_set has
        # joined every current file byte-for-byte to its append-only ledger.
        # A killed first run may instead have installed the new complete pin
        # set before exclusive ledger creation; that is the sole case in which
        # the worktree pin can differ from HEAD here.
        worktree_pin = worktree_value.pop("current_source_bound_pin", None)
        old_pin = old_value.pop("current_source_bound_pin", None)
        if worktree_value != old_value:
            refuse(f"{stem}: lineage evidence changed outside current_source_bound_pin")
        if prior_record_rel != record_rel and worktree_pin != old_pin:
            refuse(f"{stem}: committed predecessor pin and worktree pin disagree")
        if prior_record_rel is None and worktree_pin is not None:
            refuse(f"{stem}: an unledgered current-source pin appeared in the worktree")
        def_path = BODIES[stem]
        pin = current_evidence_pin(
            stem=stem,
            report_row=bodies[stem],
            coverage_row=coverage_rows[def_path],
            axes=axes,
            record_rel=record_rel,
            bindings_rel=bindings_rel,
            measured_utc=args.measured_utc,
            clean_rev=clean_rev,
            clean_tree=clean_tree,
            kernel_sha=kernel_sha,
            trust_rev=trust_rev,
            trustc_sha=sha256(args.trustc),
            driver_sha=sha256(args.driver),
            dump=args.dump,
            emitted_sha=plans[stem]["new_sha256"],
        )
        old_value["current_source_bound_pin"] = pin
        new_text = json.dumps(old_value, indent=1) + "\n"
        evidence_plans[stem] = {"path": path, "text": new_text}
        evidence_ledger[stem] = {
            "file": path.relative_to(REPO).as_posix(),
            "old_sha256": text_sha256(old_text),
            "new_sha256": text_sha256(new_text),
            "historical_top_level_lineage": old_value.get("lineage"),
            "current_lineage": pin["lineage"],
            "historical_top_level_def_index": old_value.get("def_index"),
            "current_def_index": pin["def_index"],
            "current_func_id": pin["func_id"],
            "current_flip_fired": pin["flip_event"]["fired"],
            "current_derived_mir": pin["derived_mir"],
        }

    # Prepare every replacement before the first rename.  Same-directory
    # os.replace gives each individual fixture an atomic transition; all
    # global preconditions and companion bindings were checked above.
    temps: list[tuple[Path, Path]] = []
    try:
        for stem, plan in plans.items():
            dst = FIXTURES / f"{stem}.trust-ir.txt"
            fd, name = tempfile.mkstemp(prefix=f".{stem}.", suffix=".tmp", dir=FIXTURES)
            with os.fdopen(fd, "w", encoding="utf-8") as tmp:
                tmp.write(plan["live_text"])
                tmp.flush()
                os.fsync(tmp.fileno())
            temps.append((Path(name), dst))
        for stem, plan in evidence_plans.items():
            dst = plan["path"]
            fd, name = tempfile.mkstemp(prefix=f".{stem}.evidence.", suffix=".tmp", dir=FIXTURES)
            with os.fdopen(fd, "w", encoding="utf-8") as tmp:
                tmp.write(plan["text"])
                tmp.flush()
                os.fsync(tmp.fileno())
            temps.append((Path(name), dst))
        for tmp, dst in temps:
            os.replace(tmp, dst)
        temps.clear()
    finally:
        for tmp, _dst in temps:
            tmp.unlink(missing_ok=True)

    ledger_plans: dict[str, Any] = {}
    for stem, plan in plans.items():
        ledger_plans[stem] = {k: v for k, v in plan.items() if k != "live_text"}
        exact(
            f"{stem} post-write identity",
            sha256(FIXTURES / f"{stem}.trust-ir.txt"),
            plan["new_sha256"],
        )
    current_pin_paths: set[Path] = set()
    for path in FIXTURES.glob("*.json"):
        value = json.loads(path.read_text())
        if isinstance(value, dict) and "current_source_bound_pin" in value:
            current_pin_paths.add(path)
    if current_pin_paths != expected_evidence_paths:
        refuse(
            "post-write current-source pins are not one-to-one with all primary chains: "
            f"missing={sorted(str(p.relative_to(REPO)) for p in expected_evidence_paths - current_pin_paths)}, "
            f"extra={sorted(str(p.relative_to(REPO)) for p in current_pin_paths - expected_evidence_paths)}"
        )
    for stem, plan in evidence_plans.items():
        exact(
            f"{stem} evidence post-write identity",
            sha256(plan["path"]),
            evidence_ledger[stem]["new_sha256"],
        )
    ledger = {
        "schema": "clean.crystal.fixture_rebaseline/v1",
        "measured_utc": args.measured_utc,
        "reason": args.reason,
        "supersedes_for_current_source_scope": (
            prior_record_rel if prior_record_rel != record_rel else None
        ),
        "provenance": {
            "clean_source_rev": clean_rev,
            "clean_source_tree": clean_tree,
            "clean_kernel_src_sha256": kernel_sha,
            "trust_worktree_rev": trust_rev,
            "trustc_sha256": sha256(args.trustc),
            "librustc_driver_sha256": sha256(args.driver),
            "dump_binary_sha256": sha256(binary_path),
            "dump_ir_sha256": sha256(ir_path),
            "coverage_sha256": sha256(coverage_path),
            "pre_report": args.pre_report.name,
            "pre_report_sha256": sha256(args.pre_report),
            "binding_manifest": args.bindings.name,
            "binding_manifest_sha256": sha256(args.bindings),
            "measurement_driver": "scripts/trust_ir_build.sh",
            "measurement_driver_sha256": sha256(REPO / "scripts" / "trust_ir_build.sh"),
        },
        "complete_body_set": sorted(plans),
        "primary_body_count": len(BODIES),
        "helper_body_count": len(EXTRA_BODIES),
        "bindings": manifest["bindings"],
        "fixtures": ledger_plans,
        "lineage_evidence": evidence_ledger,
        "postcondition": (
            "Every committed trust-ir fixture is byte-identical to its unique body in the "
            "exact live dump; crystal_fixture_freshness.py --strict must exit zero."
        ),
        "append_only": True,
        "generator": "scripts/crystal_fixture_rebaseline.py",
    }
    try:
        with out.open("x", encoding="utf-8") as dst:
            json.dump(ledger, dst, indent=1)
            dst.write("\n")
    except FileExistsError:
        refuse(f"append-only ledger already exists: {out}")
    print(
        f"rebaselined {len(BODIES)} primary fixtures + {len(EXTRA_BODIES)} helper; "
        f"append-only ledger: {out.relative_to(REPO)}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Refusal as exc:
        print(f"FIXTURE REBASELINE REFUSED: {exc}", file=sys.stderr)
        raise SystemExit(1)
