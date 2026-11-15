#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Derive "EvalIR semdiff coverage N/<census>" as a machine-read artifact.

The B-SEM program (docs/analysis/evalir-completion-plan-2026-08-24.md) steers by
one fraction: how many of the constructed-and-modelled `IRInst` constructors have
MEASURED three-executor agreement rows in the semdiff battery. Until now that
fraction lived in prose (CLAUDE.md, GAP2 §8, the anchors) and had to be
re-derived by eye from `data/crystal_gap2_semdiff_*.json`. This script makes it
a number a scoreboard can consume: it emits `data/evalir_coverage.json`
{schema, covered, count, total, provenance}.

Derivation rule — measured rows only, never authored ones:

  covered  = union of `coverage.exercised` over every committed
             `data/crystal_gap2_semdiff_*.json` (the gate-minted record of what
             the differential actually ran). Battery SOURCE
             (`tests/crystal_a3_semdiff.rs`, `src/ir_semdiff/`) is deliberately
             NOT a covered-set source: a Chain row that exists but was never
             minted into a dated artifact is authored, not measured, and
             counting it would round the fraction up — the exact move the
             artifact's own honesty note and the benchmark-freshness rule
             forbid. The plan's §5 ledger says it plainly: "the coverage
             fraction ... is the wave's headline number, quoted from the
             artifact only".

  total    = the pinned constructed-and-modelled `Inst` census, derived TWICE and required
             to agree: `EMITTED_INSTS` in
             `crates/clean-verify/tests/eval_ir/census.rs` and the `IRInst`
             inductive in
             `crates/clean-verify/src/spec/core_spec/eval_ir_syntax.rs`.
             Every artifact's own `irinst_constructors_total` must match, and
             every exercised name must be a census member.

Fail-closed: any schema drift in an artifact (missing coverage block, count
fields disagreeing with the list, arithmetic that does not add up, an exercised
name outside the census, duplicates), any parse failure of either denominator
source, or the two denominator derivations disagreeing, aborts with a nonzero
exit and writes NOTHING.

The output is deterministic (content-derived provenance: input sha256s, no
timestamps), so re-running on an unchanged tree is a no-op diff and the file
can be committed and diffed like any other pinned artifact.

Usage:
  python3 scripts/evalir_coverage.py               # derive + write data/evalir_coverage.json
  python3 scripts/evalir_coverage.py --check       # derive + fail if committed file differs
  python3 scripts/evalir_coverage.py --self-test   # mutation arms (planted extra/missing/... detected)
"""

from __future__ import annotations

import argparse
import copy
import glob
import hashlib
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ARTIFACT_GLOB = "data/crystal_gap2_semdiff_*.json"
CENSUS_PATH = "crates/clean-verify/tests/eval_ir/census.rs"
SYNTAX_PATH = "crates/clean-verify/src/spec/core_spec/eval_ir_syntax.rs"
OUTPUT_PATH = "data/evalir_coverage.json"
SCHEMA = "evalir-coverage/v1"


class CoverageError(Exception):
    """Fail-closed: any input we cannot fully account for aborts the run."""


# --------------------------------------------------------------- denominators


def parse_census_rs(text: str) -> list[str]:
    """The pinned EMITTED_INSTS array in census.rs, as a list of names."""
    m = re.search(
        r"EMITTED_INSTS\s*:\s*&\[&str\]\s*=\s*&\[(.*?)\];", text, re.DOTALL
    )
    if not m:
        raise CoverageError(f"{CENSUS_PATH}: EMITTED_INSTS array not found (schema drift)")
    names = re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"', m.group(1))
    if not names:
        raise CoverageError(f"{CENSUS_PATH}: EMITTED_INSTS parsed empty (schema drift)")
    if len(names) != len(set(names)):
        raise CoverageError(f"{CENSUS_PATH}: EMITTED_INSTS contains duplicates")
    return names


def parse_syntax_rs(text: str) -> list[str]:
    """Constructor names of the `IRInst` inductive in eval_ir_syntax.rs."""
    lines = text.splitlines()
    header = [i for i, ln in enumerate(lines) if "inductive IRInst : Type" in ln]
    if len(header) != 1:
        raise CoverageError(
            f"{SYNTAX_PATH}: expected exactly one `inductive IRInst : Type`, found {len(header)}"
        )
    names: list[str] = []
    for ln in lines[header[0] + 1 :]:
        m = re.match(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_]*)\s*:", ln)
        if not m:
            break
        names.append(m.group(1))
    if not names:
        raise CoverageError(f"{SYNTAX_PATH}: IRInst constructor list parsed empty (schema drift)")
    if len(names) != len(set(names)):
        raise CoverageError(f"{SYNTAX_PATH}: IRInst constructor list contains duplicates")
    return names


def derive_denominator(census_text: str, syntax_text: str) -> list[str]:
    """The constructed-Inst census, from two sources that must agree exactly."""
    census = parse_census_rs(census_text)
    syntax = parse_syntax_rs(syntax_text)
    if set(census) != set(syntax):
        only_c = sorted(set(census) - set(syntax))
        only_s = sorted(set(syntax) - set(census))
        raise CoverageError(
            "denominator sources DISAGREE: "
            f"only in {CENSUS_PATH}: {only_c}; only in {SYNTAX_PATH}: {only_s}"
        )
    return sorted(census)


# ------------------------------------------------------------------ artifacts


def validate_artifact(doc: dict, path: str, census: set[str]) -> list[str]:
    """Fail-closed schema + arithmetic + membership checks; returns exercised."""
    cov = doc.get("coverage")
    if not isinstance(cov, dict):
        raise CoverageError(f"{path}: no `coverage` object (schema drift)")
    for key, ty in (
        ("irinst_constructors_total", int),
        ("irinst_constructors_exercised", int),
        ("exercised", list),
        ("unmeasured", int),
    ):
        if not isinstance(cov.get(key), ty):
            raise CoverageError(f"{path}: coverage.{key} missing or not {ty.__name__} (schema drift)")
    exercised = cov["exercised"]
    if not all(isinstance(n, str) for n in exercised):
        raise CoverageError(f"{path}: coverage.exercised has non-string entries (schema drift)")
    if len(exercised) != len(set(exercised)):
        raise CoverageError(f"{path}: coverage.exercised contains duplicates")
    # The artifact's total is the census AT ITS OWN DATE, and the two facts a
    # mismatch can mean are NOT the same fact. Until 2026-09-10 both were one
    # error, which made adding a constructor to `IRInst` indistinguishable from
    # corrupting a dated record — and the only ways out of it were rewriting a
    # measurement's own denominator (falsifying history) or re-running a
    # battery that has an unbounded test in it.
    #
    #   artifact total  >  census   HARD ERROR. Either the census SHRANK under
    #                               a measurement, or the record is corrupt.
    #                               Both are inconsistencies, and neither has
    #                               an honest reading.
    #   artifact total  <  census   ALLOWED, and RECORDED. The census grew
    #                               after this artifact was minted. The
    #                               constructors added since are, by
    #                               construction, not in `exercised`, so they
    #                               land in `unmeasured` and the published
    #                               fraction goes DOWN. That is the correct
    #                               direction: a new constructor is unmeasured
    #                               until it is measured.
    #
    # The membership check below still runs against the CURRENT census, so a
    # name that has since been REMOVED is still a hard error.
    if cov["irinst_constructors_total"] > len(census):
        raise CoverageError(
            f"{path}: artifact total {cov['irinst_constructors_total']} EXCEEDS census "
            f"{len(census)} — a measurement cannot have covered more constructors than "
            f"exist; the census shrank under a dated record, or the record is corrupt"
        )
    if cov["irinst_constructors_exercised"] != len(exercised):
        raise CoverageError(
            f"{path}: exercised count field {cov['irinst_constructors_exercised']} "
            f"!= len(exercised) {len(exercised)}"
        )
    # Against the artifact's OWN total: this is the arithmetic the artifact
    # asserted about itself when it was minted, and it stays checkable forever.
    if cov["unmeasured"] != cov["irinst_constructors_total"] - len(exercised):
        raise CoverageError(
            f"{path}: unmeasured {cov['unmeasured']} != its own total - exercised "
            f"{cov['irinst_constructors_total'] - len(exercised)}"
        )
    alien = sorted(set(exercised) - census)
    if alien:
        raise CoverageError(f"{path}: exercised names not in the pinned census: {alien}")
    return list(exercised)


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


# --------------------------------------------------------------------- derive


def derive(root: str) -> dict:
    census_file = os.path.join(root, CENSUS_PATH)
    syntax_file = os.path.join(root, SYNTAX_PATH)
    for p in (census_file, syntax_file):
        if not os.path.isfile(p):
            raise CoverageError(f"denominator source missing: {p}")
    with open(census_file, encoding="utf-8") as f:
        census_text = f.read()
    with open(syntax_file, encoding="utf-8") as f:
        syntax_text = f.read()
    census = derive_denominator(census_text, syntax_text)

    artifact_paths = sorted(glob.glob(os.path.join(root, ARTIFACT_GLOB)))
    if not artifact_paths:
        raise CoverageError(f"no semdiff artifacts match {ARTIFACT_GLOB}: nothing is measured")

    covered: set[str] = set()
    artifacts_prov = []
    behind: list[str] = []
    for path in artifact_paths:
        rel = os.path.relpath(path, root)
        try:
            with open(path, encoding="utf-8") as f:
                doc = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            raise CoverageError(f"{rel}: unreadable ({e})") from e
        if not isinstance(doc, dict):
            raise CoverageError(f"{rel}: top level is not an object (schema drift)")
        exercised = validate_artifact(doc, rel, set(census))
        covered.update(exercised)
        artifact_total = doc["coverage"]["irinst_constructors_total"]
        entry = {"path": rel, "sha256": sha256_file(path), "exercised": sorted(exercised)}
        if artifact_total < len(census):
            entry["census_at_mint"] = artifact_total
            entry["behind_current_census_by"] = len(census) - artifact_total
            behind.append(entry["path"])
        artifacts_prov.append(entry)

    return {
        "schema": SCHEMA,
        "covered": sorted(covered),
        "count": len(covered),
        "total": len(census),
        "unmeasured": sorted(set(census) - covered),
        "artifacts_behind_the_current_census": behind,
        "provenance": {
            "derived_by": "scripts/evalir_coverage.py",
            "rule": (
                "covered = union of coverage.exercised over the artifacts below; "
                "measured rows only — authored-but-unminted battery rows never count. "
                "total = pinned constructed-Inst census, derived independently from "
                "both denominator sources, which must agree. An artifact minted "
                "against a SMALLER census is honoured at its own date and named in "
                "`artifacts_behind_the_current_census`: the constructors added since "
                "cannot appear in its `exercised` list, so they land in `unmeasured` "
                "and the fraction falls. An artifact claiming a LARGER census than "
                "exists is a hard error."
            ),
            "artifacts": artifacts_prov,
            "denominator_sources": {
                "census": {"path": CENSUS_PATH, "anchor": "EMITTED_INSTS"},
                "syntax": {"path": SYNTAX_PATH, "anchor": "inductive IRInst : Type"},
            },
        },
    }


def render(result: dict) -> str:
    return json.dumps(result, indent=2, sort_keys=False) + "\n"


# ------------------------------------------------------------------ self-test


def self_test(root: str) -> int:
    """Mutation arms: every planted defect must be DETECTED (raise), and the
    unmutated pipeline must succeed. Prints one line per arm."""
    failures = 0

    def arm(name: str, fn) -> None:
        nonlocal failures
        try:
            fn()
        except CoverageError as e:
            print(f"  self-test ARM ok: {name} -> detected ({e})")
            return
        print(f"  self-test ARM FAILED: {name} -> mutation NOT detected")
        failures += 1

    # Real inputs as the mutation substrate.
    with open(os.path.join(root, CENSUS_PATH), encoding="utf-8") as f:
        census_text = f.read()
    with open(os.path.join(root, SYNTAX_PATH), encoding="utf-8") as f:
        syntax_text = f.read()
    census = derive_denominator(census_text, syntax_text)
    artifact_paths = sorted(glob.glob(os.path.join(root, ARTIFACT_GLOB)))
    if not artifact_paths:
        print(f"self-test: no artifacts match {ARTIFACT_GLOB}", file=sys.stderr)
        return 1
    with open(artifact_paths[0], encoding="utf-8") as f:
        real_doc = json.load(f)

    def mutated(mutate):
        doc = copy.deepcopy(real_doc)
        mutate(doc)
        return doc

    # 1. Planted EXTRA constructor: internally consistent counts, alien name.
    def extra(doc):
        cov = doc["coverage"]
        cov["exercised"] = cov["exercised"] + ["planted_extra_ctor"]
        cov["irinst_constructors_exercised"] += 1
        cov["unmeasured"] -= 1

    arm("planted extra constructor in exercised", lambda: validate_artifact(mutated(extra), "<mut>", set(census)))

    # 2. The census SHRANK under a dated record: the artifact now claims more
    #    constructors than exist. This is the half of the old equality check
    #    that stays a hard error, and the arm has to shrink the census BELOW
    #    the artifact's own total to reach it — removing one name from a census
    #    that is already ahead of the artifact proves nothing.
    real_total = real_doc["coverage"]["irinst_constructors_total"]
    shrunk = set(census[: max(0, real_total - 1)])
    arm(
        f"census shrank below a dated artifact's total ({len(shrunk)} < {real_total})",
        lambda: validate_artifact(real_doc, "<mut>", shrunk),
    )

    # 2b. Same fact reached from the other side: an artifact that claims a
    #     LARGER census than exists.
    def inflate(doc):
        doc["coverage"]["irinst_constructors_total"] = len(census) + 1
        doc["coverage"]["unmeasured"] = (
            len(census) + 1 - doc["coverage"]["irinst_constructors_exercised"]
        )

    arm(
        "artifact total exceeds the current census",
        lambda: validate_artifact(mutated(inflate), "<mut>", set(census)),
    )

    # 2c. The direction that must NOT fail, asserted rather than assumed: a
    #     census that GREW since the artifact was minted is honoured at the
    #     artifact's own date. Without this arm the fix above could be
    #     "corrected" back into an equality check and every mutation arm would
    #     stay green.
    grown = set(census) | {"planted_new_constructor_since_the_mint"}
    try:
        got = validate_artifact(real_doc, "<mut>", grown)
        if sorted(got) != sorted(real_doc["coverage"]["exercised"]):
            print("  self-test ARM FAILED: grown census -> exercised list changed")
            failures += 1
        else:
            print("  self-test ARM ok: census grown since the mint -> honoured, "
                  f"exercised unchanged ({len(got)} names)")
    except CoverageError as e:
        print(f"  self-test ARM FAILED: census grown since the mint -> refused ({e})")
        failures += 1

    # 3. Denominator sources disagreeing (one census name deleted from census.rs only).
    arm(
        "denominator sources disagree",
        lambda: derive_denominator(census_text.replace(f'"{census[0]}",', "", 1), syntax_text),
    )

    # 4. Count field drifts from the list it summarizes.
    def count_drift(doc):
        doc["coverage"]["irinst_constructors_exercised"] += 1

    arm("exercised count field != len(exercised)", lambda: validate_artifact(mutated(count_drift), "<mut>", set(census)))

    # 5. Unmeasured arithmetic broken — now checked against the artifact's OWN
    #    total, so this stays a defect at any census.
    def unmeasured_drift(doc):
        doc["coverage"]["unmeasured"] -= 1

    arm("unmeasured != total - exercised", lambda: validate_artifact(mutated(unmeasured_drift), "<mut>", set(census)))

    # 6. Coverage block gone entirely (schema drift).
    def no_cov(doc):
        del doc["coverage"]

    arm("coverage block missing", lambda: validate_artifact(mutated(no_cov), "<mut>", set(census)))

    # 7. Duplicate exercised entry.
    def dup(doc):
        cov = doc["coverage"]
        cov["exercised"] = cov["exercised"] + [cov["exercised"][0]]
        cov["irinst_constructors_exercised"] += 1
        cov["unmeasured"] -= 1

    arm("duplicate exercised entry", lambda: validate_artifact(mutated(dup), "<mut>", set(census)))

    # Baseline: the unmutated pipeline must derive successfully.
    try:
        result = derive(root)
    except CoverageError as e:
        print(f"  self-test BASELINE FAILED: real derivation errored: {e}")
        return 1
    print(
        f"  self-test baseline ok: derived {result['count']}/{result['total']} "
        f"covered={result['covered']}"
    )
    if failures:
        print(f"self-test: {failures} arm(s) FAILED", file=sys.stderr)
        return 1
    print("self-test: all arms green")
    return 0


# ----------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if the committed output is stale")
    ap.add_argument("--self-test", action="store_true", help="run the mutation arms")
    args = ap.parse_args()

    if args.self_test:
        return self_test(REPO_ROOT)

    try:
        result = derive(REPO_ROOT)
    except CoverageError as e:
        print(f"evalir_coverage: FAIL-CLOSED: {e}", file=sys.stderr)
        return 1

    out_path = os.path.join(REPO_ROOT, OUTPUT_PATH)
    rendered = render(result)
    if args.check:
        try:
            with open(out_path, encoding="utf-8") as f:
                committed = f.read()
        except OSError:
            print(f"evalir_coverage: --check: {OUTPUT_PATH} missing; run without --check", file=sys.stderr)
            return 1
        if committed != rendered:
            print(f"evalir_coverage: --check: {OUTPUT_PATH} is STALE; regenerate", file=sys.stderr)
            return 1
        print(f"evalir_coverage: {OUTPUT_PATH} up to date: {result['count']}/{result['total']}")
        return 0

    with open(out_path, "w", encoding="utf-8") as f:
        f.write(rendered)
    print(
        f"evalir_coverage: wrote {OUTPUT_PATH}: {result['count']}/{result['total']} "
        f"covered={result['covered']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
