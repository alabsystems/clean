#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Failure-class classifier for Mathlib source-elaboration evidence.

WHY THIS EXISTS. The first source-elab evidence file
(`reports/source-elab/srcelab-2026-08-22-Logic-Basic-g17f4682e6.json`,
schema `clean-source-elab-evidence-v1`) carries a `failure_classes`
histogram, but the classifier that produced it was ad hoc and was never
committed, and the `report.errors` strings in that file are TRUNCATED to
400 characters while (per its own note) "counts and classes are computed
from the untruncated originals". Both facts together make that histogram
unreproducible from the committed artifact. This script is the fix: one
committed, ordered, first-match-wins rule set, and evidence files that
record the class of EVERY error alongside the (truncated) text, so a
reader can audit the histogram entry by entry without the 2.4 MB original.

The class VOCABULARY is exactly the nine names of the v1 file, so
histograms stay comparable across files; the RULES are new (they are the
first ones written down), so counts on the same input may differ from the
v1 file's. Print both; never silently merge them.

Usage:
  srcelab_classify.py --report <clean-check-report.json> [--json]
  srcelab_classify.py --stdout <captured-check-stdout>  [--json]
  srcelab_classify.py --self-test
"""

from __future__ import annotations

import argparse
import json
import re
import sys

# Ordered, first-match-wins. Each entry is (class, predicate).
#
# Rationale for the order, top to bottom:
#   1-2 front-end refusals: the declaration never reached the elaborator.
#   3   the kernel rejected a term for scoping, which is a Clean-side defect
#       class of its own (a leaked fvar is never the source file's fault).
#   4   the elaborator finished with metavariables still open.
#   5   name resolution — a missing/unresolved constant, not a type error.
#   6-7 mismatches, sort/universe FIRST so the U2 level-solver frontier is
#       not hidden inside the generic bucket. Both win over "tactic failed"
#       on purpose: `Tactic failed: type check failed: TypeMismatch {...}`
#       IS a type error, and burying it under the tactic that surfaced it
#       is what made the July taxonomy useless for prioritising.
#   8   whatever is left that a tactic reported (no-progress, no matching
#       hypothesis, instance synthesis, goal shape) — see `tactic_subclasses`.
#   9-10 two buckets carved out of "other" 2026-08-23, when the first
#       end-to-end measurement of Mathlib/Logic/Function/Basic.lean put 51 of
#       its 167 failures in "other": 28 `failed to synthesize instance` and 23
#       `Not implemented: cannot extract type name from ...`. A bucket holding
#       31% of the biggest file's failures is not a residual, it is two
#       unnamed frontiers. The v1 vocabulary is therefore a SUBSET of this one:
#       an error the v1 classifier called "other" may be one of these here.
#   11  everything else, enumerated verbatim in `other_messages`.

_SORT_EXPECTED = re.compile(r"expected:? +Sort\(")
_SORT_GOT = re.compile(r"(?:got|inferred):? +Sort\(")
_MISMATCH = re.compile(r"[Tt]ype mismatch|TypeMismatch")


def _is_sort_mismatch(e: str) -> bool:
    """Both sides of the mismatch are sorts -> a level/universe problem."""
    return bool(_SORT_EXPECTED.search(e) and _SORT_GOT.search(e))


RULES = [
    (
        "unsupported (descoped)",
        lambda e: "unsupported construct" in e or "unsupported tactic" in e,
    ),
    ("parse error", lambda e: "Parse error:" in e),
    (
        "kernel free-variable leak",
        lambda e: "contains free variables" in e or "Unknown free variable" in e,
    ),
    ("elaboration error", lambda e: "elaboration left unresolved" in e),
    ("unknown identifier", lambda e: "Unknown identifier:" in e),
    ("sort/universe mismatch", _is_sort_mismatch),
    ("type mismatch", lambda e: bool(_MISMATCH.search(e))),
    ("tactic failed", lambda e: "Tactic failed:" in e),
    # AFTER "tactic failed" on purpose: a `Tactic failed: could not synthesize
    # DecidableEq instance ...` stays attributed to the tactic that reported it
    # (and shows up in tactic_subclasses); only a bare elaborator-level failure
    # lands here.
    (
        "instance synthesis",
        lambda e: "failed to synthesize instance" in e
        or "cannot synthesize" in e
        or "could not synthesize" in e,
    ),
    ("not implemented (elaborator NYI)", lambda e: "Not implemented:" in e),
]

CLASSES = [name for name, _ in RULES] + ["other"]


def classify(error: str) -> str:
    for name, pred in RULES:
        if pred(error):
            return name
    return "other"


_DECL = re.compile(r"^(.*?): (.*)$", re.S)


def decl_of(error: str) -> str:
    m = _DECL.match(error)
    return m.group(1) if m else "?"


def message_of(error: str) -> str:
    m = _DECL.match(error)
    return m.group(2) if m else error


_TACTIC_SUB = re.compile(r"Tactic failed: ([^:\n]{1,60})")


def tactic_subclass(error: str) -> str:
    m = _TACTIC_SUB.search(error)
    return m.group(1).strip() if m else "?"


def summarize(errors: list[str]) -> dict:
    # `error` is TRUNCATED to 400 chars for the committed artifact (the
    # untruncated originals are kernel Expr dumps, megabytes per file);
    # the class is computed from the FULL string above it.
    per = [
        {"decl": decl_of(e), "class": classify(e), "error": e[:400]} for e in errors
    ]
    hist: dict[str, int] = {}
    for p in per:
        hist[p["class"]] = hist.get(p["class"], 0) + 1
    subs: dict[str, int] = {}
    for e, p in zip(errors, per):
        if p["class"] == "tactic failed":
            k = tactic_subclass(e)
            subs[k] = subs.get(k, 0) + 1
    return {
        "failure_classes": dict(sorted(hist.items(), key=lambda kv: (-kv[1], kv[0]))),
        "tactic_subclasses": dict(sorted(subs.items(), key=lambda kv: (-kv[1], kv[0]))),
        "per_error": per,
        "other_messages": [
            message_of(e)[:200] for e, p in zip(errors, per) if p["class"] == "other"
        ],
        "first_failure": (
            {
                "decl": per[0]["decl"],
                "class": per[0]["class"],
                "error": errors[0][:400],
            }
            if errors
            else None
        ),
    }


def _extract_report(text: str) -> dict:
    i = text.find("{")
    if i < 0:
        raise SystemExit("no JSON object in input")
    obj, _ = json.JSONDecoder().raw_decode(text[i:])
    # v1: the committed dated artifacts; v2 (2026-09-28) changed only the
    # meaning of `trust_summary.sorry_axioms`, which this classifier never
    # reads (cmd_core.rs `CHECK_REPORT_SCHEMA_VERSION`). The gate's own report
    # parser was taught v2 in the bump; this reader was not, so the gate
    # stopped at `failed:classify-error` on every v2 report.
    if obj.get("schema_version") in CHECK_REPORT_VERSIONS:
        return obj
    if obj.get("report", {}).get("schema_version") in CHECK_REPORT_VERSIONS:
        return obj["report"]
    raise SystemExit("input is not a Clean-check-report-v1/v2 (nor an evidence file)")


CHECK_REPORT_VERSIONS = ("Clean-check-report-v1", "Clean-check-report-v2")


def _self_test() -> int:
    cases = [
        ("parser recovery [parser.recovery]: unsupported construct `x` at line 1, column 2",
         "unsupported (descoped)"),
        ("[anonymous]: Parse error: parser recovery produced raw declaration: RAngle",
         "parse error"),
        ("f: Kernel registration failed during add_decl Theorem: Declaration f contains free variables (fvar ids [1])",
         "kernel free-variable leak"),
        ("[anonymous]: Kernel check failed for [anonymous]: Unknown free variable: FVarId(9)",
         "kernel free-variable leak"),
        ("[anonymous]: theorem f: elaboration left unresolved variables (unsolved metavariables ?[1])",
         "elaboration error"),
        ("g: Unknown identifier: not_xor; nearest theorem names: Bool.not_xor",
         "unknown identifier"),
        ("h: Kernel check failed for h: Type mismatch: expected Sort(Param(u_3)), got Sort(Param(u_2))",
         "sort/universe mismatch"),
        ("i: Tactic failed: type check failed: TypeMismatch { expected: Sort(Succ(Param(u_2))), inferred: Sort(Succ(Param(u_0))) }",
         "sort/universe mismatch"),
        ("j: Type mismatch: expected Not fvar#FVarId(0), got Iff (Not x)",
         "type mismatch"),
        ("k: Tactic failed: type mismatch: expected Prop, got FVar(FVarId(1))",
         "type mismatch"),
        ("l: Tactic failed: simp: no progress made", "tactic failed"),
        ("m: Cannot infer type", "other"),
        ("n: Not implemented: cannot extract type name from opaque type variable FVar(FVarId(1))",
         "not implemented (elaborator NYI)"),
        ("o: failed to synthesize instance `(x : α) → Decidable (p x)`",
         "instance synthesis"),
        ("p: Tactic failed: could not synthesize DecidableEq instance for App(Const(Nat))",
         "tactic failed"),
    ]
    bad = 0
    for text, want in cases:
        got = classify(text)
        if got != want:
            print(f"FAIL: {text[:60]!r}\n  want {want!r} got {got!r}", file=sys.stderr)
            bad += 1
    # tactic subclass extraction
    if tactic_subclass("l: Tactic failed: simp: no progress made") != "simp":
        print("FAIL: tactic_subclass", file=sys.stderr)
        bad += 1
    # every rule name is in CLASSES exactly once, "other" last
    if len(set(CLASSES)) != len(CLASSES) or CLASSES[-1] != "other":
        print("FAIL: CLASSES malformed", file=sys.stderr)
        bad += 1
    # the report reader accepts v1 and v2, bare or inside an evidence file,
    # and refuses any other version
    for version in ("Clean-check-report-v1", "Clean-check-report-v2"):
        for wrap in (lambda r: r, lambda r: {"report": r}):
            text = "noise\n" + json.dumps(wrap({"schema_version": version, "success_count": 1}))
            if _extract_report(text).get("success_count") != 1:
                print(f"FAIL: {version} report not read", file=sys.stderr)
                bad += 1
    try:
        _extract_report(json.dumps({"schema_version": "Clean-check-report-v9"}))
        print("FAIL: a v9 report was read", file=sys.stderr)
        bad += 1
    except SystemExit:
        pass
    print(f"srcelab_classify self-test: {len(cases) + 7 - bad}/{len(cases) + 7} pass")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--report", help="a Clean-check-report-v1 JSON file")
    ap.add_argument("--stdout", help="captured `clean check --json` stdout")
    ap.add_argument("--json", action="store_true", help="emit the summary as JSON")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return _self_test()
    src = args.report or args.stdout
    if not src:
        ap.error("one of --report / --stdout / --self-test is required")
    with open(src, encoding="utf-8", errors="replace") as f:
        report = _extract_report(f.read())
    # BOTH arrays, and this is not optional. `Clean-check-report-v1` used to
    # carry parser recovery notes inside `errors`; they now live in their own
    # `parser_recovery` array, because counting them as declaration failures made
    # `clean check` print `Checked 207 declarations` / `69 passed, 146 failed`.
    # The classifier's `parser_recovery` CLASS is unchanged and its histogram
    # must stay comparable across files minted either side of that split, so it
    # reads both. `.get` with a default keeps older artifacts working.
    out = summarize(list(report.get("errors", [])) + list(report.get("parser_recovery", [])))
    out["decl_count"] = report.get("decl_count", 0)
    out["success_count"] = report.get("success_count", 0)
    out["failed_count"] = report.get("failed_count", 0)
    if args.json:
        json.dump(out, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
        return 0
    print(f"decl_count={out['decl_count']} success={out['success_count']} failed={out['failed_count']}")
    print("failure_classes:")
    for k, v in out["failure_classes"].items():
        print(f"  {v:4d}  {k}")
    if out["tactic_subclasses"]:
        print("tactic_subclasses:")
        for k, v in out["tactic_subclasses"].items():
            print(f"  {v:4d}  {k}")
    if out["first_failure"]:
        print(f"first_failure: [{out['first_failure']['class']}] {out['first_failure']['error'][:300]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
