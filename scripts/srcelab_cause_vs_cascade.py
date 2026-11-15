#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Separate CAUSE from CASCADE in a SRCELAB residual, and rank causes.

Read-only. Consumes a committed `reports/source-elab/srcelab-*.json` plus the
Mathlib checkout it was measured against, and emits a JSON census. It runs no
build, spawns no `clean`, and enforces nothing -- it is a producer, not a gate.

WHY THIS EXISTS
---------------
~31% of the residual failures in the pinned five-file slice are "unknown
identifier", and most of those are downstream: the declaration fails only
because an EARLIER declaration in the same file never registered, so its name is
genuinely absent later. Fixing such a failure fixes nothing; fixing its cause
fixes several. Ranking by raw class size therefore ranks the symptom.

RULE R (applied mechanically; every clause is mutation-checked -- see --mutate)
------------------------------------------------------------------------------
  A failure D at source line L(D) in file F is a CASCADE iff
    some identifier X that D's error reports absent RESOLVES, under Lean name
    resolution restricted to F, to a declaration F defines at line L(E) < L(D),
    and F's failure set contains L(E).
  Otherwise D is a CAUSE.

WHAT THIS CENSUS CANNOT KNOW -- read before budgeting off any number here
------------------------------------------------------------------------
Rule R is a statement about ONE error string. `clean check` abandons a
declaration at its first error, so the input artifact carries exactly one
elaboration error per declaration and NO SECOND ERROR IS OBSERVABLE. (Measured
on the 2026-08-30 slice: 436 error rows over 428 distinct declarations, and all
8 excess rows are parser-recovery events mis-anchored onto a neighbouring
declaration -- never a second elaboration error for the same one.)

Therefore a CASCADE row means only "this declaration's first error names an
earlier failure". It does NOT mean the declaration succeeds once that failure is
fixed: whatever error the masked remainder of the declaration would have
reported is invisible until the cause is actually removed.

`recoveries_upper_bound` (and the `first_error_dependents_*` counts it is
derived from) are therefore UPPER BOUNDS on declarations recovered, never
estimates of them. `FIRST_ERROR_MASKING` below records what the ratio measured
when the removal was actually performed; the artifact carries it too, so the
caveat travels with the data instead of living in a caption.

Three points where the obvious shortcut is wrong, and is not taken:

1. Failure rows are keyed to source declarations BY LINE, never by name.
   This was FORCED by a defect, and it OUTLIVES the fix. When this census was
   first cut, Clean's own fully-qualified names were wrong in
   `Mathlib/Order/Basic.lean`: `end A.B` popped one namespace component instead
   of two, so declarations after the first dotted `end` carried a leaked prefix
   (`Mathlib.Tactic.LE.LE.LT.` ...) and name-keyed matching silently missed
   every cascade in that file.

   That defect is FIXED (`NamespaceState::exit_namespace` now restores the
   prefix its matching `enter_namespace` saw, so `end Alpha.Beta` closes both
   components, as Lean 4.30.0-rc2 does). DO NOT switch this producer to
   name-keying on the strength of it. Line-keying is independently required:
   `_root_.` declarations, anonymous instances (keyed `\\x00anon@<line>` below,
   deliberately unresolvable) and same-name declarations repeated across
   sections all collide under a name key, and a future name-computation defect
   would silently reintroduce exactly the miss above rather than erroring.
   Keying by line makes this census insensitive to how Clean names things at
   all -- which is the property that let the namespace-pop defect be FOUND
   here instead of being absorbed by it.

2. `Unknown identifier: X; dot notation `.f` on a receiver of type `T`` reports
   the FIELD, not the constant. The constant sought is `head(T).f`, and where
   `T` prints as a type FORMER (`Prop -> Type`) the receiver was itself a
   namespace-qualified constant, whose qualifier is recovered from the source.

3. The source is scanned with block comments blanked. `inductive types. -/`
   sits at column 0 inside a docstring at Logic/Function/Basic.lean:620 and the
   raw scan indexes it as a declaration named `Function.types.`.

USAGE
    python3 scripts/srcelab_cause_vs_cascade.py [REPORT.json] [-o OUT.json]
    python3 scripts/srcelab_cause_vs_cascade.py --mutate      # rule sensitivity
    python3 scripts/srcelab_cause_vs_cascade.py --self-test   # 5 arms, ~2 s

  Measuring the masked remainder (the only mode that writes outside -o):

    # 1. ARM A: `clean check` the five pinned files unmodified -> ARM_A.json
    # 2. write the stubbed sources into a COPY of the Mathlib checkout
    python3 scripts/srcelab_cause_vs_cascade.py ARM_A.json --write-stub-tree DIR
    # 3. validate DIR with an oracle that is not Clean, before spending 20 min:
    #      LEAN_PATH=... lean --root=DIR Mathlib/Logic/Basic.lean   (x5)
    #    every file must report ZERO non-`sorry` diagnostics
    # 4. ARM B: `clean check` the same five files inside DIR -> ARM_B.json
    python3 scripts/srcelab_cause_vs_cascade.py ARM_A.json --masking ARM_B.json \\
        [--masking-tree DIR] -o masking.json

    CLEAN_MATHLIB_DIR   Mathlib checkout (default: the $HOME/mathlib4-*
                        convention used by scripts/source_elab_gate.sh)
"""
from __future__ import annotations

import argparse
import collections
import glob
import json
import os
import re
import sys
import tempfile

IDENT = r"[A-Za-z_À-ɏͰ-Ͽ][A-Za-z0-9_.'!?À-ɏͰ-Ͽ₀-ₜ⁰-ⁿ]*"
DECL_KW = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
           "inductive", "opaque", "axiom")
MODS = (r"(?:@\[[^\]]*\]\s*)*"
        r"(?:protected\s+|private\s+|scoped\s+|local\s+|nonrec\s+|noncomputable\s+"
        r"|partial\s+|unsafe\s+)*")
DECL_RE = re.compile(r"^" + MODS + r"(" + "|".join(DECL_KW) + r")\b[ \t]*(" + IDENT + r")?")
ALIAS_RE = re.compile(r"^" + MODS + r"alias\b[ \t]+(" + IDENT + r")[ \t]*:=")
NS_RE = re.compile(r"^namespace\s+(" + IDENT + r")")
END_RE = re.compile(r"^end\b[ \t]*(" + IDENT + r")?\s*$")

UNK_ATTR = re.compile(r"Unknown identifier: attribute target '([^']+)' not found in environment")
UNK_CONST = re.compile(r"Unknown constant: (" + IDENT + r")")
UNK = re.compile(r"Unknown identifier: ([^;\n]+?)(?:;|$)")
DOT = re.compile(r"dot notation `\.([^`]+)` on a receiver of type `([^`]*)`")
AT_LINE = re.compile(r"at line (\d+)")

APPROX_SHAPES = {"dot-notation:bare-field"}

# Measured masking evidence, carried INTO the artifact so the caveat travels
# with the data. Each observation is a case where a cause was actually removed
# (or faithfully neutralised) and the dependents were re-measured, so the gap
# between the upper bound and the yield is a number, not an argument.
FIRST_ERROR_MASKING = {
    "statement":
        "A CASCADE row means the declaration's FIRST error names an earlier "
        "failure. `clean check` abandons a declaration at its first error, so "
        "the masked remainder is unobservable until the cause is removed. "
        "`recoveries_upper_bound` is an UPPER BOUND on declarations recovered, "
        "never an estimate of one.",
    "why_no_second_error_is_observable":
        "The input artifact carries one elaboration error per declaration. On "
        "the 2026-08-30 slice: 436 error rows over 428 distinct declarations, "
        "and all 8 excess rows are parser-recovery events mis-anchored onto a "
        "neighbouring declaration -- never a second error for the same one.",
    "evidence": "reports/source-elab/first-error-masking-2026-08-31.json",
    "observations": [
        {
            "kind": "stub sweep",
            "what": "Every stubbable CAUSE proof in the five pinned files replaced "
                    "by `sorry` at one frozen binary (sha256 7b850ab0f965e8b5), "
                    "then re-checked. See --write-stub-tree / --masking.",
            "date": "2026-08-31",
            "first_error_dependents": 110,
            "measurable": 66,
            "recovered": 26,
            "surfaced_a_different_error": 40,
            "of_those_still_a_cascade": 2,
            "not_measurable": 44,
            "rate": "26/66 = 0.39",
        },
        {
            "kind": "stub sweep, restricted to the queue's top 15 causes",
            "what": "docs/plans/BRICK_QUEUE_2026-08-31-C.md rows 1-15.",
            "date": "2026-08-31",
            "first_error_dependents": 53,
            "measurable": 25,
            "recovered": 6,
            "rate": "6/25 = 0.24",
        },
        {
            "kind": "real fix",
            "what": "Order/Basic:964 `DenselyOrdered` -- structure/class field "
                    "elaboration gained the declaration's own local instances "
                    "(27474fd8d); write-up 512ad431e.",
            "date": "2026-08-31",
            "first_error_dependents": 10,
            "recovered": 3,
            "note": "All 10 stopped reporting the stated error; 7 reported a "
                    "genuinely different one, and 2 of those then cascaded off a "
                    "NEW cause that had no census row -- i.e. a two-hop chain the "
                    "first-error census could not represent.",
        },
        {
            "kind": "real fix",
            "what": "Unique.lean:141 `Unique.mk'` -- a structure literal's "
                    "`with`-source stopped deciding the structure (b47150c84, "
                    "614210a5f). `Unique.mk'` now PASSES.",
            "date": "2026-08-31",
            "first_error_dependents": 2,
            "recovered": 0,
            "note": "Unique.lean:208 `Function.Injective.unique` moved to a kernel "
                    "free-variable leak and Unique.lean:253 to `Unknown "
                    "identifier: subsingleton_iff_isEmpty`. Upper bound 2, yield 0.",
        },
    ],
}


def default_mathlib() -> str:
    env = os.environ.get("CLEAN_MATHLIB_DIR")
    if env:
        return env
    # $HOME, not a literal home -- see scripts/source_elab_gate.sh, which
    # carried the identical defect: a hardcoded `$HOME` glob cannot
    # match on any other machine, so discovery failed for a reason unrelated
    # to whether a corpus exists.
    for cand in ["data/raw/mathlib4"] + sorted(
        glob.glob(os.path.join(os.path.expanduser("~"), "mathlib4-*"))
    ):
        if os.path.isdir(os.path.join(cand, ".lake", "build", "lib", "lean")):
            return cand
    raise SystemExit("no Mathlib checkout; set CLEAN_MATHLIB_DIR")


def blank_comments(lines: list[str]) -> list[str]:
    """Blank Lean block comments and line comments, preserving line numbering."""
    out, depth = [], 0
    for src in lines:
        res, i = [], 0
        while i < len(src):
            if src.startswith("/-", i):
                depth += 1
                res.append("  ")
                i += 2
            elif depth > 0 and src.startswith("-/", i):
                depth -= 1
                res.append("  ")
                i += 2
            elif depth == 0 and src.startswith("--", i):
                break
            else:
                res.append(" " if depth else src[i])
                i += 1
        out.append("".join(res).rstrip())
    return out


def norm_decl(name: str) -> str:
    name = name.strip()
    i = name.find("_root_.")
    return name[i + 7:] if i != -1 else name


def index_source(path: str, raw_lines: bool = False):
    """-> (lines, {line: full Lean name}, {line: open-namespace tuple}, {name: [lines]})"""
    text = open(path, encoding="utf-8").read().split("\n")
    lines = text if raw_lines else blank_comments(text)
    ns: list[str] = []
    stack: list[tuple[str, int]] = []
    by_line: dict[int, str] = {}
    ns_at: dict[int, tuple[str, ...]] = {}
    for i, ln in enumerate(lines, 1):
        ns_at[i] = tuple(ns)
        m = NS_RE.match(ln)
        if m:
            comps = m.group(1).split(".")
            ns.extend(comps)
            stack.append(("ns", len(comps)))
            continue
        if re.match(r"^section\b", ln):
            stack.append(("sec", 0))
            continue
        if END_RE.match(ln):
            if stack:
                _, n = stack.pop()
                for _ in range(n):
                    if ns:
                        ns.pop()
            continue
        m = ALIAS_RE.match(ln)
        if m:
            nm = m.group(1)
            by_line[i] = nm[7:] if nm.startswith("_root_.") else \
                (".".join(list(ns) + [nm]) if ns else nm)
            continue
        m = DECL_RE.match(ln)
        if m:
            nm = m.group(2)
            if nm is None:
                by_line[i] = "\x00anon@%d" % i     # anchorable, never resolvable
            elif nm.startswith("_root_."):
                by_line[i] = nm[7:]
            else:
                by_line[i] = ".".join(list(ns) + [nm]) if ns else nm
    name_to_lines: dict[str, list[int]] = collections.defaultdict(list)
    for line, nm in by_line.items():
        name_to_lines[nm].append(line)
    return lines, by_line, ns_at, name_to_lines


def receiver_head(ty: str):
    """Head constant of a printed receiver type, or None when it is a type former."""
    ty = ty.strip()
    if ty.startswith(("(", "Sort", "Prop", "Type")) or "->" in ty:
        return None
    m = re.match(r"^(" + IDENT + r")\b", ty)
    if not m or m.group(1).startswith("fvar#"):
        return None
    return m.group(1)


def missing_ids(err: str, body: str) -> list[tuple[str, str]]:
    """Every identifier the error reports absent, tagged with the shape that reported it."""
    out: list[tuple[str, str]] = []
    m = UNK_ATTR.search(err)
    if m:
        return [(m.group(1), "attribute-target")]
    for m in UNK_CONST.finditer(err):
        out.append((m.group(1), "unknown-constant"))
    dots = DOT.findall(err)
    for field, recv in dots:
        head = receiver_head(recv)
        if head:
            out.append((head + "." + field, "dot-notation:receiver-head"))
        for qual in re.findall(r"(" + IDENT + r")\." + re.escape(field) + r"\b", body):
            if not qual.startswith("fvar"):
                out.append((qual + "." + field, "dot-notation:source-qualifier"))
        out.append((field, "dot-notation:bare-field"))
    if not dots:
        for p in UNK.findall(err):
            out.append((p.strip(),
                        "auto-bound-implicit" if "auto-bound implicit" in err else "plain-absence"))
    seen, ded = set(), []
    for item in out:
        if item not in seen:
            seen.add(item)
            ded.append(item)
    return ded


def classify(report_path: str, mathlib: str, *, no_order=False, no_failed=False,
             no_ns=False, raw_lines=False):
    rep = json.load(open(report_path))
    files = []
    for f in rep["files"]:
        key = f["key"]
        lines, by_line, ns_at, name_to_lines = index_source(
            os.path.join(mathlib, key), raw_lines=raw_lines)
        decl_lines = sorted(by_line)
        rows = []
        for e in f["per_error_class"]:
            m = AT_LINE.search(e["error"])
            rows.append({
                "file": key,
                "line": int(m.group(1)) if m else None,
                "decl_clean": norm_decl(e["decl"]),
                "class": e["class"],
                "error": e["error"],
                "parser_recovery": e["decl"].startswith("parser recovery"),
            })
        rows.sort(key=lambda r: (r["line"] or 10 ** 9))
        for r in rows:
            r["anchor_line"] = None
            r["decl_source"] = None
            if r["line"]:
                before = [d for d in decl_lines if d <= r["line"]]
                if before and r["line"] - before[-1] <= 12:
                    r["anchor_line"] = before[-1]
                    r["decl_source"] = by_line[before[-1]]
            start = r["anchor_line"] or r["line"]
            if start:
                stop = min(next((d for d in decl_lines if d > start), len(lines) + 1),
                           start + 45)
                r["body"] = "\n".join(lines[start - 1:stop - 1])
            else:
                r["body"] = ""

        fail_lines = {r["anchor_line"] for r in rows if r["anchor_line"]}

        def resolve(x: str, at_line: int):
            opens = ns_at.get(at_line, ())
            cands = [x]
            parts = x.split(".")
            for k in range(len(parts) - 1, 0, -1):
                cands.append(".".join(parts[:k]))
            for cand in cands:
                hits = []
                depths = [0] if no_ns else list(range(len(opens), -1, -1))
                for j in depths:
                    q = ".".join(list(opens[:j]) + [cand]) if j else cand
                    hits.extend((q, dl) for dl in name_to_lines.get(q, []))
                if hits:
                    return hits          # closest enclosing scope wins, as in Lean
            return []

        for r in rows:
            r["missing"] = missing_ids(r["error"], r["body"])
            deps, deps_noapprox = [], []
            for ident, shape in r["missing"]:
                for name, dl in resolve(ident, r["line"] or 1):
                    order_ok = (dl < r["line"]) if not no_order else (dl != r["anchor_line"])
                    failed_ok = (dl in fail_lines) if not no_failed else True
                    if r["line"] and order_ok and failed_ok:
                        rec = {"missing": ident, "shape": shape,
                               "dep_name": name, "dep_line": dl}
                        deps.append(rec)
                        if shape not in APPROX_SHAPES:
                            deps_noapprox.append(rec)
            r["deps"] = deps
            r["deps_noapprox"] = deps_noapprox
            r.pop("body")
        files.append({"key": key, "rows": rows})
    return rep, files


def rank(files):
    """Rank causes by the UPPER BOUND on recoveries. -> (stats, nodes, cascade, cause)

    Every count here is over declarations whose FIRST reported error names this
    cause. That is a necessary condition for their recovery and not a sufficient
    one -- see "WHAT THIS CENSUS CANNOT KNOW" at the top of this file. The
    fields are named for what they count, and `recoveries_upper_bound` is named
    for what a planner would otherwise misread the exclusive count as.
    """
    nodes: dict[tuple, dict] = {}
    for f in files:
        for r in f["rows"]:
            if r["line"] is None or r["parser_recovery"]:
                continue
            nodes.setdefault((r["file"], r["anchor_line"] or r["line"]), r)
    succ = collections.defaultdict(set)
    pred = collections.defaultdict(set)
    for key, r in nodes.items():
        for dep in r["deps"]:
            e = (r["file"], dep["dep_line"])
            if e in nodes and e != key:
                succ[key].add(e)
                pred[e].add(key)
    cascade = {k for k in nodes if succ[k]}
    cause = set(nodes) - cascade

    anc: dict[tuple, set] = {}

    def ancestors(k, seen=frozenset()):
        if k in anc:
            return anc[k]
        if k in seen:
            return set()
        seen = seen | {k}
        out = set()
        for e in succ[k]:
            out |= {e} if e in cause else ancestors(e, seen)
        if not succ[k]:
            out.add(k)
        anc[k] = out
        return out

    for k in cascade:
        ancestors(k)

    def descendants(k):
        out, stack = set(), [k]
        while stack:
            for p in pred[stack.pop()]:
                if p not in out:
                    out.add(p)
                    stack.append(p)
        return out

    stats = []
    for c in cause:
        if not pred[c]:
            continue
        trans = descendants(c)
        excl = {k for k in trans if anc.get(k, set()) == {c}}
        r = nodes[c]
        name = lambda k: nodes[k]["decl_source"] or nodes[k]["decl_clean"]  # noqa: E731
        stats.append({
            "file": r["file"], "line": r["anchor_line"] or r["line"],
            "decl_source": r["decl_source"], "decl_clean": r["decl_clean"],
            "class": r["class"], "error": r["error"],
            # The planning column, named for its semantics. Numerically equal to
            # first_error_dependents_exclusive; kept separate because that is the
            # number a queue reads, and it must not be readable as a yield.
            "recoveries_upper_bound": len(excl),
            "first_error_dependents_direct": len(pred[c]),
            "first_error_dependents_exclusive": len(excl),
            "first_error_dependents_transitive": len(trans),
            "first_error_dependent_names_exclusive": sorted(name(k) for k in excl),
            "first_error_dependent_names_transitive": sorted(name(k) for k in trans),
        })
    stats.sort(key=lambda s: (-s["first_error_dependents_exclusive"],
                              -s["first_error_dependents_transitive"],
                              -s["first_error_dependents_direct"],
                              s["file"], s["line"]))
    return stats, nodes, cascade, cause


# ---------------------------------------------------------------------------
# Measuring the masked remainder: neutralise causes, re-check, count recoveries.
#
# The only faithful cheap neutralisation is `sorry` on a PROOF, and it is
# faithful only because a proof is opaque to its consumers: the declaration
# still registers with exactly the statement the source wrote, so a dependent
# that names it, rewrites with it, or feeds it to `simp` sees no difference.
#
# It is NOT faithful for a `def` / `abbrev` / `instance` / `class`, and that is
# measured, not assumed -- `def twice (n : Nat) : Nat := sorry` turns
# `theorem twice_zero : twice 0 = 0 := rfl` from a pass into
# `Type mismatch: ... sorryAx Nat Bool.false = sorryAx Nat Bool.false`, i.e. the
# stub INVENTS a failure the real definition would not have. So the sweep stubs
# theorem/lemma causes only, and every cascade with a non-stubbable ancestor is
# reported as NOT MEASURED rather than folded in.
# ---------------------------------------------------------------------------

STUBBABLE_KW = ("theorem", "lemma")
KW_RE = re.compile(r"^" + MODS + r"(" + "|".join(DECL_KW) + r"|alias)\b")
BR_OPEN, BR_CLOSE = "([{⟨⦃", ")]}⟩⦄"


def decl_keyword(blanked: list[str], line: int) -> str:
    if line is None or not (1 <= line <= len(blanked)):
        return "?"
    m = KW_RE.match(blanked[line - 1])
    return m.group(1) if m else "(no-keyword)"


def decl_extent(blanked: list[str], start: int, raw: list[str] | None = None) -> int:
    """Last line (1-based, inclusive) of the declaration beginning at `start`.

    A body must be indented, so the extent ends at the next column-0 command.
    A column-0 DOCSTRING also ends it: `blank_comments` leaves that line blank,
    and without the raw check the extent runs straight through `/-- ... -/` and
    the stub deletes the doc comment of the FOLLOWING declaration. Continuation
    lines inside a block comment are blank-after-blanking and are not openers,
    so they correctly do not end anything.
    """
    for i in range(start, len(blanked)):
        s = blanked[i]
        if s.strip() and not s[0].isspace():
            return i
        if raw is not None:
            r = raw[i]
            if r[:2] in ("/-", "--"):
                return i
    return len(blanked)


WHERE_RE = re.compile(r"(?<![A-Za-z0-9_.'])where(?![A-Za-z0-9_.'])")


def body_separator(blanked: list[str], start: int, end: int):
    """(0-based line, column) of the depth-0 `:=` in [start, end], else None.

    Binder defaults `(x : a := d)` and structure instances `{ f := v }` sit at
    bracket depth > 0, so for a `theorem` / `lemma` the depth-0 `:=` is the
    separator between the statement and the proof -- UNLESS a depth-0 `where`
    or `|` comes first, in which case there is no declaration-level `:=` at all
    and the one further on belongs to something inside the body.

    Both refusals are here because the pinned Lean 4.30.0-rc2 rejected the stub
    tree that lacked them, and neither the line-count guard nor the doc-comment
    guard could see either:

      `where`  `Logic/Function/Basic.lean:675 Pi.map_injective` is
               `... : A <-> B where / mp ... := ... / mpr := ...`; taking the
               field's `:=` deleted the rest -> `error: Fields missing: mpr`.
      `|`      `Order/Basic.lean:339 exists_forall_ge_and` is equation-style
               (`| <pat>, <pat> => ...`) and its arm opens `let <p> := ...`;
               taking THAT `:=` left a dangling `let <p> := sorry` ->
               `error: unexpected token '@['; expected term`.
    """
    depth = blk = 0
    for i in range(start - 1, min(end, len(blanked))):
        s, j, in_str = blanked[i], 0, False
        while j < len(s):
            c = s[j]
            if in_str:
                if c == "\\":
                    j += 2
                    continue
                in_str = c != '"'
                j += 1
                continue
            if s.startswith("/-", j):
                blk += 1
                j += 2
                continue
            if blk:
                if s.startswith("-/", j):
                    blk -= 1
                    j += 2
                    continue
                j += 1
                continue
            if s.startswith("--", j):
                break
            if c == '"':
                in_str = True
            elif c in BR_OPEN:
                depth += 1
            elif c in BR_CLOSE:
                depth -= 1
            elif depth == 0 and s.startswith(":=", j):
                return (i, j)
            elif depth == 0 and (c == "|" or WHERE_RE.match(s, j)):
                return None
            j += 1
    return None


def stub_plan(files, nodes, cause, mathlib):
    """-> ({file: {line: verdict}}, {file: (blanked, raw)}), verdict in
    {"stub", "skip:<kind>"}. `cause` keys are (file, line)."""
    plan: dict[str, dict[int, str]] = collections.defaultdict(dict)
    src: dict[str, tuple] = {}
    for f in files:
        key = f["key"]
        path = os.path.join(mathlib, key)
        src[key] = (index_source(path)[0],
                    open(path, encoding="utf-8").read().split("\n"))
    for (key, line) in sorted(cause):
        blanked, raw = src[key]
        kw = decl_keyword(blanked, line)
        if kw not in STUBBABLE_KW:
            plan[key][line] = "skip:kind=" + kw
            continue
        end = decl_extent(blanked, line, raw)
        if body_separator(blanked, line, end) is None:
            body = "\n".join(blanked[line - 1:min(end, len(blanked))])
            plan[key][line] = ("skip:where-form-body" if WHERE_RE.search(body)
                               else "skip:equation-style-body" if "|" in body
                               else "skip:no-depth-0-:=")
            continue
        plan[key][line] = "stub"
    return plan, src


def write_stub_tree(files, mathlib, out_root, plan, src):
    """Write `sorry`-stubbed copies of each pinned file, LINE NUMBERS PRESERVED."""
    written = []
    for f in files:
        key = f["key"]
        dst = os.path.join(out_root, key)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        blanked, raw = src[key]
        lines = list(raw)
        n = 0
        for line in sorted(plan.get(key, {}), reverse=True):
            if plan[key][line] != "stub":
                continue
            end = decl_extent(blanked, line, raw)
            i, j = body_separator(blanked, line, end)
            lines[i] = lines[i][:j] + ":= sorry"
            for k in range(i + 1, end):
                lines[k] = ""
            n += 1
        # Fail closed on the two ways this surgery has gone wrong. Both are
        # silent in the output and fatal to the measurement: a shifted line
        # number re-anchors every later row, and a deleted `/-- ... -/` is an
        # edit ARM B did not ask for.
        if len(lines) != len(raw):
            raise SystemExit(f"stub surgery moved line numbers in {key}: "
                             f"{len(raw)} -> {len(lines)}")
        lost = sum(1 for a, b in zip(raw, lines) if a.startswith("/--") and not b)
        if lost:
            raise SystemExit(f"stub surgery deleted {lost} doc comment(s) in {key}")
        open(dst, "w", encoding="utf-8").write("\n".join(lines))
        written.append({"key": key, "stubbed": n})
    return written


def failing_after(report_path: str, mathlib: str):
    """{file: {anchor_line: row}} for a post-stub report, anchored like the census.

    The row carries `deps`, so a declaration that is STILL a cascade after its
    own causes were neutralised -- i.e. genuinely more than one hop deep -- is
    distinguishable from one that surfaced an independent error.
    """
    _, files = classify(report_path, mathlib)
    out: dict[str, dict[int, dict]] = {}
    for f in files:
        d = {}
        for r in f["rows"]:
            if r["parser_recovery"]:
                continue
            a = r["anchor_line"] or r["line"]
            if a is not None:
                d.setdefault(a, r)
        out[f["key"]] = d
    return out


def graph(files):
    """-> (nodes, cascade, cause, ancestors) sharing rank()'s definitions."""
    stats, nodes, cascade, cause = rank(files)
    succ = collections.defaultdict(set)
    for key, r in nodes.items():
        for dep in r["deps"]:
            e = (r["file"], dep["dep_line"])
            if e in nodes and e != key:
                succ[key].add(e)
    anc: dict[tuple, set] = {}

    def ancestors(k, seen=frozenset()):
        if k in anc:
            return anc[k]
        if k in seen:
            return set()
        seen = seen | {k}
        out = set()
        for e in succ[k]:
            out |= {e} if e in cause else ancestors(e, seen)
        if not succ[k]:
            out.add(k)
        anc[k] = out
        return out

    for k in cascade:
        ancestors(k)
    return stats, nodes, cascade, cause, anc


def masking(report_a: str, report_b: str, mathlib: str, mathlib_b: str = None) -> dict:
    """How many first-error dependents actually RECOVER when their causes go?

    ARM A is the unmodified slice; ARM B is the same slice with every stubbable
    CAUSE proof replaced by `sorry` (see --write-stub-tree). A cascade is
    MEASURED only when every one of its causes was stubbable AND its stub then
    passed; it RECOVERED when ARM B reports no error anchored at its line.
    """
    # ARM A's rows and the stub plan are read against the UNMODIFIED checkout;
    # ARM B's rows against the stubbed one. Line numbers are preserved by the
    # surgery, so the two indexes agree -- but the split is stated rather than
    # relied on, and `--masking-tree` makes it checkable.
    _, files_a = classify(report_a, mathlib)
    stats, nodes, cascade, cause, anc = graph(files_a)
    plan, blanked = stub_plan(files_a, nodes, cause, mathlib)
    after = failing_after(report_b, mathlib_b or mathlib)

    def stubbed_ok(k):
        return plan.get(k[0], {}).get(k[1]) == "stub" and k[1] not in after.get(k[0], {})

    rows, per_cause = [], collections.defaultdict(lambda: [0, 0])
    for k in sorted(cascade):
        ancestors = anc.get(k, set())
        measured = bool(ancestors) and all(stubbed_ok(a) for a in ancestors)
        recovered = k[1] not in after.get(k[0], {})
        rows.append({
            "file": k[0], "line": k[1],
            "decl": nodes[k]["decl_source"] or nodes[k]["decl_clean"],
            "first_error_class": nodes[k]["class"],
            "causes": sorted("%s:%d" % a for a in ancestors),
            "measured": measured,
            "not_measured_because": None if measured else sorted(
                {plan.get(a[0], {}).get(a[1], "skip:not-a-cause")
                 if plan.get(a[0], {}).get(a[1]) != "stub" else "stub-still-failed"
                 for a in ancestors if not stubbed_ok(a)}),
            "recovered": recovered,
            "underneath": None if recovered else {
                "class": after[k[0]][k[1]]["class"],
                "error": after[k[0]][k[1]]["error"],
                # Still a cascade with its own causes neutralised = genuinely
                # more than one hop deep, which the ARM A census cannot see.
                "still_cascade": bool(after[k[0]][k[1]]["deps"]),
            },
        })
        if measured:
            for a in ancestors:
                per_cause["%s:%d" % a][0] += 1
                per_cause["%s:%d" % a][1] += 1 if recovered else 0

    meas = [r for r in rows if r["measured"]]
    rec = [r for r in meas if r["recovered"]]
    n_stub = sum(1 for d in plan.values() for v in d.values() if v == "stub")
    n_stub_ok = sum(1 for f, d in plan.items() for ln, v in d.items()
                    if v == "stub" and ln not in after.get(f, {}))
    ranked = []
    for s in stats:
        key = "%s:%d" % (s["file"], s["line"])
        if key in per_cause:
            n, r = per_cause[key]
            ranked.append({
                "cause": s["decl_source"] or s["decl_clean"],
                "file": s["file"], "line": s["line"],
                "recoveries_upper_bound": s["recoveries_upper_bound"],
                "measured_dependents": n, "recovered": r,
            })
    def arm(path):
        r = json.load(open(path))
        return {"file": os.path.basename(path), "label": r.get("commit"),
                "success": sum(f.get("success_count", 0) for f in r["files"]),
                "declarations": sum(f.get("decl_count", 0) for f in r["files"])}

    return {
        "schema_version": "Clean-srcelab-first-error-masking-v1",
        "arm_a": arm(report_a),
        "arm_b": arm(report_b),
        "method": "ARM B is ARM A's slice with every stubbable CAUSE proof replaced "
                  "by `sorry`, line numbers preserved. `sorry` is faithful only for "
                  "a proof: it registers the declaration with exactly the statement "
                  "the source wrote. It is NOT faithful for a def/abbrev/instance/"
                  "class, so those causes are not stubbed and every cascade behind "
                  "one is reported NOT MEASURED.",
        "arm_b_validated_by": "The stubbed tree is checked by an oracle that is "
                              "not Clean: the pinned Lean 4.30.0-rc2 elaborates "
                              "all five stubbed files with ZERO non-`sorry` "
                              "diagnostics. It found two surgery defects the "
                              "in-process guards could not (`where`-form bodies "
                              "and equation-style arms); both are refusals now, "
                              "pinned by --self-test arm A3.",
        "checkout_control":
            "Which checkout ARM B's rows are anchored against is INERT here, "
            "measured not argued: running this with --masking-tree pointing at "
            "the stub tree, at the unmodified checkout, and with both arms read "
            "against the stub tree gives identical totals AND identical rows. "
            "The surgery preserves line numbers and never touches a declaration "
            "header, so the two source indexes coincide -- which is why this "
            "artifact regenerates from the repo alone, with no stub tree.",
        "stubs": {"planned": n_stub, "passed_in_arm_b": n_stub_ok,
                  "skipped": collections.Counter(
                      v for d in plan.values() for v in d.values()
                      if v != "stub")},
        "totals": {
            "cascades_in_arm_a": len(cascade),
            "measured": len(meas),
            "recovered": len(rec),
            "still_failing_with_a_different_error": len(meas) - len(rec),
            "of_those_still_a_cascade_i_e_more_than_one_hop": sum(
                1 for r in meas if not r["recovered"] and r["underneath"]["still_cascade"]),
            "not_measured": len(rows) - len(meas),
        },
        "underneath_by_class": collections.Counter(
            r["underneath"]["class"] for r in meas if not r["recovered"]),
        "per_cause": ranked,
        "rows": rows,
    }


# Declarations the stub surgery must REFUSE, each pinned to the Lean 4.30.0-rc2
# error the unrefused version produced. The line-count and doc-comment guards
# are blind to both, so this is how the two refusals stay honest.
STUB_REFUSALS = {
    ("Mathlib/Logic/Function/Basic.lean", 675): "skip:where-form-body",
    ("Mathlib/Order/Basic.lean", 339): "skip:equation-style-body",
}


def self_test(report, mathlib, tmp) -> int:
    """Five arms. Three assert an invariant; two BREAK a clause and demand it fires.

    A guard nobody has seen fail is `exit 0` -- so the arms that matter here are
    M-a and M-b, which re-enable the exact defects this surgery shipped with,
    and A3, which pins the two refusals the pinned Lean binary had to find.
    """
    _, files = classify(report, mathlib)
    stats, nodes, _, cause, _ = graph(files)
    fails = []

    if any(s["recoveries_upper_bound"] != s["first_error_dependents_exclusive"]
           for s in stats):
        fails.append("A1 recoveries_upper_bound drifted from the exclusive count")

    plan0, _ = stub_plan(files, nodes, cause, mathlib)
    for (key, line), want in STUB_REFUSALS.items():
        got = plan0.get(key, {}).get(line)
        if got is None:
            continue                      # not a cause in this report; nothing to pin
        if got != want:
            fails.append(f"A3 {key}:{line} planned {got!r}, must be {want!r} "
                         "-- Lean rejects the stub tree without this refusal")

    def write(tag):
        plan, src = stub_plan(files, nodes, cause, mathlib)
        out = os.path.join(tmp, tag)
        return write_stub_tree(files, mathlib, out, plan, src)

    try:
        w = write("base")
        if sum(x["stubbed"] for x in w) == 0:
            fails.append("A2 the stub plan is empty, so every later arm is vacuous")
    except SystemExit as e:
        fails.append(f"A2 the unmutated surgery tripped its own guard: {e}")

    saved = globals()["decl_extent"]
    globals()["decl_extent"] = lambda b, s, raw=None: saved(b, s, None)
    try:
        write("mut_a")
        fails.append("M-a dropping decl_extent's raw-comment clause was NOT caught "
                     "(the doc-comment guard is asleep)")
    except SystemExit:
        pass
    finally:
        globals()["decl_extent"] = saved

    saved_sep = globals()["body_separator"]

    def flat_sep(blanked, start, end):
        """`:=` with NO bracket tracking -- the shortcut this refuses to take."""
        for i in range(start - 1, min(end, len(blanked))):
            j = blanked[i].find(":=")
            if j != -1:
                return (i, j)
        return None

    globals()["body_separator"] = flat_sep
    try:
        w2 = write("mut_b")
        base = {x["key"]: x["stubbed"] for x in w}
        if all(x["stubbed"] == base[x["key"]] for x in w2):
            hit = _flat_sep_differs(files, nodes, cause, mathlib, saved_sep, flat_sep)
            if not hit:
                fails.append("M-b dropping bracket tracking changed nothing, so the "
                             "depth-0 clause is inert on this input")
    except SystemExit:
        pass
    finally:
        globals()["body_separator"] = saved_sep

    for f in fails:
        print("FAIL " + f, file=sys.stderr)
    print(f"self-test: {5 - len(fails)}/5 arms held", file=sys.stderr)
    return 1 if fails else 0


def _flat_sep_differs(files, nodes, cause, mathlib, real, flat) -> bool:
    """True when the two separator rules disagree on at least one declaration."""
    src = {f["key"]: (index_source(os.path.join(mathlib, f["key"]))[0],
                      open(os.path.join(mathlib, f["key"]),
                           encoding="utf-8").read().split("\n")) for f in files}
    for (key, line) in sorted(cause):
        blanked, raw = src[key]
        if decl_keyword(blanked, line) not in STUBBABLE_KW:
            continue
        end = decl_extent(blanked, line, raw)
        if real(blanked, line, end) != flat(blanked, line, end):
            return True
    return False


def mutate(report, mathlib):
    """Rule sensitivity: perturb one clause at a time and report the cascade count."""
    variants = [
        ("R  (rule as applied)", {}),
        ("M1 drop 'earlier in the file'", {"no_order": True}),
        ("M2 drop 'dependency also failed'", {"no_failed": True}),
        ("M3 drop namespace resolution", {"no_ns": True}),
        ("M4 raw source lines (no comment blanking)", {"raw_lines": True}),
    ]
    print(f"{'cascade':>8} {'cause':>7}   variant")
    base = None
    for label, kw in variants:
        _, files = classify(report, mathlib, **kw)
        rows = [r for f in files for r in f["rows"] if not r["parser_recovery"]]
        c = sum(1 for r in rows if r["deps"])
        if base is None:
            base = c
        delta = "" if c == base else f"   ({c - base:+d} vs R)"
        print(f"{c:8d} {len(rows) - c:7d}   {label}{delta}")
    # the convenient approximation inside R itself
    _, files = classify(report, mathlib)
    rows = [r for f in files for r in f["rows"] if not r["parser_recovery"]]
    print(f"{sum(1 for r in rows if r['deps_noapprox']):8d} "
          f"{sum(1 for r in rows if not r['deps_noapprox']):7d}   "
          f"M5 drop the dot-notation bare-field candidate (approximation guard)")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("report", nargs="?", help="reports/source-elab/srcelab-*.json")
    ap.add_argument("-o", "--out", help="write the census JSON here")
    ap.add_argument("--mutate", action="store_true", help="rule-sensitivity table only")
    ap.add_argument("--write-stub-tree", metavar="DIR",
                    help="write `sorry`-stubbed copies of the pinned files under DIR "
                         "(the ARM B input; DIR must be a Mathlib checkout)")
    ap.add_argument("--self-test", action="store_true",
                    help="5 arms over the stub surgery and the rename invariant")
    ap.add_argument("--masking", metavar="ARM_B.json",
                    help="measure how many first-error dependents actually recover: "
                         "compare the report against a post-stub ARM B report")
    ap.add_argument("--masking-tree", metavar="DIR",
                    help="checkout ARM B was measured against (the --write-stub-tree "
                         "output); defaults to the ARM A checkout")
    args = ap.parse_args()

    report = args.report
    if not report:
        cands = glob.glob("reports/source-elab/srcelab-*.json")
        if not cands:
            ap.error("no reports/source-elab/srcelab-*.json found; pass one explicitly")
        report = max(cands, key=os.path.getmtime)
    mathlib = default_mathlib()

    if args.mutate:
        mutate(report, mathlib)
        return 0

    if args.self_test:
        with tempfile.TemporaryDirectory(prefix="srcelab-selftest-") as tmp:
            return self_test(report, mathlib, tmp)

    if args.write_stub_tree:
        _, files = classify(report, mathlib)
        _, nodes, _, cause, _ = graph(files)
        plan, blanked = stub_plan(files, nodes, cause, mathlib)
        written = write_stub_tree(files, mathlib, args.write_stub_tree, plan, blanked)
        skipped = collections.Counter(v for d in plan.values() for v in d.values()
                                      if v != "stub")
        print(json.dumps({"out": args.write_stub_tree, "files": written,
                          "skipped": skipped}, indent=1))
        return 0

    if args.masking:
        out = masking(report, args.masking, mathlib, args.masking_tree)
        text = json.dumps(out, indent=1, ensure_ascii=False)
        if args.out:
            open(args.out, "w", encoding="utf-8").write(text + "\n")
            print(f"wrote {args.out}", file=sys.stderr)
        else:
            print(text)
        t = out["totals"]
        print(f"cascades={t['cascades_in_arm_a']} measured={t['measured']} "
              f"recovered={t['recovered']} "
              f"different-error={t['still_failing_with_a_different_error']} "
              f"not-measured={t['not_measured']}", file=sys.stderr)
        return 0

    rep, files = classify(report, mathlib)
    stats, nodes, cascade, cause = rank(files)
    rows = [r for f in files for r in f["rows"]]
    decl_rows = [r for r in rows if not r["parser_recovery"]]

    by_class = collections.Counter(r["class"] for r in decl_rows)
    casc_by_class = collections.Counter(r["class"] for r in decl_rows if r["deps"])
    per_file = []
    for f in files:
        d = [r for r in f["rows"] if not r["parser_recovery"]]
        per_file.append({
            "key": f["key"], "failures": len(d),
            "cascade": sum(1 for r in d if r["deps"]),
            "cause": sum(1 for r in d if not r["deps"]),
            "parser_recovery_events": sum(1 for r in f["rows"] if r["parser_recovery"]),
        })

    out = {
        "schema_version": "Clean-srcelab-cause-cascade-v2",
        "source_report": os.path.basename(report),
        "source_report_commit": rep["commit"],
        "mathlib": os.path.basename(mathlib.rstrip("/")),
        "rule": "R: a failure is a CASCADE iff an identifier its error reports absent "
                "resolves, under Lean name resolution restricted to the file, to a "
                "declaration the file defines EARLIER that ALSO failed.",
        "attribution_unit": "the FIRST error `clean check` reports for a declaration; "
                            "no second error for the same declaration exists in the "
                            "input artifact, so a CASCADE row is a statement about one "
                            "error string and not about the declaration's fate",
        "first_error_masking": FIRST_ERROR_MASKING,
        "totals": {
            "declaration_failures": len(decl_rows),
            "parser_recovery_events": sum(1 for r in rows if r["parser_recovery"]),
            "cascade": len(cascade),
            "cause": len(cause),
            "causes_with_dependents": len(stats),
        },
        "by_class": [{"class": k, "failures": v, "cascade": casc_by_class[k],
                      "cause": v - casc_by_class[k]} for k, v in by_class.most_common()],
        "per_file": per_file,
        "ranked_causes": stats,
    }
    text = json.dumps(out, indent=1, ensure_ascii=False)
    if args.out:
        open(args.out, "w", encoding="utf-8").write(text + "\n")
        print(f"wrote {args.out}", file=sys.stderr)
    else:
        print(text)
    print(f"declaration failures={len(decl_rows)} cascade={len(cascade)} "
          f"cause={len(cause)} ranked={len(stats)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
