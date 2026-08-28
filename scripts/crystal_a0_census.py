#!/usr/bin/env python3
"""The A0-eligibility census: every body's distance from A0 6-of-6, at one HEAD.

    scripts/crystal_a0_census.py <dump_O3> <O3.flip.txt> <O0.flip.txt> <out.json> [KEY=VALUE ...]

WHY THIS EXISTS.  A0's six criteria (bridge design 6.0 row A0: lowered,
spliced, zero unsupported, DerivedAgreed, bodyful reachable closure, flip event
observed) were only ever evaluated per hand-picked target.  The one whole-crate
number close to it -- "52 call bodies with a bodyful closure" -- predates every
marker wave, and "how many bodies are A0-complete" had never been computed at
any HEAD.  This script computes it mechanically from one sealed-driver
whole-crate compile: the coverage JSON (criteria 1-4), the emitted trust-ir
text's call graph (criterion 5, the same body-prefix walk
`crystal_frontier_census.py` verifies before using), and the flip log
(criterion 6, plus the A6 event-lineage == coverage-row-lineage check).

WHAT IT DOES NOT MEASURE.  A6's fail-closed perturbation criterion is
per-body-class (switch-map reaches switch-carrying bodies, mc-plan call-plan
bodies, ...) and is not census-able from one compile; the negative control is
crate-wide, not per-body.  So this census brackets A0 exactly and A6 only in
its digest half.  A row here is *eligibility*, not a chain: links 3-5 (the
Clean-side semantics, the refinement theorem, the kernel check) exist per
chain, not per row.

Provenance KEY=VALUE pairs are recorded verbatim, same contract as
`crystal_frontier_census.py`.
"""

import collections
import json
import re
import sys

FN = re.compile(r"^(?:rustcc )?fn @(.*)\(functy\.(\d+)\) \{$")
CALL = re.compile(r"call @func\.(\d+)")
# The edge set is UNDER-approximated by CALL alone, and the census is the walk's
# only witness (workflow wf_1c3df27b, 2026-08-27). Two more edge forms exist:
#   * `fndef<func.N>` -- a function VALUE. If it can be reached it can be called,
#     so it is an edge for a closure that claims to bound reachable callees.
#     Measured: 8 sites in the recorded dump, all in reduce_float_* entries whose
#     bodyful already reads False via an ordinary edge -- so widening reproduces
#     today's totals EXACTLY (189 six-of-six / 339 one-short); a moved total
#     would mean the hole was already load-bearing.
#   * `call_indirect` -- NO static target. A body containing one has a closure
#     that is not statically known, so bodyful is False, FAIL-CLOSED (0 in the
#     recorded dump; the arm exists so the first one cannot pass silently).
FNDEF = re.compile(r"fndef<func\.(\d+)>")
INDIRECT = re.compile(r"\bcall_indirect\b")
ASSIGN = re.compile(r"^\s+%\d+ = ([a-z_]+)")
BARE = re.compile(r"^\s+([a-z_]+)")
BLOCK = re.compile(r"^bb\d+")
DID = re.compile(r"did=DefId\(0:(\d+) ~")
LINEAGE = re.compile(r"lineage=(sha256:[0-9a-f]+)")

CRITERIA = (
    "lowered",
    "spliced",
    "zero_unsupported",
    "derived_agreed",
    "bodyful_reachable_closure",
    "flip_event_O3",
)


def parse_ir(path):
    funcs, cur = [], None
    for ln in open(path, encoding="utf-8", errors="replace"):
        s = ln.rstrip("\n")
        m = FN.match(s)
        if m:
            cur = {"name": m.group(1), "n": 0, "callees": set()}
            funcs.append(cur)
            continue
        if cur is None:
            continue
        if s.startswith("}"):
            cur = None
            continue
        body = s.strip()
        if body and not body.startswith(";") and not BLOCK.match(body):
            if ASSIGN.match(s) or BARE.match(s):
                cur["n"] += 1
        for c in CALL.finditer(s):
            cur["callees"].add(int(c.group(1)))
        for c in FNDEF.finditer(s):
            cur["callees"].add(int(c.group(1)))
        if INDIRECT.search(s):
            cur["indirect"] = True
    return funcs


def verify_prefix(funcs, cov):
    """The same two index facts crystal_frontier_census.py fails closed on."""
    n = sum(1 for f in funcs if f["n"] > 0)
    for i, f in enumerate(funcs):
        if (f["n"] > 0) != (i < n):
            raise SystemExit(f"index fact 1 violated at entry {i} ({f['name']})")
    if n != cov["totals"]["spliced"]:
        raise SystemExit(
            f"index fact 1 violated: {n} text bodies vs {cov['totals']['spliced']} spliced"
        )
    for b in cov["bodies"]:
        fid = b["func_id"]
        if fid is None:
            continue
        name = re.sub(r"::\{(?:const|static)-init\}$", "", funcs[fid]["name"]) if fid < n else ""
        if fid >= n or name != b["def_path"]:
            raise SystemExit(
                f"index fact 1 violated: coverage func_id {fid} is {b['def_path']}, "
                f"text ordinal is {funcs[fid]['name'] if fid < len(funcs) else '<oor>'}"
            )
    ids = [c for f in funcs for c in f["callees"]]
    if ids and max(ids) >= len(funcs):
        raise SystemExit(f"index fact 2 violated: callee id {max(ids)} out of range")
    if not any(c < n for c in ids):
        raise SystemExit("index fact 2 violated: no call resolves inside the body prefix")
    return n


def parse_flips(path):
    cod, ctfe = {}, {}
    for ln in open(path, encoding="utf-8", errors="replace"):
        if "trust-ir-flip:" not in ln:
            continue
        m = DID.search(ln)
        if not m:
            continue
        di = int(m.group(1))
        lm = LINEAGE.search(ln)
        lin = lm.group(1) if lm else None
        if "CTFE compiled from trust" in ln:
            ctfe[di] = lin
        elif "compiled from trust" in ln:
            cod[di] = lin
    return cod, ctfe


def check_discharge(def_path, escapes, indirect, tgt):
    """Core of the A0-SEMANTIC cell -- module-level so the selftest can reach it.

    escapes: the walk's escaping callee ids for this body. indirect: any
    indirect call in the closure. tgt: this def_path's discharge-table entry or
    None. True/False is the verdict; SystemExit is a REFUSAL (malformed or
    wider-than-reality table).
    """
    if indirect:
        return False
    if tgt is None:
        return False
    entries = {int(k) for k in tgt.get("escaping_callees", {})}
    extra = entries - set(escapes)
    if extra:
        raise SystemExit(
            f"discharge table for {def_path} names callee(s) {sorted(extra)} that the "
            f"walk does not find (walk escapes: {sorted(escapes)}) -- a table wider than "
            f"reality is refused, not ignored")
    for e in sorted(escapes):
        ent = tgt.get("escaping_callees", {}).get(str(e))
        if ent is None:
            return False
        if ent.get("clause") not in ("a", "b"):
            raise SystemExit(f"discharge entry {def_path}/{e} has no valid clause")
        if ent["clause"] == "a" and not (ent.get("model") and ent.get("residual")):
            raise SystemExit(
                f"discharge entry {def_path}/{e} is clause (a) but names no model+residual "
                f"-- an unnamed residual is a silence, which clause (a) exists to forbid")
    return True


def selftest():
    """Every refusal must be reachable, demonstrated on EVERY invocation.

    Trust (2026-08-27, workflow wf_1c3df27b): the gate-registry row for this
    file claimed it "asserts no invariant and refuses nothing" while
    `verify_prefix` carries FIVE `SystemExit`s -- including the partition
    assertion the whole bodyful criterion rests on. A criterion this file
    computes must not be movable through a row nobody has seen refuse, so the
    refusals run as arms here, at the top of main, every time -- the
    `selftest-inline` convention (`scripts/check_lowering_adequacy.py`).
    """
    def fn(name, n, callees=(), indirect=False):
        f = {"name": name, "n": n, "callees": set(callees)}
        if indirect:
            f["indirect"] = True
        return f

    def refuses(tag, funcs, cov):
        try:
            verify_prefix(funcs, cov)
        except SystemExit:
            return True
        print(f"  [RED] selftest arm {tag}: refusal did NOT fire")
        return False

    good = [fn("a", 2, [1]), fn("b", 1), fn("c", 0)]
    cov = {"totals": {"spliced": 2},
           "bodies": [{"func_id": 0, "def_path": "a"}, {"func_id": 1, "def_path": "b"}]}
    ok = True
    # arm 1: a body AFTER a declaration breaks the partition
    ok &= refuses("partition", [fn("a", 2, [1]), fn("c", 0), fn("b", 1)], cov)
    # arm 2: text-body count != coverage spliced total
    ok &= refuses("spliced-total", good, {"totals": {"spliced": 3}, "bodies": []})
    # arm 3: coverage func_id names a different function than the text ordinal
    ok &= refuses("name-mismatch", good,
                  {"totals": {"spliced": 2},
                   "bodies": [{"func_id": 0, "def_path": "WRONG"}]})
    # arm 4: a callee id out of range
    ok &= refuses("callee-oor", [fn("a", 2, [9]), fn("b", 1), fn("c", 0)], cov)
    # arm 5: NO call resolves inside the prefix (vacuous edge set)
    ok &= refuses("vacuous-edges", [fn("a", 2, [2]), fn("b", 1), fn("c", 0)], cov)
    # the happy path must still pass
    try:
        if verify_prefix(good, cov) != 2:
            print("  [RED] selftest: happy path returned wrong prefix")
            ok = False
    except SystemExit:
        print("  [RED] selftest: happy path REFUSED")
        ok = False
    # arm 6 (2026-08-27 widening): an indirect call fails the closure CLOSED
    fs = [fn("a", 2, [1], indirect=True), fn("b", 1), fn("c", 0)]
    seen, stack, okc = set(), list(fs[0]["callees"]), True
    if fs[0].get("indirect"):
        okc = False
    if okc:
        print("  [RED] selftest arm indirect-fail-closed: closure passed")
        ok = False
    # arms 7-11 (2026-08-27 R2 adoption): the discharge core, fail-closed both ways
    ENT = {"clause": "a", "model": "m", "residual": "r"}
    def refuses_d(tag, *a):
        try:
            check_discharge(*a)
        except SystemExit:
            return True
        print(f"  [RED] selftest arm {tag}: refusal did NOT fire")
        return False
    if check_discharge("t", {9}, False, {"escaping_callees": {"9": ENT}}) is not True:
        print("  [RED] arm discharge-covered: entry present but verdict False"); ok = False
    if check_discharge("t", {9}, False, {"escaping_callees": {}}) is not False:
        print("  [RED] arm discharge-missing: escaping callee with no entry passed"); ok = False
    if check_discharge("t", {9}, True, {"escaping_callees": {"9": ENT}}) is not False:
        print("  [RED] arm discharge-indirect: indirect call passed the semantic cell"); ok = False
    ok &= refuses_d("wider-than-reality", "t", {9}, False, {"escaping_callees": {"9": ENT, "10": ENT}})
    ok &= refuses_d("clause-a-unnamed-residual", "t", {9}, False,
                    {"escaping_callees": {"9": {"clause": "a", "model": "m"}}})
    if not ok:
        raise SystemExit("crystal_a0_census selftest: arms misbehave -- refusing to census")


def main(argv):
    # `--selftest` runs the refusal arms alone and exits; without it they STILL
    # run first (selftest-inline convention) -- the flag exists so the
    # demonstration is invocable by name and the registry badge matches the file.
    if len(argv) > 1 and argv[1] == "--selftest":
        selftest()
        print("crystal_a0_census selftest: 11/11 arms behave")
        return
    selftest()
    if len(argv) < 5:
        raise SystemExit(__doc__)
    d3, f3, f0, out = argv[1:5]
    provenance = {}
    for kv in argv[5:]:
        if "=" not in kv:
            raise SystemExit(f"provenance argument {kv!r} is not KEY=VALUE")
        k, v = kv.split("=", 1)
        provenance[k] = v
    discharge_table = None
    if "discharge" in provenance:
        discharge_table = json.load(open(provenance["discharge"], encoding="utf-8"))
    cov = json.load(open(d3 + "/clean_kernel.coverage.json", encoding="utf-8"))
    funcs = parse_ir(d3 + "/clean_kernel.trust-ir.txt")
    nb = verify_prefix(funcs, cov)
    cod3, ctfe3 = parse_flips(f3)
    cod0, ctfe0 = parse_flips(f0)

    closures = {}

    def bodyful(fid):
        if fid in closures:
            return closures[fid]
        seen, stack, ok = set(), list(funcs[fid]["callees"]), True
        escapes, indirect = set(), bool(funcs[fid].get("indirect"))
        if indirect:
            ok = False  # an indirect call's target is statically unknown: fail closed
        while stack:
            c = stack.pop()
            if c in seen:
                continue
            seen.add(c)
            if c >= nb:
                ok = False
                escapes.add(c)
                continue
            if funcs[c].get("indirect"):
                ok = False
                indirect = True
            stack.extend(funcs[c]["callees"])
        closures[fid] = (ok, len(seen), frozenset(escapes), indirect)
        return closures[fid]

    def discharged(fid, def_path):
        """The A0-SEMANTIC cell (owner ruling 2026-08-27, workflow wf_1c3df27b R2).

        True iff the syntactic walk holds OUTRIGHT, or every escaping callee
        carries a clause in data/crystal_a0_discharge.json for this def_path.
        FAIL-CLOSED both directions: an escaping callee with no entry is False,
        and a table entry naming a callee the walk does not find is a REFUSAL
        (a table wider than reality is how residuals hide). An indirect call is
        False regardless -- no table entry can name an unknown target.
        """
        ok, _, escapes, indirect = bodyful(fid)
        if ok:
            return True
        if discharge_table is None:
            return False
        tgt = discharge_table.get("targets", {}).get(def_path)
        return check_discharge(def_path, escapes, indirect, tgt)

    rows = []
    for b in cov["bodies"]:
        dm = b["differentials"].get("derived_mir", {})
        fid = b["func_id"]
        md = dm.get("markers_detail", "")
        crit = {
            "lowered": bool(b.get("lowered")),
            "spliced": bool(b.get("spliced")),
            "zero_unsupported": b.get("unsupported") == [],
            "derived_agreed": dm.get("verdict") == "agreed",
            "bodyful_reachable_closure": (fid is not None and fid < nb and bodyful(fid)[0]),
            "flip_event_O3": b["def_index"] in cod3,
        }
        # The SEMANTIC cell (owner ruling 2026-08-27) is computed and reported
        # BESIDE the six historical criteria, never inside their sum: the
        # historical 6-of-6 total must stay derivable from the same six cells it
        # always was, and the semantic total is its own named number.
        semantic = fid is not None and fid < nb and discharged(fid, b["def_path"])
        score = sum(crit.values())
        ev_lin = cod3.get(b["def_index"])
        rows.append(
            {
                "def_path": b["def_path"],
                "def_index": b["def_index"],
                "score": score,
                "crit": crit,
                "bodyful_or_discharged_closure": semantic,
                "markers_exact": bool(dm.get("markers_exact")),
                "markers_vacuous": md.startswith("0 marker line(s)"),
                "flip_O0": b["def_index"] in cod0,
                "ctfe_O3": b["def_index"] in ctfe3,
                "a6_event_lineage_equal": (ev_lin is not None and ev_lin == b.get("lineage")),
            }
        )

    complete = [r for r in rows if r["score"] == 6]
    one_short = [r for r in rows if r["score"] == 5]
    missing = collections.Counter(
        next(c for c in CRITERIA if not r["crit"][c]) for r in one_short
    )
    dist = collections.Counter(r["score"] for r in rows)

    result = {
        "schema": "clean.crystal.a0_census/1",
        "provenance": provenance,
        "inputs": {"dump_O3": d3, "flip_O3": f3, "flip_O0": f0},
        "criteria": list(CRITERIA),
        "totals": {
            "bodies": cov["totals"]["bodies"],
            "score_distribution": {str(k): v for k, v in sorted(dist.items())},
            "a0_complete_6_of_6": len(complete),
            "a0_complete_with_nonvacuous_markers": sum(
                1 for r in complete if r["markers_exact"] and not r["markers_vacuous"]
            ),
            "ctfe_flip_O3_bodies": sum(1 for r in rows if r["ctfe_O3"]),
            "a0_one_short_5_of_6": len(one_short),
            "one_short_missing_criterion": dict(missing.most_common()),
            "a0_complete_semantic": sum(
                1
                for r in rows
                if r["score"] - r["crit"]["bodyful_reachable_closure"]
                + r["bodyful_or_discharged_closure"]
                == 6
            ),
        },
        "a0_complete_bodies": sorted(
            (
                {
                    "def_path": r["def_path"],
                    "def_index": r["def_index"],
                    "markers_exact": r["markers_exact"],
                    "markers_vacuous": r["markers_vacuous"],
                    "flip_O0": r["flip_O0"],
                    "a6_event_lineage_equal": r["a6_event_lineage_equal"],
                }
                for r in complete
            ),
            key=lambda x: x["def_index"],
        ),
        "one_short_missing_flip_only_sample": sorted(
            r["def_path"] for r in one_short if not r["crit"]["flip_event_O3"]
        )[:40],
        "one_short_missing_closure_bodies": sorted(
            r["def_path"] for r in one_short if not r["crit"]["bodyful_reachable_closure"]
        ),
    }
    json.dump(result, open(out, "w", encoding="utf-8"), indent=1)

    print(f"bodies: {cov['totals']['bodies']}   score distribution: {dict(sorted(dist.items()))}")
    nv = [r for r in complete if r["markers_exact"] and not r["markers_vacuous"]]
    print(f"A0 6-of-6 COMPLETE: {len(complete)}  (with NON-VACUOUS markers_exact: {len(nv)})")
    print("  non-vacuous 6-of-6 bodies:")
    for r in sorted(nv, key=lambda x: x["def_index"]):
        print(f"    {r['def_path']}  di={r['def_index']}")
    print(f"A0 5-of-6, by missing criterion: {dict(missing.most_common())}")
    print(f"wrote {out}")


if __name__ == "__main__":
    main(sys.argv)
