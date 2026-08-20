#!/usr/bin/env python3
"""The MARKER-LINE ledger: what `markers_exact: true` actually compared.

WHY THIS FILE EXISTS
====================
`markers_exact` is **wall 2** — the gate that refuses `level::Level::is_zero` at
the deployed profile (`trust/crates/trust-thir-lower/src/flip_registry.rs`), and
the reason it declines silently. It is also two claims wearing one name:

  * agreement over a REAL, non-empty storage-marker sequence, and
  * agreement over two EMPTY ones.

Measured 2026-08-13 (`data/crystal_markers_vacuity_2026-08-13.json`), only **27
of 1,082** `markers_exact` rows were the first kind. The other 1,055 compared
nothing. **Matching emptiness is honest agreement — it is not a bug and this
file does not turn it into one.** But it is not EVIDENCE either, and a boolean
that cannot tell the two apart lets a body lose 100% of its marker content while
the column stays `true`.

Until now that split was a STUDY: a number someone had to remember, re-derived
by hand each time it was quoted, and named in `docs/CRYSTAL_STATUS.md` §0.6 as
one of the ASSUMED figures because **no clean-side axis recorded it**. This file
is that axis. It turns the split into row data:

  * every coverage row gets a marker CLASS and, where the artifact determines
    them, its **built** and **derived** marker line counts;
  * where the producer does not record a count, the count is `null` and the
    row lands in `not_recorded_by_producer` — never `0`, because `0` is a
    measurement and `null` is its absence;
  * `agreed_lines` — the marker lines that DID match before the first
    divergence — is counted on the refused rows too, so "how much marker
    evidence does a refusal carry" stops being unanswerable.

WHAT THE PRODUCER RECORDS, AND WHAT IT DOES NOT
-----------------------------------------------
`mir_differential.rs` writes `markers_detail` in exactly four shapes:

    "<N> marker line(s) identical"                     both sides, N lines, equal
    "markers differ: line <I>: built `<B>` vs derived `<D>`"   first divergence
    "marker channel(built|derived): <reason>"          the channel refused to run
    ""                                                 step 5 was never reached

On the `markers differ` shape the sentinel `<end>` means "that side's sequence
ended here", so **one** side's exact length is determined (`I`) and the other is
known only to be `> I`. That asymmetry is the whole reason `built_lines` and
`derived_lines` are separate fields rather than one number: on 462 of 462
refused rows in `clean-kernel` today it is the DERIVED side that is `<end>` at
line 0, which is a far more specific fact than "the markers differ" — it says
the derived side emitted no storage markers at all.

Recording a count the producer never wrote would need a `mir_differential.rs`
edit, and that file is frozen byte-identical for the crystal measurement. So
this file is deliberately a READER: everything it reports is derivable from the
committed artifact, and anything that is not is `null`.

USAGE
-----
    trust_ir_markers.py ledger   --coverage COV.json [--out L.json] [--top N]
    trust_ir_markers.py residual --o3 O3.coverage.json --o3-log O3.flip.txt \
                                 --o0 O0.coverage.json --o0-log O0.flip.txt [--out R.json]
    trust_ir_markers.py selftest

`residual` re-derives the marker gate's PRICE: the flip events that fire at
`-Copt-level=0` (where `RemoveStorageMarkers` makes a marker divergence
codegen-immaterial and the gate is bypassed) and do not fire at `-O3`. Every
such event is attributed to its `-O3` marker class, so "the marker residual" is
a classified set of named bodies instead of a subtraction.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys

SCHEMA_LEDGER = "clean.trust_ir_markers.ledger.v1"
SCHEMA_RESIDUAL = "clean.trust_ir_markers.residual.v1"

#: The marker classes, in report order. `vacuous` is a PROPERTY of a class, not
#: a class of its own: `exact-vacuous` is the honest-but-contentless agreement.
CLASSES = (
    "exact-nonvacuous",
    "exact-vacuous",
    "differ-derived-empty",
    "differ-built-empty",
    "differ-content",
    "channel-skip",
    "not-compared",
    "unparseable",
)

#: Classes whose `markers_exact` is true. Their union is the `markers_exact` count.
EXACT_CLASSES = ("exact-nonvacuous", "exact-vacuous")

#: Classes that carry real marker evidence. Exactly one, and that is the point.
EVIDENCE_CLASSES = ("exact-nonvacuous",)

_EXACT_RE = re.compile(r"^(\d+) marker line\(s\) identical$")
_DIFF_HEAD = "markers differ: line "
_DIFF_MID = ": built `"
_DIFF_TAIL = "` vs derived `"
_END = "<end>"


def _parse_diff(detail: str) -> tuple[int, str, str] | None:
    """`markers differ: line I: built `B` vs derived `D`` -> (I, B, D), or None.

    Split rather than regex: `B` and `D` are clipped Rust `Debug` payloads that
    routinely contain braces, quotes and colons, and the producer clips them at
    240 bytes mid-token. Anchoring on the two literal separators and taking the
    LAST occurrence of the tail is the only form that cannot mis-split a payload
    that happens to contain the separator text. Anything unexpected returns
    None, which the caller classes `unparseable` — never a minted count.
    """
    if not detail.startswith(_DIFF_HEAD):
        return None
    rest = detail[len(_DIFF_HEAD):]
    head, mid, rest = rest.partition(_DIFF_MID)
    if not mid or not head.isdigit():
        return None
    built, sep, derived = rest.rpartition(_DIFF_TAIL)
    if not sep or not derived.endswith("`"):
        return None
    return int(head), built, derived[:-1]


def classify(derived_mir: dict | None) -> dict:
    """The marker ledger entry for one coverage row's `derived_mir` record.

    Returns `class`, the two line counts, and the counts' lower bounds. A count
    is `None` when the artifact does not determine it. `agreed_lines` is the
    number of marker lines that matched before the first divergence — defined on
    EVERY compared row, including the refused ones, because "how much marker
    evidence backs this refusal" is a question the boolean cannot answer.
    """
    dm = derived_mir or {}
    detail = dm.get("markers_detail") or ""
    exact = bool(dm.get("markers_exact"))

    if exact:
        match = _EXACT_RE.match(detail)
        if match is None:
            # `markers_exact` with a detail we cannot read is the one shape that
            # must never be counted as evidence OR as vacuum.
            return _entry("unparseable", exact, None, None, None)
        n = int(match.group(1))
        cls = "exact-vacuous" if n == 0 else "exact-nonvacuous"
        return _entry(cls, exact, n, n, n)

    if detail.startswith(_DIFF_HEAD):
        parsed = _parse_diff(detail)
        if parsed is None:
            return _entry("unparseable", exact, None, None, None)
        line, built, derived = parsed
        if derived == _END:
            # The derived sequence ENDED at `line`: its length is known exactly.
            return _entry("differ-derived-empty", exact, None, line, line,
                          built_min=line + 1, first_diff=line)
        if built == _END:
            return _entry("differ-built-empty", exact, line, None, line,
                          derived_min=line + 1, first_diff=line)
        return _entry("differ-content", exact, None, None, line,
                      built_min=line + 1, derived_min=line + 1, first_diff=line)

    if detail.startswith("marker channel("):
        return _entry("channel-skip", exact, None, None, None)
    if detail == "":
        return _entry("not-compared", exact, None, None, None)
    return _entry("unparseable", exact, None, None, None)


def _entry(cls, exact, built, derived, agreed, *, built_min=None,
           derived_min=None, first_diff=None) -> dict:
    return {
        "class": cls,
        "markers_exact": exact,
        "built_lines": built,
        "derived_lines": derived,
        "agreed_lines": agreed,
        "built_lines_min": built if built is not None else built_min,
        "derived_lines_min": derived if derived is not None else derived_min,
        "first_diff_line": first_diff,
        "vacuous": cls == "exact-vacuous",
    }


def ledger(coverage: dict) -> dict:
    """Per-row marker accounting for a whole `<crate>.coverage.json`."""
    rows = []
    counts = collections.Counter()
    lines_total = 0
    agreed_on_refused = 0
    not_recorded = 0
    for body in coverage.get("bodies", []):
        entry = classify((body.get("differentials") or {}).get("derived_mir"))
        counts[entry["class"]] += 1
        if entry["class"] == "exact-nonvacuous":
            lines_total += entry["built_lines"]
        if entry["class"].startswith("differ"):
            agreed_on_refused += entry["agreed_lines"] or 0
        if entry["built_lines"] is None or entry["derived_lines"] is None:
            not_recorded += 1
        rows.append({
            "def_path": body.get("def_path"),
            "def_index": body.get("def_index"),
            **entry,
        })
    exact = sum(counts[c] for c in EXACT_CLASSES)
    return {
        "schema_self": SCHEMA_LEDGER,
        "crate": coverage.get("crate"),
        "bodies": coverage.get("totals", {}).get("bodies"),
        "classes": {c: counts[c] for c in CLASSES},
        "totals": {
            "markers_exact": exact,
            "markers_exact_vacuous": counts["exact-vacuous"],
            "markers_exact_nonvacuous": counts["exact-nonvacuous"],
            "markers_lines_total": lines_total,
            "markers_differ": (counts["differ-derived-empty"]
                               + counts["differ-built-empty"]
                               + counts["differ-content"]),
            "markers_differ_derived_empty": counts["differ-derived-empty"],
            "markers_differ_built_empty": counts["differ-built-empty"],
            "markers_differ_content": counts["differ-content"],
            "markers_channel_skipped": counts["channel-skip"],
            "markers_agreed_prefix_lines": agreed_on_refused,
            "markers_unparseable": counts["unparseable"],
            "not_recorded_by_producer": not_recorded,
            "vacuous_fraction_of_exact": (
                round(counts["exact-vacuous"] / exact, 6) if exact else None
            ),
        },
        "rows": rows,
    }


# ---------------------------------------------------------------------------
# the residual: what the gate actually costs, as named bodies
# ---------------------------------------------------------------------------
FLIP_RE = re.compile(
    r"trust-ir-flip: (?P<ctfe>CTFE )?compiled from trust-ir, "
    r"did=DefId\((?P<krate>\d+):(?P<index>\d+) "
)


def read_flips(path: str, crate: str = "clean_kernel") -> dict[str, list[int]]:
    """`def_index` lists for the codegen and CTFE flip lanes, plus foreign count."""
    codegen: list[int] = []
    ctfe: list[int] = []
    foreign = 0
    with open(path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if "compiled from trust-ir" not in line:
                continue
            match = FLIP_RE.search(line)
            if match is None or crate not in line:
                foreign += 1
                continue
            (ctfe if match.group("ctfe") else codegen).append(int(match.group("index")))
    return {"codegen": codegen, "ctfe": ctfe, "foreign": foreign}


def residual(o3_cov: dict, o3_flips: dict, o0_cov: dict, o0_flips: dict) -> dict:
    """The bodies that flip at `-O0` and not at `-O3`, attributed by marker class.

    The join is by `def_path` because `def_index` is NOT stable across two
    cfg-differing compiles (`docs/CRYSTAL_STATUS.md` §7 (a2)); within one compile
    the join to the coverage row is by `def_index`, which is.

    A body that flips at `-O0` and not at `-O3` is not automatically the marker
    gate's doing, so the attribution is measured rather than assumed: each such
    body is reported with its `-O3` `derived_mir` verdict and marker class, and
    the summary counts how many are `agreed & !markers_exact` — the signature of
    a marker refusal — versus how many are something else.
    """
    def index(cov):
        return {int(b["def_index"]): b for b in cov.get("bodies", [])}

    def names(cov_index, idxs):
        got = collections.Counter()
        missing = 0
        for i in idxs:
            row = cov_index.get(i)
            if row is None:
                missing += 1
            else:
                got[row["def_path"]] += 1
        return got, missing

    i3, i0 = index(o3_cov), index(o0_cov)
    by_path3 = {b["def_path"]: b for b in o3_cov.get("bodies", [])}
    out = {
        "schema_self": SCHEMA_RESIDUAL,
        "bodies_o3": o3_cov.get("totals", {}).get("bodies"),
        "bodies_o0": o0_cov.get("totals", {}).get("bodies"),
        "lanes": {},
        "residual_rows": [],
    }
    total_extra = 0
    attributed = 0
    cls_counts = collections.Counter()
    for lane in ("codegen", "ctfe"):
        n3, miss3 = names(i3, o3_flips[lane])
        n0, miss0 = names(i0, o0_flips[lane])
        extra = n0 - n3
        lost = n3 - n0
        out["lanes"][lane] = {
            "o3_events": len(o3_flips[lane]),
            "o0_events": len(o0_flips[lane]),
            "unjoinable_o3": miss3,
            "unjoinable_o0": miss0,
            "extra_at_o0": sum(extra.values()),
            "lost_at_o0": sum(lost.values()),
            "lost_names": sorted(lost.elements()),
        }
        for name, n in sorted(extra.items()):
            row = by_path3.get(name)
            dm = ((row or {}).get("differentials") or {}).get("derived_mir") or {}
            entry = classify(dm)
            marker_refusal = (dm.get("verdict") == "agreed"
                              and not dm.get("markers_exact"))
            total_extra += n
            attributed += n if marker_refusal else 0
            cls_counts[entry["class"]] += n
            out["residual_rows"].append({
                "lane": lane,
                "def_path": name,
                "events": n,
                "o3_verdict": dm.get("verdict"),
                "o3_markers_exact": bool(dm.get("markers_exact")),
                "marker_class": entry["class"],
                "derived_lines": entry["derived_lines"],
                "built_lines_min": entry["built_lines_min"],
                "is_marker_refusal": marker_refusal,
                "markers_detail": (dm.get("markers_detail") or "")[:200],
            })
    out["summary"] = {
        "residual_events": total_extra,
        "residual_attributed_to_marker_gate": attributed,
        "residual_unattributed": total_extra - attributed,
        "residual_by_marker_class": dict(cls_counts),
        "ceiling_codegen": [out["lanes"]["codegen"]["o3_events"],
                            out["lanes"]["codegen"]["o0_events"]],
        "ceiling_total": [out["lanes"]["codegen"]["o3_events"] + out["lanes"]["ctfe"]["o3_events"],
                          out["lanes"]["codegen"]["o0_events"] + out["lanes"]["ctfe"]["o0_events"]],
    }
    return out


# ---------------------------------------------------------------------------
def selftest() -> int:
    fails: list[str] = []

    def check(name: str, cond: bool) -> None:
        if not cond:
            fails.append(name)

    def cls(detail, exact):
        return classify({"markers_exact": exact, "markers_detail": detail})

    # -- the split the whole file exists for ------------------------------
    v = cls("0 marker line(s) identical", True)
    check("empty-vs-empty is exact-vacuous", v["class"] == "exact-vacuous")
    check("a vacuous row is NOT an error", v["markers_exact"] is True)
    check("a vacuous row's counts are MEASURED zeros, not nulls",
          v["built_lines"] == 0 and v["derived_lines"] == 0)
    n = cls("21 marker line(s) identical", True)
    check("21 lines is exact-nonvacuous", n["class"] == "exact-nonvacuous")
    check("nonvacuous carries both counts", n["built_lines"] == n["derived_lines"] == 21)
    check("nonvacuous is not vacuous", n["vacuous"] is False)

    # THE MUTATION §4c-i validates against: 21 -> 0 with `markers_exact` still
    # true. The boolean cannot see it; the class must.
    check("the 21 -> 0 mutation changes CLASS", n["class"] != v["class"])
    check("the 21 -> 0 mutation changes LINES", n["built_lines"] != v["built_lines"])

    # -- the refused shapes ------------------------------------------------
    d = cls("markers differ: line 0: built `mk b0.0:live s0:bool` vs derived `<end>`", False)
    check("derived <end> is differ-derived-empty", d["class"] == "differ-derived-empty")
    check("derived <end> at line 0 DETERMINES derived_lines = 0",
          d["derived_lines"] == 0)
    check("derived <end> leaves built_lines unknown", d["built_lines"] is None)
    check("derived <end> gives built a lower bound", d["built_lines_min"] == 1)
    check("nothing agreed before a line-0 divergence", d["agreed_lines"] == 0)

    b = cls("markers differ: line 3: built `<end>` vs derived `mk b1.0:dead s2:u8`", False)
    check("built <end> is differ-built-empty", b["class"] == "differ-built-empty")
    check("built <end> at line 3 determines built_lines = 3", b["built_lines"] == 3)
    check("built <end> leaves derived unknown", b["derived_lines"] is None)
    check("3 marker lines agreed before the divergence", b["agreed_lines"] == 3)

    c = cls("markers differ: line 2: built `mk b0.0:live s0:u8` vs derived `mk b0.0:live s0:u16`",
            False)
    check("two concrete lines is differ-content", c["class"] == "differ-content")
    check("content divergence determines NEITHER count",
          c["built_lines"] is None and c["derived_lines"] is None)
    check("content divergence bounds both", c["built_lines_min"] == c["derived_lines_min"] == 3)

    # a payload containing the separator text must not mis-split
    nasty = ("markers differ: line 1: built `mk b0.0:live s0:opaque:Ref { name: \"` vs derived `\" }`"
             " vs derived `<end>`")
    p = cls(nasty, False)
    check("a payload containing the separator still splits on the LAST one",
          p["class"] == "differ-derived-empty" and p["derived_lines"] == 1)

    # -- the shapes that must NOT mint a number ----------------------------
    ch = cls("marker channel(built): storage marker in unwalked block 8 (cleanup/dead code)", False)
    check("channel skip is its own class", ch["class"] == "channel-skip")
    check("channel skip mints no counts",
          ch["built_lines"] is None and ch["derived_lines"] is None
          and ch["agreed_lines"] is None)
    nc = cls("", False)
    check("no detail is not-compared", nc["class"] == "not-compared")
    check("not-compared mints no counts", nc["built_lines"] is None)
    check("an absent derived_mir is not-compared", classify(None)["class"] == "not-compared")
    for junk in ("canonical forms differ (no line-level diff?)",
                 "markers differ: line X: built `a` vs derived `b`",
                 "markers differ: line 1: built `a` vs derived b",
                 "7 marker lines identical"):
        check(f"unreadable detail {junk[:24]!r} is unparseable",
              cls(junk, junk.startswith("7"))["class"] == "unparseable")
    check("markers_exact with an unreadable detail is NOT counted as evidence",
          cls("who knows", True)["built_lines"] is None)

    # -- the ledger aggregate ---------------------------------------------
    cov = {
        "crate": "clean_kernel",
        "totals": {"bodies": 5},
        "bodies": [
            {"def_path": "a", "def_index": 1,
             "differentials": {"derived_mir": {"markers_exact": True,
                                               "markers_detail": "21 marker line(s) identical"}}},
            {"def_path": "b", "def_index": 2,
             "differentials": {"derived_mir": {"markers_exact": True,
                                               "markers_detail": "2 marker line(s) identical"}}},
            {"def_path": "c", "def_index": 3,
             "differentials": {"derived_mir": {"markers_exact": True,
                                               "markers_detail": "0 marker line(s) identical"}}},
            {"def_path": "d", "def_index": 4,
             "differentials": {"derived_mir": {
                 "markers_exact": False,
                 "markers_detail": "markers differ: line 4: built `x` vs derived `<end>`"}}},
            {"def_path": "e", "def_index": 5, "differentials": {"derived_mir": {}}},
        ],
    }
    led = ledger(cov)
    t = led["totals"]
    check("ledger counts markers_exact", t["markers_exact"] == 3)
    check("ledger splits vacuity", (t["markers_exact_vacuous"],
                                    t["markers_exact_nonvacuous"]) == (1, 2))
    check("ledger sums marker lines", t["markers_lines_total"] == 23)
    check("ledger counts the refused prefix", t["markers_agreed_prefix_lines"] == 4)
    check("ledger reports the vacuous fraction",
          abs(t["vacuous_fraction_of_exact"] - 1 / 3) < 1e-5)
    # `d` (built unknown) and `e` (never compared) — the two rows whose counts
    # the artifact does not determine. `c` is a MEASURED (0, 0), not an absence.
    check("ledger counts what the producer did not record",
          t["not_recorded_by_producer"] == 2)
    check("ledger emits one row per body", len(led["rows"]) == 5)
    check("every ledger row carries a class",
          all(r["class"] in CLASSES for r in led["rows"]))

    # -- the residual ------------------------------------------------------
    def cov_of(paths):
        return {"crate": "clean_kernel", "totals": {"bodies": len(paths)},
                "bodies": [{"def_path": p, "def_index": i,
                            "differentials": {"derived_mir": dm}}
                           for i, (p, dm) in enumerate(paths.items(), start=1)]}
    refused = {"verdict": "agreed", "markers_exact": False,
               "markers_detail": "markers differ: line 0: built `mk b0.0:live s0:bool` "
                                 "vs derived `<end>`"}
    okrow = {"verdict": "agreed", "markers_exact": True,
             "markers_detail": "0 marker line(s) identical"}
    o3 = cov_of({"p": okrow, "q": refused})
    o0 = cov_of({"p": okrow, "q": refused})
    res = residual(o3, {"codegen": [1], "ctfe": []},
                   o0, {"codegen": [1, 2], "ctfe": []})
    s = res["summary"]
    check("residual is the O0-minus-O3 set", s["residual_events"] == 1)
    check("residual attributes to the marker gate when the row says so",
          s["residual_attributed_to_marker_gate"] == 1)
    check("residual names the body", res["residual_rows"][0]["def_path"] == "q")
    check("residual classes the body", res["residual_rows"][0]["marker_class"]
          == "differ-derived-empty")
    check("residual prints the ceiling", s["ceiling_codegen"] == [1, 2])
    # a body that flips at O0 for a NON-marker reason must not be attributed
    o3b = cov_of({"p": okrow, "r": {"verdict": "unsupported", "markers_exact": False,
                                    "markers_detail": ""}})
    o0b = cov_of({"p": okrow, "r": {"verdict": "unsupported", "markers_exact": False,
                                    "markers_detail": ""}})
    res2 = residual(o3b, {"codegen": [1], "ctfe": []},
                    o0b, {"codegen": [1, 2], "ctfe": []})
    check("a non-marker gain is counted but NOT attributed",
          res2["summary"]["residual_events"] == 1
          and res2["summary"]["residual_attributed_to_marker_gate"] == 0)

    # -- the flip-log reader ----------------------------------------------
    check("flip regex matches a codegen event",
          FLIP_RE.search("trust-ir-flip: compiled from trust-ir, did=DefId(0:9 ~ clean_kernel"
                         "[4676]::x), lineage=sha256:aa") is not None)

    check("class table is closed", len(set(CLASSES)) == len(CLASSES))

    for name in fails:
        print(f"SELFTEST FAIL: {name}", file=sys.stderr)
    print(f"markers selftest: {len(fails)} failure(s)")
    return 1 if fails else 0


# ---------------------------------------------------------------------------
def _render_ledger(led: dict, top: int, stream) -> None:
    t = led["totals"]
    print(f"crate {led['crate']}  bodies {led['bodies']}", file=stream)
    width = max(len(c) for c in CLASSES)
    for c in CLASSES:
        n = led["classes"][c]
        if n:
            print(f"  {c:<{width}}  {n:>7}", file=stream)
    print("", file=stream)
    print(f"  markers_exact                {t['markers_exact']:>7}", file=stream)
    print(f"    vacuous (two empty seqs)   {t['markers_exact_vacuous']:>7}"
          f"   {'' if t['vacuous_fraction_of_exact'] is None else format(100 * t['vacuous_fraction_of_exact'], '.1f') + '%'}",
          file=stream)
    print(f"    NON-vacuous                {t['markers_exact_nonvacuous']:>7}", file=stream)
    print(f"  marker LINES behind them     {t['markers_lines_total']:>7}", file=stream)
    print(f"  refused rows                 {t['markers_differ']:>7}"
          f"   (derived-empty {t['markers_differ_derived_empty']},"
          f" built-empty {t['markers_differ_built_empty']},"
          f" content {t['markers_differ_content']})", file=stream)
    print(f"  marker lines agreed on them  {t['markers_agreed_prefix_lines']:>7}", file=stream)
    print(f"  channel skips                {t['markers_channel_skipped']:>7}", file=stream)
    print(f"  counts the producer omits    {t['not_recorded_by_producer']:>7}", file=stream)
    if t["markers_unparseable"]:
        print(f"  UNPARSEABLE                  {t['markers_unparseable']:>7}", file=stream)
    rich = sorted((r for r in led["rows"] if r["class"] == "exact-nonvacuous"),
                  key=lambda r: (-r["built_lines"], r["def_path"]))
    if rich and top:
        print("", file=stream)
        print(f"  the {min(top, len(rich))} richest non-vacuous rows "
              f"(of {len(rich)}) — this is ALL the marker evidence there is:",
              file=stream)
        for r in rich[:top]:
            print(f"    {r['built_lines']:>4}  {r['def_path']}", file=stream)


def _render_residual(res: dict, stream) -> None:
    s = res["summary"]
    print(f"bodies: O3 {res['bodies_o3']}  O0 {res['bodies_o0']}", file=stream)
    for lane, d in res["lanes"].items():
        print(f"  {lane:<8} O3 {d['o3_events']:>4}  ->  O0 {d['o0_events']:>4}"
              f"   extra {d['extra_at_o0']}   lost {d['lost_at_o0']}"
              f"   unjoinable {d['unjoinable_o3']}/{d['unjoinable_o0']}", file=stream)
    print("", file=stream)
    print(f"  residual events                    {s['residual_events']:>4}", file=stream)
    print(f"    attributed to the marker gate    {s['residual_attributed_to_marker_gate']:>4}",
          file=stream)
    print(f"    NOT attributed                   {s['residual_unattributed']:>4}", file=stream)
    print(f"  by marker class: {s['residual_by_marker_class']}", file=stream)
    print(f"  ceiling codegen {s['ceiling_codegen'][0]} -> {s['ceiling_codegen'][1]}"
          f"   total {s['ceiling_total'][0]} -> {s['ceiling_total'][1]}", file=stream)
    print("", file=stream)
    for r in res["residual_rows"]:
        mark = " " if r["is_marker_refusal"] else "?"
        print(f"  {mark}{r['lane']:<8} {r['marker_class']:<21} {r['def_path']}", file=stream)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_led = sub.add_parser("ledger")
    p_led.add_argument("--coverage", required=True)
    p_led.add_argument("--out")
    p_led.add_argument("--top", type=int, default=20)

    p_res = sub.add_parser("residual")
    for flag in ("--o3", "--o3-log", "--o0", "--o0-log"):
        p_res.add_argument(flag, required=True)
    p_res.add_argument("--out")

    sub.add_parser("selftest")
    args = parser.parse_args()

    if args.cmd == "selftest":
        return selftest()

    if args.cmd == "ledger":
        with open(args.coverage, encoding="utf-8") as handle:
            led = ledger(json.load(handle))
        _render_ledger(led, args.top, sys.stdout)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as handle:
                handle.write(json.dumps(led, indent=1) + "\n")
        return 0

    with open(args.o3, encoding="utf-8") as handle:
        o3 = json.load(handle)
    with open(args.o0, encoding="utf-8") as handle:
        o0 = json.load(handle)
    res = residual(o3, read_flips(args.o3_log), o0, read_flips(args.o0_log))
    _render_residual(res, sys.stdout)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as handle:
            handle.write(json.dumps(res, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
