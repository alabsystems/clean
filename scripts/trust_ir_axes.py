#!/usr/bin/env python3
"""The axis extractor and ratchet comparator for `scripts/trust_ir_build.sh`.

WHY THIS FILE EXISTS
====================
The trust-ir coverage artifact (`<crate>.coverage.json`, schema
`trust.thir-lower.crate-module.coverage.v2`) carries ~30 distinct per-body and
per-crate axes. Until 2026-08-15 the committed ratchet watched exactly four of
them -- `lowered`, `spliced`, `flip_events`, `mismatch` -- and that gap has now
bitten three times:

  1. `lowered` / `spliced` were once not columns in the review harness, which
     hid three stub collapses.
  2. `markers_class` was not an axis, which hid a fourth.
  3. trust `80c7e86f55` (2026-08-13) turned 38 `agreed` verdicts into `not-run`
     -- 36 interpreter + 2 seam -- and dropped the CTFE flip lane from 32/32
     semantically backed to 11/32. It went unnoticed for two days. NONE of the
     four watched axes moved: `lowered` 9067, `spliced` 7571, `derived_mir`
     agreed 1542, mismatch 0, flip events 209 were BIT-IDENTICAL across the
     regression. See `reports/crystal-38-lost-agreed-bisect-2026-08-15.md`.

So the ratchet's blind spot was not an oversight in one axis: it was that
nobody had ever written the axis list down. This file writes it down. Every
axis the artifact carries appears in `AXES` below with an explicit direction --
including the ones deliberately NOT gated, each with the measured reason.

DIRECTIONS
----------
  grow    the value may only increase   (evidence axes)
  shrink  the value may only decrease   (alarm axes)
  pin     the value may not change      (identity / capability markers)
  record  measured and printed, never gated -- with a stated reason

A gated axis missing from the baseline is RED ("unbaselined"), never a silent
pass. That is the whole point: an unwatched axis is the defect.

USAGE
-----
  trust_ir_axes.py measure  --coverage COV.json --log BUILD.log [--out M.json]
  trust_ir_axes.py check    --measured M.json --baseline B.json [--bodies S.json]
  trust_ir_axes.py tighten  --measured M.json --baseline B.json [--bodies S.json]
  trust_ir_axes.py table                     # print the axis inventory
  trust_ir_axes.py selftest                  # comparator unit tests, no build

`check` exits 0 when every gated axis holds, 1 otherwise. It evaluates EVERY
axis and reports them all before failing, so a standing red on one axis can
never mask another -- which matters right now, because `lowered`/`spliced` are
red at HEAD by established COMPILER DRIFT
(`reports/trust-ir-ratchet-verdict-2026-08-13.md`) and that red is deliberately
left for the owner to settle.
"""

from __future__ import annotations

import argparse
import collections
import datetime
import json
import re
import sys

SCHEMA_MEASURED = "clean.trust_ir_build.measured.v1"
SCHEMA_BODIES = "clean.trust_ir_build.agreed_bodies.v1"

# ---------------------------------------------------------------------------
# THE AXIS INVENTORY.
#
# (key, direction, source, why)
#
# `source` is where the number comes from, so a reader can check it by hand:
#   totals   -- coverage.json `totals.*`
#   header   -- coverage.json top-level identity / capability fields
#   bodies   -- an aggregate over coverage.json `bodies[]`
#   log      -- the trustc flip log (`RUSTC_LOG=...trust_ir_flip=info`)
#   join     -- flip log joined to `bodies[]` by `def_index`
# ---------------------------------------------------------------------------
AXES: list[tuple[str, str, str, str]] = [
    # -- identity and capability -------------------------------------------
    ("schema", "pin", "header",
     "a schema bump changes what every other axis means; move it deliberately"),
    ("crate", "pin", "header",
     "the subject unit; a change here means the wrapper attached to the wrong crate"),
    ("direct_obligation_capability", "pin", "header",
     "the artifact's trust marker (`structural-parity-only-v1`)"),
    ("proof_authority", "pin", "header",
     "whether the artifact may be read as source-proof authority; must not drift silently"),
    ("native_verification_requests", "pin", "header",
     "whether the producer emits direct native verification requests"),

    # -- crate size (recorded, not gated) ----------------------------------
    ("bodies", "record", "totals",
     "crate size: falls whenever clean-kernel deletes code, so it has no monotone direction"),
    ("declarations", "record", "totals", "crate size"),
    ("initializer_bodies", "record", "totals", "crate size"),
    ("instr_count", "record", "totals", "crate size"),
    ("symbolic", "record", "totals",
     "lowered-but-symbolic; up can mean more reach OR more imprecision -- no agreed direction"),
    ("unsupported", "record", "totals",
     "sum of per-body unsupported counts; grows with the crate, so a rise is not a regression"),
    ("calls_resolved", "record", "totals", "crate size"),
    ("calls_extern_decls", "record", "totals", "crate size"),
    ("calls_unresolved", "record", "totals",
     "grows with the crate; the meaningful signal is per-body, not the sum"),

    # -- lowering reach (pre-existing gates) --------------------------------
    ("lowered", "grow", "totals",
     "PRE-EXISTING. Bodies THIR->trust-ir lowering accepted"),
    ("spliced", "grow", "totals",
     "PRE-EXISTING. Bodies spliced into the assembled module"),

    # -- the structural differential ---------------------------------------
    ("derived_mir_agreed", "grow", "bodies",
     "NEW GATE (was recorded, never checked). Structural derived-MIR agreement"),
    ("mismatch", "shrink", "bodies",
     "PRE-EXISTING. derived-MIR mismatch: a real divergence alarm"),
    ("derived_mir_unsupported", "record", "bodies",
     "complement of agreed+mismatch over a moving body count"),
    ("markers_exact", "record", "bodies",
     "MEASURED VACUOUS: 1,057 of 1,084 carry `0 marker line(s) identical`. "
     "A gain here is NOT a fidelity gain, so gating it would be a false gate"),
    ("markers_exact_nonvacuous", "grow", "bodies",
     "NEW GATE. The 27 rows whose marker agreement is over a NON-EMPTY marker set -- "
     "the part of `markers_exact` that carries content"),

    # -- the semantic differential: THE HOLE THAT LET 38 VERDICTS VANISH ----
    ("interpreter_agreed", "grow", "bodies",
     "NEW GATE. Bodies where the reference interpreter agreed on sampled inputs. "
     "This is the axis 80c7e86f55 moved 606 -> 570 unnoticed"),
    ("interpreter_mismatch", "shrink", "bodies",
     "NEW GATE. A real THIR divergence alarm; must never grow"),
    ("interpreter_samples_total", "grow", "bodies",
     "NEW GATE. Evidence DEPTH: `agreed` on 1 sample is weaker than on 25, and a "
     "count-only gate cannot see the difference. Size-coupled -- see the honesty note"),
    ("interpreter_not_run", "record", "bodies",
     "complement; the informative form is the reason histogram printed on a red"),
    ("interpreter_unsupported", "record", "bodies", "complement"),

    ("seam_agreed", "grow", "bodies",
     "NEW GATE. Call-bearing bodies resolved at crate finalize. 80c7e86f55 moved this 2 -> 0"),
    ("seam_mismatch", "shrink", "bodies", "NEW GATE. Divergence alarm on the seam channel"),
    ("seam_samples_total", "grow", "bodies", "NEW GATE. Evidence depth on the seam channel"),
    ("seam_resolved", "record", "bodies", "size-coupled: how many bodies deferred to the seam at all"),
    ("seam_not_run", "record", "bodies", "complement"),

    # -- lineage -----------------------------------------------------------
    ("lineage_rows", "grow", "bodies",
     "NEW GATE (was recorded, never checked). A flip event CANNOT fire without a "
     "lineage digest, so lineage coverage is a precondition of the flip lane"),
    ("func_id_rows", "record", "bodies", "assembled-module addresses; an address is not a fidelity axis"),

    # -- the flip lane -----------------------------------------------------
    ("flip_events_total", "grow", "log", "PRE-EXISTING. Bodies whose shipped code came from trust-ir"),
    ("flip_events_codegen", "grow", "log",
     "NEW GATE (was recorded, never checked). The codegen half, gated on its own so a "
     "CTFE gain cannot mask a codegen loss inside the total"),
    ("flip_events_ctfe", "grow", "log", "NEW GATE (was recorded, never checked). The CTFE half"),
    ("flip_backed_total", "grow", "join",
     "NEW GATE. Flips whose body ALSO carries a live interpreter or seam `agreed` verdict"),
    ("flip_backed_codegen", "grow", "join", "NEW GATE. The codegen half of the backed count"),
    ("flip_backed_ctfe", "grow", "join",
     "NEW GATE. The CTFE half. 80c7e86f55 moved this 32 -> 11 -- two thirds of the "
     "CTFE flip lane lost its semantic backing while the flip count never moved"),
]

AXIS_BY_KEY = {a[0]: a for a in AXES}
GATED = {k for k, d, _s, _w in AXES if d != "record"}

# Backward-compatible baseline key spellings: the committed baseline predates
# this file and named three axes differently. Reading through this map is what
# lets the pre-existing gates keep their EXACT recorded values -- in particular
# `lowered` 9068 / `spliced` 7572, which are red at HEAD and must NOT be moved.
LEGACY_KEYS = {
    "flip_events_total": ("flip_events_total",),
    "flip_events_codegen": ("flip_events_codegen",),
    "flip_events_ctfe": ("flip_events_ctfe",),
    "derived_mir_agreed": ("derived_mir_agreed",),
}

FLIP_RE = re.compile(
    r"trust-ir-flip: (?P<ctfe>CTFE )?compiled from trust-ir, "
    r"did=DefId\((?P<krate>\d+):(?P<index>\d+) "
)


# ---------------------------------------------------------------------------
# measure
# ---------------------------------------------------------------------------
def _verdict(body: dict, channel: str) -> str:
    """The verdict marker for a channel, or `not-applicable` for an absent seam."""
    diffs = body["differentials"]
    if channel == "seam":
        seam = diffs.get("seam") or {}
        if seam.get("state") != "resolved":
            return "not-applicable"
        return seam.get("verdict", "not-applicable")
    return diffs[channel]["verdict"]


def _samples(body: dict, channel: str) -> int:
    diffs = body["differentials"]
    if channel == "seam":
        seam = diffs.get("seam") or {}
        return int(seam.get("samples", 0)) if seam.get("state") == "resolved" else 0
    return int(diffs[channel].get("samples", 0))


def measure(coverage_path: str, log_path: str) -> dict:
    with open(coverage_path, encoding="utf-8") as handle:
        cov = json.load(handle)
    rows = cov["bodies"]
    totals = cov["totals"]
    by_index: dict[int, dict] = {}
    for row in rows:
        by_index[int(row["def_index"])] = row

    def count(channel: str, verdict: str) -> int:
        return sum(1 for r in rows if _verdict(r, channel) == verdict)

    markers = [r for r in rows if r["differentials"]["derived_mir"].get("markers_exact")]
    # A marker agreement over an EMPTY marker set proves nothing. The producer
    # spells that case `0 marker line(s) identical`; 1,057 of 1,084 rows are
    # exactly that, which is why `markers_exact` itself is not a gated axis.
    vacuous = [
        r for r in markers
        if r["differentials"]["derived_mir"].get("markers_detail", "").startswith("0 marker line")
    ]

    # -- flip log -> def_index, then join to coverage rows ------------------
    codegen: list[int] = []
    ctfe: list[int] = []
    foreign = 0
    with open(log_path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if "compiled from trust-ir" not in line:
                continue
            match = FLIP_RE.search(line)
            if match is None:
                # An event we cannot attribute is worse than none: it is counted
                # as foreign so the caller's attribution invariant fails closed.
                foreign += 1
                continue
            if "clean_kernel" not in line:
                foreign += 1
                continue
            (ctfe if match.group("ctfe") else codegen).append(int(match.group("index")))

    def backed(indexes: list[int]) -> tuple[int, int, list[str]]:
        """(backed, unjoinable, backed def_paths) for a set of flip def_indexes."""
        hits, missing, names = 0, 0, []
        for index in indexes:
            row = by_index.get(index)
            if row is None:
                missing += 1
                continue
            if _verdict(row, "interpreter") == "agreed" or _verdict(row, "seam") == "agreed":
                hits += 1
                names.append(row["def_path"])
        return hits, missing, names

    cg_backed, cg_missing, cg_names = backed(codegen)
    ct_backed, ct_missing, ct_names = backed(ctfe)

    measured = {
        "schema": cov.get("schema"),
        "crate": cov.get("crate"),
        "direct_obligation_capability": cov.get("direct_obligation_capability"),
        "proof_authority": cov.get("proof_authority"),
        "native_verification_requests": cov.get("native_verification_requests"),

        "bodies": totals["bodies"],
        "lowered": totals["lowered"],
        "symbolic": totals["symbolic"],
        "spliced": totals["spliced"],
        "declarations": totals["declarations"],
        "initializer_bodies": totals["initializer_bodies"],
        "instr_count": totals["instr_count"],
        "unsupported": totals["unsupported"],
        "calls_resolved": totals["calls"]["resolved"],
        "calls_extern_decls": totals["calls"]["extern_decls"],
        "calls_unresolved": totals["calls"]["unresolved"],

        "interpreter_agreed": count("interpreter", "agreed"),
        "interpreter_mismatch": count("interpreter", "mismatch"),
        "interpreter_not_run": count("interpreter", "not-run"),
        "interpreter_unsupported": count("interpreter", "unsupported"),
        "interpreter_samples_total": sum(_samples(r, "interpreter") for r in rows),

        "seam_agreed": count("seam", "agreed"),
        "seam_mismatch": count("seam", "mismatch"),
        "seam_not_run": count("seam", "not-run"),
        "seam_resolved": sum(1 for r in rows if _verdict(r, "seam") != "not-applicable"),
        "seam_samples_total": sum(_samples(r, "seam") for r in rows),

        "derived_mir_agreed": count("derived_mir", "agreed"),
        "mismatch": count("derived_mir", "mismatch"),
        "derived_mir_unsupported": count("derived_mir", "unsupported"),
        "markers_exact": len(markers),
        "markers_exact_nonvacuous": len(markers) - len(vacuous),

        "lineage_rows": sum(1 for r in rows if r.get("lineage")),
        "func_id_rows": sum(1 for r in rows if r.get("func_id") is not None),

        "flip_events_total": len(codegen) + len(ctfe),
        "flip_events_codegen": len(codegen),
        "flip_events_ctfe": len(ctfe),
        "flip_backed_total": cg_backed + ct_backed,
        "flip_backed_codegen": cg_backed,
        "flip_backed_ctfe": ct_backed,
    }

    invariants = {
        "foreign_flip_events": foreign,
        "flip_events_unjoinable": cg_missing + ct_missing,
    }

    sets = {
        "interpreter_agreed": sorted(
            r["def_path"] for r in rows if _verdict(r, "interpreter") == "agreed"
        ),
        "seam_agreed": sorted(r["def_path"] for r in rows if _verdict(r, "seam") == "agreed"),
        "flip_backed": sorted(cg_names + ct_names),
    }

    # Reason buckets for the `not-run` population, keyed by the leading clause of
    # the detail string. Diagnostic only -- printed on a red so the next reader
    # gets the attribution the 2026-08-13 loss did not have. Never gated: the
    # detail text is prose, not a contract.
    buckets = collections.Counter(
        r["differentials"]["interpreter"]["detail"].split(";")[0][:90]
        for r in rows
        if _verdict(r, "interpreter") == "not-run"
    )

    return {
        "schema_self": SCHEMA_MEASURED,
        "measured": measured,
        "invariants": invariants,
        "sets": sets,
        "not_run_reasons": buckets.most_common(6),
    }


# ---------------------------------------------------------------------------
# check / tighten
# ---------------------------------------------------------------------------
def _baseline_value(baseline: dict, key: str):
    measured = baseline.get("measured", {})
    if key in measured:
        return measured[key]
    for alias in LEGACY_KEYS.get(key, ()):  # pragma: no cover - identity today
        if alias in measured:
            return measured[alias]
    return None


def compare(measured: dict, baseline: dict) -> tuple[list[dict], list[str]]:
    """Evaluate EVERY axis. Returns (rows, failures). Never short-circuits."""
    rows: list[dict] = []
    failures: list[str] = []
    now_all = measured["measured"]
    for key, direction, source, why in AXES:
        now = now_all.get(key)
        was = _baseline_value(baseline, key)
        if direction == "record":
            rows.append({"axis": key, "dir": direction, "was": was, "now": now,
                         "state": "RECORD", "source": source, "why": why})
            continue
        if was is None:
            rows.append({"axis": key, "dir": direction, "was": None, "now": now,
                         "state": "UNBASELINED", "source": source, "why": why})
            failures.append(
                f"{key} is UNBASELINED — a gated axis with no baseline is exactly the "
                f"blind spot this ratchet exists to close; seed it with --tighten"
            )
            continue
        if direction == "pin":
            ok = now == was
        elif direction == "grow":
            ok = now >= was
        elif direction == "shrink":
            ok = now <= was
        else:  # pragma: no cover - table is closed
            raise ValueError(f"unknown direction {direction!r} for axis {key!r}")
        rows.append({"axis": key, "dir": direction, "was": was, "now": now,
                     "state": "ok" if ok else "RED", "source": source, "why": why})
        if not ok:
            verb = {"pin": "CHANGED", "grow": "REGRESSED", "shrink": "GREW"}[direction]
            failures.append(f"{key} {verb}: {was} -> {now}   [{why}]")
    return rows, failures


def _lost(baseline_names: list[str], now_names: list[str]) -> list[str]:
    was = collections.Counter(baseline_names)
    now = collections.Counter(now_names)
    lost: list[str] = []
    for name, n in sorted((was - now).items()):
        lost.extend([name] * n)
    return lost


def render(rows: list[dict], measured: dict, bodies: dict | None,
           failures: list[str], stream) -> None:
    width = max(len(r["axis"]) for r in rows)
    print(f"{'':2}{'axis':<{width}}  dir     source   baseline -> measured", file=stream)
    print("-" * (width + 46), file=stream)
    for row in rows:
        was = "—" if row["was"] is None else row["was"]
        mark = {"ok": "  ", "RECORD": "· ", "RED": "!!", "UNBASELINED": "??"}[row["state"]]
        print(f"{mark}{row['axis']:<{width}}  {row['dir']:<6}  {row['source']:<7}  "
              f"{was} -> {row['now']}", file=stream)

    inv = measured["invariants"]
    print("", file=stream)
    print(f"invariants: foreign_flip_events={inv['foreign_flip_events']}  "
          f"flip_events_unjoinable={inv['flip_events_unjoinable']}", file=stream)

    if not failures:
        return

    print("", file=stream)
    for line in failures:
        print(f"RED: {line}", file=stream)

    # Attribution: name the bodies, not just the delta.
    if bodies:
        for channel in ("interpreter_agreed", "seam_agreed", "flip_backed"):
            was = bodies.get(channel)
            if was is None:
                continue
            lost = _lost(was, measured["sets"].get(channel, []))
            if not lost:
                continue
            print("", file=stream)
            print(f"  {len(lost)} body/bodies LOST `{channel}` since the baseline set:",
                  file=stream)
            for name in lost[:15]:
                print(f"    - {name}", file=stream)
            if len(lost) > 15:
                print(f"    … and {len(lost) - 15} more", file=stream)
    else:
        print("  (no agreed-body sidecar: scalar deltas only, no body names)", file=stream)

    if any("interpreter" in f for f in failures):
        print("", file=stream)
        print("  interpreter `not-run` reasons in THIS run (top 6):", file=stream)
        for reason, n in measured["not_run_reasons"]:
            print(f"    {n:>6}  {reason}", file=stream)


def tighten(measured: dict, baseline: dict) -> tuple[dict, list[str], set[str]]:
    """Seed missing gated axes and raise improving ones. NEVER loosens.

    This is the mode that makes new axes usable while an OLD axis is legitimately
    red: it seeds every unbaselined axis from the measurement and moves an
    existing baseline only in the strictly-stricter direction. An axis that
    regressed keeps its old baseline and therefore stays RED. It is arithmetically
    incapable of making a failing gate pass.
    """
    now_all = measured["measured"]
    changes: list[str] = []
    doc = dict(baseline)
    values = dict(doc.get("measured", {}))
    # Per-axis provenance. A baseline is not taken all at once: an axis that is
    # legitimately red keeps a value measured under an OLDER compiler while the
    # rest move forward, and a reader who cannot see that will mis-attribute the
    # red. `lowered`/`spliced` are exactly that case today.
    stamped = dict(doc.get("axis_updated", {}))
    moved: set[str] = set()
    today = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
    for key, direction, _source, _why in AXES:
        if direction == "record":
            continue
        now = now_all.get(key)
        was = _baseline_value(baseline, key)
        if was is None:
            values[key] = now
            stamped[key] = today
            moved.add(key)
            changes.append(f"seed  {key} = {now}")
            continue
        if direction == "pin":
            continue  # a pin is neither better nor worse; move it with --update
        stricter = (now > was) if direction == "grow" else (now < was)
        if stricter:
            values[key] = now
            stamped[key] = today
            moved.add(key)
            changes.append(f"raise {key}: {was} -> {now}")
    doc["measured"] = values
    doc["axis_updated"] = stamped
    return doc, changes, moved


# ---------------------------------------------------------------------------
# selftest — the comparator, proved without a compiler
# ---------------------------------------------------------------------------
def selftest() -> int:
    fails: list[str] = []

    def check(name: str, cond: bool) -> None:
        if not cond:
            fails.append(name)

    base = {"measured": {k: 10 for k, d, _s, _w in AXES if d in ("grow", "shrink")}}
    base["measured"].update({
        "schema": "trust.thir-lower.crate-module.coverage.v2",
        "crate": "clean_kernel",
        "direct_obligation_capability": "structural-parity-only-v1",
        "proof_authority": False,
        "native_verification_requests": False,
    })
    now = {"measured": dict(base["measured"]), "invariants": {}, "sets": {}, "not_run_reasons": []}
    _rows, failures = compare(now, base)
    check("identical measurement is green", failures == [])

    # every `grow` axis alone must be able to go red
    for key, direction, _s, _w in AXES:
        if direction != "grow":
            continue
        bad = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
               "not_run_reasons": []}
        bad["measured"][key] = 9
        _rows, failures = compare(bad, base)
        check(f"grow axis {key} goes red alone", len(failures) == 1 and key in failures[0])

    for key, direction, _s, _w in AXES:
        if direction != "shrink":
            continue
        bad = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
               "not_run_reasons": []}
        bad["measured"][key] = 11
        _rows, failures = compare(bad, base)
        check(f"shrink axis {key} goes red alone", len(failures) == 1 and key in failures[0])

    # a missing gated key is RED, not a silent pass — the defect class itself
    holed = {"measured": {k: v for k, v in base["measured"].items()
                          if k != "interpreter_agreed"}}
    _rows, failures = compare(now, holed)
    check("unbaselined gated axis is red", any("UNBASELINED" in f for f in failures))

    # tighten cannot rescue a regression
    regressed = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
                 "not_run_reasons": []}
    regressed["measured"]["interpreter_agreed"] = 3
    doc, _changes, _moved = tighten(regressed, base)
    _rows, failures = compare(regressed, doc)
    check("tighten cannot make a regression pass",
          any("interpreter_agreed" in f for f in failures))

    # tighten does raise an improvement, and seeds a hole
    improved = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
                "not_run_reasons": []}
    improved["measured"]["interpreter_agreed"] = 42
    doc, _changes, _moved = tighten(improved, holed)
    check("tighten seeds and raises", doc["measured"]["interpreter_agreed"] == 42)

    # the body-set differ names what was lost, with multiplicity
    lost = _lost(["a", "b", "b", "c"], ["b", "c"])
    check("lost set is a multiset difference", lost == ["a", "b"])

    # the flip-log regex must actually match the emitted line shape
    line = (" INFO rustc_mir_transform::trust_ir_flip trust-ir-flip: CTFE compiled from "
            "trust-ir, did=DefId(0:721 ~ clean_kernel[4676]::cert::bundle::MAX), asserts=1, "
            "lineage=sha256:37a9, flipped_so_far=1")
    match = FLIP_RE.search(line)
    check("flip regex matches a CTFE event", match is not None and match.group("index") == "721")
    line_cg = line.replace("CTFE compiled", "compiled")
    match_cg = FLIP_RE.search(line_cg)
    check("flip regex matches a codegen event",
          match_cg is not None and match_cg.group("ctfe") is None)

    check("every axis has a direction", all(d in ("grow", "shrink", "pin", "record")
                                            for _k, d, _s, _w in AXES))
    check("axis keys are unique", len(AXIS_BY_KEY) == len(AXES))

    for name in fails:
        print(f"SELFTEST FAIL: {name}", file=sys.stderr)
    print(f"selftest: {len(fails)} failure(s) over {len(AXES)} axes")
    return 1 if fails else 0


# ---------------------------------------------------------------------------
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_measure = sub.add_parser("measure")
    p_measure.add_argument("--coverage", required=True)
    p_measure.add_argument("--log", required=True)
    p_measure.add_argument("--out")

    for name in ("check", "tighten"):
        p = sub.add_parser(name)
        p.add_argument("--measured", required=True)
        p.add_argument("--baseline", required=True)
        p.add_argument("--bodies")
        if name == "tighten":
            p.add_argument("--write", action="store_true")

    sub.add_parser("table")
    sub.add_parser("selftest")

    args = parser.parse_args()

    if args.cmd == "selftest":
        return selftest()

    if args.cmd == "table":
        width = max(len(a[0]) for a in AXES)
        for key, direction, source, why in AXES:
            print(f"{key:<{width}}  {direction:<6}  {source:<7}  {why}")
        gated = sum(1 for _k, d, _s, _w in AXES if d != "record")
        print(f"\n{len(AXES)} axes: {gated} gated, {len(AXES) - gated} recorded-not-gated")
        return 0

    if args.cmd == "measure":
        doc = measure(args.coverage, args.log)
        text = json.dumps(doc, indent=1, sort_keys=False) + "\n"
        if args.out:
            with open(args.out, "w", encoding="utf-8") as handle:
                handle.write(text)
        else:
            sys.stdout.write(text)
        return 0

    with open(args.measured, encoding="utf-8") as handle:
        measured = json.load(handle)
    with open(args.baseline, encoding="utf-8") as handle:
        baseline = json.load(handle)
    bodies = None
    if args.bodies:
        try:
            with open(args.bodies, encoding="utf-8") as handle:
                bodies = json.load(handle)
        except FileNotFoundError:
            bodies = None

    if args.cmd == "check":
        rows, failures = compare(measured, baseline)
        render(rows, measured, bodies, failures, sys.stdout)
        inv = measured["invariants"]
        if inv.get("flip_events_unjoinable"):
            print(f"RED: {inv['flip_events_unjoinable']} flip event(s) do not join to a "
                  f"coverage row by def_index — the backed counts are not trustworthy",
                  file=sys.stdout)
            failures = failures + ["flip_events_unjoinable"]
        return 1 if failures else 0

    doc, changes, moved = tighten(measured, baseline)
    doc["note"] = (
        "Monotonic baseline for scripts/trust_ir_build.sh. The direction of every axis is "
        "declared in scripts/trust_ir_axes.py::AXES (run `trust_ir_axes.py table`); a gated "
        "axis absent from this file is RED, not a silent pass. Counts are clean-kernel only: "
        "the wrapper attaches -Ztrust-ir-flip to the subject unit alone, and the script "
        "refuses any event that does not name clean_kernel."
    )
    doc["updated_utc_date"] = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
    if args.write:
        with open(args.baseline, "w", encoding="utf-8") as handle:
            handle.write(json.dumps(doc, indent=1) + "\n")
        if args.bodies:
            # The sidecar follows the SAME one-directional rule as the scalars it
            # explains. A channel whose scalar axis did not move (or moved the
            # wrong way) keeps its stored set: overwriting it from a regressed run
            # would erase the very names the red is supposed to print.
            channel_axis = {
                "interpreter_agreed": "interpreter_agreed",
                "seam_agreed": "seam_agreed",
                "flip_backed": "flip_backed_total",
            }
            merged = bodies if isinstance(bodies, dict) else {}
            out = {
                "schema": SCHEMA_BODIES,
                "note": ("The def_path multiset behind the gated `interpreter_agreed`, "
                         "`seam_agreed` and `flip_backed` counts. Diagnostic, not a gate: on a "
                         "red the ratchet names the bodies that were lost instead of only the "
                         "delta. def_path is not injective over bodies (closures and promoted "
                         "constants share names), so this is compared as a MULTISET. A channel "
                         "is rewritten only when its scalar axis was seeded or raised."),
                "updated_utc_date": doc["updated_utc_date"],
            }
            for channel, axis in channel_axis.items():
                if axis in moved or channel not in merged:
                    out[channel] = measured["sets"][channel]
                else:
                    out[channel] = merged[channel]
            with open(args.bodies, "w", encoding="utf-8") as handle:
                handle.write(json.dumps(out, indent=1) + "\n")
    for line in changes:
        print(line)
    print(f"tighten: {len(changes)} axis change(s)"
          + ("" if args.write else "  (dry run — pass --write)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
