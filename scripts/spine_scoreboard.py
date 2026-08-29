#!/usr/bin/env python3
"""G-SCORE v0 — the spine/lattice scoreboard.

Generates data/spine_scoreboard.json from committed producer artifacts and
enforces per-row ratchet directions against the committed baseline (the
generated file itself is the baseline once committed).

Program doc: designs/2026-08-22-spine-and-lattice-program.md, Track G (G-SCORE)
and §6. Quoting any row of the scoreboard from prose is a bug: read the
artifact.

Direction vocabulary
  up        monotone non-decreasing vs baseline
  down      monotone non-increasing vs baseline
  frozen    must equal baseline; re-base only via a dated re-measure that
            commits a new baseline (G-SPINE-SET rule for spine-set size)
  equal_11  absolute: value must equal 11 (the clean-verify axiom census)
  none      reported, not ratcheted (freshness/informational rows)

UNKNOWN is a first-class value, never 0. UNKNOWN never satisfies and never
violates a direction — it reports.

A row's direction is itself ratcheted: a direction that changes against the
committed baseline is a violation, not a silent re-base. R5 — gates are never
weakened to manufacture a green — applies to the direction column too.

Cross-checked denominators (fail closed, never round, never pick a side)
  Some producers report a fraction whose denominator is authoritative
  ELSEWHERE. Those denominators are re-derived here from the authority and
  compared:
    evalir     total=28 vs the pinned constructed-Inst census, derived from
               census.rs (EMITTED_INSTS) and eval_ir_syntax.rs (IRInst) by
               scripts/evalir_coverage.py's own parsers, which must agree
    verdict_io site_total=211 vs data/verdict_set.json
               partitions.b_io_bearing.io_site_total (the shared denominator
               the model's own derivation block pins itself to)
  On disagreement the DEPENDENT rows go UNKNOWN carrying both numbers, and a
  `*.denominator_disagreements` row (direction down, baseline 0) turns the
  ratchet RED. The scoreboard withholds a number it cannot stand behind; it
  never emits an averaged, preferred, or rounded one.

Data-driven row families (parity tiers and their guards, contracts) are
emitted from the producer artifact. When that artifact is absent the family's
SUMMARY rows are emitted UNKNOWN-with-reason and the per-item rows are not
emitted at all — which the never-silently-dropped rule then reports as a
violation naming each vanished row. An artifact disappearing is a regression,
not an UNKNOWN.

Usage:
  spine_scoreboard.py             generate + write data/spine_scoreboard.json
                                  (generator mode — same write as --refresh)
  spine_scoreboard.py --refresh   regenerate the committed baseline, stated
                                  explicitly (the only flag that writes)
  spine_scoreboard.py --ratchet   READ-ONLY: enforce directions vs the
                                  committed baseline, exit 1 naming the row on
                                  violation. Never writes — on green it touches
                                  nothing, on violation it leaves the baseline
                                  alone, and a missing/unreadable baseline is
                                  itself a failure (mint one with --refresh and
                                  commit it; the ratchet cannot mint)
  spine_scoreboard.py --self-test run the direction/UNKNOWN/missing-producer/
                                  read-only-ratchet arms, plus per-row-class
                                  arms for every producer family (planted
                                  regression detected and NAMED, missing
                                  artifact -> UNKNOWN-with-reason, denominator
                                  disagreement detected, producer arithmetic
                                  that does not close withheld), exit 1 on any
                                  failure
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as _dt
import hashlib
import importlib.util
import io
import json
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCOREBOARD_REL = "data/spine_scoreboard.json"
UNKNOWN = "UNKNOWN"
CENSUS_TARGET = 11
DIRECTIONS = ("up", "down", "frozen", "equal_11", "none")

SPINE_FAMILIES = [
    "tc::infer",
    "tc::def_eq",
    "tc::whnf",
    "tc::infer_proj",
    "tc::reduction",
    "env::decl_add",
]

EVALIR_CENSUS_SRC = "crates/clean-verify/tests/eval_ir/census.rs"
EVALIR_SYNTAX_SRC = "crates/clean-verify/src/spec/core_spec/eval_ir_syntax.rs"

PRODUCERS = {
    "spine_set": "data/spine_set.json",
    "a0_census": "data/crystal_a0_census_2026-08-22.json",
    "axiom_ratchet": "data/clean_verify_axiom_ratchet.json",
    "unchecked_decl_ratchet": "data/unchecked_decl_ratchet.json",
    "env_bypass_census": "data/env_bypass_census.json",
    "assumption_ledger": "data/spine_assumption_ledger.json",
    "parity_tiers": "data/parity_tiers.json",
    "evalir_coverage": "data/evalir_coverage.json",
    "evalir_adequacy_grid": "data/evalir_adequacy_grid.json",
    "evalir_census_src": EVALIR_CENSUS_SRC,
    "evalir_syntax_src": EVALIR_SYNTAX_SRC,
    "verdict_io_contracts": "data/verdict_io_contracts.json",
    "verdict_set": "data/verdict_set.json",
}

SPINE_SET_ABSENT_REASON = (
    "spine_set not yet minted (post-a5aae3bde dump owed, trust host)"
)
REPLAY_ABSENT_REASON = (
    "no machine-readable replay record — B-2ND owes one "
    "(the 2026-08-11 replay exists only as prose, "
    "docs/SELF_VERIFICATION_CERTIFICATE.md:832)"
)


def _load_json(path: Path):
    """Return parsed JSON or None if the file is absent/unreadable."""
    try:
        with path.open(encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError):
        return None


def _sha256(path: Path):
    try:
        return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return "ABSENT"


def _row(row_id, value, direction, producer, reason=None, provenance=None):
    row = {"id": row_id, "value": value, "direction": direction, "producer": producer}
    if value == UNKNOWN:
        row["reason"] = reason or "producer artifact absent"
    if provenance:
        row["provenance"] = provenance
    return row


# ---------------------------------------------------------------- producers


def rows_spine_set(repo_root: Path):
    """spine-set size + agreed/flipping/chained per family (data/spine_set.json)."""
    rows = []
    producer = PRODUCERS["spine_set"]
    doc = _load_json(repo_root / PRODUCERS["spine_set"])
    members = None
    if isinstance(doc, dict) and isinstance(doc.get("members"), list):
        members = doc["members"]
    elif isinstance(doc, list):
        members = doc

    if members is None:
        rows.append(_row("spine_set.size", UNKNOWN, "frozen", producer,
                         SPINE_SET_ABSENT_REASON))
        for fam in SPINE_FAMILIES:
            for metric in ("agreed", "flipping", "chained"):
                rows.append(_row(f"spine_set.family.{fam}.{metric}", UNKNOWN,
                                 "up", producer, SPINE_SET_ABSENT_REASON))
        return rows

    rows.append(_row("spine_set.size", len(members), "frozen", producer))
    for fam in SPINE_FAMILIES:
        fam_members = [m for m in members
                       if isinstance(m, dict) and m.get("family") == fam]
        for metric, keys in (("agreed", ("agreed",)),
                             ("flipping", ("flipping", "flip")),
                             ("chained", ("chained",))):
            if any(any(k in m for k in keys) for m in fam_members):
                count = sum(1 for m in fam_members
                            if any(m.get(k) is True for k in keys))
                rows.append(_row(f"spine_set.family.{fam}.{metric}", count,
                                 "up", producer))
            else:
                rows.append(_row(
                    f"spine_set.family.{fam}.{metric}", UNKNOWN, "up", producer,
                    f"spine_set.json present but carries no '{metric}' "
                    "measurement for this family yet"))
    return rows


def rows_a0_census(repo_root: Path):
    """Whole-crate chains-complete + A0 6-of-6 non-vacuous split."""
    rows = []
    producer = PRODUCERS["a0_census"]
    doc = _load_json(repo_root / PRODUCERS["a0_census"])
    if not isinstance(doc, dict) or not isinstance(doc.get("totals"), dict):
        reason = "crystal_a0_census_2026-08-22.json absent or schema unreadable"
        rows.append(_row("a0.whole_crate_chains_complete", UNKNOWN, "up",
                         producer, reason))
        rows.append(_row("a0.six_of_six_nonvacuous", UNKNOWN, "up", producer,
                         reason))
        return rows

    totals = doc["totals"]
    src_prov = doc.get("provenance") or {}
    complete = totals.get("a0_complete_6_of_6")
    nonvacuous = totals.get("a0_complete_with_nonvacuous_markers")
    prov = {
        "clean_rev": src_prov.get("clean_rev", UNKNOWN),
        "trust_rev": src_prov.get("trust_rev", UNKNOWN),
        "measured_utc": src_prov.get("measured_utc", UNKNOWN),
        "driver_dylib_sha256": src_prov.get("driver_dylib_sha256", UNKNOWN),
        "flags": ["predates a5aae3bde"],
    }
    if isinstance(complete, int) and isinstance(nonvacuous, int):
        prov["nonvacuous_split"] = {
            "a0_complete_6_of_6": complete,
            "nonvacuous_markers": nonvacuous,
            "vacuous_markers": complete - nonvacuous,
        }
    rows.append(_row(
        "a0.whole_crate_chains_complete",
        complete if isinstance(complete, int) else UNKNOWN,
        "up", producer,
        "totals.a0_complete_6_of_6 missing from census", prov))
    rows.append(_row(
        "a0.six_of_six_nonvacuous",
        nonvacuous if isinstance(nonvacuous, int) else UNKNOWN,
        "up", producer,
        "totals.a0_complete_with_nonvacuous_markers missing from census", prov))
    return rows


def rows_census(repo_root: Path):
    """clean-verify axiom census — must equal 11."""
    producer = PRODUCERS["axiom_ratchet"]
    doc = _load_json(repo_root / PRODUCERS["axiom_ratchet"])
    if not isinstance(doc, dict) or not isinstance(doc.get("count"), int):
        return [_row("census.axiom_count", UNKNOWN, "equal_11", producer,
                     "clean_verify_axiom_ratchet.json absent or 'count' "
                     "field missing")]
    prov = {
        "schema": doc.get("_schema", UNKNOWN),
        "last_updated": doc.get("_last_updated", UNKNOWN),
    }
    axioms = doc.get("axioms")
    if isinstance(axioms, list):
        prov["axioms_list_len"] = len(axioms)
        if len(axioms) != doc["count"]:
            prov["note"] = "count field disagrees with len(axioms)"
    return [_row("census.axiom_count", doc["count"], "equal_11", producer,
                 provenance=prov)]


def _read_env_bypass_items(doc):
    """Best-effort item list from env_bypass_census.json (schema in flight)."""
    if isinstance(doc, list):
        return doc
    if isinstance(doc, dict):
        for key in ("items", "census", "doors", "entries", "rows"):
            if isinstance(doc.get(key), list):
                return doc[key]
    return None


def rows_bypass_doors(repo_root: Path):
    """Bypass doors watched/unwatched/proved.

    Watched sites from data/unchecked_decl_ratchet.json (always committed);
    data/env_bypass_census.json merged when present (it cross-references,
    never copies, the ratchet rows — one accounting point per site, so
    summing is double-count-safe by construction).
    """
    rows = []
    census_path = repo_root / PRODUCERS["env_bypass_census"]
    ratchet = _load_json(repo_root / PRODUCERS["unchecked_decl_ratchet"])
    census_doc = _load_json(census_path)
    census_present = census_path.exists()

    watched = None
    prov = {}
    if isinstance(ratchet, dict):
        ec = ratchet.get("extend_constants") or {}
        parts = [
            ratchet.get("add_decl_structural_count"),
            ratchet.get("add_decl_unchecked_count"),
            ec.get("unchecked_production_count") if isinstance(ec, dict) else None,
            ec.get("structural_production_count") if isinstance(ec, dict) else None,
        ]
        if all(isinstance(p, int) for p in parts):
            watched = sum(parts)
            prov["unchecked_decl_ratchet"] = {
                "add_decl_structural": parts[0],
                "add_decl_unchecked": parts[1],
                "extend_constants_unchecked": parts[2],
                "extend_constants_structural": parts[3],
                "last_updated": ratchet.get("last_updated", UNKNOWN),
            }

    unwatched = UNKNOWN
    proved = UNKNOWN
    unwatched_reason = proved_reason = (
        "env_bypass_census.json not yet committed (G-ADD lane in flight)")
    items = _read_env_bypass_items(census_doc)
    if census_present:
        if items is None:
            unwatched_reason = proved_reason = (
                "env_bypass_census.json present but its item list was not "
                "recognized (schema in flight) — fail closed to UNKNOWN")
        else:
            statuses = [i.get("status") for i in items if isinstance(i, dict)]
            if any(isinstance(s, str) for s in statuses):
                unwatched = sum(1 for s in statuses if s == "unwatched")
                proved = sum(1 for s in statuses if s == "proved")
                extra_watched = sum(
                    1 for s in statuses if s in ("watched", "proved"))
                if watched is not None:
                    watched += extra_watched
                    prov["env_bypass_census_watched_rows"] = extra_watched
            else:
                unwatched_reason = proved_reason = (
                    "env_bypass_census.json items carry no 'status' field "
                    "yet — fail closed to UNKNOWN")

    producer = (PRODUCERS["unchecked_decl_ratchet"] + " + "
                + PRODUCERS["env_bypass_census"])
    rows.append(_row(
        "bypass_doors.watched",
        watched if watched is not None else UNKNOWN, "none", producer,
        "unchecked_decl_ratchet.json absent or count fields missing",
        prov or None))
    rows.append(_row("bypass_doors.unwatched", unwatched, "down", producer,
                     unwatched_reason))
    rows.append(_row("bypass_doors.proved", proved, "up", producer,
                     proved_reason))
    return rows


def rows_assumption_ledger(repo_root: Path):
    """The §3.6 assumption ledger — the consolidated file, plus the lane-(b)
    rows that stay in data/verdict_io_contracts.json and are cross-referenced.

    The consolidated file is minted by scripts/spine_assumption_ledger.py.
    `count` is its LIVE debt (rows with status=measured) and is the number
    §3.6 ratchets down; `prospective_count` holds rows for assumptions of jobs
    that have not run, which is why they are reported (`none`) and never
    ratcheted — converting one into a live row RAISES count, and that is
    progress, not a regression.

    verdict_io_contracts.json's ledger block names its own destination
    ("data/spine_assumption_ledger.json, when that file exists") and its own
    direction (down). The consolidated ledger CROSS-REFERENCES those 44 rows
    rather than absorbing them — one accounting point per assumption — so the
    two counts stay disjoint, and the cross-reference's own row count is
    checked against the lane-(b) artifact here.
    """
    producer = PRODUCERS["assumption_ledger"]
    doc = _load_json(repo_root / producer)

    blocked = None
    entries = doc.get("entries") if isinstance(doc, dict) else None
    if not isinstance(doc, dict) or not isinstance(entries, list):
        blocked = ("data/spine_assumption_ledger.json absent, unreadable, or "
                   "carrying no 'entries' list — the §3.6 ledger is not minted "
                   "here (mint: scripts/spine_assumption_ledger.py)")
    elif not entries:
        blocked = ("the ledger carries ZERO entries — that is schema drift, not "
                   "an empty ledger; fail closed")
    else:
        missing = [k for k in ("count", "prospective_count", "row_count")
                   if not isinstance(doc.get(k), int)]
        if missing:
            blocked = ("ledger totals missing or non-integer: %s (schema drift)"
                       % ", ".join(missing))
        else:
            # The ledger's own arithmetic must close, or none of it is quoted.
            bad = []
            if doc["row_count"] != len(entries):
                bad.append("row_count=%d but len(entries)=%d"
                           % (doc["row_count"], len(entries)))
            live = sum(1 for e in entries
                       if isinstance(e, dict) and e.get("status") == "measured")
            prospective = sum(1 for e in entries
                              if isinstance(e, dict)
                              and e.get("status") == "prospective")
            if doc["count"] != live:
                bad.append("count=%d but %d entries carry status=measured"
                           % (doc["count"], live))
            if doc["prospective_count"] != prospective:
                bad.append("prospective_count=%d but %d entries carry "
                           "status=prospective" % (doc["prospective_count"],
                                                   prospective))
            if live + prospective != len(entries):
                bad.append("count + prospective_count = %d != len(entries) %d "
                           "(a row carries a status outside the vocabulary)"
                           % (live + prospective, len(entries)))
            if bad:
                blocked = ("the ledger disagrees with itself (" + "; ".join(bad)
                           + ") — the count is withheld rather than a side "
                           "picked")

    prov = None
    if blocked is None:
        src_prov = doc.get("provenance") if isinstance(doc.get("provenance"), dict) else {}
        prov = {
            "counts_by_class": doc.get("counts_by_class", UNKNOWN),
            "counts_by_origin": doc.get("counts_by_origin", UNKNOWN),
            "derived_classes": src_prov.get("derived_classes", UNKNOWN),
            "seeded_classes": src_prov.get("seeded_classes", UNKNOWN),
            "note": "count is the LIVE debt (status=measured); the "
                    "prospective rows are reported separately and are disjoint "
                    "from it, as are the lane-(b) rows below",
        }

    rows = [
        _row("assumption_ledger.count",
             doc["count"] if blocked is None else UNKNOWN,
             "down", producer, blocked, prov),
        # Reported, never ratcheted: a prospective row is an assumption of a
        # job that has NOT run. It falls when the job lands and mints live
        # rows — which RAISES assumption_ledger.count. Ratcheting this down
        # would reward deleting a planned assumption instead of doing it.
        _row("assumption_ledger.prospective",
             doc["prospective_count"] if blocked is None else UNKNOWN,
             "none", producer, blocked),
    ]
    rows.append(_ledger_xref_row(repo_root, doc if blocked is None else None))
    rows.append(_ledger_lane_b_row(repo_root))
    return rows


def _ledger_xref_row(repo_root: Path, ledger_doc):
    """The consolidated ledger's cross-reference to lane (b) must still hold.

    The two artifacts are counted separately ON PURPOSE, so the pointer
    between them is the only thing keeping the split honest: if the ledger
    claims lane (b) has N rows and lane (b) has M, one of the two counts is
    stale and the split is no longer a split. Direction down, baseline 0 —
    the same shape as the evalir/verdict_io denominator cross-checks.
    """
    row_id = "assumption_ledger.cross_reference_disagreements"
    producer = (PRODUCERS["assumption_ledger"] + " vs "
                + PRODUCERS["verdict_io_contracts"])
    if not isinstance(ledger_doc, dict):
        return _row(row_id, UNKNOWN, "down", producer,
                    "the consolidated ledger could not be read (see "
                    "assumption_ledger.count) — there is nothing to compare")
    refs = ledger_doc.get("cross_references")
    if not isinstance(refs, list) or not refs:
        return _row(row_id, UNKNOWN, "down", producer,
                    "the ledger carries no 'cross_references' list — the "
                    "lane-(b) split cannot be checked, so no number is "
                    "published")
    doc = _load_json(repo_root / PRODUCERS["verdict_io_contracts"])
    ledger = doc.get("ledger") if isinstance(doc, dict) else None
    if not isinstance(ledger, dict) or not isinstance(ledger.get("row_count"), int):
        return _row(row_id, UNKNOWN, "down", producer,
                    "data/verdict_io_contracts.json absent, or its ledger block "
                    "carries no integer 'row_count' — nothing to compare the "
                    "cross-reference against")
    disagreements = []
    checked = 0
    for ref in refs:
        if not isinstance(ref, dict) or ref.get("path") != PRODUCERS["verdict_io_contracts"]:
            continue
        checked += 1
        claimed = ref.get("row_count")
        if not isinstance(claimed, int):
            disagreements.append("cross-reference %r states no integer row_count"
                                 % ref.get("id"))
        elif claimed != ledger["row_count"]:
            disagreements.append(
                "%s cross-references %s at row_count=%d; that artifact reports "
                "%d" % (PRODUCERS["assumption_ledger"],
                        PRODUCERS["verdict_io_contracts"], claimed,
                        ledger["row_count"]))
    if checked == 0:
        return _row(row_id, UNKNOWN, "down", producer,
                    "the ledger's cross_references name no row for "
                    "data/verdict_io_contracts.json — the lane-(b) split is "
                    "unchecked")
    return _row(row_id, len(disagreements), "down", producer,
                provenance={"cross_references_checked": checked,
                            "detail": disagreements} if disagreements
                else {"cross_references_checked": checked})


def _ledger_lane_b_row(repo_root: Path):
    """Ring R2 lane (b)'s §3.6 ledger rows, read from their interim home."""
    producer = PRODUCERS["verdict_io_contracts"] + " (ledger block)"
    row_id = "assumption_ledger.verdict_io_lane_b"
    doc = _load_json(repo_root / PRODUCERS["verdict_io_contracts"])
    ledger = doc.get("ledger") if isinstance(doc, dict) else None
    if not isinstance(ledger, dict):
        return _row(row_id, UNKNOWN, "down", producer,
                    "data/verdict_io_contracts.json absent or carries no "
                    "'ledger' block — lane (b)'s §3.6 rows cannot be counted "
                    "(mint: scripts/verdict_io_contracts.py)")

    count = ledger.get("row_count")
    listed = ledger.get("rows")
    ratchet = ledger.get("row_ratchet") if isinstance(ledger.get("row_ratchet"), dict) else {}
    measured = ratchet.get("measured_rows")
    if not isinstance(count, int) or not isinstance(listed, list):
        return _row(row_id, UNKNOWN, "down", producer,
                    "ledger block present but 'row_count' is not an int or "
                    "'rows' is not a list (schema drift) — fail closed")
    disagreements = []
    if len(listed) != count:
        disagreements.append(
            "row_count=%d but len(rows)=%d" % (count, len(listed)))
    if isinstance(measured, int) and measured != count:
        disagreements.append(
            "row_count=%d but row_ratchet.measured_rows=%d" % (count, measured))
    if disagreements:
        return _row(row_id, UNKNOWN, "down", producer,
                    "lane (b) ledger disagrees with itself (" +
                    "; ".join(disagreements) + ") — the count is withheld "
                    "rather than a side picked")

    prov = {
        "declared_direction": ledger.get("direction", UNKNOWN),
        "destination": ledger.get("destination", UNKNOWN),
        "rows_by_class": ledger.get("rows_by_class", UNKNOWN),
        "baseline_rows": ratchet.get("baseline_rows", UNKNOWN),
        "rebases": len(ratchet["rebases"]) if isinstance(ratchet.get("rebases"), list) else UNKNOWN,
        "note": "counted in this scoreboard IN ADDITION to "
                "assumption_ledger.count; the two are disjoint until "
                "data/spine_assumption_ledger.json absorbs these rows, at "
                "which point this row must be re-based to avoid double count",
    }
    return _row(row_id, count, "down", producer, provenance=prov)


# ------------------------------------------------- L3 parity tiers (R3)


def rows_parity_tiers(repo_root: Path):
    """R3's fidelity tiers — summary rows always, per-tier/per-guard rows
    from the artifact.

    Directions are NOT invented here: each tier row takes the tier's own
    `ratchet` field and each guard row takes the guard's own `direction`. A
    value carrying an unrecognized direction is withheld as UNKNOWN rather
    than published under a guessed one.
    """
    producer = PRODUCERS["parity_tiers"]
    doc = _load_json(repo_root / PRODUCERS["parity_tiers"])
    summary = doc.get("summary") if isinstance(doc, dict) else None
    tiers = doc.get("tiers") if isinstance(doc, dict) else None

    blocked = None
    if not isinstance(doc, dict):
        blocked = ("data/parity_tiers.json absent or unreadable — R3's tier "
                   "generator has not been run in this checkout "
                   "(mint: scripts/parity_tiers.py)")
    elif not isinstance(tiers, list) or not tiers:
        blocked = ("data/parity_tiers.json present but its 'tiers' list is "
                   "missing or empty (schema drift) — fail closed")
    else:
        names = [t.get("name") if isinstance(t, dict) else None for t in tiers]
        if not all(isinstance(n, str) and n for n in names):
            blocked = ("data/parity_tiers.json has a tier with no usable "
                       "'name' (schema drift) — row ids cannot be formed, "
                       "so the whole family is withheld")
        elif len(set(names)) != len(names):
            blocked = ("data/parity_tiers.json has duplicate tier names "
                       "(schema drift) — row ids would collide, so the whole "
                       "family is withheld")

    def summary_row(key, direction):
        row_id = "parity_tiers." + key
        if blocked is not None:
            return _row(row_id, UNKNOWN, direction, producer, blocked)
        val = summary.get(key) if isinstance(summary, dict) else None
        if not isinstance(val, int):
            return _row(row_id, UNKNOWN, direction, producer,
                        "summary.%s missing or not an int in "
                        "data/parity_tiers.json (schema drift)" % key)
        return _row(row_id, val, direction, producer)

    rows = [
        summary_row("tiers", "none"),
        summary_row("measured", "up"),
        summary_row("unknown", "down"),
        # Freshness, deliberately unratcheted: this rises whenever commits
        # land without a re-measure, so ratcheting it would turn ordinary
        # work into a false red. Reported, per the `none` vocabulary.
        summary_row("stale_vs_generation_head", "none"),
    ]
    if blocked is not None:
        return rows

    for tier in tiers:
        rows.extend(_parity_tier_rows(tier, producer))
    return rows


def _parity_tier_rows(tier, producer):
    name = tier["name"]
    rows = []
    row_id = "parity_tiers.tier.%s.value" % name
    direction = tier.get("ratchet")
    status = tier.get("status")
    value = tier.get("value")
    prov = {
        "unit": tier.get("unit", UNKNOWN),
        "denominator": tier.get("denominator", UNKNOWN),
        "status": status if isinstance(status, str) else UNKNOWN,
        "measured_at_commit": (tier.get("measured_at") or {}).get("commit", UNKNOWN)
        if isinstance(tier.get("measured_at"), dict) else UNKNOWN,
        "staleness": (tier.get("staleness") or {}).get("label", UNKNOWN)
        if isinstance(tier.get("staleness"), dict) else UNKNOWN,
    }
    if direction not in DIRECTIONS:
        rows.append(_row(
            row_id, UNKNOWN, "none", producer,
            "tier declares ratchet %r, which is not a direction this "
            "scoreboard enforces — the value is withheld rather than "
            "published under a guessed direction" % (direction,), prov))
    elif status != "measured" or not isinstance(value, int):
        reason = tier.get("reason")
        if not isinstance(reason, str) or not reason:
            reason = ("tier status is %r with no machine-readable integer "
                      "value and no stated reason" % (status,))
        rows.append(_row(row_id, UNKNOWN, direction, producer, reason, prov))
    else:
        rows.append(_row(row_id, value, direction, producer, provenance=prov))

    guards = tier.get("guards")
    if not isinstance(guards, list):
        return rows
    for guard in guards:
        if not isinstance(guard, dict):
            continue
        key = guard.get("key")
        if not isinstance(key, str) or not key:
            continue
        gid = "parity_tiers.tier.%s.guard.%s" % (name, key)
        gdir = guard.get("direction")
        gval = guard.get("value")
        gprov = {"note": guard.get("note", UNKNOWN)}
        if gdir not in DIRECTIONS:
            rows.append(_row(gid, UNKNOWN, "none", producer,
                             "guard declares direction %r, which is not a "
                             "direction this scoreboard enforces" % (gdir,),
                             gprov))
        elif not isinstance(gval, int):
            rows.append(_row(gid, UNKNOWN, gdir, producer,
                             "guard carries no integer value", gprov))
        else:
            rows.append(_row(gid, gval, gdir, producer, provenance=gprov))
    return rows


# ------------------------------------------------------- EvalIR (B-SEM)


_EVALIR_COVERAGE_CACHE = []


def _import_evalir_coverage():
    """The denominator parsers, reused from their owning script.

    Re-implementing EMITTED_INSTS / `inductive IRInst` parsing here would
    create a second denominator authority, which is the exact failure the
    cross-check exists to catch. Load the one that already fails closed —
    by file path, not via sys.path, so this never shadows anything.
    """
    if _EVALIR_COVERAGE_CACHE:
        return _EVALIR_COVERAGE_CACHE[0]
    src = Path(__file__).resolve().parent / "evalir_coverage.py"
    try:
        spec = importlib.util.spec_from_file_location(
            "clean_spine_scoreboard_evalir_coverage", str(src))
        if spec is None or spec.loader is None:
            raise ImportError("no loader for " + str(src))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        result = (module, None)
    except Exception as exc:  # any load failure is a fail-closed condition
        result = (None, "scripts/evalir_coverage.py is not loadable (%s: %s)"
                  % (type(exc).__name__, exc))
    _EVALIR_COVERAGE_CACHE.append(result)
    return result


def _evalir_census(repo_root: Path):
    """(names, reason) — the pinned constructed-Inst census, or None + why."""
    mod, err = _import_evalir_coverage()
    if mod is None:
        return None, err
    texts = []
    for rel in (EVALIR_CENSUS_SRC, EVALIR_SYNTAX_SRC):
        path = repo_root / rel
        try:
            texts.append(path.read_text(encoding="utf-8"))
        except OSError:
            return None, "denominator source absent or unreadable: " + rel
    try:
        return mod.derive_denominator(texts[0], texts[1]), None
    except Exception as exc:  # CoverageError, or any parse drift
        return None, "denominator sources unusable: %s" % (exc,)


def rows_evalir(repo_root: Path):
    """EvalIR semdiff coverage N/28 and the B-SEM §4(c) adequacy grid."""
    cov_rel = PRODUCERS["evalir_coverage"]
    grid_rel = PRODUCERS["evalir_adequacy_grid"]
    den_producer = EVALIR_CENSUS_SRC + " + " + EVALIR_SYNTAX_SRC
    cov = _load_json(repo_root / cov_rel)
    grid = _load_json(repo_root / grid_rel)
    census, census_err = _evalir_census(repo_root)
    total = len(census) if census is not None else None

    # --- denominator cross-check: every artifact that RESTATES the census
    #     must agree with the census derived from its two authorities.
    disagreements = []
    reported = []
    if isinstance(cov, dict) and isinstance(cov.get("total"), int):
        reported.append((cov_rel, "total", cov["total"]))
    if isinstance(grid, dict) and isinstance(grid.get("constructors"), int):
        reported.append((grid_rel, "constructors", grid["constructors"]))
    if total is not None:
        for rel, field, val in reported:
            if val != total:
                disagreements.append(
                    "%s reports %s=%d, the pinned census derives %d from %s"
                    % (rel, field, val, total, den_producer))
    disagreeing_artifacts = set(d.split(" reports ")[0] for d in disagreements)

    rows = []
    rows.append(_row(
        "evalir.constructor_census",
        total if total is not None else UNKNOWN, "frozen", den_producer,
        (census_err or "") + " — the constructed-Inst denominator cannot be "
        "re-derived, so it is not published",
        {"cross_checked_against": [r[0] + ":" + r[1] for r in reported],
         "disagreements": disagreements}))
    rows.append(_row(
        "evalir.denominator_disagreements",
        len(disagreements) if total is not None else UNKNOWN, "down",
        den_producer,
        "no census could be derived (%s) — there is nothing to compare the "
        "artifacts' reported totals against" % (census_err,),
        {"detail": disagreements} if disagreements else None))

    # --- coverage rows, withheld when their denominator is in dispute
    cov_blocked = None
    if not isinstance(cov, dict) or not isinstance(cov.get("count"), int):
        cov_blocked = ("data/evalir_coverage.json absent, unreadable, or "
                       "carrying no integer 'count' (mint: "
                       "scripts/evalir_coverage.py)")
    elif total is None:
        cov_blocked = ("the 28-constructor denominator could not be "
                       "re-derived (%s) — a fraction is never published over "
                       "an underivable denominator" % (census_err,))
    elif cov_rel in disagreeing_artifacts:
        cov_blocked = ("denominator DISAGREEMENT: " +
                       "; ".join(d for d in disagreements
                                 if d.startswith(cov_rel)) +
                       " — fail closed, neither number is published")
    cov_prov = None
    if cov_blocked is None:
        cov_prov = {"covered": cov.get("covered", UNKNOWN),
                    "denominator": total,
                    "rule": (cov.get("provenance") or {}).get("rule", UNKNOWN)
                    if isinstance(cov.get("provenance"), dict) else UNKNOWN}
    rows.append(_row(
        "evalir.semdiff_covered",
        cov["count"] if cov_blocked is None else UNKNOWN, "up", cov_rel,
        cov_blocked, cov_prov))
    rows.append(_row(
        "evalir.semdiff_unmeasured",
        total - cov["count"] if cov_blocked is None else UNKNOWN, "down",
        cov_rel, cov_blocked))

    rows.extend(_evalir_adequacy_rows(grid, grid_rel, total, census_err,
                                      disagreements, disagreeing_artifacts))
    return rows


# Grid totals published as scoreboard rows: (totals key, row suffix,
# direction). The three debt states are monotone-down: each is an obligation
# the encoding currently stands on and does not discharge, so growing one
# without a dated re-base is exactly what the ratchet is for. The two surface
# sizes are `none` — they move whenever IRInst gains a field, which is
# neither progress nor regression.
_GRID_ROWS = (
    ("field_rows", "field_rows", "none"),
    ("relevant-by-design", "relevant_by_design", "none"),
    ("irrelevance-proved-await-mint", "irrelevance_proved_await_mint", "down"),
    ("audit-pin", "audit_pin", "down"),
    ("declared-delta", "declared_delta", "down"),
)


def _evalir_adequacy_rows(grid, grid_rel, total, census_err, disagreements,
                          disagreeing_artifacts):
    totals = grid.get("totals") if isinstance(grid, dict) else None
    blocked = None
    if not isinstance(grid, dict) or not isinstance(totals, dict):
        blocked = ("data/evalir_adequacy_grid.json absent, unreadable, or "
                   "carrying no 'totals' block (mint: "
                   "scripts/evalir_adequacy_grid.py)")
    elif total is None:
        blocked = ("the 28-constructor denominator could not be re-derived "
                   "(%s) — the grid's per-constructor account is not "
                   "published over an underivable denominator" % (census_err,))
    elif grid_rel in disagreeing_artifacts:
        blocked = ("denominator DISAGREEMENT: " +
                   "; ".join(d for d in disagreements
                             if d.startswith(grid_rel)) +
                   " — fail closed, the grid's totals are withheld")
    else:
        missing = [k for k, _, _ in _GRID_ROWS
                   if not isinstance(totals.get(k), int)]
        rows_total = totals.get("rows")
        listed = grid.get("rows")
        if missing:
            blocked = ("grid totals missing or non-integer: %s (schema drift)"
                       % ", ".join(missing))
        elif not isinstance(rows_total, int) or not isinstance(listed, list):
            blocked = "grid 'totals.rows' or 'rows' missing (schema drift)"
        else:
            # The grid's own arithmetic must close, or none of it is quoted.
            bad = []
            if len(listed) != rows_total:
                bad.append("totals.rows=%d but len(rows)=%d"
                           % (rows_total, len(listed)))
            parts = (totals["relevant-by-design"]
                     + totals["irrelevance-proved-await-mint"])
            if parts != totals["field_rows"]:
                bad.append("relevant-by-design + irrelevance-proved-await-mint"
                           " = %d != field_rows %d" % (parts, totals["field_rows"]))
            whole = (totals["field_rows"] + totals["audit-pin"]
                     + totals["declared-delta"])
            if whole != rows_total:
                bad.append("field_rows + audit-pin + declared-delta = %d != "
                           "totals.rows %d" % (whole, rows_total))
            if bad:
                blocked = ("grid arithmetic does not close (" + "; ".join(bad)
                           + ") — fail closed, its totals are withheld")

    out = []
    for key, suffix, direction in _GRID_ROWS:
        row_id = "evalir.adequacy." + suffix
        if blocked is not None:
            out.append(_row(row_id, UNKNOWN, direction, grid_rel, blocked))
        else:
            out.append(_row(row_id, totals[key], direction, grid_rel))
    return out


# ------------------------------------- Ring R2 lane (b): IO contracts


def rows_verdict_io(repo_root: Path):
    """The IO-boundary contract model's measured classification.

    site_total is cross-checked against data/verdict_set.json's
    partitions.b_io_bearing.io_site_total — the shared denominator the
    model's own derivation block says a disagreeing total must abort on.
    """
    producer = PRODUCERS["verdict_io_contracts"]
    authority = PRODUCERS["verdict_set"]
    doc = _load_json(repo_root / producer)
    vset = _load_json(repo_root / authority)

    authoritative = None
    if isinstance(vset, dict):
        part = (vset.get("partitions") or {}).get("b_io_bearing")
        if isinstance(part, dict) and isinstance(part.get("io_site_total"), int):
            authoritative = part["io_site_total"]

    cls = doc.get("classification") if isinstance(doc, dict) else None
    blocked = None
    disagreement = None
    if not isinstance(doc, dict) or not isinstance(cls, dict):
        blocked = ("data/verdict_io_contracts.json absent, unreadable, or "
                   "carrying no 'classification' block (mint: "
                   "scripts/verdict_io_contracts.py)")
    elif not isinstance(cls.get("site_total"), int):
        blocked = "classification.site_total missing or not an int (schema drift)"
    elif authoritative is None:
        blocked = ("data/verdict_set.json absent, or its "
                   "partitions.b_io_bearing.io_site_total is missing — the "
                   "shared denominator this model pins itself to cannot be "
                   "cross-checked, so its counts are withheld")
    elif cls["site_total"] != authoritative:
        disagreement = ("%s reports site_total=%d, the authority %s reports "
                        "partitions.b_io_bearing.io_site_total=%d"
                        % (producer, cls["site_total"], authority, authoritative))
        blocked = ("denominator DISAGREEMENT: " + disagreement +
                   " — fail closed, neither number is published")
    else:
        bad = []
        pair = (cls.get("sites_issuing_io"), cls.get("sites_issuing_no_io"))
        if all(isinstance(p, int) for p in pair):
            if pair[0] + pair[1] != cls["site_total"]:
                bad.append("sites_issuing_io + sites_issuing_no_io = %d != "
                           "site_total %d" % (pair[0] + pair[1], cls["site_total"]))
        else:
            bad.append("sites_issuing_io / sites_issuing_no_io missing")
        dep = cls.get("by_dependence")
        if isinstance(dep, dict) and all(isinstance(v, int) for v in dep.values()):
            if sum(dep.values()) != cls["site_total"]:
                bad.append("sum(by_dependence) = %d != site_total %d"
                           % (sum(dep.values()), cls["site_total"]))
        else:
            bad.append("by_dependence missing or non-integer")
        if not isinstance(cls.get("unclassified"), int):
            bad.append("unclassified missing or not an int")
        if bad:
            blocked = ("lane (b) classification does not close (" +
                       "; ".join(bad) + ") — fail closed")

    def cls_row(row_id, getter, direction, provenance=None):
        if blocked is not None:
            return _row(row_id, UNKNOWN, direction, producer, blocked)
        val = getter()
        if not isinstance(val, int):
            return _row(row_id, UNKNOWN, direction, producer,
                        "field missing or not an int (schema drift)")
        return _row(row_id, val, direction, producer, provenance=provenance)

    prov_total = None
    if blocked is None:
        prov_total = {"cross_checked_against":
                      authority + ":partitions.b_io_bearing.io_site_total",
                      "authoritative_value": authoritative}
    rows = [
        cls_row("verdict_io.site_total", lambda: cls["site_total"], "none",
                prov_total),
        _row("verdict_io.denominator_disagreements",
             UNKNOWN if authoritative is None or not isinstance(cls, dict)
             or not isinstance(cls.get("site_total"), int)
             else (1 if disagreement else 0),
             "down", producer + " vs " + authority,
             "the authority %s could not be read, or the model reports no "
             "integer site_total — nothing to compare" % authority,
             {"detail": disagreement} if disagreement else None),
        cls_row("verdict_io.sites_issuing_io",
                lambda: cls["sites_issuing_io"], "none"),
        cls_row("verdict_io.content_bearing",
                lambda: (cls.get("by_dependence") or {}).get("content-bearing"),
                "none"),
        cls_row("verdict_io.unclassified", lambda: cls["unclassified"], "down"),
    ]

    contracts = doc.get("contracts") if isinstance(doc, dict) else None
    if not isinstance(contracts, list):
        rows.append(_row("verdict_io.contracts_stated", UNKNOWN, "none",
                         producer, "no 'contracts' list in "
                         "data/verdict_io_contracts.json"))
    else:
        absent = doc.get("measured_absent")
        residue = doc.get("residue_class")
        rows.append(_row(
            "verdict_io.contracts_stated", len(contracts), "none", producer,
            provenance={
                "measured_absent": len(absent) if isinstance(absent, list) else UNKNOWN,
                "residue_class": residue.get("id", UNKNOWN)
                if isinstance(residue, dict) else UNKNOWN,
            }))
    return rows


def rows_replay(_repo_root: Path):
    """Replay age vs newest milestone gate — needs B-2ND's machine record."""
    return [_row("replay.age", UNKNOWN, "none",
                 "B-2ND machine-readable replay record (not yet minted)",
                 REPLAY_ABSENT_REASON)]


def generate_rows(repo_root: Path):
    rows = []
    for fn in (rows_spine_set, rows_a0_census, rows_census, rows_bypass_doors,
               rows_assumption_ledger, rows_parity_tiers, rows_evalir,
               rows_verdict_io, rows_replay):
        rows.extend(fn(repo_root))
    return rows


def build_scoreboard(repo_root: Path):
    return {
        "schema": "clean.spine.scoreboard/1",
        "_doc": [
            "G-SCORE scoreboard — designs/2026-08-22-spine-and-lattice-program.md §6.",
            "Regenerate: /opt/homebrew/bin/python3.14 scripts/spine_scoreboard.py --refresh",
            "Ratchet:    scripts/spine_scoreboard.py --ratchet (READ-ONLY; baseline = this file as committed)",
            "UNKNOWN is a first-class value, never 0; it neither satisfies nor violates a direction.",
            "Quoting any row of this file from prose is a bug: read the artifact.",
        ],
        "generated_at_utc": _dt.datetime.now(_dt.timezone.utc)
        .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "generator": "scripts/spine_scoreboard.py",
        "inputs": {name: _sha256(repo_root / rel)
                   for name, rel in PRODUCERS.items()},
        "rows": generate_rows(repo_root),
    }


# ------------------------------------------------------------------ ratchet


def check_directions(current_rows, baseline_rows):
    """Return (violations, reports); violations name the row."""
    violations, reports = [], []
    baseline = {r["id"]: r for r in baseline_rows if isinstance(r, dict)}
    current = {r["id"]: r for r in current_rows}

    for row_id, row in current.items():
        val, direction = row["value"], row["direction"]
        base_row = baseline.get(row_id)
        if base_row is not None and base_row.get("direction") not in (None, direction):
            # R5: a row's ratchet is never weakened silently. Directions that
            # come from a producer artifact (parity tiers, guards) can move,
            # and when they do it is a dated decision that re-bases the
            # committed scoreboard, not a change the gate should absorb.
            violations.append(
                "%s: direction changed (%s -> %s) — a row's ratchet direction "
                "is re-based only by regenerating and committing the baseline"
                % (row_id, base_row.get("direction"), direction))
        if direction == "equal_11":
            if val == UNKNOWN:
                reports.append(f"{row_id}: UNKNOWN (reports; equal-11 not checkable)")
            elif val != CENSUS_TARGET:
                violations.append(
                    f"{row_id}: census must equal {CENSUS_TARGET}, got {val}")
            continue
        if base_row is None:
            reports.append(f"{row_id}: new row (no baseline)")
            continue
        bval = base_row.get("value")
        if val == UNKNOWN or bval == UNKNOWN:
            reports.append(
                f"{row_id}: UNKNOWN present (current={val}, baseline={bval}) — "
                "reports, never satisfies or violates")
            continue
        if direction == "up" and val < bval:
            violations.append(
                f"{row_id}: monotone-up row decreased ({bval} -> {val})")
        elif direction == "down" and val > bval:
            violations.append(
                f"{row_id}: monotone-down row increased ({bval} -> {val})")
        elif direction == "frozen" and val != bval:
            violations.append(
                f"{row_id}: frozen row changed ({bval} -> {val}) — re-base "
                "requires a dated re-measure committed as a new baseline")

    for row_id in baseline:
        if row_id not in current:
            violations.append(
                f"{row_id}: row present in baseline but missing from "
                "regenerated scoreboard (rows are never silently dropped)")
    return violations, reports


def print_rows(rows):
    width = max(len(r["id"]) for r in rows)
    for r in rows:
        line = f"  {r['id']:<{width}}  {r['value']!s:>8}  [{r['direction']}]"
        if r["value"] == UNKNOWN:
            line += f"  reason: {r['reason']}"
        print(line)


# ---------------------------------------------------------------- self-test


def _mk(row_id, value, direction):
    return {"id": row_id, "value": value, "direction": direction,
            "producer": "self-test"}


def _write(root, rel, doc):
    """Write a JSON (dict/list) or raw-text producer into a temp repo root."""
    path = Path(root) / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(doc, str):
        path.write_text(doc, encoding="utf-8")
    else:
        path.write_text(json.dumps(doc), encoding="utf-8")
    return path


def _fixture_parity_tiers(value=63, guard=5, ratchet="up"):
    return {
        "summary": {"tiers": 2, "measured": 1, "unknown": 1,
                    "stale_vs_generation_head": 1},
        "tiers": [
            {"name": "t-measured", "status": "measured", "value": value,
             "denominator": 63, "unit": "snippets", "ratchet": ratchet,
             "guards": [{"key": "kernel_check_failures", "value": guard,
                         "direction": "down", "note": "self-test guard"}]},
            {"name": "t-unknown", "status": "unknown", "value": None,
             "ratchet": "up", "guards": [],
             "reason": "self-test: no committed artifact backs this tier"},
        ],
    }


def _fixture_evalir_sources(names=("br", "ret", "load")):
    census_rs = ('pub const EMITTED_INSTS: &[&str] = &[\n'
                 + "".join('    "%s",\n' % n for n in names) + '];\n')
    syntax_rs = ("inductive IRInst : Type\n"
                 + "".join("  | %s : IRInst\n" % n for n in names))
    return census_rs, syntax_rs


def _fixture_evalir_coverage(count=2, total=3):
    return {"schema": "evalir-coverage/v1", "covered": ["br", "ret"][:count],
            "count": count, "total": total}


def _fixture_evalir_grid(constructors=3):
    return {
        "schema": "evalir-adequacy-grid/v1",
        "constructors": constructors,
        "rows": [{"kind": "field"}] * 8,
        "totals": {"rows": 8, "field_rows": 5, "relevant-by-design": 4,
                   "irrelevance-proved-await-mint": 1, "audit-pin": 2,
                   "declared-delta": 1},
    }


def _fixture_verdict_io(site_total=211, ledger_rows=44, listed=None):
    n = ledger_rows if listed is None else listed
    return {
        "classification": {
            "site_total": site_total,
            "sites_issuing_io": site_total - 83,
            "sites_issuing_no_io": 83,
            "by_dependence": {"content-bearing": site_total - 113,
                              "verdict-irrelevant": 83, "success-only": 30},
            "unclassified": 0,
        },
        "contracts": [{"id": "C-A"}, {"id": "C-B"}],
        "measured_absent": [{"id": "C-NET-DIRECT"}],
        "residue_class": {"id": "C-NONE"},
        "ledger": {
            "direction": "down", "row_count": ledger_rows,
            "rows": [{"id": i} for i in range(n)],
            "rows_by_class": {"meta": 2},
            "row_ratchet": {"direction": "down", "baseline_rows": 44,
                            "measured_rows": ledger_rows, "rebases": []},
        },
    }


def _fixture_verdict_set(io_site_total=211):
    return {"partitions": {"b_io_bearing": {"io_site_total": io_site_total}}}


def _fixture_assumption_ledger(measured=26, prospective=3, row_count=None,
                               count=None, xref_rows=44, xref=True):
    entries = ([{"id": "A-M-%d" % i, "status": "measured"} for i in range(measured)]
               + [{"id": "A-P-%d" % i, "status": "prospective"}
                  for i in range(prospective)])
    doc = {
        "schema": "clean.spine.assumption-ledger/1",
        "count": measured if count is None else count,
        "prospective_count": prospective,
        "row_count": len(entries) if row_count is None else row_count,
        "counts_by_class": {"self-test": len(entries)},
        "counts_by_origin": {"derived": len(entries)},
        "cross_references": [],
        "entries": entries,
        "provenance": {"derived_classes": ["self-test"], "seeded_classes": []},
    }
    if xref:
        doc["cross_references"] = [{
            "id": "XREF-VERDICT-IO-LANE-B",
            "path": "data/verdict_io_contracts.json",
            "block": "ledger",
            "row_count": xref_rows,
        }]
    return doc


def self_test():
    failures = []

    def expect(name, cond, detail=""):
        status = "ok" if cond else "FAIL"
        print(f"self-test: {name}: {status}{(' — ' + detail) if detail else ''}")
        if not cond:
            failures.append(name)

    v, _ = check_directions([_mk("r.up", 4, "up")], [_mk("r.up", 5, "up")])
    expect("up_decrease_violates", len(v) == 1 and "r.up" in v[0])
    v, _ = check_directions([_mk("r.up", 6, "up")], [_mk("r.up", 5, "up")])
    expect("up_increase_ok", v == [])
    v, _ = check_directions([_mk("r.up", 5, "up")], [_mk("r.up", 5, "up")])
    expect("up_hold_ok", v == [])

    v, _ = check_directions([_mk("r.down", 3, "down")], [_mk("r.down", 2, "down")])
    expect("down_increase_violates", len(v) == 1 and "r.down" in v[0])
    v, _ = check_directions([_mk("r.down", 1, "down")], [_mk("r.down", 2, "down")])
    expect("down_decrease_ok", v == [])

    v, _ = check_directions([_mk("r.fr", 27, "frozen")], [_mk("r.fr", 26, "frozen")])
    expect("frozen_change_violates", len(v) == 1 and "r.fr" in v[0])
    v, _ = check_directions([_mk("r.fr", 26, "frozen")], [_mk("r.fr", 26, "frozen")])
    expect("frozen_hold_ok", v == [])

    v, _ = check_directions([_mk("census.axiom_count", 12, "equal_11")], [])
    expect("equal11_wrong_violates", len(v) == 1 and "census" in v[0])
    v, _ = check_directions([_mk("census.axiom_count", 11, "equal_11")], [])
    expect("equal11_ok", v == [])
    v, r = check_directions([_mk("census.axiom_count", UNKNOWN, "equal_11")], [])
    expect("equal11_unknown_reports", v == [] and len(r) == 1)

    v, r = check_directions([_mk("r.up", UNKNOWN, "up")], [_mk("r.up", 5, "up")])
    expect("unknown_current_reports_not_violates", v == [] and len(r) == 1)
    v, r = check_directions([_mk("r.down", UNKNOWN, "down")], [_mk("r.down", 1, "down")])
    expect("unknown_current_down_reports", v == [] and len(r) == 1)
    v, r = check_directions([_mk("r.up", 5, "up")], [_mk("r.up", UNKNOWN, "up")])
    expect("unknown_baseline_reports_not_violates", v == [] and len(r) == 1)

    v, _ = check_directions([], [_mk("r.gone", 5, "up")])
    expect("dropped_row_violates", len(v) == 1 and "r.gone" in v[0])
    v, _ = check_directions([_mk("r.none", 99, "none")], [_mk("r.none", 1, "none")])
    expect("direction_none_never_violates", v == [])

    with tempfile.TemporaryDirectory() as tmp:
        rows = generate_rows(Path(tmp))
        by_id = {r["id"]: r for r in rows}
        expect("missing_producer_all_unknown",
               all(r["value"] == UNKNOWN and r.get("reason") for r in rows),
               f"{sum(1 for r in rows if r['value'] == UNKNOWN)}/{len(rows)} UNKNOWN")
        expect("missing_spine_set_reason",
               by_id["spine_set.size"]["reason"] == SPINE_SET_ABSENT_REASON)
        v, r = check_directions(rows, rows)
        expect("all_unknown_ratchet_reports_only", v == [] and len(r) > 0)

    with tempfile.TemporaryDirectory() as tmp:
        _write(tmp, "data/env_bypass_census.json", {
            "items": [{"item": 1, "status": "watched"},
                      {"item": 2, "status": "unwatched"},
                      {"item": 3, "status": "proved"}]})
        by_id = {r["id"]: r for r in rows_bypass_doors(Path(tmp))}
        expect("env_census_present_counts",
               by_id["bypass_doors.unwatched"]["value"] == 1
               and by_id["bypass_doors.proved"]["value"] == 1)

    with tempfile.TemporaryDirectory() as tmp:
        _write(tmp, "data/env_bypass_census.json", {"surprise": True})
        by_id = {r["id"]: r for r in rows_bypass_doors(Path(tmp))}
        expect("env_census_unrecognized_fails_closed_to_unknown",
               by_id["bypass_doors.unwatched"]["value"] == UNKNOWN
               and by_id["bypass_doors.proved"]["value"] == UNKNOWN)

    # --------------------------------------------- L3 parity tiers (R3)

    with tempfile.TemporaryDirectory() as tmp:
        _write(tmp, "data/parity_tiers.json", _fixture_parity_tiers())
        by_id = {r["id"]: r for r in rows_parity_tiers(Path(tmp))}
        expect("parity_rows_carry_producer_direction_value",
               by_id["parity_tiers.measured"]["value"] == 1
               and by_id["parity_tiers.unknown"]["direction"] == "down"
               and by_id["parity_tiers.stale_vs_generation_head"]["direction"] == "none"
               and by_id["parity_tiers.tier.t-measured.value"]["value"] == 63
               and by_id["parity_tiers.tier.t-measured.value"]["direction"] == "up"
               and by_id["parity_tiers.tier.t-measured.guard."
                         "kernel_check_failures"]["direction"] == "down",
               "%d rows" % len(by_id))
        expect("parity_unknown_tier_keeps_its_own_reason",
               by_id["parity_tiers.tier.t-unknown.value"]["value"] == UNKNOWN
               and "no committed artifact"
               in by_id["parity_tiers.tier.t-unknown.value"]["reason"])

        base = list(by_id.values())
        # planted regression: a monotone-up tier value falls, a monotone-down
        # guard rises — each must be caught and NAMED.
        _write(tmp, "data/parity_tiers.json",
               _fixture_parity_tiers(value=62, guard=6))
        cur = rows_parity_tiers(Path(tmp))
        v, _ = check_directions(cur, base)
        expect("parity_planted_regression_detected",
               len(v) == 2
               and any("tier.t-measured.value" in x and "62" in x for x in v)
               and any("guard.kernel_check_failures" in x for x in v),
               "; ".join(v))

        # a producer that WEAKENS a row's direction is a violation, not a
        # silent re-base (R5).
        _write(tmp, "data/parity_tiers.json",
               _fixture_parity_tiers(ratchet="none"))
        v, _ = check_directions(rows_parity_tiers(Path(tmp)), base)
        expect("parity_direction_weakening_detected",
               any("direction changed (up -> none)" in x for x in v),
               "; ".join(v))

        _write(tmp, "data/parity_tiers.json",
               _fixture_parity_tiers(ratchet="sideways"))
        by_id = {r["id"]: r for r in rows_parity_tiers(Path(tmp))}
        expect("parity_unrecognized_ratchet_withholds_value",
               by_id["parity_tiers.tier.t-measured.value"]["value"] == UNKNOWN
               and "not a direction"
               in by_id["parity_tiers.tier.t-measured.value"]["reason"])

    with tempfile.TemporaryDirectory() as tmp:
        rows = rows_parity_tiers(Path(tmp))
        expect("parity_missing_artifact_unknown_summary_only",
               len(rows) == 4
               and all(r["value"] == UNKNOWN and "absent" in r["reason"]
                       for r in rows))
        _write(tmp, "data/parity_tiers.json", {"summary": {}, "tiers": [
            {"name": "dup", "status": "measured", "value": 1, "ratchet": "up"},
            {"name": "dup", "status": "measured", "value": 2, "ratchet": "up"}]})
        rows = rows_parity_tiers(Path(tmp))
        expect("parity_duplicate_tier_names_fail_closed",
               len(rows) == 4 and all(r["value"] == UNKNOWN for r in rows)
               and "duplicate tier names" in rows[0]["reason"])

    # ---------------------------------------------------- EvalIR (B-SEM)

    with tempfile.TemporaryDirectory() as tmp:
        census_rs, syntax_rs = _fixture_evalir_sources()
        _write(tmp, EVALIR_CENSUS_SRC, census_rs)
        _write(tmp, EVALIR_SYNTAX_SRC, syntax_rs)
        _write(tmp, "data/evalir_coverage.json", _fixture_evalir_coverage())
        _write(tmp, "data/evalir_adequacy_grid.json", _fixture_evalir_grid())
        by_id = {r["id"]: r for r in rows_evalir(Path(tmp))}
        expect("evalir_agreeing_denominator_publishes_fraction",
               by_id["evalir.constructor_census"]["value"] == 3
               and by_id["evalir.denominator_disagreements"]["value"] == 0
               and by_id["evalir.semdiff_covered"]["value"] == 2
               and by_id["evalir.semdiff_unmeasured"]["value"] == 1
               and by_id["evalir.adequacy.declared_delta"]["value"] == 1)
        base = list(by_id.values())

        _write(tmp, "data/evalir_coverage.json", _fixture_evalir_coverage(count=1))
        v, _ = check_directions(rows_evalir(Path(tmp)), base)
        expect("evalir_planted_coverage_regression_detected",
               len(v) == 2
               and any("evalir.semdiff_covered" in x for x in v)
               and any("evalir.semdiff_unmeasured" in x for x in v),
               "; ".join(v))

        # the artifact restates the denominator: a restatement that drifts
        # from the pinned census is DETECTED, counted, and fails the fraction
        # closed instead of picking a side.
        _write(tmp, "data/evalir_coverage.json",
               _fixture_evalir_coverage(total=28))
        cur = rows_evalir(Path(tmp))
        by_id = {r["id"]: r for r in cur}
        v, _ = check_directions(cur, base)
        expect("evalir_denominator_disagreement_detected",
               by_id["evalir.denominator_disagreements"]["value"] == 1
               and by_id["evalir.semdiff_covered"]["value"] == UNKNOWN
               and "DISAGREEMENT" in by_id["evalir.semdiff_covered"]["reason"]
               and by_id["evalir.constructor_census"]["value"] == 3
               and by_id["evalir.adequacy.declared_delta"]["value"] == 1
               and any("evalir.denominator_disagreements" in x for x in v),
               "; ".join(v))

        # the grid restates it too, and is blocked independently.
        _write(tmp, "data/evalir_coverage.json", _fixture_evalir_coverage())
        _write(tmp, "data/evalir_adequacy_grid.json",
               _fixture_evalir_grid(constructors=28))
        by_id = {r["id"]: r for r in rows_evalir(Path(tmp))}
        expect("evalir_grid_denominator_disagreement_blocks_only_the_grid",
               by_id["evalir.denominator_disagreements"]["value"] == 1
               and by_id["evalir.adequacy.field_rows"]["value"] == UNKNOWN
               and by_id["evalir.semdiff_covered"]["value"] == 2)

        # grid arithmetic that does not close is withheld entirely.
        broken = _fixture_evalir_grid()
        broken["totals"]["audit-pin"] = 99
        _write(tmp, "data/evalir_adequacy_grid.json", broken)
        by_id = {r["id"]: r for r in rows_evalir(Path(tmp))}
        expect("evalir_grid_arithmetic_must_close",
               by_id["evalir.adequacy.audit_pin"]["value"] == UNKNOWN
               and "does not close"
               in by_id["evalir.adequacy.audit_pin"]["reason"])

        # the two denominator AUTHORITIES disagreeing withholds everything.
        _write(tmp, "data/evalir_adequacy_grid.json", _fixture_evalir_grid())
        _write(tmp, EVALIR_SYNTAX_SRC,
               _fixture_evalir_sources(("br", "ret"))[1])
        by_id = {r["id"]: r for r in rows_evalir(Path(tmp))}
        expect("evalir_denominator_sources_disagree_fails_closed",
               by_id["evalir.constructor_census"]["value"] == UNKNOWN
               and by_id["evalir.denominator_disagreements"]["value"] == UNKNOWN
               and by_id["evalir.semdiff_covered"]["value"] == UNKNOWN
               and "DISAGREE"
               in by_id["evalir.constructor_census"]["reason"].upper())

    with tempfile.TemporaryDirectory() as tmp:
        rows = rows_evalir(Path(tmp))
        expect("evalir_missing_artifact_unknown",
               all(r["value"] == UNKNOWN and r.get("reason") for r in rows),
               "%d rows" % len(rows))

    # ------------------------------------ Ring R2 lane (b): IO contracts

    with tempfile.TemporaryDirectory() as tmp:
        _write(tmp, "data/verdict_io_contracts.json", _fixture_verdict_io())
        _write(tmp, "data/verdict_set.json", _fixture_verdict_set())
        base_io = rows_verdict_io(Path(tmp))
        base_ledger = rows_assumption_ledger(Path(tmp))
        by_id = {r["id"]: r for r in base_io}
        by_id.update({r["id"]: r for r in base_ledger})
        expect("verdict_io_agreeing_denominator_publishes_counts",
               by_id["verdict_io.site_total"]["value"] == 211
               and by_id["verdict_io.denominator_disagreements"]["value"] == 0
               and by_id["verdict_io.unclassified"]["value"] == 0
               and by_id["verdict_io.contracts_stated"]["value"] == 2
               and by_id["assumption_ledger.verdict_io_lane_b"]["value"] == 44
               and by_id["assumption_ledger.verdict_io_lane_b"]["direction"] == "down")

        _write(tmp, "data/verdict_io_contracts.json",
               _fixture_verdict_io(ledger_rows=45))
        v, _ = check_directions(rows_assumption_ledger(Path(tmp)), base_ledger)
        expect("verdict_io_ledger_planted_regression_detected",
               any("assumption_ledger.verdict_io_lane_b" in x
                   and "44 -> 45" in x for x in v), "; ".join(v))

        _write(tmp, "data/verdict_io_contracts.json",
               _fixture_verdict_io(ledger_rows=44, listed=43))
        by_id2 = {r["id"]: r for r in rows_assumption_ledger(Path(tmp))}
        expect("verdict_io_ledger_self_disagreement_fails_closed",
               by_id2["assumption_ledger.verdict_io_lane_b"]["value"] == UNKNOWN
               and "disagrees with itself"
               in by_id2["assumption_ledger.verdict_io_lane_b"]["reason"])

        _write(tmp, "data/verdict_io_contracts.json", _fixture_verdict_io())
        _write(tmp, "data/verdict_set.json", _fixture_verdict_set(210))
        cur = rows_verdict_io(Path(tmp))
        by_id3 = {r["id"]: r for r in cur}
        v, _ = check_directions(cur, base_io)
        expect("verdict_io_denominator_disagreement_detected",
               by_id3["verdict_io.denominator_disagreements"]["value"] == 1
               and by_id3["verdict_io.site_total"]["value"] == UNKNOWN
               and "210" in by_id3["verdict_io.site_total"]["reason"]
               and "211" in by_id3["verdict_io.site_total"]["reason"]
               and any("verdict_io.denominator_disagreements" in x for x in v),
               "; ".join(v))

        # the authority itself going missing withholds the counts too.
        (Path(tmp) / "data/verdict_set.json").unlink()
        by_id4 = {r["id"]: r for r in rows_verdict_io(Path(tmp))}
        expect("verdict_io_missing_denominator_authority_fails_closed",
               by_id4["verdict_io.site_total"]["value"] == UNKNOWN
               and by_id4["verdict_io.denominator_disagreements"]["value"] == UNKNOWN)

        # classification arithmetic that does not close is withheld.
        _write(tmp, "data/verdict_set.json", _fixture_verdict_set())
        bad = _fixture_verdict_io()
        bad["classification"]["sites_issuing_no_io"] = 84
        _write(tmp, "data/verdict_io_contracts.json", bad)
        by_id5 = {r["id"]: r for r in rows_verdict_io(Path(tmp))}
        expect("verdict_io_classification_must_close",
               by_id5["verdict_io.site_total"]["value"] == UNKNOWN
               and "does not close" in by_id5["verdict_io.site_total"]["reason"]
               and by_id5["verdict_io.denominator_disagreements"]["value"] == 0)

    with tempfile.TemporaryDirectory() as tmp:
        rows = rows_verdict_io(Path(tmp)) + [_ledger_lane_b_row(Path(tmp))]
        expect("verdict_io_missing_artifact_unknown",
               all(r["value"] == UNKNOWN and r.get("reason") for r in rows),
               "%d rows" % len(rows))

    # --------------------------------------- §3.6 assumption ledger (R8)

    with tempfile.TemporaryDirectory() as tmp:
        rows = rows_assumption_ledger(Path(tmp))
        expect("assumption_ledger_missing_artifact_unknown",
               len(rows) == 4
               and all(r["value"] == UNKNOWN and r.get("reason") for r in rows)
               and "not minted" in rows[0]["reason"],
               "%d rows" % len(rows))

        _write(tmp, "data/verdict_io_contracts.json", _fixture_verdict_io())
        _write(tmp, "data/spine_assumption_ledger.json",
               _fixture_assumption_ledger())
        base_al = rows_assumption_ledger(Path(tmp))
        by_id = {r["id"]: r for r in base_al}
        expect("assumption_ledger_publishes_live_and_prospective",
               by_id["assumption_ledger.count"]["value"] == 26
               and by_id["assumption_ledger.count"]["direction"] == "down"
               and by_id["assumption_ledger.prospective"]["value"] == 3
               and by_id["assumption_ledger.prospective"]["direction"] == "none"
               and by_id["assumption_ledger.cross_reference_disagreements"]["value"] == 0
               and by_id["assumption_ledger.verdict_io_lane_b"]["value"] == 44,
               "%d rows" % len(base_al))

        # planted regression: the ledger of unproved things GREW.
        _write(tmp, "data/spine_assumption_ledger.json",
               _fixture_assumption_ledger(measured=27))
        v, _ = check_directions(rows_assumption_ledger(Path(tmp)), base_al)
        expect("assumption_ledger_planted_regression_detected",
               len(v) == 1 and "assumption_ledger.count" in v[0]
               and "26 -> 27" in v[0], "; ".join(v))

        # a prospective row is REPORTED, never ratcheted: a job that has not
        # run cannot make the gate red by existing.
        _write(tmp, "data/spine_assumption_ledger.json",
               _fixture_assumption_ledger(prospective=4))
        v, _ = check_directions(rows_assumption_ledger(Path(tmp)), base_al)
        expect("assumption_ledger_prospective_reported_not_ratcheted",
               v == [], "; ".join(v))

        # the ledger's own arithmetic must close, in each shape.
        _write(tmp, "data/spine_assumption_ledger.json",
               _fixture_assumption_ledger(count=25))
        by_id = {r["id"]: r for r in rows_assumption_ledger(Path(tmp))}
        expect("assumption_ledger_count_len_disagreement_fails_closed",
               by_id["assumption_ledger.count"]["value"] == UNKNOWN
               and "disagrees with itself"
               in by_id["assumption_ledger.count"]["reason"]
               and "status=measured" in by_id["assumption_ledger.count"]["reason"]
               and by_id["assumption_ledger.prospective"]["value"] == UNKNOWN)

        _write(tmp, "data/spine_assumption_ledger.json",
               _fixture_assumption_ledger(row_count=30))
        by_id = {r["id"]: r for r in rows_assumption_ledger(Path(tmp))}
        expect("assumption_ledger_row_count_disagreement_fails_closed",
               by_id["assumption_ledger.count"]["value"] == UNKNOWN
               and "row_count=30" in by_id["assumption_ledger.count"]["reason"])

        # the lane-(b) split is only honest while the pointer between the two
        # artifacts holds: a stale cross-reference is a detected disagreement,
        # not a silently double-counted or dropped set of rows.
        _write(tmp, "data/spine_assumption_ledger.json",
               _fixture_assumption_ledger(xref_rows=43))
        cur = rows_assumption_ledger(Path(tmp))
        by_id = {r["id"]: r for r in cur}
        v, _ = check_directions(cur, base_al)
        expect("assumption_ledger_cross_reference_disagreement_detected",
               by_id["assumption_ledger.cross_reference_disagreements"]["value"] == 1
               and by_id["assumption_ledger.count"]["value"] == 26
               and any("cross_reference_disagreements" in x for x in v),
               "; ".join(v))

        _write(tmp, "data/spine_assumption_ledger.json",
               _fixture_assumption_ledger(xref=False))
        by_id = {r["id"]: r for r in rows_assumption_ledger(Path(tmp))}
        expect("assumption_ledger_missing_cross_reference_fails_closed",
               by_id["assumption_ledger.cross_reference_disagreements"]["value"] == UNKNOWN
               and "cross_references"
               in by_id["assumption_ledger.cross_reference_disagreements"]["reason"])

        _write(tmp, "data/spine_assumption_ledger.json", {"entries": []})
        by_id = {r["id"]: r for r in rows_assumption_ledger(Path(tmp))}
        expect("assumption_ledger_empty_entries_fails_closed",
               by_id["assumption_ledger.count"]["value"] == UNKNOWN
               and "ZERO entries" in by_id["assumption_ledger.count"]["reason"])

    # Read-only ratchet / explicit refresh contract, against a temp repo root
    # (their prints are swallowed so the arm verdicts below stay readable).
    quiet = io.StringIO()
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        sb_path = root / SCOREBOARD_REL

        with contextlib.redirect_stdout(quiet):
            rc = run_ratchet(root)
        expect("ratchet_missing_baseline_fails_closed_writes_nothing",
               rc == 1 and not sb_path.exists())

        with contextlib.redirect_stdout(quiet):
            rc = run_refresh(root)
        refreshed = _load_json(sb_path)
        expect("refresh_writes_baseline",
               rc == 0 and isinstance(refreshed, dict)
               and refreshed.get("schema") == "clean.spine.scoreboard/1"
               and isinstance(refreshed.get("rows"), list))

        green_bytes = sb_path.read_bytes()
        with contextlib.redirect_stdout(quiet):
            rc = run_ratchet(root)
        expect("ratchet_green_leaves_bytes_untouched",
               rc == 0 and sb_path.read_bytes() == green_bytes)

        tampered = json.loads(green_bytes.decode("utf-8"))
        tampered["rows"].append(
            {"id": "self.test.gone", "value": 1, "direction": "up",
             "producer": "self-test"})
        sb_path.write_text(json.dumps(tampered, indent=2) + "\n",
                           encoding="utf-8")
        tampered_bytes = sb_path.read_bytes()
        with contextlib.redirect_stdout(quiet):
            rc = run_ratchet(root)
        expect("ratchet_violation_leaves_bytes_untouched",
               rc == 1 and sb_path.read_bytes() == tampered_bytes
               and "self.test.gone" in quiet.getvalue())

        garbage = b"{ not json"
        sb_path.write_bytes(garbage)
        with contextlib.redirect_stdout(quiet):
            rc = run_ratchet(root)
        expect("ratchet_unreadable_baseline_fails_closed_writes_nothing",
               rc == 1 and sb_path.read_bytes() == garbage)

        with contextlib.redirect_stdout(quiet):
            rc = run_refresh(root)
        expect("refresh_overwrites_unreadable_baseline",
               rc == 0 and sb_path.read_bytes() != garbage
               and isinstance(_load_json(sb_path), dict))

    if failures:
        print(f"self-test: FAIL ({len(failures)} arm(s)): {', '.join(failures)}")
        return 1
    print("self-test: PASS (all arms)")
    return 0


# -------------------------------------------------------------------- modes


def run_ratchet(repo_root: Path):
    """READ-ONLY direction enforcement vs the committed baseline.

    Never writes, in any outcome: on green it touches nothing, on violation
    it exits 1 naming the row and leaves the baseline alone, and a missing or
    unreadable baseline is itself a failure — the gate leg that calls this
    used to fail hard on a missing baseline (via its save/restore wrapper's
    `cp`), and going read-only must not weaken that. Mint a baseline with
    --refresh and commit it; the ratchet cannot mint one.
    """
    out_path = repo_root / SCOREBOARD_REL
    baseline_doc = _load_json(out_path)
    if not isinstance(baseline_doc, dict) or \
            not isinstance(baseline_doc.get("rows"), list):
        print(f"spine_scoreboard --ratchet: RED — no committed baseline at "
              f"{SCOREBOARD_REL} (absent or unreadable). --ratchet is "
              "read-only and cannot mint one; regenerate with --refresh and "
              "commit the result")
        return 1
    rows = generate_rows(repo_root)
    violations, reports = check_directions(rows, baseline_doc["rows"])
    for line in reports:
        print(f"  report: {line}")
    if violations:
        for line in violations:
            print(f"  VIOLATION: {line}")
        print(f"spine_scoreboard --ratchet: RED — {len(violations)} "
              f"violation(s); baseline {SCOREBOARD_REL} left untouched")
        return 1
    unknown = sum(1 for r in rows if r["value"] == UNKNOWN)
    print(f"spine_scoreboard: ratchet OK (read-only) — {len(rows)} rows "
          f"({unknown} UNKNOWN, first-class) vs baseline {SCOREBOARD_REL}")
    return 0


def run_refresh(repo_root: Path):
    """Regenerate + write the baseline artifact (generator mode)."""
    out_path = repo_root / SCOREBOARD_REL
    scoreboard = build_scoreboard(repo_root)
    rows = scoreboard["rows"]
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as fh:
        json.dump(scoreboard, fh, indent=2)
        fh.write("\n")
    print_rows(rows)
    unknown = sum(1 for r in rows if r["value"] == UNKNOWN)
    print(f"spine_scoreboard: generated — {len(rows)} rows "
          f"({unknown} UNKNOWN, first-class) -> {SCOREBOARD_REL}")
    return 0


# --------------------------------------------------------------------- main


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--ratchet", action="store_true",
                      help="READ-ONLY: enforce directions vs the committed "
                           "baseline; never writes (missing baseline fails "
                           "closed — mint with --refresh)")
    mode.add_argument("--refresh", action="store_true",
                      help="regenerate data/spine_scoreboard.json (the "
                           "no-flag generator mode, stated explicitly)")
    mode.add_argument("--self-test", action="store_true",
                      help="run the direction/UNKNOWN/missing-producer/"
                           "read-only-ratchet arms")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    if args.ratchet:
        return run_ratchet(REPO_ROOT)
    return run_refresh(REPO_ROOT)


if __name__ == "__main__":
    sys.exit(main())
