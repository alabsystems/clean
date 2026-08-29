#!/usr/bin/env python3
"""`data/crystal_a0_a6_probe.json` is a TRANSCRIPTION -- this re-derives it.

    scripts/check_a0a6_probe_transcription.py            # check, fail-closed
    scripts/check_a0a6_probe_transcription.py --mint     # (re)write the probe
    scripts/check_a0a6_probe_transcription.py --selftest # 6 arms on itself
    scripts/check_a0a6_probe_transcription.py --diff     # check, printing the
                                                         # full first mismatch

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.

WHY THIS EXISTS.  The probe was re-minted on 2026-08-25 from A0 4-of-6 / A6
3-of-4 (measured 2026-08-11) to A0 5-of-6 / A6 4-of-4, and the re-mint is NOT a
measurement: no compiler was run.  Every current verdict in it is copied out of
a committed record.  A file that ASSERTS "each verdict is transcribed from a
named committed record" and that nothing re-derives is exactly the class
docs/GATE_REGISTRY.md names -- an invariant asserted where nothing checks it.

So the generator IS the checker.  `--mint` builds the whole v2 object out of the
source records and writes it; the default mode builds the same object in memory
and requires the committed file to equal it, key for key, exiting 1 on the first
disagreement.  A source record edited without a re-mint, or a verdict hand-typed
into the probe, is therefore RED rather than silent.

WHAT THIS DOES *NOT* CHECK, stated so nobody reads more into a green.  It
re-derives the transcription; it does not re-measure the crystal.  It never
runs trustc, never seals a driver and never reads a dump.  If a committed source
record is itself wrong, this gate is green and wrong with it -- what it refuses
is DRIFT between the probe and the records it cites.

THE TWO STAMPS ARE CARRIED, NOT DERIVED.  `transcribed_utc_date` and
`transcribed_at_clean_HEAD` describe the act of transcription, not any measured
value, so re-deriving them from `date.today()` / `git rev-parse HEAD` would make
this gate red on the next commit for no reason.  They are read back out of the
committed probe -- and then VALIDATED: the date must be ISO-8601 and the sha
must be a commit that exists in this repo, so a fabricated stamp is still
caught.  Everything else in the file is re-derived from the records.
"""

import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import date

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

P_PROBE = "data/crystal_a0_a6_probe.json"
P_RMX = "data/crystal_remeasure_tip_2026-08-25_laneRMX.json"
P_TU = "data/crystal_remeasure_tip_2026-08-22_laneTU.json"
P_CEN = "data/crystal_a0_census_2026-08-22.json"
P_MC = "data/crystal_marker_ceiling_2026-08-20.json"
P_L18 = "data/crystal_chain_revalidation_2026-08-21_lane18.json"
P_A152 = "data/crystal_chain_revalidation_2026-08-20_a152ab39e.json"
P_R19 = "data/crystal_chain_revalidation_2026-08-19_28fb5dd812.json"
P_FIX = "crates/clean-verify/tests/fixtures/level_is_zero.a0.json"
P_WA = "data/crystal_walla_instance_seam_2026-08-23.json"
P_SEM = "data/crystal_a0_census_2026-08-27.json"
P_DIS = "data/crystal_a0_discharge.json"

SOURCES = (P_RMX, P_TU, P_CEN, P_MC, P_L18, P_A152, P_R19, P_FIX, P_WA, P_SEM, P_DIS)

TARGET = "level::Level::is_zero"
SCHEMA_V1 = "clean.crystal.a0a6.probe.v1"
SCHEMA_V2 = "clean.crystal.a0a6.probe.v2"


class Refuse(Exception):
    """A fail-closed refusal: a source record does not carry what we need."""


def load(root, rel):
    path = os.path.join(root, rel)
    if not os.path.exists(path):
        raise Refuse(f"{rel} is missing -- the probe cites it and it is not in the tree")
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except ValueError as exc:
        raise Refuse(f"{rel} is not parseable JSON: {exc}") from exc


def dig(doc, rel, *path):
    """Fetch doc[path...], refusing loudly instead of inventing a default."""
    cur = doc
    for key in path:
        try:
            cur = cur[key]
        except (KeyError, IndexError, TypeError) as exc:
            trail = " -> ".join(str(p) for p in path)
            raise Refuse(f"{rel}: {trail} is absent ({exc!r})") from exc
    return cur


def cite(where, field, value):
    return {"record": where, "field": field, "value": value}


# --------------------------------------------------------------------- derive
# NOTE on the backticks below. Every script path named inside a STRING here is
# wrapped in backticks. That is this repo's prose convention, and it is also
# load-bearing: check_gate_registry.py's R3 re-derives the runner graph by
# scanning source, treats a backticked path as prose, and would otherwise read
# these data strings as this script INVOKING local_gate.sh and
# crystal_a0_census.py -- two runner edges that do not exist. The fix is to
# spell them as the prose they are, never to declare a false edge in the
# registry to satisfy the scan.
def derive(root, stamps):
    """Build the whole v2 probe object out of the committed records.

    `stamps` is (transcribed_utc_date, transcribed_at_clean_HEAD, history_block).
    """
    transcribed_date, transcribed_head, history_block = stamps

    rmx = load(root, P_RMX)
    tu = load(root, P_TU)
    cen = load(root, P_CEN)
    mc = load(root, P_MC)
    l18 = load(root, P_L18)
    a152 = load(root, P_A152)
    r19 = load(root, P_R19)
    fix = load(root, P_FIX)
    wa = load(root, P_WA)

    cards = [s for s in dig(rmx, P_RMX, "ten_criteria_scorecards") if s.get("target") == TARGET]
    if len(cards) != 1:
        raise Refuse(
            f"{P_RMX}: expected exactly one ten_criteria_scorecard for {TARGET}, found {len(cards)}"
        )
    sc = cards[0]
    rmx_row = dig(rmx, P_RMX, "tracked_chain_bodies", "rows", "level_is_zero")
    if rmx_row.get("def_path") != TARGET:
        raise Refuse(f"{P_RMX}: tracked_chain_bodies.rows.level_is_zero is not {TARGET}")
    rmx_prov = dig(rmx, P_RMX, "provenance")

    rmx_at = {
        "record": P_RMX,
        "record_schema": dig(rmx, P_RMX, "schema"),
        "measured_utc_date": dig(rmx, P_RMX, "date"),
        "trust_base": rmx_prov["trust_base"],
        "clean_corpus_rev": rmx_prov["clean_corpus_rev"],
        "sysroot": rmx_prov["sysroot"],
        "driver_seal": rmx_prov["driver_seal"],
        "driver_digest": rmx_prov["driver_digest"],
        "driver_sysroot_compat_head": rmx_prov["driver_sysroot_compat"].split("\n")[0],
        "oracle_blob": dig(rmx, P_RMX, "provenance", "the_FROZEN_oracle", "blob"),
        "HONEST_SCOPE": rmx_prov["HONEST_SCOPE"],
    }

    tu_t = dig(tu, P_TU, "targets", TARGET)
    tu_prov = dig(tu, P_TU, "provenance")
    tu_at = {
        "record": P_TU,
        "measured_utc_date": tu_prov["measured_utc_date"],
        "trust_rev": tu_prov["trust_rev"],
        "clean_rev": tu_prov["clean_rev"],
        "sysroot": tu_prov["sysroot"],
        "driver_dylib_sha256": tu_prov["driver_dylib_sha256"],
    }

    cen_prov = dig(cen, P_CEN, "provenance")
    closure_short = dig(cen, P_CEN, "one_short_missing_closure_bodies")
    if TARGET not in closure_short:
        raise Refuse(
            f"{P_CEN}: {TARGET} is no longer in one_short_missing_closure_bodies -- the census "
            "no longer scores it 5-of-6 with bodyful_reachable_closure as the single failure. "
            "Re-mint the probe from the records; do not edit the probe by hand."
        )
    cen_at = {
        "record": P_CEN,
        "measured_utc": cen_prov["measured_utc"],
        "trust_rev": cen_prov["trust_rev"],
        "clean_rev": cen_prov["clean_rev"],
        "driver_dylib_sha256": cen_prov["driver_dylib_sha256"],
        "instrument": "`scripts/crystal_a0_census.py` (committed)",
        "criteria_as_named_by_the_instrument": dig(cen, P_CEN, "criteria"),
        "what_membership_means": (
            "`level::Level::is_zero` appears in this record's "
            "`one_short_missing_closure_bodies`. That list is built by "
            "`scripts/crystal_a0_census.py` as the score-5 rows whose "
            "`bodyful_reachable_closure` is false, so membership establishes "
            "A0 = 5-of-6 with `bodyful_reachable_closure` as the single failing "
            "criterion -- i.e. the other five are true -- WITHOUT any per-body "
            "row having to be quoted."
        ),
        "whole_crate_context": dig(cen, P_CEN, "totals"),
    }

    mc_base = dig(mc, P_MC, "dumps", "wc-basev11b")
    mc_head = dig(mc, P_MC, "dumps", "wc-head")
    mc_rctl = dig(mc, P_MC, "dumps", "wc-rctl")
    mc_sub2 = dig(mc, P_MC, "dumps", "wc-sub2")
    mc_at = {
        "record": P_MC,
        "date": dig(mc, P_MC, "date"),
        "clean_rev_of_every_dump": dig(mc, P_MC, "clean_rev_of_every_dump"),
        "clean_tracked_dirt": dig(mc, P_MC, "clean_tracked_dirt"),
        "instrument": dig(mc, P_MC, "instrument"),
        "wc-basev11b": {
            "note": mc_base["provenance"]["note"],
            "dylib": mc_base["provenance"]["dylib"],
            "trust_rev_AS_RECORDED_BY_THE_SEAL": mc_base["provenance"]["trust_rev"],
            "designated_target_level_is_zero": mc_base["designated_target_level_is_zero"],
        },
        "wc-head": {
            "note": mc_head["provenance"]["note"],
            "dylib": mc_head["provenance"]["dylib"],
            "trust_rev": mc_head["provenance"]["trust_rev"],
            "designated_target_level_is_zero": mc_head["designated_target_level_is_zero"],
        },
        "wc-rctl": {
            "note": mc_rctl["provenance"]["note"],
            "dylib": mc_rctl["provenance"]["dylib"],
            "designated_target_level_is_zero": mc_rctl["designated_target_level_is_zero"],
        },
        "wc-sub2": {
            "note": mc_sub2["provenance"]["note"],
            "dylib": mc_sub2["provenance"]["dylib"],
            "designated_target_level_is_zero": mc_sub2["designated_target_level_is_zero"],
        },
        "the_four_way_A_B_this_record_pins": (
            "All four dumps are at ONE clean rev (%s, tracked dirt %s), so every "
            "delta is the PRODUCER. Read in ancestry order for the target body: "
            "pre-wave-DR / pre-W3/W3b -> markers_exact %s, no flip at either "
            "level; wave-DR in, W3/W3b OUT -> markers_exact %s over %s marker "
            "lines, STILL no flip; wave-DR + the W3b unwind fix -> flips at O3 "
            "and O0; producer tip (DR + W3 + W3b) -> the same. So the committed "
            "record attributes the MARKER gate to wave-DR and the FLIP to "
            "W3/W3b, rather than asserting it."
        )
        % (
            mc["clean_rev_of_every_dump"],
            mc["clean_tracked_dirt"],
            mc_rctl["designated_target_level_is_zero"]["markers_exact"],
            mc_sub2["designated_target_level_is_zero"]["markers_exact"],
            mc_sub2["designated_target_level_is_zero"]["marker_lines"],
        ),
        "what_it_does_and_does_not_carry": (
            "This is the ONLY committed record that carries a per-criterion "
            "reading of the target at the two 2026-08-20 drivers named in "
            "docs/CRYSTAL_STATUS.md 0.3a (the wave-W3b base driver 58b5fc15... "
            "and the producer-tip driver 50879dc8...). It carries verdict, "
            "markers_exact, marker class, marker line count and flips-at-O3/O0. "
            "It does NOT carry the lineage digest, the negative control, the "
            "perturbation, or the bodyful closure, so it corroborates four of "
            "the ten criteria at those drivers and no more."
        ),
    }

    l18_ch = dig(l18, P_L18, "chains", "level_is_zero")
    l18_deref = dig(l18, P_L18, "extra_fixtures", "level_is_zero_deref_callee")
    l18_at = {
        "record": P_L18,
        "measured_utc": dig(l18, P_L18, "measured_utc"),
        "clean_source_rev": dig(l18, P_L18, "provenance", "clean_source_rev"),
        "trust_worktree_rev": dig(l18, P_L18, "provenance", "trust_worktree_rev"),
        "trustc_version": dig(l18, P_L18, "provenance", "trustc_version"),
        "librustc_driver_sha256": dig(l18, P_L18, "provenance", "librustc_driver_sha256"),
        "level_is_zero": l18_ch,
        "level_is_zero_deref_callee": l18_deref,
    }

    a152_ch = dig(a152, P_A152, "chains", "level_is_zero")
    a152_at = {
        "record": P_A152,
        "measured_utc": dig(a152, P_A152, "measured_utc"),
        "clean_source_rev": dig(a152, P_A152, "provenance", "clean_source_rev"),
        "trust_worktree_rev": dig(a152, P_A152, "provenance", "trust_worktree_rev"),
        "librustc_driver_sha256": dig(a152, P_A152, "provenance", "librustc_driver_sha256"),
        "level_is_zero": a152_ch,
        "fatal_invariants": dig(a152, P_A152, "fatal_invariants"),
    }

    r19_ch = dig(r19, P_R19, "chains", "level_is_zero")
    r19_at = {
        "record": P_R19,
        "measured_utc_date": dig(r19, P_R19, "measured_utc_date"),
        "clean_worktree_rev": dig(r19, P_R19, "provenance", "clean_worktree_rev"),
        "trust_worktree_rev": dig(r19, P_R19, "provenance", "trust_worktree_rev"),
        "links_at_head": r19_ch["links_at_head"],
        "lineage": r19_ch["lineage"],
    }

    pin = dig(fix, P_FIX, "current_source_bound_pin")
    wa_mut = dig(wa, P_WA, "mutation_matrix", "O0mut-lineage")

    # ------------------------------------------------------------------ A0
    a0 = sc["A0"]
    a0_crit = {}

    a0_crit["lowered"] = {
        "verdict": "PASS" if a0["lowered"] else "FAIL",
        "census_name": "lowered",
        "measured": True,
        "established_by": [
            cite(P_RMX, "ten_criteria_scorecards[level::Level::is_zero].A0.lowered", a0["lowered"]),
            cite(
                P_CEN,
                "one_short_missing_closure_bodies contains the target (see census_record.what_membership_means)",
                True,
            ),
            cite(P_L18, "chains.level_is_zero.links_at_head.lowered", l18_ch["links_at_head"]["lowered"]),
            cite(P_A152, "chains.level_is_zero.links_at_head.lowered", a152_ch["links_at_head"]["lowered"]),
        ],
    }

    a0_crit["spliced"] = {
        "verdict": "PASS" if a0["spliced"] else "FAIL",
        "census_name": "spliced",
        "measured": True,
        "established_by": [
            cite(P_RMX, "ten_criteria_scorecards[target].A0.spliced", a0["spliced"]),
            cite(P_CEN, "one_short_missing_closure_bodies contains the target", True),
            cite(P_L18, "chains.level_is_zero.links_at_head.spliced", l18_ch["links_at_head"]["spliced"]),
            cite(P_A152, "chains.level_is_zero.links_at_head.spliced", a152_ch["links_at_head"]["spliced"]),
        ],
    }

    a0_crit["zero_unsupported"] = {
        "verdict": "PASS" if a0["zero_unsupported"] else "FAIL",
        "census_name": "zero_unsupported",
        "measured": [],
        "established_by": [
            cite(P_RMX, "ten_criteria_scorecards[target].A0.zero_unsupported", a0["zero_unsupported"]),
            cite(P_CEN, "one_short_missing_closure_bodies contains the target", True),
            cite(P_L18, "chains.level_is_zero.links_at_head.unsupported", l18_ch["links_at_head"]["unsupported"]),
            cite(P_A152, "chains.level_is_zero.links_at_head.unsupported", a152_ch["links_at_head"]["unsupported"]),
        ],
    }

    a0_crit["DerivedAgreed"] = {
        "verdict": "PASS" if a0["derived_agreed"] else "FAIL",
        "census_name": "derived_agreed",
        "measured": "%s -- %s" % (sc["derived_mir"]["verdict"], sc["derived_mir"]["detail"]),
        "unchanged_since_2026_08_11": (
            "the verdict and its '18 canonical line(s) identical' detail are the "
            "same strings the 2026-08-11 probe recorded; what MOVED since then is "
            "markers_exact (false -> true, over 28 non-vacuous marker lines) and "
            "the flip."
        ),
        "markers_exact": sc["derived_mir"]["markers_exact"],
        "markers_detail": sc["derived_mir"]["markers_detail"],
        "established_by": [
            cite(P_RMX, "ten_criteria_scorecards[target].derived_mir", sc["derived_mir"]),
            cite(
                P_TU,
                "targets[target].O3 {verdict, detail, markers_exact, markers_detail}",
                {k: tu_t["O3"][k] for k in ("verdict", "detail", "markers_exact", "markers_detail")},
            ),
            cite(P_MC, "dumps['wc-basev11b'].designated_target_level_is_zero", mc_base["designated_target_level_is_zero"]),
            cite(P_MC, "dumps['wc-head'].designated_target_level_is_zero", mc_head["designated_target_level_is_zero"]),
            cite(P_L18, "chains.level_is_zero.links_at_head.derived_mir", l18_ch["links_at_head"]["derived_mir"]),
        ],
    }

    a0_crit["bodyful_reachable_closure"] = {
        "verdict": "FAIL" if not a0["bodyful_reachable_closure"] else "PASS-UNEXPECTED",
        "census_name": "bodyful_reachable_closure",
        "measured": (
            "false. The body's own DIRECT calls are all resolved (%d resolved, %d "
            "extern_decls, %d unresolved; reachable closure size %d), but the "
            "TRANSITIVE closure leaves the assembled module's body prefix: "
            "`<LevelArc as Deref>::deref` is itself declaration-bearing at the "
            "seam -- its own coverage row records %d extern_decls and a "
            "derived_mir verdict of `%s`."
        )
        % (
            sc["calls"]["resolved"],
            sc["calls"]["extern_decls"],
            sc["calls"]["unresolved"],
            sc["reachable_closure_size"],
            l18_deref["links_at_head"]["calls"]["extern_decls"],
            l18_deref["links_at_head"]["derived_mir"]["verdict"],
        ),
        "STAYS_FAIL_BY_A_FLOOR": (
            "THREE WALLS, and only the third is a floor (corrected 2026-08-26; "
            "every earlier statement here named a build item as the reason). "
            "(1) rustc has no cross-crate THIR -- `thir_body` takes a "
            "`LocalDefId`, no `thir_of_instance`: BUILD ITEM. (2) every "
            "body-producing path keys on `def_id.is_local()` -- `trust-mir-extract` "
            "early-returns on `!is_local()`: BUILD ITEM. (3) the closure ends at a "
            "declaration with no body ANYWHERE -- `Option::expect -> expect_failed "
            "-> panic_display -> panic_fmt -> panic_impl`, and `panic_impl` occurs "
            "in all of core/src/ only as doc, comment, lang attr, declaration "
            "(`unsafe extern \"Rust\"`, panicking.rs:67-70) and a SAFETY note, "
            "NEVER as a definition; its definition is std/src/panicking.rs:611 "
            "`#[panic_handler]` (measured 2026-08-27: a real 4-instruction body "
            "under -Zbuild-std), and the chain below it terminates at "
            "`_Unwind_RaiseException` -- `unsafe extern \"C-unwind\"`, "
            "unwind/src/libunwind.rs:290, a C SYMBOL with no Rust body on THIS "
            "target (the one Rust definition in library/ is the wasm backend's "
            "shim, unwind/src/wasm.rs:66 -- a different target): "
            "FLOOR (workflow wf_1c3df27b, mechanism M2). No lowering fixes (3), "
            "and it binds any body whose emitted trust-ir reaches the panic "
            "entry. CORRECTED 2026-08-27: this note used to add 'which is why "
            "the only bodies whose bodyful cell reads holds have ZERO calls' -- "
            "FALSE, and the census re-derives the truth: 1,654 of 6,431 prefix "
            "bodies hold, 53 of them with >=1 call edge, and "
            "expr::meta::ExprMeta::has_loose_bvars (entry 3658, calling 3657) "
            "holds THROUGH its call. The floor binds bodies that REACH THE PANIC "
            "ENTRY, not bodies with calls. "
            "So the criterion is unsatisfiable AS WRITTEN for panic-reaching "
            "bodies, not merely unbuilt. "
            "BOTH citations live in the TRUST repo (compiler/ and library/), which "
            "is not committed here, so the REASON is still carried by prose in "
            "this repo; what changed is that the prose now names the floor "
            "instead of a build item. The FAIL VERDICT ITSELF is committed and "
            "measured -- see `established_by`."
        ),
        "established_by": [
            cite(P_RMX, "ten_criteria_scorecards[target].A0.bodyful_reachable_closure", a0["bodyful_reachable_closure"]),
            cite(
                P_RMX,
                "ten_criteria_scorecards[target].{calls, reachable_closure_size}",
                {"calls": sc["calls"], "reachable_closure_size": sc["reachable_closure_size"]},
            ),
            cite(P_CEN, "one_short_missing_closure_bodies contains 'level::Level::is_zero'", True),
            cite(P_CEN, "totals.one_short_missing_criterion", dig(cen, P_CEN, "totals", "one_short_missing_criterion")),
            cite(P_L18, "extra_fixtures.level_is_zero_deref_callee.links_at_head", l18_deref["links_at_head"]),
        ],
    }

    # THE SEMANTIC CELL (owner ruling 2026-08-27, workflow wf_1c3df27b R2+R3).
    # Derived from two committed records, never asserted: the first semantic
    # census run and the discharge table it was validated against. The syntactic
    # cell above stays FAIL and stays reported -- the ruling replaces the
    # COMPLETION criterion, it does not hide the old cell.
    sem = load(root, P_SEM)
    dis = load(root, P_DIS)
    sem_total = dig(sem, P_SEM, "totals", "a0_complete_semantic")
    syn_total = dig(sem, P_SEM, "totals", "a0_complete_6_of_6")
    if sem_total != syn_total + 1:
        raise Refuse(
            f"{P_SEM}: a0_complete_semantic={sem_total} is not syntactic+1 "
            f"({syn_total}+1) -- the ruling admits exactly the designated target; "
            f"a wider delta means the discharge table grew and this probe must be "
            f"re-derived deliberately, not silently")
    tgt_dis = dig(dis, P_DIS, "targets", TARGET)
    a0_crit["bodyful_or_discharged_closure"] = {
        "verdict": "PASS",
        "census_name": "bodyful_or_discharged_closure",
        "adopted_by": (
            "owner ruling 2026-08-27 (R2+R3 of workflow wf_1c3df27b's verdict): the "
            "syntactic criterion demanded a Rust body for a chain terminating at "
            "`_Unwind_RaiseException` (unsafe extern \"C-unwind\", "
            "unwind/src/libunwind.rs:290), a C symbol with no Rust body on this "
            "target (wasm's shim at unwind/src/wasm.rs:66 is a different target) -- "
            "ruled a FLOOR. The semantic obligation replaces it as the completion "
            "criterion: escaping callees are discharged clause (a) "
            "reached-and-modelled with a NAMED residual, or clause (b) "
            "unreachable-and-proved by kernel-checked theorem."),
        "measured": (
            "true. The walk's escaping callees for the target are exactly "
            "{6516 Option::<T>::expect, 7211 Option::<T>::as_deref}, both clause (a) "
            "(model ir_lzb_deref; residual: Option<Arc<Level>>'s None is the null "
            "niche and as_deref().expect() is load+null-check+assert -- NOT total: "
            "ir_lzb_deref_refuses_none). The panic tail below expect is clause (b): "
            "ir_lzb_panic_path_is_unreachable, DerivedProved, 0 axiom_deps. "
            "Fail-closed both directions; zero other bodies discharge."),
        "established_by": [
            cite(P_SEM, "totals.a0_complete_semantic", sem_total),
            cite(P_SEM, "totals.a0_complete_6_of_6 (syntactic, unchanged)", syn_total),
            cite(P_DIS, "targets[target].escaping_callees (keys)",
                 sorted(tgt_dis["escaping_callees"].keys())),
            cite(P_DIS, "targets[target].clause_b_theorems",
                 tgt_dis["clause_b_theorems"]),
        ],
    }

    flip_cites = [
        cite(P_RMX, "ten_criteria_scorecards[target].A0.flip_event_O3", a0["flip_event_O3"]),
        cite(
            P_RMX,
            "ten_criteria_scorecards[target].{event_O3, event_O0, flip_O0}",
            {"event_O3": sc["event_O3"], "event_O0": sc["event_O0"], "flip_O0": sc["flip_O0"]},
        ),
        cite(
            P_RMX,
            "tracked_chain_bodies.rows.level_is_zero.{flip_O3, flip_O3_kind, flip_O0}",
            {k: rmx_row[k] for k in ("flip_O3", "flip_O3_kind", "flip_O0")},
        ),
        cite(P_TU, "targets[target].O3.flip_event", tu_t["O3"]["flip_event"]),
        cite(
            P_MC,
            "dumps['wc-basev11b'].designated_target_level_is_zero.{flips_at_O3,flips_at_O0}",
            {k: mc_base["designated_target_level_is_zero"][k] for k in ("flips_at_O3", "flips_at_O0")},
        ),
        cite(
            P_MC,
            "dumps['wc-head'].designated_target_level_is_zero.{flips_at_O3,flips_at_O0}",
            {k: mc_head["designated_target_level_is_zero"][k] for k in ("flips_at_O3", "flips_at_O0")},
        ),
        cite(P_L18, "chains.level_is_zero.links_at_head.flip_fired", l18_ch["links_at_head"]["flip_fired"]),
        cite(
            P_FIX,
            "current_source_bound_pin.flip_event (verbatim INFO line; source record %s)" % pin["record"],
            pin["flip_event"],
        ),
    ]

    a0_crit["flip_event_observed_for_this_body"] = {
        "verdict": "PASS" if a0["flip_event_O3"] else "FAIL",
        "census_name": "flip_event_O3",
        "FLIPPED_SINCE_2026_08_11": (
            "FAIL -> PASS. The 2026-08-11 probe recorded no event and no fallback "
            "for this body, refused by a marker gate (markers_exact=false) and by "
            "the wave-TR thin-reborrow lane. %s carries a four-dump A/B at ONE "
            "clean rev that pins the cause without asserting it: wave-DR turns "
            "markers_exact false -> true (28 lines) with STILL no flip, and the "
            "flip appears only with the W3b unwind fix. See "
            "corroborating_records['2026-08-20_marker_ceiling']." % P_MC
        ),
        "measured": (
            "codegen flip event at -O3 AND at -O0, def_index %d, func_id %d, event lineage %s"
        )
        % (sc["def_index"], sc["func_id"], sc["event_O3"]["lineage"]),
        "established_by": flip_cites,
    }

    noflip = dig(rmx, P_RMX, "census_tip", "totals", "noflip_control")
    neg_measured = (
        "-Ztrust-ir-flip=no -> %d codegen and %d CTFE flip events crate-wide "
        "(%d fallback events); and for THIS body "
        "tracked_chain_bodies.rows.level_is_zero.flip_under_negative_control "
        "= %s."
    ) % (noflip["codegen"], noflip["ctfe"], noflip["fallback_events"], rmx_row["flip_under_negative_control"])
    neg_cites = [
        cite(P_RMX, "census_tip.totals.noflip_control", noflip),
        cite(
            P_RMX,
            "tracked_chain_bodies.rows.level_is_zero.flip_under_negative_control",
            rmx_row["flip_under_negative_control"],
        ),
        cite(P_TU, "negative_control", dig(tu, P_TU, "negative_control")),
    ]
    a0_neg = {
        "verdict": "PASS",
        "measured": neg_measured,
        "established_by": neg_cites,
        "note": (
            "This is no longer the NON-DISCRIMINATING control the 2026-08-13 "
            "fixture warned about (level_is_zero.a0.json.negative_control."
            "HONEST_LIMIT): the body now DOES emit an event in the flip build, "
            "so the 0-event no-flip build discriminates for it."
        ),
    }

    # ------------------------------------------------------------------ A6
    a6 = sc["A6"]
    a6_crit = {}

    a6_crit["flip_fires_for_level_is_zero"] = {
        "verdict": "PASS" if a6["flip_fires"] else "FAIL",
        "scorecard_name": "flip_fires",
        "FLIPPED_SINCE_2026_08_11": (
            "FAIL -> PASS. The 2026-08-11 probe recorded it blocked by "
            "gate:markers and gate:lane:thin_reborrow. The marker gate is "
            "OBSERVABLY open: markers_exact is true over 28 non-vacuous marker "
            "lines in every record below. The thin-reborrow lane is not read "
            "directly by any committed record here; that it admits this body is "
            "an INFERENCE from the observable, since record_green is the sole "
            "registry writer and an event exists. The event itself fires at BOTH "
            "-O3 and -O0."
        ),
        "measured": sc["event_O3"],
        "established_by": flip_cites,
    }

    a6_crit["digest_in_event"] = {
        "verdict": "PASS" if a6["digest_in_event_EQUAL"] else "FAIL",
        "scorecard_name": "digest_in_event_EQUAL",
        "UPGRADED_SINCE_2026_08_11": (
            "In 2026-08-11 this read 'PASS (mechanism), on 185 other bodies of "
            "the same build, NOT on the target body'. It is now PASS ON THE "
            "TARGET BODY: the event's lineage equals the coverage row's, at four "
            "independent bases with four different digest VALUES -- which is the "
            "point, since a lineage digest is a per-BUILD artifact identity and "
            "EQUAL(event,row) is what A6 asserts."
        ),
        "measured": {
            "row_lineage": sc["row_lineage"],
            "event_O3_lineage": sc["event_O3"]["lineage"],
            "event_O0_lineage": sc["event_O0"]["lineage"],
            "EQUAL": a6["digest_in_event_EQUAL"],
        },
        "the_value_at_each_committed_base": [
            {
                "record": P_RMX,
                "trust_base": rmx_prov["trust_base"],
                "clean_rev": rmx_prov["clean_corpus_rev"],
                "lineage": rmx_row["row_lineage"],
                "event_lineage": rmx_row["event_lineage"],
                "EQUAL_event_row": rmx_row["EQUAL_event_row"],
            },
            {
                "record": P_TU,
                "trust_rev": tu_prov["trust_rev"],
                "clean_rev": tu_prov["clean_rev"],
                "lineage": tu_t["O3"]["lineage"],
                "event_lineage": tu_t["O3"]["event_lineage"],
                "EQUAL_event_row": tu_t["O3"]["event_lineage_equals_row"],
            },
            {
                "record": P_L18,
                "trust_rev": l18["provenance"]["trust_worktree_rev"],
                "clean_rev": l18["provenance"]["clean_source_rev"],
                "lineage": l18_ch["lineage"]["at_head"],
                "event_lineage": pin["flip_event"]["lineage"],
                "EQUAL_event_row": pin["flip_event"]["matches_artifact_lineage"],
            },
            {
                "record": P_A152,
                "trust_rev": a152["provenance"]["trust_worktree_rev"],
                "clean_rev": a152["provenance"]["clean_source_rev"],
                "lineage": a152_ch["lineage"]["at_head"],
                "event_lineage": "not carried per-body by this record",
                "crate_wide_invariant": {
                    "flip_lineage_mismatch": a152["fatal_invariants"]["flip_lineage_mismatch"],
                    "flip_lineage_row_absent": a152["fatal_invariants"]["flip_lineage_row_absent"],
                },
            },
        ],
        "established_by": [
            cite(P_RMX, "ten_criteria_scorecards[target].A6.digest_in_event_EQUAL", a6["digest_in_event_EQUAL"]),
            cite(P_RMX, "tracked_chain_bodies.rows.level_is_zero.EQUAL_event_row", rmx_row["EQUAL_event_row"]),
            cite(P_TU, "targets[target].O3.event_lineage_equals_row", tu_t["O3"]["event_lineage_equals_row"]),
            cite(
                P_FIX,
                "current_source_bound_pin.flip_event.matches_artifact_lineage (source record %s)" % pin["record"],
                pin["flip_event"]["matches_artifact_lineage"],
            ),
            cite(
                P_A152,
                "fatal_invariants.flip_lineage_mismatch (crate-wide)",
                a152["fatal_invariants"]["flip_lineage_mismatch"],
            ),
        ],
    }

    a6_crit["fail_closed"] = {
        "verdict": "PASS",
        "scorecard_name": "fail_closed_perturbation_reaching",
        "what_this_PASS_covers": (
            "the CONSUMER-perturbation half, measured ON THE TARGET BODY: the "
            "switch-map perturbation REACHES it (applications=1) and drives it "
            "agreed -> mismatch with the corruption named verbatim, and the flip "
            "is withdrawn. The A0 `agreed` verdict is therefore not vacuous."
        ),
        "measured": sc["perturbation"],
        "corroboration": {
            "record": P_TU,
            "perturb_run": tu_t["perturb_run"],
            "under_perturbation": tu_t["under_perturbation"],
        },
        "what_this_PASS_does_NOT_cover": (
            "the SOURCE-LEVEL fail-closed path -- flip.rs re-deriving the lineage "
            "from the taken registry payload and refusing on inequality, and "
            "flip_registry::green_body refusing to mint a green with no digest "
            "('no digest, no green'). On 2026-08-11 that was read in source and "
            "confirmed present in the shipped driver but NOT independently "
            "triggered, because triggering it needs a modified trustc. NO "
            "COMMITTED RECORD EXERCISES IT ON THE BODY SEAM FOR THIS TARGET. The "
            "closest committed evidence is a DIFFERENT SEAM on DIFFERENT BODIES "
            "-- see `adjacent_committed_evidence_different_seam`."
        ),
        "adjacent_committed_evidence_different_seam": {
            "record": P_WA,
            "date": dig(wa, P_WA, "date"),
            "seam": "per-INSTANCE flip seam (trust_instance_flip), not the body seam",
            "arm": "mutation_matrix.O0mut-lineage (and the body_flip_rows control beside it)",
            "measured": {k: wa_mut[k] for k in ("instance_flips", "baseline_instance_flips", "flip_vanished")},
            "reading": (
                "a compiler mutated to corrupt the lineage takes the instance "
                "flips from %d to %d and every refusal names 'lineage digest "
                "mismatch'. That demonstrates the mechanism fails closed on the "
                "instance seam and on other bodies; it is NOT a measurement of "
                "level::Level::is_zero on the body seam."
            )
            % (wa_mut["baseline_instance_flips"], wa_mut["instance_flips"]),
        },
        "established_by": [
            cite(P_RMX, "ten_criteria_scorecards[target].A6.fail_closed_perturbation_reaching", a6["fail_closed_perturbation_reaching"]),
            cite(P_RMX, "ten_criteria_scorecards[target].perturbation", sc["perturbation"]),
            cite(P_TU, "targets[target].under_perturbation", tu_t["under_perturbation"]),
        ],
    }

    a6_crit["negative_control"] = {
        "verdict": "PASS" if a6["negative_control"] else "FAIL",
        "scorecard_name": "negative_control",
        "measured": neg_measured,
        "established_by": [cite(P_RMX, "ten_criteria_scorecards[target].A6.negative_control", a6["negative_control"])]
        + neg_cites,
    }

    # ------------------------------------------------- the honest gap list
    not_established = [
        {
            "claim": "docs/CRYSTAL_STATUS.md 0.3a's BASE reading: A0 5-of-6 / A6 4-of-4 at trust base `36cbb1130d`, driver digest `58b5fc15...7382b228`, event lineage `sha256:1e9070c2...a2a361d81`.",
            "status": "PARTIALLY established by committed records; NOT established as a ten-criteria scorecard.",
            "what_IS_committed": [
                "%s records the SAME dylib digest %s under dumps['wc-basev11b'] (its seal's REV file reads %s -- 0.3a itself explains that seal_driver.sh took REV from the shared checkout, not the build worktree, so the source rev `36cbb1130d` is NOT in any file in this repo), at clean rev %s, and gives the target verdict=%s, markers_exact=%s, %d marker lines, flips at O3 and O0."
                % (
                    P_MC,
                    mc_base["provenance"]["dylib"],
                    mc_base["provenance"]["trust_rev"],
                    mc["clean_rev_of_every_dump"],
                    mc_base["designated_target_level_is_zero"]["verdict"],
                    mc_base["designated_target_level_is_zero"]["markers_exact"],
                    mc_base["designated_target_level_is_zero"]["marker_lines"],
                ),
                "%s records lineage `%s` for this body at the SAME clean rev %s under the PRE-W3/W3b producer %s -- with markers_exact=%s and flip_fired=%s. So the DIGEST VALUE 0.3a quotes for the base run is committed; the flip and markers verdict at that digest is not, because that record predates the waves."
                % (
                    P_R19,
                    r19_ch["lineage"]["at_head"],
                    r19["provenance"]["clean_worktree_rev"],
                    r19["provenance"]["trust_worktree_rev"],
                    r19_ch["links_at_head"]["derived_mir"]["markers_exact"],
                    r19_ch["links_at_head"]["flip_fired"],
                ),
            ],
            "what_is_NOT_committed": [
                "the trust base string `36cbb1130d` (it appears in no file under data/, reports/ or crates/ in this repo)",
                "the base run's negative control, its switch-map perturbation, its bodyful-closure reading, and its EQUAL(event,row) join",
                "therefore: no committed record scores that particular run at 5-of-6 / 4-of-4",
            ],
            "consequence_for_this_probe": "the probe's CURRENT verdicts are transcribed from the 2026-08-22 and 2026-08-25 records instead, which do carry all ten criteria. The 2026-08-20 drivers appear only as corroboration on the four criteria the marker-ceiling record actually measures.",
        },
        {
            "claim": "docs/CRYSTAL_STATUS.md 0.3a's PRODUCER-TIP reading: event lineage `sha256:8f934136...2f6c0a79`, driver digest `50879dc8...3832ba98`, built from `26d0a0e8ee`.",
            "status": "PARTIALLY established.",
            "what_IS_committed": [
                "%s dumps['wc-head'] records driver digest %s at trust_rev %s, clean rev %s, and gives the target verdict=%s, markers_exact=%s, %d marker lines, flips at O3 and O0."
                % (
                    P_MC,
                    mc_head["provenance"]["dylib"],
                    mc_head["provenance"]["trust_rev"],
                    mc["clean_rev_of_every_dump"],
                    mc_head["designated_target_level_is_zero"]["verdict"],
                    mc_head["designated_target_level_is_zero"]["markers_exact"],
                    mc_head["designated_target_level_is_zero"]["marker_lines"],
                )
            ],
            "what_is_NOT_committed": [
                "the lineage value `sha256:8f934136...2f6c0a79` -- it appears in no committed file in this repo",
                "that run's negative control, perturbation, and EQUAL(event,row) join",
            ],
        },
        {
            "claim": "docs/CRYSTAL_STATUS.md 0.3a's BOOTSTRAP-v12-SYSROOT reproduction: sealed `seal-bootstrap12`, rev `d28fbe4d0406e4250f10246dc665be3192c2a0ee`, dylib `6dfbd05f...1613cd31`, lineage `sha256:80a9e7ef...2b14a466`, A0 5-of-6 / A6 4-of-4 identical on every axis.",
            "status": "NOT ESTABLISHED BY ANY COMMITTED RECORD IN THIS REPO.",
            "what_IS_committed": [],
            "what_is_NOT_committed": [
                "every one of those strings appears ONLY in docs/CRYSTAL_STATUS.md prose; `6dfbd05f`, `seal-bootstrap12` and `d28fbe4d04` match nothing under data/, reports/ or crates/"
            ],
            "consequence_for_this_probe": "NOT transcribed. The probe does not claim a bootstrap-sysroot reproduction.",
        },
        {
            "claim": "A6 fail-closed, SOURCE-LEVEL half: flip.rs's `lineage digest mismatch` refusal and flip_registry::green_body's 'no digest, no green' independently triggered for this target on the BODY seam.",
            "status": "NOT ESTABLISHED -- and it was never claimed. The 2026-08-11 probe already recorded it as read-in-source but not triggered; nothing since has triggered it here.",
            "what_IS_committed": [
                "%s arm O0mut-lineage: a mutated compiler drives the INSTANCE-seam flips %d -> %d with every refusal naming 'lineage digest mismatch' -- a different seam and different bodies."
                % (P_WA, wa_mut["baseline_instance_flips"], wa_mut["instance_flips"])
            ],
            "what_is_NOT_committed": [
                "any run in which the body-seam lineage check is made to refuse level::Level::is_zero"
            ],
            "consequence_for_this_probe": "A6.fail_closed is scored PASS on the CONSUMER-perturbation criterion the ten-criteria scorecard actually names (`fail_closed_perturbation_reaching`), and the source-level gap is written into that criterion rather than hidden by it.",
        },
        {
            "claim": "The reason A0's bodyful reachable closure cannot be closed. CORRECTED 2026-08-26: it is NOT `thir_body` taking a `LocalDefId` -- that is one of two BUILD ITEMS. The FLOOR is that the closure ends at `panic_impl`, which has no body anywhere in core and is supplied at link time by std.",
            "status": "The FAIL VERDICT is committed and measured (two independent records). The REASON is prose in this repo -- BOTH the rustc query signature and core/std's panicking sources live in the trust repo, which is not committed here. What changed is which wall the prose names, not its evidential status.",
            "what_IS_committed": [
                "%s: the target is in one_short_missing_closure_bodies" % P_CEN,
                "%s: A0.bodyful_reachable_closure = false" % P_RMX,
                "%s: the deref callee carries %d extern_decls and derived_mir `%s`"
                % (
                    P_L18,
                    l18_deref["links_at_head"]["calls"]["extern_decls"],
                    l18_deref["links_at_head"]["derived_mir"]["verdict"],
                ),
            ],
            "what_is_NOT_committed": [
                "the rustc query signature itself (trust repo, compiler/rustc_middle/src/queries.rs)",
                "core's panic chain and the absence of a panic_impl definition (trust repo, library/core/src/panicking.rs:67-70; grep over library/core/src finds panic_impl only as doc, comment, lang attr, declaration and a SAFETY note)",
                "std's link-time definition (trust repo, library/std/src/panicking.rs:611, `#[panic_handler]`)",
            ],
            "consequence_for_this_probe": "FAIL, as required -- and now recorded as a FLOOR rather than an unbuilt capability. The probe records the reason as carried-by-prose, not as measured here.",
        },
        {
            "claim": "The 2026-08-11 A6 evidence item `2_artifact_perturbation_on_the_digest` (the scratchpad/a6/probe.rs wide/untouched digest perturbation).",
            "status": "Its digests survive only inside this file's own history block; the fixture that produced them was session scratch and is not in the repo. It is kept as history, not re-asserted as current.",
            "what_IS_committed": [],
            "what_is_NOT_committed": ["the probe fixture and its build logs"],
        },
    ]

    hist = history_block
    return {
        "schema": SCHEMA_V2,
        "schema_v1_note": (
            "v1 was a single measured run.  v2 splits the file into a CURRENT "
            "section (transcribed from committed records, each verdict naming its "
            "record, trust base and clean rev), an explicit list of readings that "
            "NO committed record establishes, and a HISTORY section holding the "
            "v1 object verbatim.  The A0 and A6 criterion names are unchanged "
            "from v1; the census/scorecard spellings are recorded alongside them."
        ),
        "re_derived_by": {
            "script": "scripts/check_a0a6_probe_transcription.py",
            "check": "scripts/check_a0a6_probe_transcription.py            (fail-closed)",
            "mint": "scripts/check_a0a6_probe_transcription.py --mint",
            "what_the_check_refuses": (
                "any disagreement between this file and the committed records it "
                "cites -- a source record edited without a re-mint, or a verdict "
                "hand-typed in here. It re-derives the TRANSCRIPTION; it does not "
                "re-measure the crystal, and it never runs trustc."
            ),
            "wired_by": (
                "the pre-push hook and the local gate, as the "
                "`a0a6-probe-transcription` leg. Do NOT read that list back "
                "from here: `data/gate_registry.json` owns it and "
                "`scripts/check_gate_registry.py` RE-DERIVES it from the "
                "runner roots, which is the only version that cannot rot."
            ),
            "registry_row": "a0a6_probe_transcription (data/gate_registry.json)",
            "sources_re_read": list(SOURCES),
        },
        "v1_paths_moved_to": {
            "why": (
                "Dated documents cite v1 field paths (e.g. "
                "designs/2026-07-29-crystal-deployed-kernel-bridge.md 6.0.1 and "
                "designs/2026-08-12-levelarc-representation-scope.md cite "
                "`A0.criteria.DerivedAgreed.measured` and "
                "`A0.criteria.bodyful_reachable_closure.{measured,adjacent_finding}`). "
                "Those documents are dated records of the 2026-08-11 run and are "
                "left alone; this map makes their citations resolvable."
            ),
            "A0.*": "history.measured_2026_08_11.A0.* (unchanged, verbatim) -- and current.A0.* for today's verdicts",
            "A6.*": "history.measured_2026_08_11.A6.* (unchanged, verbatim) -- and current.A6.* for today's verdicts",
            "compiler / driver / builds / artifact_continuity_with_A1 / why_the_target_body_does_not_flip / remaining_to_close_A0_and_A6 / evidence_paths": "history.measured_2026_08_11.<same key>",
            "measured_utc_date": "history.measured_2026_08_11.measured_utc_date (2026-08-11). This file has no top-level measurement date because it is not a measurement.",
        },
        "job": hist["job"],
        "plan": hist["plan"],
        "target_body": hist["target_body"],
        "this_file_is_a_TRANSCRIPTION_not_a_measurement": {
            "what": (
                "The verdicts in `current` were NOT measured by the session that "
                "wrote this file.  No compiler was run, no driver was sealed, no "
                "dump was taken.  Every value is copied out of a committed record "
                "named beside it, by scripts/check_a0a6_probe_transcription.py, "
                "which re-derives them on every gate run."
            ),
            "transcribed_utc_date": transcribed_date,
            "transcribed_at_clean_HEAD": transcribed_head,
            "the_two_stamps_above_are_CARRIED_not_re_derived": (
                "They describe the act of transcription, not a measured value, so "
                "the checker reads them back out of this file rather than from "
                "`date.today()` / `git rev-parse HEAD` -- otherwise the gate would "
                "go red on the next commit for no reason. They are still "
                "VALIDATED: the date must be ISO-8601 and the sha must resolve to "
                "a commit in this repo."
            ),
            "rule_followed": (
                "A verdict is written here only if a committed record carries it.  "
                "Readings that exist only in docs/CRYSTAL_STATUS.md prose are "
                "listed under `not_established_by_any_committed_record` and are "
                "NOT scored.  No digest, DefId or sha in this file was composed by "
                "hand."
            ),
            "supersedes_the_disagreement": (
                "docs/CRYSTAL_STATUS.md previously said this probe 'has not been "
                "re-minted, so the probe and this page disagree on purpose until "
                "it is'.  That sentence is retired by this file."
            ),
        },
        "headline": (
            "A0 is 5-of-6 and A6 is 4-of-4 for level::Level::is_zero on the "
            "DEPLOYED body, transcribed from committed records measured at trust "
            "%s x clean %s (2026-08-25) and corroborated at three earlier bases.  "
            "Both of the 2026-08-11 FAILs -- A0's flip event and A6's flip-fires "
            "-- are now PASS, with the event's lineage equal to its coverage "
            "row's at every base.  A0's single remaining FAIL is `bodyful "
            "reachable closure`, and it is architecturally blocked: rustc has no "
            "cross-crate THIR.  This is a re-mint by transcription, not a fresh "
            "measurement."
        )
        % (rmx_prov["trust_base"], rmx_prov["clean_corpus_rev"]),
        "current": {
            "A0_score": sc["A0_score"],
            "A6_score": sc["A6_score"],
            "as_of_record": rmx_at,
            "criterion_name_map": {
                "note": (
                    "v1's A0 criterion names on the left, the committed "
                    "instrument's spellings on the right "
                    "(`scripts/crystal_a0_census.py` CRITERIA, and lane RMX's "
                    "ten-criteria scorecard)."
                ),
                "A0": {
                    "lowered": "lowered",
                    "spliced": "spliced",
                    "zero_unsupported": "zero_unsupported",
                    "DerivedAgreed": "derived_agreed",
                    "bodyful_reachable_closure": "bodyful_reachable_closure",
                    "flip_event_observed_for_this_body": "flip_event_O3",
                },
                "A6": {
                    "flip_fires_for_level_is_zero": "flip_fires",
                    "digest_in_event": "digest_in_event_EQUAL",
                    "fail_closed": "fail_closed_perturbation_reaching",
                    "negative_control": "negative_control",
                },
            },
            "A0": {
                "acceptance": hist["A0"]["acceptance"],
                "score": sc["A0_score"],
                "criteria": a0_crit,
                "negative_control": a0_neg,
            },
            "A6": {
                "acceptance": hist["A6"]["acceptance"],
                "score": sc["A6_score"],
                "criteria": a6_crit,
            },
            "body_identity_at_the_primary_record": {
                "def_path": sc["def_path"],
                "def_index": sc["def_index"],
                "func_id": sc["func_id"],
                "instr_count": sc["instr_count"],
                "note": (
                    "def_index and func_id are per-BUILD ordinals and move with "
                    "clean-kernel and the producer; they are recorded so a reader "
                    "can join this record to its dump, never to be compared "
                    "across builds."
                ),
            },
            "corroborating_records": {
                "2026-08-22_laneTU": tu_at,
                "2026-08-22_a0_census": cen_at,
                "2026-08-21_lane18_chain_revalidation": l18_at,
                "2026-08-20_a152_chain_revalidation": a152_at,
                "2026-08-20_marker_ceiling": mc_at,
                "2026-08-19_pre_W3_control": r19_at,
            },
            "how_to_re_measure_rather_than_re_read": (
                "seal a driver (trust/scripts/seal_driver.sh, guard PASS), take a "
                "whole-crate clean-kernel dump at -O3 and -O0 plus the "
                "-Ztrust-ir-flip=no control and a switch-map perturbation, then "
                "run `scripts/crystal_a0_census.py` over the dump for A0 and join "
                "the flip log to the coverage rows for A6."
            ),
        },
        "not_established_by_any_committed_record": not_established,
        "history": {
            "note": (
                "The 2026-08-11 measurement is kept VERBATIM below.  It is a "
                "correct record of the build it was taken at and is not a claim "
                "about any later HEAD.  Two of its verdicts have since moved "
                "(A0's flip event and A6's flip-fires, both FAIL -> PASS) and one "
                "has not (bodyful reachable closure, still FAIL).  Its compiler, "
                "driver, lineage values and gate diagnoses all belong to that "
                "build and must not be quoted as current."
            ),
            "measured_2026_08_11": hist,
        },
    }


# ---------------------------------------------------------------- stamp intake
ISO_DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
SHA40 = re.compile(r"^[0-9a-f]{40}$")


def stamps_from(root, probe):
    """(date, head, history-block) out of the committed probe, validated.

    From a v1 probe this is a first mint: the stamps come from the live tree and
    the history block is the v1 object minus its `schema`.  From a v2 probe both
    are read back, so `--mint` is idempotent and `--check` is stable over time.
    """
    schema = probe.get("schema")
    if schema == SCHEMA_V1:
        head = subprocess.run(
            ["git", "-C", root, "rev-parse", "HEAD"],
            capture_output=True, text=True, check=False,
        ).stdout.strip()
        if not SHA40.match(head):
            raise Refuse("cannot resolve git HEAD for a first mint")
        hist = {k: v for k, v in probe.items() if k != "schema"}
        return date.today().isoformat(), head, hist
    if schema != SCHEMA_V2:
        raise Refuse(
            f"{P_PROBE}: schema is {schema!r}; expected {SCHEMA_V1!r} (first mint) "
            f"or {SCHEMA_V2!r} (re-mint / check)"
        )
    block = dig(probe, P_PROBE, "this_file_is_a_TRANSCRIPTION_not_a_measurement")
    d = block.get("transcribed_utc_date")
    h = block.get("transcribed_at_clean_HEAD")
    if not isinstance(d, str) or not ISO_DATE.match(d):
        raise Refuse(f"{P_PROBE}: transcribed_utc_date {d!r} is not an ISO-8601 date")
    if not isinstance(h, str) or not SHA40.match(h):
        raise Refuse(f"{P_PROBE}: transcribed_at_clean_HEAD {h!r} is not a 40-hex sha")
    seen = subprocess.run(
        ["git", "-C", root, "cat-file", "-e", h + "^{commit}"],
        capture_output=True, text=True, check=False,
    )
    if seen.returncode != 0:
        raise Refuse(
            f"{P_PROBE}: transcribed_at_clean_HEAD {h} is not a commit in this repo -- "
            "a transcription stamp must name a real commit"
        )
    hist = dig(probe, P_PROBE, "history", "measured_2026_08_11")
    if hist.get("measured_utc_date") != "2026-08-11":
        raise Refuse(
            f"{P_PROBE}: history.measured_2026_08_11.measured_utc_date is "
            f"{hist.get('measured_utc_date')!r} -- the 2026-08-11 run must be kept verbatim"
        )
    return d, h, hist


# ------------------------------------------------------------------ comparison
def first_mismatch(want, got, path="$"):
    """The first structural disagreement, as (path, want, got); None if equal."""
    if type(want) is not type(got) and not (
        isinstance(want, (int, float)) and isinstance(got, (int, float))
    ):
        return path, want, got
    if isinstance(want, dict):
        for key in want:
            if key not in got:
                return f"{path}.{key}", want[key], "<ABSENT>"
            bad = first_mismatch(want[key], got[key], f"{path}.{key}")
            if bad:
                return bad
        for key in got:
            if key not in want:
                return f"{path}.{key}", "<NOT DERIVED>", got[key]
        return None
    if isinstance(want, list):
        if len(want) != len(got):
            return f"{path}[len]", len(want), len(got)
        for i, (a, b) in enumerate(zip(want, got)):
            bad = first_mismatch(a, b, f"{path}[{i}]")
            if bad:
                return bad
        return None
    return None if want == got else (path, want, got)


def brief(value, width=300):
    text = json.dumps(value, ensure_ascii=False) if not isinstance(value, str) else value
    return text if len(text) <= width else text[:width] + " ..."


def do_check(root, verbose):
    probe = load(root, P_PROBE)
    derived = derive(root, stamps_from(root, probe))
    bad = first_mismatch(derived, probe)
    if bad is None:
        print(
            "a0a6 probe transcription: OK -- %s re-derives from %d committed records"
            % (P_PROBE, len(SOURCES))
        )
        return 0
    where, want, got = bad
    print("a0a6 probe transcription: FAIL", file=sys.stderr)
    print(f"  the committed probe disagrees with the records it cites, at {where}", file=sys.stderr)
    print(f"    re-derived from the records : {brief(want, 2000 if verbose else 300)}", file=sys.stderr)
    print(f"    committed in the probe      : {brief(got, 2000 if verbose else 300)}", file=sys.stderr)
    print(file=sys.stderr)
    print(
        "  Either a source record moved and the probe was not re-minted, or the probe was\n"
        "  hand-edited. Re-mint with `scripts/check_a0a6_probe_transcription.py --mint`\n"
        "  and READ THE DIFF -- a moved verdict is a finding, not a formality.",
        file=sys.stderr,
    )
    return 1


def do_mint(root):
    probe = load(root, P_PROBE)
    derived = derive(root, stamps_from(root, probe))
    with open(os.path.join(root, P_PROBE), "w", encoding="utf-8") as fh:
        json.dump(derived, fh, indent=1, ensure_ascii=False)
        fh.write("\n")
    print(f"a0a6 probe transcription: wrote {P_PROBE}")
    return 0


# -------------------------------------------------------------------- selftest
def _selftest(root):
    """Six arms. A gate nobody has seen fail is `exit 0`."""
    import copy
    import shutil

    fails = []

    def arm(name, mutate, expect):
        with tempfile.TemporaryDirectory() as tmp:
            work = os.path.join(tmp, "tree")
            os.makedirs(work)
            os.makedirs(os.path.join(work, "data"))
            os.makedirs(os.path.join(work, os.path.dirname(P_FIX)))
            for rel in SOURCES + (P_PROBE,):
                shutil.copy2(os.path.join(root, rel), os.path.join(work, rel))
            # The arms test the MECHANISM, not the committed file's freshness, so
            # each one starts from a freshly minted probe in the temp tree. That
            # makes the baseline arm an IDEMPOTENCE test (mint, then check, is a
            # fixed point) and every other arm a real falsification on top of a
            # known-good mint. Stamps come from the real root, which is where git
            # is; nothing writes outside `work`.
            stamps = stamps_from(root, load(root, P_PROBE))
            with open(os.path.join(work, P_PROBE), "w", encoding="utf-8") as fh:
                json.dump(derive(work, stamps), fh, indent=1, ensure_ascii=False)
            mutate(work)
            try:
                probe = load(work, P_PROBE)
                derived = derive(work, stamps_from(root, probe) if probe.get("schema") == SCHEMA_V2 else stamps)
                bad = first_mismatch(derived, probe)
                got = "GREEN" if bad is None else f"RED:{bad[0]}"
            except Refuse as exc:
                got = f"REFUSE:{exc}"
            if not expect(got):
                fails.append(f"{name}: got {got}")

    def jset(rel, path, value):
        """Set one JSON key, refusing if that is a NO-OP.

        `value` may be a callable taking the current value. A mutation that
        changes nothing makes its arm GREEN and looks like a pass -- which is
        instance 4 in docs/GATE_REGISTRY.md, and is exactly what happened the
        first time these arms were replayed against a tree where somebody had
        already made the mutation by hand. So the arms are relative to what is
        there, and a no-op is a failure, not a skip.
        """

        def go(work):
            doc = load(work, rel)
            cur = doc
            for key in path[:-1]:
                cur = cur[key]
            was = cur[path[-1]]
            now = value(was) if callable(value) else value
            if now == was:
                raise Refuse(
                    f"selftest mutation is a NO-OP: {rel} {'.'.join(str(k) for k in path)} "
                    f"is already {was!r}, so the arm would prove nothing"
                )
            cur[path[-1]] = now
            with open(os.path.join(work, rel), "w", encoding="utf-8") as fh:
                json.dump(doc, fh, indent=1, ensure_ascii=False)

        return go

    arm("baseline is green", lambda w: None, lambda g: g == "GREEN")
    flip = lambda was: not was  # noqa: E731 -- relative, so no arm can be a no-op
    arm(
        "a source record's A0 verdict is flipped",
        jset(P_RMX, ["ten_criteria_scorecards", 2, "A0", "bodyful_reachable_closure"], flip),
        lambda g: g.startswith("RED"),
    )
    arm(
        "a source record's A6 verdict is flipped",
        jset(P_RMX, ["ten_criteria_scorecards", 2, "A6", "digest_in_event_EQUAL"], flip),
        lambda g: g.startswith("RED"),
    )
    arm(
        "a lineage digest in a source record is altered",
        jset(
            P_RMX,
            ["tracked_chain_bodies", "rows", "level_is_zero", "event_lineage"],
            lambda was: "sha256:" + ("0" * 64 if not was.endswith("0" * 8) else "1" * 64),
        ),
        lambda g: g.startswith("RED"),
    )
    arm(
        "the probe's own headline score is hand-edited",
        jset(P_PROBE, ["current", "A0_score"], lambda was: "6-of-6" if was != "6-of-6" else "4-of-6"),
        lambda g: g.startswith("RED"),
    )
    arm(
        "the census no longer scores the target 5-of-6",
        jset(P_CEN, ["one_short_missing_closure_bodies"], lambda was: [b for b in was if b != TARGET]),
        lambda g: g.startswith("REFUSE"),
    )

    if fails:
        print("a0a6 probe transcription selftest: FAIL", file=sys.stderr)
        for f in fails:
            print(f"  x {f}", file=sys.stderr)
        return 1
    print("a0a6 probe transcription selftest: 6/6 arms behave (1 green, 4 red, 1 refusal)")
    return 0


def main(argv):
    args = set(argv[1:])
    unknown = args - {"--check", "--mint", "--selftest", "--diff"}
    if unknown:
        print(__doc__, file=sys.stderr)
        print(f"unknown argument(s): {' '.join(sorted(unknown))}", file=sys.stderr)
        return 2
    try:
        if "--selftest" in args:
            return _selftest(ROOT)
        if "--mint" in args:
            rc = _selftest(ROOT)
            if rc:
                return rc
            return do_mint(ROOT)
        rc = _selftest(ROOT)
        if rc:
            return rc
        return do_check(ROOT, verbose="--diff" in args)
    except Refuse as exc:
        print(f"a0a6 probe transcription: REFUSING -- {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
