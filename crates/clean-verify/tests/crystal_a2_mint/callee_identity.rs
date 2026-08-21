// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **M8 — callee identity: the numeral in `(call N …)` denotes a function, and
//! the gate says WHICH.**
//!
//! ## The defect this lane exists for
//!
//! A core module carries the function's own id in `(func N …)` and a callee id
//! in `(call M …)`. Those are ONE namespace, not two — that is what the
//! specification says, not a convention adopted here: `ir_func_find`
//! (`spec/core_spec/eval_ir_state.rs`) resolves a callee by scanning for a
//! function whose OWN id equals it, and `ir_call_exec` goes through it.
//!
//! Until 2026-08-20 both writers of the core form printed the literal `0` for
//! the function's own id while interning callees from a SEPARATE counter that
//! also started at `0` (`ir_mint/emitted.rs` and `scripts/crystal_a2_project`).
//! In the committed `ir_lz.core.txt` that made the numeral `0` denote two
//! different functions in one module:
//!
//! ```text
//! (func 0 …)                            ← level::Level::is_zero, artifact 4925
//! (node (results 12) (call 0 (args 9)))  ← @func.4914 = LevelArc::deref
//! (node (results 13) (call 1 (args 12))) ← @func.4925 = is_zero ITSELF
//! ```
//!
//! [`the_swap_counterexample_is_closed`] is the constructed witness: swap the
//! two `@func.N` literals in the emitted fixture and first-use interning maps
//! `4925 → 0`, `4914 → 1`, so the two cores come out BYTE-IDENTICAL — while
//! `P` computes `is_zero(deref(p))` and `Q` computes `deref(is_zero(p))`. Two
//! modules the gate accepted as equal that denote different programs. That test
//! stays here permanently; it is the proof the defect cannot come back.
//!
//! ## What closes it, and what stays open
//!
//! The two namespaces are now one, the body's own id interned FIRST — see
//! `ir_mint::SelfFunc` for the mechanism and for the precise strength of an
//! UNPINNED read, which reproduces reader A's numbering on every body that does
//! not call itself and diverges, loudly, on every body that does.
//!
//! Still open and NOT claimed here: this lane pins which crate-level id each
//! canonical index denotes and records the NAME reader A read for it. It does
//! not re-derive that name from the emitted text, because the text does not
//! carry it. See `data/crystal_mint_blind_slots.json`, row `callee-name`.

use std::collections::BTreeMap;

use clean_verify::ir_mint::{self, SelfFunc, SELF_FUNC_INDEX};

use super::{canon, PRODUCER_AB};

/// The designated target's emitted body: ten blocks, six call sites, two
/// distinct callees — one of which is the body itself.
const LZ_FIXTURE: &str = include_str!("../fixtures/level_is_zero.trust-ir.txt");

/// `level::Level::is_zero`'s own crate-level id in the build the fixture was
/// taken from, read from the committed tag table rather than written here.
fn lz_tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_LZ_TAGS).expect("the lz tag table must parse")
}

/// P and Q: the committed body, and the same body with its two callee ids
/// exchanged. Q is a DIFFERENT program — it composes the deref and the
/// recursive call the other way round.
fn swapped(text: &str) -> String {
    let (a, b) = ("@func.4914", "@func.4925");
    assert!(
        text.contains(a) && text.contains(b),
        "the swap anchors are gone, so the counterexample would be vacuous"
    );
    text.replace(a, "@func.__swap__")
        .replace(b, a)
        .replace("@func.__swap__", b)
}

// ────────────────────────────────────────────────────────────────────────────
// The counterexample, and its closure.
// ────────────────────────────────────────────────────────────────────────────

/// **The constructed counterexample, kept as a permanent regression.**
///
/// Under the pin, P and Q must project to DIFFERENT core modules. Before
/// 2026-08-20 they projected to byte-identical ones.
#[test]
fn the_swap_counterexample_is_closed() {
    let pin = lz_tags().self_func();
    assert_eq!(
        pin,
        SelfFunc::Pinned(4925),
        "the counterexample is about the body's OWN id; if the table stopped pinning it this test \
         would silently stop testing anything"
    );

    let q_text = swapped(LZ_FIXTURE);
    assert_ne!(q_text, LZ_FIXTURE, "the swap must actually change the text");

    let (p, _) = ir_mint::read_emitted_with_self(LZ_FIXTURE, pin).expect("P reads");
    let (q, _) = ir_mint::read_emitted_with_self(&q_text, pin).expect("Q reads");

    assert_ne!(
        canon(&p),
        canon(&q),
        "TWO PROGRAMS, ONE CORE MODULE. `is_zero(deref(p))` and `deref(is_zero(p))` projected to \
         the same core module, so every check downstream of the projection — M1 through M7 — \
         passes on either. This is the 2026-08-20 namespace collision; if it is failing here the \
         function's own id and its callee ids have been split back into two counters."
    );

    // …and the difference is exactly where it should be: the SELF index moved
    // between the two call sites, nowhere else.
    let p_calls = call_indices(&canon(&p));
    let q_calls = call_indices(&canon(&q));
    assert_eq!(
        p_calls,
        vec![1, 0, 1, 0, 1, 0],
        "P is deref-then-self at every payload read: the deref is a foreign callee (1) and the \
         recursive call is the body itself ({SELF_FUNC_INDEX})"
    );
    assert_eq!(
        q_calls,
        vec![0, 1, 0, 1, 0, 1],
        "Q is self-then-deref — the program the old core form could not distinguish from P"
    );
}

/// The blindness that remains, stated as a test rather than as prose.
///
/// Without the pin the two programs are still indistinguishable to reader B —
/// they must be, because the emitted text does not say which index is the body.
/// What changed is that this is now a DECLARED state with a name
/// (`SelfFunc::Unpinned`) that no callee can reach index `0` from, instead of
/// the silent default.
#[test]
fn an_unpinned_read_is_blind_to_the_swap_and_reserves_index_zero() {
    let q_text = swapped(LZ_FIXTURE);
    let (p, pt) = ir_mint::read_emitted_with_self(LZ_FIXTURE, SelfFunc::Unpinned).expect("P");
    let (q, qt) = ir_mint::read_emitted_with_self(&q_text, SelfFunc::Unpinned).expect("Q");
    assert_eq!(
        canon(&p),
        canon(&q),
        "an unpinned text read cannot tell these apart — if it suddenly can, reader B has learned \
         something from the text that the text does not carry, and that inference needs auditing"
    );

    for (label, t) in [("P", &pt), ("Q", &qt)] {
        assert!(
            !t.funcs.contains_key(&SELF_FUNC_INDEX),
            "{label}: index {SELF_FUNC_INDEX} is the function's OWN index. Unpinned, it must stay \
             empty — a callee interned there is exactly the collision this lane closed."
        );
        assert_eq!(
            t.funcs.keys().copied().collect::<Vec<u32>>(),
            vec![1, 2],
            "{label}: unpinned callees intern from 1, densely"
        );
    }

    // And the consequence is fail-closed, not lenient: an unpinned read of a
    // self-calling body DISAGREES with reader A rather than matching it.
    let (pinned, _) =
        ir_mint::read_emitted_with_self(LZ_FIXTURE, lz_tags().self_func()).expect("pinned");
    assert_ne!(
        canon(&p),
        canon(&pinned),
        "reader B must not produce the same module with and without the pin for a body that calls \
         itself; if it did, the pin would be decoration"
    );
}

/// The property behind both tests above: nothing but the body itself ever
/// reaches [`SELF_FUNC_INDEX`].
#[test]
fn no_foreign_callee_can_claim_the_functions_own_index() {
    let pin = lz_tags().self_func();
    let (_, observed) = ir_mint::read_emitted_with_self(LZ_FIXTURE, pin).expect("read");
    let SelfFunc::Pinned(self_id) = pin else {
        panic!("the lz table must pin the body's own id");
    };
    assert_eq!(
        observed.funcs.get(&SELF_FUNC_INDEX),
        Some(&self_id),
        "the pinned own id must occupy the reserved index"
    );
    for (canonical, crate_id) in &observed.funcs {
        if *canonical == SELF_FUNC_INDEX {
            continue;
        }
        assert_ne!(
            *crate_id, self_id,
            "the body's own id appears at canonical {canonical} as well as at \
             {SELF_FUNC_INDEX}; the namespace is no longer a function"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the funcs pin still describes the artifact.
//
// `scripts/crystal_fixture_freshness.py` classified `callee-index` as AMBER
// because it was "read by NO gate lane". This is that lane.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_funcs_tag_table_still_describes_the_artifact() {
    let t = lz_tags();
    let (_, observed) =
        ir_mint::read_emitted_with_self(LZ_FIXTURE, t.self_func()).expect("reader B");

    assert_eq!(
        observed.funcs.len(),
        t.funcs.len(),
        "the emitted body names {} function id(s) (its own included); the tag table lists {}",
        observed.funcs.len(),
        t.funcs.len()
    );
    for (canonical, crate_id) in &observed.funcs {
        let (recorded, name) = t.func_pin(*canonical).expect("a listed canonical index");
        assert_eq!(
            recorded, crate_id,
            "CALLEE TAG DRIFT, not a module change: canonical function {canonical} (`{name}`) is \
             recorded as crate id {recorded} and the emitted body names {crate_id}. Re-pin \
             `generated/ir_lz.tags.json` after checking the artifact — and check the NAME, which \
             is the half that does not move."
        );
    }

    // …and reader A's independent record of the same ids. Reader A interns the
    // body's own id FIRST, so `crate_func_ids_seen` is in canonical order and
    // its head is the self entry.
    let rec: serde_json::Value =
        serde_json::from_str(PRODUCER_AB).expect("the producer A/B record must parse");
    let row = rec["rows"]
        .as_array()
        .expect("rows")
        .iter()
        .find(|r| r["chain"] == "level_is_zero")
        .expect("the designated target");

    let by_canonical: Vec<u32> = (0..u32::try_from(t.funcs.len()).expect("small"))
        .map(|c| t.func_pin(c).expect("dense").0)
        .collect();
    let mut any_producer_matched = false;
    for (i, per_producer) in row["crate_func_ids_seen"]
        .as_array()
        .expect("ids")
        .iter()
        .enumerate()
    {
        let ids: Vec<u32> = per_producer
            .as_array()
            .expect("one list per producer")
            .iter()
            .map(|v| u32::try_from(v.as_u64().expect("id")).expect("small"))
            .collect();
        assert_eq!(
            ids.len(),
            t.funcs.len(),
            "producer {i} saw {} function id(s), the table lists {}",
            ids.len(),
            t.funcs.len()
        );
        // The body's own id must be the head of every producer's list, which is
        // what "one namespace, self interned first" MEANS on reader A's side.
        let own = u32::try_from(
            row["artifact_func_id"].as_array().expect("fids")[i]
                .as_u64()
                .expect("fid"),
        )
        .expect("small");
        assert_eq!(
            ids.first(),
            Some(&own),
            "producer {i}: the body's own id {own} is not the head of crate_func_ids_seen {ids:?}. \
             Reader A is interning callees before itself again, which is the collision."
        );
        if ids == by_canonical {
            any_producer_matched = true;
        }
    }
    assert!(
        any_producer_matched,
        "no producer in the A/B record saw the ids the tag table pins ({by_canonical:?}). The \
         fixture and the table must come from the same build; the pin names which one."
    );
}

/// **The `LevelArc::deref` wall, made real.**
///
/// `crystal_a1_lineage/level_is_zero.rs` justifies leaving link 2a open partly
/// on this claim: *"a minted `ir_lz_module` contains `call` to a callee that is
/// not in the module, `ir_call_exec` is fail-closed on that."* Under the old
/// core form that was FALSE for the deref: it was interned at `0`, `ir_func_find`
/// matches on a function's OWN id, the only function in the module has id `0`,
/// and so the deref call would have resolved — silently — to a recursive call
/// to `is_zero`. Half a wall.
///
/// With one namespace the claim holds as written, and this pins it: every
/// foreign callee sits at a non-zero index, and the module declares exactly one
/// function, at index `0`.
#[test]
fn every_foreign_callee_is_unresolvable_in_a_one_function_module() {
    let core = ir_mint::parse(ir_mint::IR_LZ_CORE).expect("reader A's committed core parses");
    let funcs = core.tagged("module").expect("module")[0]
        .tagged("funcs")
        .expect("funcs");
    assert_eq!(
        funcs.len(),
        1,
        "a chain module declares exactly one function"
    );
    let declared = funcs[0].tagged("func").expect("func")[0]
        .num()
        .expect("the function's own id");
    assert_eq!(
        declared,
        u128::from(SELF_FUNC_INDEX),
        "the only function in the module is the body itself"
    );

    let t = lz_tags();
    let calls = call_indices(ir_mint::IR_LZ_CORE);
    assert_eq!(calls.len(), 6, "six call sites");
    let mut foreign = 0usize;
    for c in &calls {
        let (_, name) = t.func_pin(*c).expect("every callee index is pinned");
        if u128::from(*c) == declared {
            assert_eq!(name, "level::Level::is_zero", "index 0 must be the body");
        } else {
            foreign += 1;
            assert_eq!(
                name, "<level::LevelArc as std::ops::Deref>::deref",
                "the one foreign callee"
            );
        }
    }
    assert_eq!(
        foreign, 3,
        "three of the six sites call OUT of the module — `ir_func_find` cannot resolve any of \
         them, which is the fail-closed wall `crystal_a1_lineage` relies on. Under the old \
         namespace this count was 0 and the wall was not there."
    );
}

/// Readers A and B agree on the DESIGNATED TARGET, not just on the width-one
/// chain — which is what makes the regenerated `ir_lz.core.txt` a checked
/// artifact rather than a hand edit.
#[test]
fn reader_a_and_reader_b_agree_on_the_designated_target() {
    let a = ir_mint::parse(ir_mint::IR_LZ_CORE).expect("reader A's core parses");
    assert_eq!(
        canon(&a),
        ir_mint::IR_LZ_CORE,
        "reader A's committed core module is not in canonical form"
    );
    let (masked, ledger) = ir_mint::mask_text_unwitnessed(&a).expect("mask");
    let names: Vec<String> = ledger.iter().map(ToString::to_string).collect();
    assert_eq!(
        names,
        vec!["bb0#2 switch arg4".to_string()],
        "the set of fields the emitted TEXT cannot witness must be exactly the declared one"
    );
    let (b, _) = ir_mint::read_emitted_with_self(LZ_FIXTURE, lz_tags().self_func()).expect("B");
    assert_eq!(
        canon(&masked),
        canon(&b),
        "reader A (the artifact BINARY) and reader B (the emitted TEXT) disagree about \
         `level::Level::is_zero`. Masked slots: {names:?}"
    );
}

/// **The one-namespace invariant across reader A's WHOLE record, not just this
/// chain.**
///
/// `crate_func_ids_seen` is the same namespace `(func N …)` and `(call M …)`
/// share, so its head is the body's own id for every body — including the ten
/// that call nothing, whose list is exactly that one entry. Before 2026-08-20
/// those ten recorded `[]` and `level_is_zero` recorded its callees with its
/// own id buried among them, which is the record's view of the collision.
#[test]
fn m8_every_row_of_reader_as_record_leads_with_the_bodys_own_id() {
    let rec: serde_json::Value =
        serde_json::from_str(PRODUCER_AB).expect("the producer A/B record must parse");
    let rows = rec["rows"].as_array().expect("rows");
    assert!(rows.len() >= 11, "the record must cover every chained body");
    let mut calling = 0usize;
    for row in rows {
        let chain = row["chain"].as_str().unwrap_or("?");
        let fids = row["artifact_func_id"].as_array().expect("func ids");
        let seen = row["crate_func_ids_seen"].as_array().expect("namespace");
        let names = row["crate_func_names_seen"]
            .as_array()
            .unwrap_or_else(|| panic!("{chain}: reader A must record the NAMES it resolved"));
        assert_eq!(seen.len(), 3, "{chain}: one namespace per producer");
        assert_eq!(names.len(), 3, "{chain}: one name list per producer");
        for i in 0..3 {
            let ids = seen[i].as_array().expect("ids");
            assert!(
                !ids.is_empty(),
                "{chain}, producer {i}: an EMPTY function namespace. Every body is in its \
                 own namespace, so the list can never be empty — an empty one means the own id \
                 was written somewhere else, which is the collision."
            );
            assert_eq!(
                ids[0], fids[i],
                "{chain}, producer {i}: the namespace does not lead with the body's own id"
            );
            assert_eq!(
                names[i].as_array().expect("names").len(),
                ids.len(),
                "{chain}, producer {i}: one name per id"
            );
            if ids.len() > 1 {
                calling += 1;
            }
        }
    }
    assert_eq!(
        calling, 3,
        "exactly one of the eleven bodies calls anything, on all three producers — and it is \
         the one this lane's counterexample is built on. If this changed, another chain acquired \
         a callee namespace and needs a `funcs` lane of its own."
    );
}

/// The precise strength of [`SelfFunc::Unpinned`], which is neither "safe" nor
/// "broken": it reproduces reader A's numbering exactly when the body does not
/// call ITSELF, and diverges when it does.
#[test]
fn unpinned_matches_reader_a_on_every_body_that_does_not_self_call() {
    let two_foreign = "rustcc fn @m::f(functy.0) {
bb0(%0: ptr):
    %1 = call @func.100(%0)
    %2 = call @func.200(%1)
    ret %2
}
";
    // Reader A's numbering for this body: own id 999 -> 0, then 100 -> 1,
    // 200 -> 2. Reader B unpinned reserves 0 and interns from 1: the same.
    let (pinned, _) =
        ir_mint::read_emitted_with_self(two_foreign, SelfFunc::Pinned(999)).expect("pinned");
    let (unpinned, _) =
        ir_mint::read_emitted_with_self(two_foreign, SelfFunc::Unpinned).expect("unpinned");
    assert_eq!(
        canon(&pinned),
        canon(&unpinned),
        "with no self-call, the pin changes nothing — that is why ten of the eleven chains \
         need no `funcs` lane"
    );
    assert_eq!(call_indices(&canon(&pinned)), vec![1, 2]);

    // And the one case where it does change something.
    let self_calling = two_foreign.replace("@func.200", "@func.999");
    let (p2, _) =
        ir_mint::read_emitted_with_self(&self_calling, SelfFunc::Pinned(999)).expect("pinned");
    let (u2, _) =
        ir_mint::read_emitted_with_self(&self_calling, SelfFunc::Unpinned).expect("unpinned");
    assert_eq!(call_indices(&canon(&p2)), vec![1, 0], "the self-call is 0");
    assert_eq!(
        call_indices(&canon(&u2)),
        vec![1, 2],
        "unpinned, the self-call is just another stranger"
    );
    assert_ne!(canon(&p2), canon(&u2));
}

/// Coverage denominator for this lane: the ids it pins are actually used.
#[test]
fn the_designated_target_really_calls_two_distinct_functions() {
    let calls = call_indices(ir_mint::IR_LZ_CORE);
    let distinct: BTreeMap<u32, usize> = calls.iter().fold(BTreeMap::new(), |mut m, c| {
        *m.entry(*c).or_default() += 1;
        m
    });
    assert_eq!(
        distinct.len(),
        2,
        "two distinct callees, or this lane is comparing a namespace with one inhabitant"
    );
    assert!(
        distinct.values().all(|n| *n == 3),
        "three sites each: {distinct:?}"
    );
}

/// Every `(call N …)` index in a printed core module, in program order.
fn call_indices(core: &str) -> Vec<u32> {
    core.match_indices("(call ")
        .filter_map(|(i, _)| {
            core[i + "(call ".len()..]
                .split(|c: char| !c.is_ascii_digit())
                .next()
                .and_then(|d| d.parse::<u32>().ok())
        })
        .collect()
}
