// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Link 2a for the strict_monads chain — the first MUTATING body:
//! `env::Environment::set_lean4_core_strict_monads`.**
//!
//! ```text
//! bb0(%0: ptr, %1: bool):
//!     %2 = load struct.441, ptr %0
//!     %3 = insertfield struct.441 %2, 81, %1
//!     store struct.441 %3, ptr %0
//!     ret
//! ```
//!
//! This body is why the `insertfields` and `stores` lanes exist (added
//! 2026-08-20, AHEAD of the chain): before them, `insertfield … 80` wrote a
//! DIFFERENT field and differed in no compared lane, and a `store` of %2
//! instead of %3 — writing back the UNMODIFIED aggregate, deleting the whole
//! mutation — was visible only to `order` as a class token whose operands
//! nothing read. Both directions of both lanes are perturbed below. The `ret`
//! is VOID: `rets` pins the EMPTY list, and `ret %3` is a different function.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. `ir_sm_module` is hand-transcribed:
//! this makes an incorrect transcription FAIL, not a correct one automatic.
//! And the A0 evidence is pinned AT THE STRENGTH IT WAS MEASURED: the
//! producer's interpreter differential is **NOT-RUN on this body (0
//! samples)** — unlike the float closures' agreed/64 — and the last test
//! asserts that refusal as recorded, so nothing downstream can quietly claim
//! interpreter agreement for this chain.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn strict_monads_proved_module_matches_the_emitted_artifact() {
    let text = fixture("strict_monads.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @env::Environment::set_lean4_core_strict_monads("),
        "the fixture must be the setter body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_strict_monads.rs", "const SRC_IR_SM_B0"),
        "def ir_sm_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so pin what the
    // emitted body actually contains before comparing anything.
    assert_eq!(
        emitted.blocks,
        vec![0u32],
        "ONE block; parser found {:?}",
        emitted.blocks
    );
    assert_eq!(
        emitted.loads,
        BTreeMap::from([(0, vec![(2, 0)])]),
        "one load, through the RECEIVER %0, binding %2: {:?}",
        emitted.loads
    );
    assert_eq!(
        emitted.load_tys,
        BTreeMap::from([(0, vec![(2, "struct441".to_string(), false)])]),
        "…at struct.441, non-volatile: {:?}",
        emitted.load_tys
    );
    // *** THE FIRST OF THE TWO LANES THIS CHAIN EXISTS FOR. ***
    assert_eq!(
        emitted.insertfields,
        BTreeMap::from([(0, vec![(3, "struct441".to_string(), 2, 81, 1)])]),
        "one insertfield: (result %3, struct.441, source %2, FIELD 81, value %1). The field \
         index is the semantic payload — `ir_if_at` bounds-checks it and `ir_vals_set` rewrites \
         exactly that slot — and 81 is where this artifact lays out \
         lean4_core_strict_monads. Found {:?}",
        emitted.insertfields
    );
    // *** AND THE SECOND: the first `store` in any chained body. ***
    assert_eq!(
        emitted.stores,
        BTreeMap::from([(0, vec![(0, "struct441".to_string(), 3)])]),
        "one store: (POINTER %0, struct.441, value %3) — pointer FIRST on both sides although \
         the artifact prints `store struct.441 %3, ptr %0`. It stores the REWRITTEN aggregate \
         %3 back through the SAME pointer the load read. Found {:?}",
        emitted.stores
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![])]),
        "the ret is VOID — the empty id list, not a missing entry. A body that returned %3 \
         would hand the new Environment back by value: {:?}",
        emitted.rets
    );
    assert_eq!(
        emitted.order,
        BTreeMap::from([(
            0,
            vec![
                ("load".to_string(), vec![2]),
                ("insertfield".to_string(), vec![3]),
                ("store".to_string(), vec![]),
                ("ret".to_string(), vec![]),
            ]
        )]),
        "load, insertfield, store, ret — in that order, with the store and the ret binding \
         nothing: {:?}",
        emitted.order
    );
    assert!(
        emitted.extracts.is_empty()
            && emitted.icmps.is_empty()
            && emitted.binops.is_empty()
            && emitted.condbrs.is_empty()
            && emitted.casts.is_empty()
            && emitted.geps.is_empty()
            && emitted.asserts.is_empty()
            && emitted.consts.is_empty()
            && emitted.int_consts.is_empty()
            && emitted.agg_consts.is_empty()
            && emitted.branches.is_empty()
            && emitted.cases.is_empty()
            && emitted.param_blocks.is_empty(),
        "this body reads no field, compares nothing, branches nowhere and materializes no \
         constant: it loads, rewrites ONE field, stores, and returns nothing"
    );
    assert_eq!(emitted.default, u32::MAX, "no switch");

    // The two parameters, and the ALIASING pin: %0 is read by the load AND by
    // the store — the body writes through the pointer it loaded from.
    assert!(
        text.contains("bb0(%0: ptr, %1: bool):"),
        "TWO parameters: the &mut Environment receiver and the bool"
    );
    assert_eq!(
        text.matches("ptr %0").count(),
        2,
        "the receiver is dereferenced TWICE — once to load, once to store back: {text}"
    );
    let func = clean_block_sources("eval_ir_strict_monads.rs", "const SRC_IR_SM_FUNC");
    assert!(
        func.contains("IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0"),
        "the registered IRFunc must bind the same two parameter ids in the same order: {func}"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    // cases/default/branches/param_blocks and the three constant lanes are
    // empty on both sides (pinned above) and re-compared by assert_lanes'
    // final whole-Cfg equality.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_strict_monads.rs", "const SRC_IR_SM_FUNC"),
        "strict_monads",
    );
    assert_lanes(&emitted, &clean, "strict_monads");
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
    assert!(
        !text.contains("call "),
        "the body must make no calls — that is what makes its reachable closure bodyful, and \
         it is the A0 criterion Level::is_zero fails"
    );
}

/// **The two write lanes are load-bearing — artifact side.** Each drifted
/// emission is caught by exactly the lane that owns it, while every other lane
/// stays bit-identical — which is the measurement that the lane was needed.
#[test]
fn strict_monads_the_write_lanes_catch_what_every_old_lane_misses() {
    let text = fixture("strict_monads.trust-ir.txt");
    let real = parse_emitted(&text);
    for (what, from, to) in [
        (
            "a different FIELD INDEX — writes a different field of the same Environment",
            "insertfield struct.441 %2, 81, %1",
            "insertfield struct.441 %2, 80, %1",
        ),
        (
            "a different INSERTED VALUE — writes the receiver pointer into the flag slot",
            "insertfield struct.441 %2, 81, %1",
            "insertfield struct.441 %2, 81, %0",
        ),
        (
            "a different SOURCE aggregate for the rewrite",
            "insertfield struct.441 %2, 81, %1",
            "insertfield struct.441 %0, 81, %1",
        ),
        (
            "a different insertfield TYPE — a module the compiler did not emit",
            "insertfield struct.441 %2, 81, %1",
            "insertfield struct.5 %2, 81, %1",
        ),
    ] {
        let mutated = text.replace(from, to);
        assert_ne!(mutated, text, "must actually apply: {what}");
        let got = parse_emitted(&mutated);
        assert_ne!(got.insertfields, real.insertfields, "NOT CAUGHT ({what})");
        assert_eq!(got.stores, real.stores, "({what}) the store lane moved too");
        assert_eq!(got.loads, real.loads, "({what}) the load lane moved");
        assert_eq!(got.order, real.order, "({what}) program order moved");
        assert_eq!(got.rets, real.rets, "({what}) the ret lane moved");
    }
    for (what, from, to) in [
        (
            "storing %2 — the UNMODIFIED aggregate. This deletes the whole mutation and \
             differed in NO lane before `stores` existed",
            "store struct.441 %3, ptr %0",
            "store struct.441 %2, ptr %0",
        ),
        (
            "storing through a DIFFERENT pointer — the mutation lands on another object",
            "store struct.441 %3, ptr %0",
            "store struct.441 %3, ptr %2",
        ),
        (
            "a different store TYPE",
            "store struct.441 %3, ptr %0",
            "store struct.5 %3, ptr %0",
        ),
    ] {
        let mutated = text.replace(from, to);
        assert_ne!(mutated, text, "must actually apply: {what}");
        let got = parse_emitted(&mutated);
        assert_ne!(got.stores, real.stores, "NOT CAUGHT ({what})");
        assert_eq!(
            got.insertfields, real.insertfields,
            "({what}) the insertfield lane moved too"
        );
        assert_eq!(got.loads, real.loads, "({what}) the load lane moved");
        assert_eq!(got.order, real.order, "({what}) program order moved");
    }
    // The void ret: `ret %3` returns the new Environment BY VALUE. Only the
    // rets lane sees it (the order class list records ("ret", []) either way,
    // because a terminator binds nothing).
    let by_value = parse_emitted(&text.replace("\n    ret  ;", "\n    ret %3  ;"));
    assert_ne!(
        by_value.rets, real.rets,
        "rets must see [3] where [] is pinned"
    );
    assert_eq!(by_value.stores, real.stores);
    assert_eq!(by_value.order, real.order, "order cannot see a ret operand");
    // Deleting the store outright IS visible to `order` (the class vanishes) —
    // that was exactly the pre-lane blindness boundary: presence yes, operands no.
    let deleted =
        parse_emitted(&text.replace("    store struct.441 %3, ptr %0  ; #loc: 368 3479 8\n", ""));
    assert_ne!(
        deleted.stores, real.stores,
        "the store lane loses its entry"
    );
    assert_ne!(
        deleted.order, real.order,
        "…and order loses the class token"
    );
}

/// **The other direction: perturb the CLEAN side**, parsed with the same
/// reader the gate uses.
#[test]
fn strict_monads_the_lanes_catch_a_drifted_spec_module_too() {
    let emitted = parse_emitted(&fixture("strict_monads.trust-ir.txt"));
    let src = clean_block_sources("eval_ir_strict_monads.rs", "const SRC_IR_SM_B0");
    let good = parse_clean(&src, "def ir_sm_b");
    assert_eq!(
        emitted.insertfields, good.insertfields,
        "the unmutated registered module must agree, or the mutations below prove nothing"
    );
    assert_eq!(emitted.stores, good.stores);
    assert_eq!(emitted.rets, good.rets);

    // Field index 80: the registered module proves a theorem about the wrong field.
    let wrong_field = parse_clean(
        &src.replace("ir_d2 81 ir_d1", "ir_d2 80 ir_d1"),
        "def ir_sm_b",
    );
    assert_ne!(emitted.insertfields, wrong_field.insertfields);
    assert_eq!(
        emitted.stores, wrong_field.stores,
        "only insertfields may move"
    );

    // The store's constructor operands EXCHANGED — `IRInst.store` is
    // pointer-then-value, the REVERSE of the printed order, so a single-side
    // swap must fail here by construction rather than compare a value to a
    // pointer.
    let swapped = parse_clean(
        &src.replace(
            "IRInst.store ir_sm_tenv ir_d0 ir_d3 Bool.false",
            "IRInst.store ir_sm_tenv ir_d3 ir_d0 Bool.false",
        ),
        "def ir_sm_b",
    );
    assert_ne!(
        emitted.stores, swapped.stores,
        "(ptr, ty, val) = (0, struct441, 3) must not equal (3, struct441, 0)"
    );
    assert_eq!(emitted.insertfields, swapped.insertfields);

    // Storing the loaded value %2 instead of the rewritten %3 — the Clean-side
    // form of the write-elision drift.
    let elided = parse_clean(
        &src.replace(
            "IRInst.store ir_sm_tenv ir_d0 ir_d3 Bool.false",
            "IRInst.store ir_sm_tenv ir_d0 ir_d2 Bool.false",
        ),
        "def ir_sm_b",
    );
    assert_ne!(emitted.stores, elided.stores);
    assert_eq!(
        emitted.order, elided.order,
        "order cannot see a store operand"
    );

    // The insertfield at a type the artifact does not name.
    let wrong_ty = parse_clean(
        &src.replace(
            "IRInst.insertfield ir_sm_tenv",
            "IRInst.insertfield (IRTy.struct_ 5)",
        ),
        "def ir_sm_b",
    );
    assert_ne!(emitted.insertfields, wrong_ty.insertfields);

    // A volatile LOAD is carried (load_tys has the slot) — not refused.
    let vol_load = parse_clean(
        &src.replace(
            "IRInst.load ir_sm_tenv ir_d0 Bool.false",
            "IRInst.load ir_sm_tenv ir_d0 Bool.true",
        ),
        "def ir_sm_b",
    );
    assert_ne!(
        emitted.load_tys, vol_load.load_tys,
        "the volatile flag travels in load_tys"
    );
}

/// **The volatile-store refusal fires on BOTH sides.** The store lane carries
/// no volatile slot; a flag that parsed to nothing on both sides could agree
/// by omission, so each parser must PANIC on it — the `?usize` rule.
#[test]
fn strict_monads_a_volatile_store_is_refused_not_dropped() {
    let text = fixture("strict_monads.trust-ir.txt");
    let mutated = text.replace(
        "store struct.441 %3, ptr %0",
        "volatile store struct.441 %3, ptr %0",
    );
    assert_ne!(mutated, text);
    let err = std::panic::catch_unwind(|| parse_emitted(&mutated))
        .expect_err("the emitted parser must refuse a volatile store");
    assert!(
        panic_msg(&*err).contains("VOLATILE"),
        "the refusal must name the flag and the repair"
    );

    let src = clean_block_sources("eval_ir_strict_monads.rs", "const SRC_IR_SM_B0");
    let vol = src.replace(
        "IRInst.store ir_sm_tenv ir_d0 ir_d3 Bool.false",
        "IRInst.store ir_sm_tenv ir_d0 ir_d3 Bool.true",
    );
    assert_ne!(vol, src);
    let err = std::panic::catch_unwind(|| parse_clean(&vol, "def ir_sm_b"))
        .expect_err("the Clean parser must refuse a volatile store term");
    assert!(
        panic_msg(&*err).contains("VOLATILE"),
        "the refusal must name the flag and the repair"
    );
}

/// The payload of a caught parser refusal, whichever string type it carries.
fn panic_msg(err: &(dyn std::any::Any + Send)) -> &str {
    err.downcast_ref::<String>().map_or_else(
        || err.downcast_ref::<&str>().copied().unwrap_or_default(),
        String::as_str,
    )
}

/// **The A0 evidence, pinned at the strength it was actually measured — and
/// no higher.** In particular: the producer's interpreter differential is
/// NOT-RUN on this body, and that refusal is asserted as recorded so nothing
/// can later quote interpreter agreement for this chain.
#[test]
fn strict_monads_a0_evidence_is_recorded_at_the_strength_it_was_measured() {
    let j = fixture("strict_monads.lineage.json");
    let ev: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0 evidence must be valid JSON");
    assert_eq!(
        ev["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert!(
        !j.contains("envprobe") && !j.contains("monadsprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );

    let body = &ev["body"];
    assert_eq!(
        body["def_path"].as_str(),
        Some("env::Environment::set_lean4_core_strict_monads")
    );
    assert_eq!(body["instr_count"].as_u64(), Some(4));

    // A0, criterion by criterion.
    assert_eq!(body["lowered"].as_bool(), Some(true));
    assert_eq!(body["spliced"].as_bool(), Some(true));
    assert_eq!(
        body["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(body["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(body["derived_mir"]["markers_exact"].as_bool(), Some(true));
    assert_eq!(
        body["derived_mir"]["markers_detail"].as_str(),
        Some("2 marker line(s) identical"),
        "markers_exact must be NON-VACUOUS here; `0 marker line(s) identical` is a true \
         statement about two empty sequences"
    );
    // *** THE HONESTY PIN. *** Unlike the float closures (agreed/64), the
    // interpreter differential sampled this body ZERO times. The evidence for
    // this chain is agreed + markers_exact + flip-lineage equality + the
    // kernel-executed witnesses in eval_ir_strict_monads.rs — NOT an
    // interpreter differential.
    assert_eq!(body["interpreter"]["verdict"].as_str(), Some("not-run"));
    assert_eq!(body["interpreter"]["samples"].as_u64(), Some(0));
    assert!(
        body["interpreter"]["note"]
            .as_str()
            .is_some_and(|n| n.contains("nothing may claim one")),
        "the refusal must stay spelled out in the fixture, not summarized away"
    );
    for k in ["resolved", "extern_decls", "unresolved"] {
        assert_eq!(
            body["calls"][k].as_u64(),
            Some(0),
            "a non-zero {k} call count would reopen the closure question"
        );
    }
    assert_eq!(body["flip_kind"].as_str(), Some("codegen"));

    // A6's join, as recorded: flag AND digests.
    assert_eq!(
        ev["lineage_domain"].as_str(),
        Some("trust_thir_lower.body_lineage.v2"),
        "a digest and its domain travel together or neither means anything"
    );
    assert_eq!(body["flip_lineage_equals_coverage"].as_bool(), Some(true));
    let coverage = body["coverage_row_lineage"]
        .as_str()
        .expect("the coverage-row lineage must be recorded");
    let flip = body["flip_event_lineage"]
        .as_str()
        .expect("the flip-event lineage must be recorded");
    assert!(coverage.starts_with("sha256:") && coverage.len() > "sha256:".len());
    assert_eq!(
        flip.trim_end_matches(','),
        coverage,
        "the flip-event and coverage-row digests must be the same characters"
    );
    assert_eq!(Some(coverage), ev["lineage"].as_str());
    assert_eq!(body["def_index"].as_u64(), ev["def_index"].as_u64());

    // Provenance at its measured strength: THREE byte-identical clean builds
    // of an UNSEALED local stage1 — stronger than one build, weaker than the
    // sealed-driver protocol — plus the float_div byte-for-byte control.
    assert_eq!(
        ev["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true),
        "three clean builds must reproduce the digest, or `lineage` is not a measurement"
    );
    let r1 = ev["reproduction"]["sha256_run1"].as_str().unwrap_or("");
    assert!(!r1.is_empty(), "the reproduction runs must record digests");
    assert_eq!(ev["reproduction"]["sha256_run2"].as_str(), Some(r1));
    assert_eq!(ev["reproduction"]["sha256_run3"].as_str(), Some(r1));
    assert!(
        ev["build"]["provenance_strength"]
            .as_str()
            .is_some_and(|s| s.contains("THREE clean non-incremental builds")
                && s.contains("unsealed local stage1")),
        "the provenance must be carried at the strength it was measured, and say so"
    );
    assert!(
        ev["build"]["control"]
            .as_str()
            .is_some_and(|s| s.contains("float_div.trust-ir.txt")),
        "the control tying this producer to the revalidated series"
    );
    assert_eq!(
        ev["head_measurement"]["at_head_lineage"].as_str(),
        Some(coverage),
        "the freshness record and this fixture must name the same artifact"
    );
}
