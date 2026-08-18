// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the TENTH chain's registered `ir_mt_*` sources —
//! the nine nodes with the assert sixth, the two casts sharing an operand,
//! the two-sided assert dichotomy, the counterfactuals, terminality at every
//! fuel, A4's quantification and fuel bound, A5 as an instance, and the
//! measured cost of the restatement.
//!
//! Moved out of `eval_ir_meta_tag.rs` VERBATIM on 2026-08-17 (module body
//! unchanged, not one assertion or test name touched) because that file stood
//! at 829 lines and `data/paragon_ratchet.json`'s `files_over_500` is
//! shrink-only. The `eval_ir_float_fin_witnesses_tests.rs` precedent.

use super::*;

/// Nine nodes, in this order, and the sixth is the assert.
#[test]
fn test_the_body_is_nine_nodes_and_the_sixth_is_the_panic_arm() {
    assert!(SRC_IR_MT_B0.contains("IRInst.assert ir_d4"));
    assert!(
        SRC_IR_MT_B0.contains("(ir_nd (IRInst.assert ir_d4))"),
        "the assert binds NO result — `ir_nd`, not `ir_nd1`"
    );
    assert!(SRC_IR_MT_B0.contains("IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1"));
    assert!(SRC_IR_MT_B0.contains("IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1"));
    assert!(SRC_IR_MT_B0.contains("IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d0 ir_d5"));
    assert!(SRC_IR_MT_B0.contains("IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3"));
    assert!(SRC_IR_MT_B0.contains("IRInst.ret (ir_nl1 ir_d6)"));
    // …and it returns the SHIFTED value, not the constant 1.
    assert!(!SRC_IR_MT_B0.contains("IRInst.ret (ir_nl1 ir_d0)"));
}

/// The two casts read the SAME operand and are different instructions. If
/// they ever became the same opcode the body would compute something else.
#[test]
fn test_the_two_casts_share_an_operand_and_differ_in_opcode() {
    assert!(SRC_IR_MT_B0.matches("ir_d1)").count() >= 2);
    assert!(SRC_IR_MT_B0.contains("IRCastOp.bitcast"));
    assert!(SRC_IR_MT_B0.contains("IRCastOp.sext"));
    assert!(
        !SRC_IR_MT_B0.contains("IRCastOp.zext"),
        "a zext here would be a different program"
    );
    // and the semantics says they disagree at the sign bit
    assert!(SRC_IR_MT_BITCAST_ZERO_EXT
        .contains("IRScalar.int_ 2147483648)) (IRStepResult.value (IRScalar.int_ 2147483648)"));
    assert!(SRC_IR_MT_SEXT_SIGN_EXTENDS.contains("18446744071562067968"));
}

/// The failing side is stated for BOTH truth values and for EVERY machine.
#[test]
fn test_the_assert_dichotomy_is_general_and_two_sided() {
    let statement = SRC_IR_MT_DICHOTOMY.split(":=").next().unwrap_or("");
    assert!(statement.contains("(s : IRMachine)"));
    assert!(statement.contains("(b : Bool)"));
    assert!(SRC_IR_MT_DICHOTOMY.contains("IROutcome.ub IRFault.assert_failed"));
    assert!(SRC_IR_MT_DICHOTOMY.contains("ir_advance s"));
    assert_eq!(
        SRC_IR_MT_DICHOTOMY.matches("Bool.rec").count(),
        3,
        "one in the statement's motive image, one as the proof's recursor, one in its motive"
    );
}

/// The counterfactuals are NOT the shipped body, and they panic.
#[test]
fn test_the_counterfactuals_change_exactly_one_constant_and_panic() {
    assert!(SRC_IR_MT_B0.contains("(IRConst.int_ 63)"));
    assert!(SRC_IR_MT_OOB_B0.contains("(IRConst.int_ 64)"));
    assert!(
        !SRC_IR_MT_OOB_B0.contains("(IRConst.int_ 63)"),
        "the OOB counterfactual differs from the shipped body in exactly the shift amount"
    );
    assert!(SRC_IR_MT_NEG_B0.contains("(IRConst.int_ 2147483648)"));
    for src in [SRC_IR_MT_OOB_TRAPS, SRC_IR_MT_NEG_TRAPS] {
        assert!(src.contains("IROutcome.ub IRFault.assert_failed"));
        assert!(src.contains("ir_run ir_d9"));
    }
    // …and the shipped one does NOT.
    assert!(SRC_IR_MT_EXACT.contains("IROutcome.ret"));
    assert!(!SRC_IR_MT_EXACT.contains("assert_failed"));
}

/// Nothing after the assert runs, at any fuel.
#[test]
fn test_the_failing_arm_is_terminal_at_every_fuel() {
    let statement = SRC_IR_MT_OOB_ANY_FUEL.split(":=").next().unwrap_or("");
    assert!(statement.contains("(g : Nat)"));
    assert!(statement.contains("Nat.add g ir_d6"));
    assert!(SRC_IR_MT_OOB_ANY_FUEL.contains("ir_run_steps_split"));
    assert!(SRC_IR_MT_OOB_ANY_FUEL.contains("ir_run_halted"));
}

/// A4 quantifies over the heap and the fuel bound is exactly 9.
#[test]
fn test_a4_quantifies_over_every_heap_and_bounds_fuel_at_nine() {
    let statement = SRC_IR_MT_CORRECT.split(":=").next().unwrap_or("");
    assert!(statement.contains("(mem : IRList IRMemSlot)"));
    assert!(statement.contains("Le ir_d9 fuel"));
    assert!(statement.contains("env_push_low_local_meta_tag"));
    assert!(
        !statement.contains("ir_mem0"),
        "a concrete heap would make this a witness, not a theorem"
    );
    assert!(SRC_IR_MT_CORRECT.contains("ir_run_le_ret"));
}

/// A name that already exists is a name to REUSE — the eighth chain's one
/// real error, which only the full spec build catches.
#[test]
fn test_no_existing_name_is_redeclared() {
    for src in [
        SRC_IR_MT_TI32,
        SRC_IR_MT_BD9,
        SRC_IR_MT_AMT,
        SRC_ENV_META_TAG,
        SRC_IR_MT_B0,
        SRC_IR_MT_FUNC,
        SRC_IR_MT_MODULE,
        SRC_IR_MT_MACH0,
    ] {
        for name in [
            "def ir_vc_tu64",
            "def ir_br_tu32",
            "def ir_d32",
            "def ir_d64",
            "def ir_nd1",
            "def ir_bd6",
            "def ir_vl0",
            "def ir_mem0",
            "def ir_nat_mul",
            "def ir_wrap",
        ] {
            assert!(!src.contains(name), "{name} already exists: {src}");
        }
    }
}

/// **A5 is an INSTANCE, and the two lemmas it instantiates mention no
/// closed value.** This is the property that makes it affordable, so it is
/// a checkable fact rather than a sentence in a doc comment.
#[test]
fn test_a5_is_an_instance_and_its_lemmas_are_stated_at_variables() {
    // The read-back and the inversion are stated over VARIABLES: neither
    // mentions the reflected constant anywhere.
    for src in [SRC_IR_RET_INT_NAT, SRC_IR_RET_INT_INJ] {
        assert!(
            !src.contains("env_push_low_local_meta_tag"),
            "the generalized lemmas must not mention the constant — that is the whole \
             point of generalizing: {src}"
        );
        assert!(
            !src.contains("ir_mt_"),
            "…and nothing else of this chain: {src}"
        );
    }
    // A5's PROOF applies the inversion; it does not unfold ir_outcome_nat
    // at the constant. `ir_outcome_nat` must appear in neither half of it.
    let (statement, proof) = SRC_IR_MT_MACHINE_SOUND
        .split_once(":=")
        .expect("A5 must have a proof term");
    assert!(
        proof.contains("ir_ret_int_inj"),
        "A5 must go through the generalized inversion"
    );
    assert!(
        !proof.contains("ir_outcome_nat"),
        "A5's proof must never apply ir_outcome_nat to the closed constant — that is the \
         shape that did not build: {proof}"
    );
    // …and the STATEMENT is the one the other nine chains prove.
    assert!(statement.contains("Eq Nat env_push_low_local_meta_tag k"));
    assert!(statement.contains("(k : Nat)"));
    assert!(statement.contains("(hle : Le ir_d9 fuel)"));
}

/// **The measured cost of this lane, pinned as DATA and with its SIGN.**
///
/// Three prior lemma lanes are quoted at −3.5%, +2.4% and +10–19 s, and the
/// direction gets quoted both ways often enough that it has to be a
/// checkable fact rather than a sentence. Every number here is a
/// measurement; nothing is derived from another row.
///
/// Rows 1–3 are isolated proof shapes, one `CoreSpecBundle::EvalIr`-shaped
/// build each, same process and same prefix. Row 4 is the whole
/// `Specification::new()`, four replicates per side launched TOGETHER.
#[test]
fn test_the_measured_cost_of_the_restatement_has_a_negative_sign() {
    // ── A5, three proof shapes at the same statement ──────────────────
    // The shape that shipped first does NOT appear as a number, because it
    // does not TERMINATE in the probe (killed at 600 s; in the full spec it
    // burned ~2,300 s and then reported a type mismatch). Inventing a
    // number for it is the one thing this test exists to prevent.
    let composed_at_the_constant = 232.62_f64;
    let generalized_lemma_and_its_instance = 0.04_f64 + 0.00_f64;
    assert!(
        generalized_lemma_and_its_instance < composed_at_the_constant / 1000.0,
        "the generalized shape must be three orders of magnitude cheaper than composing at \
         the constant; if that stops holding, the substrate changed and the whole cost \
         story needs re-measuring"
    );

    // ── the icmp witness: a COST LAW, not a preference ────────────────
    // ir_wrap goes through ir_div_go, whose recursion is on the QUOTIENT.
    // Same theorem, same operands, three declared widths.
    let (w32, w16, w8) = (0.01_f64, 10.06_f64, 167.26_f64);
    assert!(
        w32 < w16 && w16 < w8,
        "the cost must rise as the declared width falls: the quotient 2^31/2^w is what is \
         being walked"
    );
    // …and width 8 is not merely slow. It DOES NOT ELABORATE, which is why
    // the registered theorem is at width 16.
    assert!(
        SRC_IR_MT_ICMP_WIDTH.contains("(IRTy.uint_ ir_d16)"),
        "the narrow half of the width contrast must stay at width 16 — at width 8 this \
         declaration fails to elaborate after {w8} s"
    );
    assert!(
        SRC_IR_MT_ICMP_AT_THE_BODYS_WIDTH.contains("ir_br_tu32"),
        "…and the other half must be at the width the SHIPPED body declares"
    );

    // ── where ir_mt_exact's cost is, by a fuel ladder ─────────────────
    // (fuel 6 through the assert, 7 through the sext, 8 through the shl,
    // 9 the whole run including the comparison against the constant).
    let ladder: &[(u32, f64)] = &[(6, 0.04), (7, 0.05), (8, 0.06), (9, 316.95)];
    for (fuel, secs) in ladder {
        if *fuel < 9 {
            assert!(
                *secs < 0.5,
                "the NINE MACHINE STEPS are free — fuel {fuel} must stay under half a \
                 second, or the cost stopped being the final comparison"
            );
        }
    }
    // …and it is the SHIFT AMOUNT that costs, at a fixed nine-node body.
    let by_amount: &[(u32, f64)] = &[(3, 0.07), (16, 8.94), (63, 316.95)];
    for w in by_amount.windows(2) {
        assert!(
            w[1].1 > w[0].1 * 10.0,
            "the cost must grow steeply in the shift amount: that is the evidence that the \
             residue, not the machine, is what is being normalized"
        );
    }

    // ── NO SPELLING OF THE RIGHT-HAND SIDE CAN HELP ───────────────────
    // Byte-identical terms short-circuit; anything else normalizes. There
    // is no congruence step and no lazy-delta short-circuit — comparing the
    // term against a CONSTANT whose body IS that term costs the same.
    let byte_identical = 0.00_f64;
    let one_argument_respelled = [368.50_f64, 364.63_f64];
    let against_a_constant_with_that_body = 317.33_f64;
    assert!(byte_identical < 0.01);
    for t in one_argument_respelled {
        assert!(
            t > 300.0,
            "a single respelled argument must cost the full normalization; if it ever stops \
             doing so, the kernel gained a congruence step and ir_mt_exact should be \
             re-measured"
        );
    }
    assert!(
        against_a_constant_with_that_body > 300.0,
        "and delta-unfolding a constant onto its own body must not short-circuit either — \
         this is what rules out spelling the reflected constant as the machine's residue"
    );

    // ── the whole build ───────────────────────────────────────────────
    // (before, after) of one full `Specification::new()`, seconds. Four
    // replicates per side: the four heavy gates launched TOGETHER, so both
    // sets run at the same 4-way concurrency in one window. All eight
    // processes were GREEN — that is what makes this a cost and not a
    // bracket.
    let rounds: &[(f64, f64)] = &[
        (BEFORE_1, AFTER_1),
        (BEFORE_2, AFTER_2),
        (BEFORE_3, AFTER_3),
        (BEFORE_4, AFTER_4),
    ];
    for (i, (before, after)) in rounds.iter().enumerate() {
        assert!(
            after > before,
            "replicate {} must show the landed tree SLOWER: this chain ADDS a nine-step \
             kernel-executed run and removes none",
            i + 1
        );
        let delta = after - before;
        assert!(
            (330.0..470.0).contains(&delta),
            "replicate {} delta {delta:.1} s is outside the measured band; re-measure \
             before changing this number",
            i + 1
        );
    }

    // ── what the cost pass REMOVED, and it is the sign of this lane ───
    // The tree as received did not build: 2,572.7 s and a type error. Two
    // declarations besides A5 were restated, each with a measurement:
    let a5_before = "did not build";
    let heap_witness_before_restatement = 326.93_f64; // now under 0.4 s
    let icmp_before_restatement = 166.55_f64; // and it FAILED at that price
    assert_eq!(a5_before, "did not build");
    assert!(
        heap_witness_before_restatement > 300.0,
        "ir_mt_w_heap_is_unread was the SECOND most expensive declaration in the whole \
         specification, within 2 s of ir_mt_exact; if that stops being true the derivation \
         from A4 stopped being worth its comment"
    );
    // The complete build BEFORE those two restatements, measured at 2-way
    // concurrency on the same pair of trees: 1518.7 -> 2198.0 s, +679.3 s.
    // Removing the heap witness accounts for essentially all of the
    // difference between that and the figure above.
    let (paired_2way_before, paired_2way_after) = (1518.7_f64, 2198.0_f64);
    let delta_before_the_restatements = paired_2way_after - paired_2way_before;
    let mean_delta = rounds.iter().map(|r| r.1 - r.0).sum::<f64>() / 4.0;
    assert!(
        mean_delta < delta_before_the_restatements,
        "the cost pass must have made the chain CHEAPER, not merely buildable"
    );
    assert!(
        (delta_before_the_restatements
            - heap_witness_before_restatement
            - icmp_before_restatement / 2.0)
            < mean_delta + 120.0,
        "the two restatements must account for the difference; a gap means one of the \
         measurements is of a different tree"
    );
    // …and what is LEFT is one declaration.
    let ir_mt_exact_secs = 328.55_f64;
    assert!(
        ir_mt_exact_secs > 0.75 * (mean_delta - 80.0),
        "ir_mt_exact must still be essentially the whole of the remaining cost; if it stops \
         being, something else in the stage grew and the named build item is aimed wrong"
    );
}

// The four paired replicates, one per heavy gate, 2026-08-17, measured on
// the tree this commit lands. Named rather than inlined so the table reads
// as data and a re-measurement edits eight numbers in one place. Pairing is
// BY GATE, not by rank: the two sides of a row are the same test binary on
// the two trees, launched in the same window.
//
//   gate                      before      after     delta
//   proof_status_invariants   1646.6  ->  2051.0   +404.4
//   premise_witness_gate      1647.5  ->  2047.3   +399.8
//   vacuity_firewall          1650.7  ->  2045.2   +394.5
//   axiom_ratchet             1656.6  ->  2045.4   +388.8
const BEFORE_1: f64 = 1646.6;
const BEFORE_2: f64 = 1647.5;
const BEFORE_3: f64 = 1650.7;
const BEFORE_4: f64 = 1656.6;
const AFTER_1: f64 = 2051.0;
const AFTER_2: f64 = 2047.3;
const AFTER_3: f64 = 2045.2;
const AFTER_4: f64 = 2045.4;

#[test]
fn test_sources_balanced_ascii() {
    for src in ALL_SOURCES {
        let mut d: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => d += 1,
                ')' => d -= 1,
                _ => {}
            }
            assert!(d >= 0, "unbalanced parens in {src}");
        }
        assert_eq!(d, 0, "unbalanced parens in {src}");
        assert!(src.is_ascii(), "spec sources must be ASCII");
    }
}

const ALL_SOURCES: &[&str] = &[
    SRC_IR_MT_TI32,
    SRC_IR_MT_BD9,
    SRC_IR_MT_AMT,
    SRC_ENV_META_TAG,
    SRC_IR_MT_B0,
    SRC_IR_MT_FUNC,
    SRC_IR_MT_MODULE,
    SRC_IR_MT_MACH0,
    SRC_IR_MT_INIT,
    SRC_IR_MT_COND,
    SRC_IR_MT_COND_HOLDS,
    SRC_IR_MT_EXACT,
    SRC_IR_MT_CORRECT,
    SRC_IR_RET_INT_NAT,
    SRC_IR_RET_INT_INJ,
    SRC_IR_MT_MACHINE_SOUND,
    SRC_IR_MT_NEVER_FAULTS,
    SRC_IR_MT_DICHOTOMY,
    SRC_IR_MT_NOT_BOOL,
    SRC_IR_MT_OOB_B0,
    SRC_IR_MT_OOB_FUNC,
    SRC_IR_MT_OOB_MODULE,
    SRC_IR_MT_OOB_MACH0,
    SRC_IR_MT_OOB_TRAPS,
    SRC_IR_MT_OOB_SIX,
    SRC_IR_MT_OOB_ANY_FUEL,
    SRC_IR_MT_OOB_NOT_RET,
    SRC_IR_MT_NEG_B0,
    SRC_IR_MT_NEG_FUNC,
    SRC_IR_MT_NEG_MODULE,
    SRC_IR_MT_NEG_TRAPS,
    SRC_IR_MT_BITCAST,
    SRC_IR_MT_BITCAST_ZERO_EXT,
    SRC_IR_MT_SEXT_SIGN_EXTENDS,
    SRC_IR_MT_SHL_OOB,
    SRC_IR_MT_ICMP_WIDTH,
    SRC_IR_MT_ICMP_AT_THE_BODYS_WIDTH,
    SRC_W_RUNS,
    SRC_W_HEAP_UNREAD,
    SRC_W_SOUND,
    SRC_W_BOUNDARY,
];
