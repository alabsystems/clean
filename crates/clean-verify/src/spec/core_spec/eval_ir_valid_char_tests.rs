// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the SIXTH chain's registered `ir_vc_*` sources —
//! the two `condbr`s and the entry one's polarity, the second comparison's
//! constant sitting on the LEFT, the chained join blocks, the carried
//! literals, the A4/A5 shape and the single concrete run.
//!
//! Moved out of `eval_ir_valid_char.rs` VERBATIM on 2026-08-17 (module body
//! unchanged, not one assertion or test name touched) because that file stood
//! at 509 lines and `data/paragon_ratchet.json`'s `files_over_500` is
//! shrink-only. The `eval_ir_float_fin_witnesses_tests.rs` precedent.

use super::*;

/// Two `condbr`s with the emitted targets, and the entry one has the
/// OPPOSITE polarity to the fifth chain's.
#[test]
fn test_two_condbrs_with_the_emitted_targets() {
    assert!(SRC_IR_VC_B0.contains("IRInst.condbr ir_d4 ir_d2 ir_nl0 ir_d1 ir_nl0"));
    assert!(SRC_IR_VC_B1.contains("IRInst.condbr ir_d6 ir_d4 ir_nl0 ir_d5 ir_nl0"));
    assert!(
        !SRC_IR_VC_B0.contains("IRInst.switch") && !SRC_IR_VC_B1.contains("IRInst.switch"),
        "this body dispatches with condbr, not with a switch"
    );
    // The entry condbr's THEN target is the higher-numbered block (bb2, the
    // immediate `true`) and its ELSE target the lower one. Exchanging them
    // negates what the body computes and changes no other lane.
    assert!(SRC_IR_VC_B0.contains("condbr ir_d4 ir_d2 "));
}

/// The constant is the LEFT operand of the second comparison. This is the
/// structurally new instruction in the chain and the whole reason the
/// residue has to be reduced rather than left stuck.
#[test]
fn test_the_second_comparison_has_its_constant_on_the_left() {
    assert!(SRC_IR_VC_B1.contains("IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d5 ir_d0) ir_d6"));
    assert!(SRC_IR_VC_B0.contains("IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d3) ir_d4"));
    assert!(SRC_IR_VC_B4.contains("IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d8) ir_d9"));
    // …and the reflected predicate mirrors the operand order.
    assert!(SRC_IR_VC_C2.starts_with(
        "def ir_vc_c2 (n : Nat) : Bool := ir_nat_ltb (ir_wrap ir_d64 (ir_wrap ir_d64 57343))"
    ));
    assert!(SRC_IR_VC_C1.contains("ir_nat_ltb (ir_wrap ir_d64 n)"));
    assert!(SRC_IR_VC_C3.contains("ir_nat_ltb (ir_wrap ir_d64 n)"));
}

/// Two join blocks, and the inner one branches into the outer one.
#[test]
fn test_two_join_blocks_chained() {
    assert!(SRC_IR_VC_B3.contains("IRBlock.mk ir_d3 (ir_nl1 ir_d1)"));
    assert!(SRC_IR_VC_B6.contains("IRBlock.mk ir_d6 (ir_nl1 ir_d2)"));
    assert!(
        SRC_IR_VC_B6.contains("IRInst.br ir_d3 (ir_nl1 ir_d2)"),
        "the inner join forwards its parameter to the outer join"
    );
    assert!(
        SRC_IR_VC_B3.contains("IRInst.ret"),
        "only the outer join returns"
    );
    // bb2 reaches the OUTER join directly, not through bb6.
    assert!(SRC_IR_VC_B2.contains("IRInst.br ir_d3 (ir_nl1 ir_d7)"));
}

/// The reflected function must mirror the CFG, not the surface `||` / `&&`.
#[test]
fn test_reflected_function_is_the_branch_shape() {
    assert!(
        !SRC_ENV_IS_VALID_CHAR.contains("Bool.and") && !SRC_ENV_IS_VALID_CHAR.contains("Bool.or"),
        "the emitted body has no `and` and no `or` instruction; both short circuits are \
         control flow"
    );
    assert_eq!(
        SRC_ENV_IS_VALID_CHAR.matches("Bool.rec").count(),
        2,
        "two nested case analyses, one per emitted condbr"
    );
    // Bool.rec's minor order is (false, true): the FALSE minor of the outer
    // recursion is the arm that still has to decide the surrogate range.
    assert!(SRC_ENV_IS_VALID_CHAR.contains(
        "(Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) (ir_vc_c2 n)) Bool.true \
         (ir_vc_c1 n)"
    ));
}

/// The three literals are the ones the emitted `IRInst.const_`s carry, the
/// double residue is recorded rather than simplified, and no sentinel is
/// hidden behind a name.
#[test]
fn test_the_literals_are_carried_not_named() {
    assert!(SRC_IR_VC_B0.contains("IRConst.int_ 55296"));
    assert!(SRC_IR_VC_B1.contains("IRConst.int_ 57343"));
    assert!(SRC_IR_VC_B4.contains("IRConst.int_ 1114112"));
    assert!(SRC_IR_VC_M1.contains("IRScalar.int_ (ir_wrap ir_d64 55296)"));
    assert!(SRC_IR_VC_M4.contains("IRScalar.int_ (ir_wrap ir_d64 57343)"));
    for src in [SRC_IR_VC_C1, SRC_IR_VC_C2, SRC_IR_VC_C3] {
        assert_eq!(
            src.matches("ir_wrap ir_d64").count(),
            3,
            "each comparison canonicalizes both operands, and one of them is itself a \
             canonicalized literal: three wraps, recorded rather than collapsed"
        );
    }
    // A name for a large literal is what made the fifth chain undecidable.
    for src in [
        SRC_IR_VC_C1,
        SRC_IR_VC_C2,
        SRC_IR_VC_C3,
        SRC_IR_VC_M1,
        SRC_IR_VC_M4,
    ] {
        assert!(
            !src.contains("max") && !src.contains("sentinel"),
            "every constant must be the literal the emitted body materializes"
        );
    }
}

/// A4 stays universally quantified; A5 exists and reaches the argument.
#[test]
fn test_a4_a5_shape() {
    let statement = SRC_IR_VC_CORRECT.split(":=").next().unwrap_or("");
    assert!(statement.contains("(n : Nat)") && statement.contains("(mem : IRList IRMemSlot)"));
    assert!(SRC_IR_VC_CORRECT.contains("Le ir_d11 fuel ->"));
    assert!(SRC_IR_VC_CORRECT.contains("ir_run_le_ret"));
    assert!(
        !statement.contains("ir_mem0"),
        "a concrete heap would make this a witness, not a theorem"
    );
    assert_eq!(
        SRC_IR_VC_CORRECT.matches("EncodesU64Val.rec").count(),
        1,
        "one recursor for the one parameter"
    );
    assert!(SRC_IR_VC_MACHINE_SOUND.contains(": Eq Bool (env_is_valid_char n) c"));
    assert!(SRC_IR_VC_MACHINE_SOUND.contains("ir_outcome_bool"));
    // …and A5 goes further than the reflected function, onto the argument.
    assert!(SRC_IR_VC_MACHINE_SOUND_NOT_SURROGATE
        .contains(": Eq Bool (Bool.or (ir_vc_c1 n) (ir_vc_c2 n)) Bool.true"));
    assert!(SRC_IR_VC_MACHINE_SOUND_NOT_SURROGATE.contains("ir_vc_machine_sound mem fuel na"));
}

/// `ir_vc_exact` is proved by the 9+2 step split, and the split stops
/// BEFORE the first `condbr`.
#[test]
fn test_exact_goes_through_the_two_step_split() {
    assert!(
        SRC_IR_VC_EXACT.contains("ir_run_steps_split ir_vc_module ir_d9 ir_d2"),
        "the 11-step goal must be peeled as 9 + 2 by the general semantics lemma"
    );
    assert!(SRC_IR_VC_EXACT.contains("ir_vc_two_steps n mem na"));
    assert!(SRC_IR_VC_EXACT.contains("ir_vc_split1 n mem na (ir_vc_c1 n)"));
    assert!(SRC_IR_VC_TWO_STEPS.contains("ir_steps ir_d2 ir_vc_module"));
    assert!(
        SRC_IR_VC_TWO_STEPS.contains(":= Eq.refl IRConfig"),
        "two steps of the machine are decided by computation, not by a case analysis"
    );
    let statement = SRC_IR_VC_EXACT.split(":=").next().unwrap_or("");
    assert!(statement.contains("ir_run ir_d11 ir_vc_module"));
    assert!(statement.contains("IRConfig.running (ir_vc_mach0 n mem na)"));
    assert!(statement.contains("IRScalar.bool_ (env_is_valid_char n)"));
}

/// Four PATH witnesses cover both `condbr` edges, and exactly ONE concrete
/// execution exists — the one whose path does not reach `ir_vc_c3`.
#[test]
fn test_path_witnesses_and_the_single_concrete_run() {
    assert!(SRC_IR_VC_PATH_ASCII.contains("ir_vc_split1 n mem na Bool.true"));
    assert!(SRC_IR_VC_PATH_ABOVE_SURROGATE_START.contains("ir_vc_split1 n mem na Bool.false"));
    assert!(SRC_IR_VC_PATH_UPPER.contains("ir_vc_split2 n mem na Bool.true"));
    assert!(SRC_IR_VC_PATH_SURROGATE.contains("ir_vc_split2 n mem na Bool.false"));
    assert!(SRC_IR_VC_PATH_SURROGATE.contains("(IRScalar.bool_ Bool.false)"));
    // The one concrete run is a real `ir_eval`, discharged by Eq.refl, at an
    // argument whose emitted path is bb0 -> bb2 -> bb3 and therefore never
    // materializes 0x110000 (whose residue measures 439.8 s on its own).
    assert!(SRC_IR_VC_CONCRETE_ASCII.contains("ir_eval ir_d11 ir_vc_module"));
    assert!(SRC_IR_VC_CONCRETE_ASCII.contains("(IRScalar.int_ 65)"));
    assert!(SRC_IR_VC_CONCRETE_ASCII.contains(":= Eq.refl IROutcome"));
    for src in [
        SRC_IR_VC_PATH_ASCII,
        SRC_IR_VC_PATH_ABOVE_SURROGATE_START,
        SRC_IR_VC_PATH_UPPER,
        SRC_IR_VC_PATH_SURROGATE,
        SRC_IR_VC_CORRECT_WITNESS,
    ] {
        assert!(
            !src.contains("1114112"),
            "no witness may materialize 0x110000: its width-64 residue measures 439.8 s"
        );
    }
}
