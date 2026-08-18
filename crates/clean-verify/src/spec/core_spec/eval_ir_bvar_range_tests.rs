// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the FIFTH chain's registered `ir_br_*` sources —
//! the two `condbr`s and their emitted targets, the twice-computed lower
//! bound, the chained join blocks, the A4/A5 shape and the path witnesses
//! covering both `condbr` edges.
//!
//! Moved out of `eval_ir_bvar_range.rs` VERBATIM on 2026-08-17 (module body
//! unchanged, not one assertion or test name touched) because that file stood
//! at 532 lines and `data/paragon_ratchet.json`'s `files_over_500` is
//! shrink-only. The `eval_ir_float_fin_witnesses_tests.rs` precedent.

use super::*;

/// Two `condbr`s with the emitted targets. Exchanging either pair negates
/// what the body computes.
#[test]
fn test_two_condbrs_with_the_emitted_targets() {
    assert!(SRC_IR_BR_B0.contains("IRInst.condbr ir_d6 ir_d1 ir_nl0 ir_d2 ir_nl0"));
    assert!(SRC_IR_BR_B2.contains("IRInst.condbr ir_d8 ir_d4 ir_nl0 ir_d5 ir_nl0"));
    assert!(
        !SRC_IR_BR_B0.contains("IRInst.switch") && !SRC_IR_BR_B2.contains("IRInst.switch"),
        "this body dispatches with condbr, not with a switch"
    );
    // Neither condbr passes block arguments: the joins are fed by `br`.
    assert_eq!(SRC_IR_BR_B0.matches("ir_nl0").count(), 3);
}

/// The two `icmp uge` are SEPARATE instructions in separate blocks binding
/// separate SSA ids. Sharing one would be a smaller CFG.
#[test]
fn test_the_lower_bound_is_computed_twice() {
    assert!(SRC_IR_BR_B1.contains("IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d0 ir_d1) ir_d7"));
    assert!(SRC_IR_BR_B2.contains("IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d0 ir_d1) ir_d8"));
    assert!(SRC_IR_BR_B4.contains("IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d0 ir_d2) ir_d9"));
}

/// Two join blocks, and the inner one branches into the outer one.
#[test]
fn test_two_join_blocks_chained() {
    assert!(SRC_IR_BR_B3.contains("IRBlock.mk ir_d3 (ir_nl1 ir_d3)"));
    assert!(SRC_IR_BR_B6.contains("IRBlock.mk ir_d6 (ir_nl1 ir_d4)"));
    assert!(
        SRC_IR_BR_B6.contains("IRInst.br ir_d3 (ir_nl1 ir_d4)"),
        "the inner join forwards its parameter to the outer join"
    );
    assert!(
        SRC_IR_BR_B3.contains("IRInst.ret"),
        "only the outer join returns"
    );
}

/// The reflected function must mirror the CFG, not the surface `&&`.
#[test]
fn test_reflected_function_is_the_branch_shape() {
    assert!(
        !SRC_EXPR_BVAR_IN_RANGE.contains("Bool.and"),
        "the emitted body has no `and` instruction; the short circuit is control flow"
    );
    assert_eq!(
        SRC_EXPR_BVAR_IN_RANGE.matches("Bool.rec").count(),
        2,
        "two nested case analyses, one per emitted condbr"
    );
    // Bool.rec's minor order is (false, true): the FALSE minor of the outer
    // recursion is the BOUNDED arm.
    assert!(SRC_EXPR_BVAR_IN_RANGE
        .contains("(Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) (ir_br_c2 i s)) (ir_br_c2 i s) (ir_br_c1 e)"));
}

/// The double residue is deliberate and must not be quietly simplified —
/// and the sentinel must be the LITERAL, not a name for it.
#[test]
fn test_the_double_wrap_is_recorded_not_simplified() {
    assert!(
        SRC_IR_BR_C1.contains("(ir_wrap ir_d32 (ir_wrap ir_d32 4294967295))"),
        "IRInst.const_ canonicalizes the literal and ir_int_cmp canonicalizes again; the \
         reflected predicate records both because ir_wrap idempotence is not proved"
    );
    // Naming the sentinel is what cost this chain its registration. The
    // machine materialises `ir_wrap ir_d32 4294967295`; against
    // `ir_wrap ir_d32 <a definition equal to it>` the kernel reduces both
    // residues instead of comparing arguments, and a width-32 residue is
    // ~2^32 `Nat.rec` unfoldings (measured: 0.021/0.431/6.586 s at w =
    // 8/12/16). Both sites must carry the literal the emitted IR carries.
    assert!(
        !SRC_IR_BR_C1.contains("umax") && !SRC_IR_BR_M1.contains("umax"),
        "the sentinel must be the literal the emitted body materialises, not a name for it"
    );
    assert!(SRC_IR_BR_M1.contains("IRScalar.int_ (ir_wrap ir_d32 4294967295)"));
    assert_eq!(SRC_IR_BR_C2.matches("ir_wrap ir_d32").count(), 2);
    assert_eq!(SRC_IR_BR_C3.matches("ir_wrap ir_d32").count(), 2);
}

/// A4 stays universally quantified; A5 exists and is used for more than
/// restating itself.
#[test]
fn test_a4_a5_shape() {
    let statement = SRC_IR_BR_CORRECT.split(":=").next().unwrap_or("");
    assert!(statement.contains("(i : Nat)") && statement.contains("(mem : IRList IRMemSlot)"));
    assert!(SRC_IR_BR_CORRECT.contains("Le ir_d9 fuel ->"));
    assert!(SRC_IR_BR_CORRECT.contains("ir_run_le_ret"));
    assert!(
        !statement.contains("ir_mem0"),
        "a concrete heap would make this a witness, not a theorem"
    );
    assert_eq!(
        SRC_IR_BR_CORRECT.matches("EncodesU32Val.rec").count(),
        3,
        "one recursor per parameter; fewer would leave a premise unused"
    );
    assert!(SRC_IR_BR_MACHINE_SOUND.contains(": Eq Bool (expr_bvar_in_range i s e) c"));
    assert!(SRC_IR_BR_MACHINE_SOUND.contains("ir_outcome_bool"));
    // …and A5 goes further than the reflected function, onto the arguments.
    assert!(SRC_IR_BR_MACHINE_SOUND_LOWER.contains(": Eq Bool (ir_br_c2 i s) Bool.true"));
    assert!(SRC_IR_BR_MACHINE_SOUND_LOWER.contains("ir_br_machine_sound mem fuel na"));
}

/// `ir_br_exact` is proved by the 7+2 step split, and the split stops
/// BEFORE the first `condbr`. Reverting it to the one-line instantiation is
/// the change that could not be shown to terminate.
#[test]
fn test_exact_goes_through_the_two_step_split() {
    assert!(
        SRC_IR_BR_EXACT.contains("ir_run_steps_split ir_br_module ir_d7 ir_d2"),
        "the 9-step goal must be peeled as 7 + 2 by the general semantics lemma"
    );
    assert!(SRC_IR_BR_EXACT.contains("ir_br_two_steps i s e mem na"));
    assert!(SRC_IR_BR_EXACT.contains("ir_br_split1 i s e mem na (ir_br_c1 e)"));
    // The two-step lemma stops at ir_d2 — one step further reaches the
    // condbr, whose scrutinee is symbolic, and the check stops being bounded.
    assert!(SRC_IR_BR_TWO_STEPS.contains("ir_steps ir_d2 ir_br_module"));
    assert!(
        SRC_IR_BR_TWO_STEPS.contains(":= Eq.refl IRConfig"),
        "two steps of the machine are decided by computation, not by a case analysis"
    );
    // …and the statement of A4's machine lemma is unchanged: same fuel, same
    // entry configuration, same reflected answer.
    let statement = SRC_IR_BR_EXACT.split(":=").next().unwrap_or("");
    assert!(statement.contains("ir_run ir_d9 ir_br_module"));
    assert!(statement.contains("IRConfig.running (ir_br_mach0 i s e mem na)"));
    assert!(statement.contains("IRScalar.bool_ (expr_bvar_in_range i s e)"));
}

/// The path witnesses execute the machine along every emitted path, with
/// the branch conditions supplied as literals — the only executions the
/// kernel can perform for this body.
#[test]
fn test_path_witnesses_cover_both_condbr_edges() {
    assert!(SRC_IR_BR_PATH_UNBOUNDED.contains("ir_br_split1 i s e mem na Bool.true"));
    assert!(SRC_IR_BR_PATH_BOUNDED.contains("ir_br_split1 i s e mem na Bool.false"));
    assert!(SRC_IR_BR_PATH_UPPER.contains("ir_br_split2 i s e mem na Bool.true"));
    assert!(SRC_IR_BR_PATH_SHORT_CIRCUIT.contains("ir_br_split2 i s e mem na Bool.false"));
    // the short-circuit path answers a CONSTANT false, which is what makes
    // it the operational content of `&&`
    assert!(SRC_IR_BR_PATH_SHORT_CIRCUIT.contains("(IRScalar.bool_ Bool.false)"));
    // …and no witness pretends to evaluate the sentinel comparison, which
    // the kernel cannot decide at width 32.
    for src in [
        SRC_IR_BR_PATH_UNBOUNDED,
        SRC_IR_BR_PATH_BOUNDED,
        SRC_IR_BR_PATH_UPPER,
        SRC_IR_BR_PATH_SHORT_CIRCUIT,
        SRC_IR_BR_CORRECT_WITNESS,
    ] {
        assert!(
            !src.contains("ir_br_c1"),
            "no witness may depend on deciding ir_br_c1: the width-32 residue costs ~2^32 \
             Nat.rec unfoldings, and a witness that needed it would hang the spec build"
        );
    }
}
