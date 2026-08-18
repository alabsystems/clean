// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the EIGHTH chain's registered `ir_fd_*` sources —
//! the single typed `fdiv` and its `ret`, binary64, the three parameters,
//! A4's totality over a partial value domain, A5's inversion, the refusal
//! boundary proved both ways and the witnesses either side of it.
//!
//! Moved out of `eval_ir_float_div.rs` VERBATIM on 2026-08-17 (module body
//! unchanged, not one assertion or test name touched) because that file stood
//! at 521 lines and `data/paragon_ratchet.json`'s `files_over_500` is
//! shrink-only. The `eval_ir_float_fin_witnesses_tests.rs` precedent.

use super::*;

/// The whole body: one `fdiv` at f64 over `%1, %2` into `%3`, then `ret %3`.
/// Every token in that sentence is a lane the CFG gate compares.
#[test]
fn test_the_body_is_one_typed_fdiv_and_a_ret_of_its_result() {
    assert!(SRC_IR_FD_B0.contains("IRInst.binop IRBinOp.fdiv ir_fd_tf64 ir_d1 ir_d2) ir_d3"));
    assert!(SRC_IR_FD_B0.contains("IRInst.ret (ir_nl1 ir_d3)"));
    // …and it returns the QUOTIENT, not the dividend. This is the assertion
    // the `rets` lane exists for: `ret %1` agreed with every earlier lane.
    assert!(!SRC_IR_FD_B0.contains("IRInst.ret (ir_nl1 ir_d1)"));
    assert!(
        !SRC_IR_FD_B0.contains("condbr")
            && !SRC_IR_FD_B0.contains("switch")
            && !SRC_IR_FD_B0.contains("IRInst.br "),
        "one block, no control flow at all"
    );
}

/// binary64, spelled as the width the dispatcher decides.
#[test]
fn test_the_type_is_binary64() {
    // Split rather than restated whole: a second verbatim copy of the
    // declaration would be a second thing the CFG type lane's alias scanner
    // reads, and a perturbation that changed only one of them would fail
    // for the wrong reason.
    assert_eq!(SRC_IR_FD_TF64.split(":= ").nth(1), Some("IRTy.float_ 64"));
    assert!(SRC_IR_FD_TF64.starts_with("def ir_fd_tf64"));
    assert!(
        SRC_W_F32.contains("IRTy.float_ 32") && SRC_W_F32.contains("ir_float_fault"),
        "the same operands at binary32 must be registered as UNMODELLED, or the width on the \
         instruction is decoration"
    );
}

/// Three parameters, and the first is the closure environment.
#[test]
fn test_three_parameters_and_the_env_pointer_is_unconstrained() {
    assert!(SRC_IR_FD_FUNC.contains("IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0"));
    assert!(SRC_IR_FD_MACH0.contains("ir_bind_params (ir_nl3 ir_d0 ir_d1 ir_d2)"));
    // …through the FIFTH chain's builders. Re-declaring `ir_nl3` / `ir_vl3`
    // here is a duplicate definition that only the FULL spec build rejects.
    assert!(!SRC_IR_FD_MACH0.contains("def ir_nl3") && !SRC_IR_FD_MACH0.contains("def ir_vl3"));
    // A4 takes `p : IRScalar` with NO premise on it.
    let statement = SRC_IR_FD_CORRECT.split(":=").next().unwrap_or("");
    assert!(statement.contains("(p : IRScalar)"));
    assert!(
        !statement.contains("EncodesF64Val p"),
        "the environment pointer is never read; constraining it would weaken the theorem"
    );
}

/// A4 is TOTAL and its conclusion is NOT an `IROutcome.ret`.
#[test]
fn test_a4_is_total_over_a_partial_value_domain() {
    let statement = SRC_IR_FD_CORRECT.split(":=").next().unwrap_or("");
    assert!(statement.contains("(a : Nat)") && statement.contains("(b : Nat)"));
    assert!(statement.contains("(mem : IRList IRMemSlot)"));
    assert!(statement.contains("Le ir_d2 fuel ->"));
    assert!(
        statement.contains("(ir_fd_res (env_reduce_float_div a b))"),
        "the conclusion must be the CLASSIFIED outcome, refusals included"
    );
    assert!(
        !statement.contains("IROutcome.ret"),
        "a conclusion restricted to returns would throw away the half of this theorem that \
         says the emitted body's refusals are the reflected function's refusals"
    );
    assert!(
        !statement.contains("ir_mem0"),
        "a concrete heap would make this a witness, not a theorem"
    );
    assert_eq!(
        SRC_IR_FD_CORRECT.matches("EncodesF64Val.rec").count(),
        2,
        "one recursor per float parameter"
    );
    // …and it must go through the NEW monotonicity, not the ret-only one.
    assert!(SRC_IR_FD_CORRECT.contains("ir_fd_run_le"));
    assert!(!SRC_IR_FD_CORRECT.contains("ir_run_le_ret"));
}

/// The fuel induction must refute exhaustion rather than assume it away,
/// at BOTH constructors of the outcome image.
#[test]
fn test_exhaustion_is_refuted_on_both_arms() {
    assert!(SRC_IR_FD_FUELOUT_ABSURD.contains("ir_outcome_fuelout_ne_unmodelled_prop"));
    assert!(SRC_IR_FD_FUELOUT_ABSURD.contains("ir_outcome_fuelout_ne_ret_prop"));
    assert!(SRC_IR_FD_RUN_SUCC.contains("ir_fd_fuelout_absurd"));
    assert!(
        SRC_IR_FD_RUN_LE.contains("Le.rec f "),
        "parameter comes first"
    );
}

/// A5 exists, inverts, and reaches the ARGUMENTS.
#[test]
fn test_a5_inverts_and_reaches_the_arguments() {
    assert!(SRC_IR_FD_MACHINE_SOUND
        .contains(": Eq (IROption Nat) (env_reduce_float_div a b) (IROption.some Nat k)"));
    assert!(SRC_IR_FD_MACHINE_SOUND.contains("ir_fd_answer_res"));
    // The division-by-zero corollary concludes about the OPERANDS' signs.
    assert!(SRC_IR_FD_MACHINE_SOUND_DIVZERO.contains("(ir_f64_class b) IRF64Class.zero_"));
    assert!(SRC_IR_FD_MACHINE_SOUND_DIVZERO.contains(": Eq Nat (ir_f64_qinf a b) k"));
    assert!(SRC_IR_FD_MACHINE_SOUND_DIVZERO.contains("ir_fd_machine_sound mem fuel na"));
}

/// The refusal boundary is PROVED, in both directions, and the trap-freedom
/// corollary is separate from it.
#[test]
fn test_the_refusal_boundary_is_proved_both_ways() {
    assert!(SRC_IR_FD_RETURNS_IFF_MODELLED.contains(
        ": Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem \
         na)) (ir_option_is_some (env_reduce_float_div a b))"
    ));
    assert!(SRC_IR_FD_NEVER_TRAPS.contains("(ir_outcome_is_trap"));
    assert!(SRC_IR_FD_NEVER_TRAPS.contains("Bool.false"));
    // `unmodelled` must NOT count as a trap: it is a stated refusal.
    assert!(
        SRC_IR_OUTCOME_IS_TRAP.contains(
            "(fun (_ : IRFault) => Bool.true) (fun (_ : IRFault) => Bool.true) (fun (_ : \
             IRFault) => Bool.false) (fun (_ : IRFault) => Bool.true) Bool.true"
        ),
        "IROutcome's order is ret/ub/type_error/unmodelled/stuck/fuel_out, and only the \
         FOURTH is not a trap"
    );
}

/// Both sides of the boundary are executed by the kernel, and the
/// embarrassing refusal is registered along with the flattering answers.
#[test]
fn test_witnesses_cover_both_sides_of_the_boundary() {
    for src in [
        SRC_W_ONE_OVER_PLUS_ZERO,
        SRC_W_ONE_OVER_MINUS_ZERO,
        SRC_W_MINUS_ONE_OVER_PLUS_ZERO,
        SRC_W_ONE_OVER_INF,
        SRC_W_MINUS_ZERO_OVER_INF,
        SRC_W_ORDER,
    ] {
        assert!(src.contains("ir_eval ir_d2 ir_fd_module"));
        assert!(src.contains("IROutcome.ret"), "an answering witness");
        assert!(src.contains(":= Eq.refl IROutcome"));
    }
    for src in [
        SRC_W_INF_OVER_INF,
        SRC_W_ZERO_OVER_ZERO,
        SRC_W_FIN_OVER_FIN,
        SRC_W_NAN,
    ] {
        assert!(src.contains("ir_eval ir_d2 ir_fd_module"));
        assert!(
            src.contains("IROutcome.unmodelled IRFault.float_domain"),
            "a refusing witness must be the TAGGED refusal, never a value"
        );
    }
    // 1/+0 and 1/-0 must give DIFFERENT infinities, or the signed zero is
    // being treated as noise.
    assert!(SRC_W_ONE_OVER_PLUS_ZERO.contains("IRScalar.float_ 9218868437227405312)))"));
    assert!(SRC_W_ONE_OVER_MINUS_ZERO.contains("IRScalar.float_ 18442240474082181120)))"));
    // …and 2.0/1.0, whose answer is obvious, is registered as REFUSED.
    assert!(SRC_W_FIN_OVER_FIN.contains("4611686018427387904"));
}

/// The float lane must be measurably different from the integer lane.
#[test]
fn test_float_division_by_zero_is_not_integer_division_by_zero() {
    assert!(SRC_W_UDIV_CONTRAST.contains("IRBinOp.udiv"));
    assert!(SRC_W_UDIV_CONTRAST.contains("IROutcome.ub IRFault.div_zero"));
    assert!(SRC_W_ONE_OVER_PLUS_ZERO.contains("IRScalar.float_ 0)"));
    assert!(SRC_W_ONE_OVER_PLUS_ZERO.contains("IROutcome.ret"));
}

#[test]
fn test_sources_balanced_ascii() {
    for src in [
        SRC_IR_FD_TF64,
        SRC_ENV_REDUCE_FLOAT_DIV,
        SRC_ENCODESF64VAL,
        SRC_IR_FD_RES,
        SRC_IR_FD_B0,
        SRC_IR_FD_FUNC,
        SRC_IR_FD_MODULE,
        SRC_IR_FD_MACH0,
        SRC_IR_FD_M1,
        SRC_IR_FD_ONE_STEP,
        SRC_IR_FD_SPLIT,
        SRC_IR_FD_EXACT,
        SRC_FUELOUT_NE_UNMODELLED,
        SRC_IR_FD_FUELOUT_ABSURD,
        SRC_IR_FD_RUN_SUCC,
        SRC_IR_FD_RUN_LE,
        SRC_IR_FD_CORRECT,
        SRC_IR_FD_HEAD_FLOAT,
        SRC_IR_FD_ANSWER,
        SRC_IR_FD_ANSWER_RES,
        SRC_IR_FD_MACHINE_SOUND,
        SRC_IR_FD_DIV_FIN_ZERO,
        SRC_IR_OPTION_GET,
        SRC_IR_FD_MACHINE_SOUND_DIVZERO,
        SRC_IR_OPTION_IS_SOME,
        SRC_IR_FD_RES_IS_RET,
        SRC_IR_FD_RETURNS_IFF_MODELLED,
        SRC_IR_OUTCOME_IS_TRAP,
        SRC_IR_FD_RES_NEVER_TRAPS,
        SRC_IR_FD_NEVER_TRAPS,
        SRC_W_ONE_OVER_PLUS_ZERO,
        SRC_W_ONE_OVER_MINUS_ZERO,
        SRC_W_MINUS_ONE_OVER_PLUS_ZERO,
        SRC_W_ONE_OVER_INF,
        SRC_W_MINUS_ZERO_OVER_INF,
        SRC_W_INF_OVER_INF,
        SRC_W_ZERO_OVER_ZERO,
        SRC_W_FIN_OVER_FIN,
        SRC_W_NAN,
        SRC_W_ORDER,
        SRC_W_INT_OPERAND,
        SRC_W_F32,
        SRC_W_UDIV_CONTRAST,
        SRC_W_CORRECT_WITNESS,
        SRC_W_DIVZERO_WITNESS,
    ] {
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
