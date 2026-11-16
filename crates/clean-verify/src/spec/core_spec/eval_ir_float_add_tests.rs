// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the TWELFTH chain's registered `ir_fa_*` sources —
//! the single typed `fadd` and its `ret`, binary64, the three parameters,
//! A4's totality over a partial value domain, A5 stated at the image, the
//! signed-zero AND rule, and the answering witnesses re-derived from the
//! hardware.
//!
//! Moved out of `eval_ir_float_add.rs` on 2026-08-21 (the
//! `eval_ir_float_div_tests.rs` precedent: that file stood at the 500-line
//! convention that `data/paragon_ratchet.json`'s `files_over_500` enforces
//! shrink-only) as part of the A2 MINT migration. The only assertions that
//! changed with the move are the ones that read the now-minted module lines:
//! they read `MINTED_IR_FA` where they read `SRC_IR_FA_B0` / `_FUNC` /
//! `_MODULE` before.

use super::*;

/// The minted `def` line for one name, from the committed script.
fn minted_line(name: &str) -> &'static str {
    let prefix = format!("def {name} ");
    ir_fa_module_defs()
        .iter()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("the minted script must define {name}"))
}

/// The whole body: one `fadd` at f64 over `%1, %2` into `%3`, then `ret %3`
/// — the SUM and not an operand, and no control flow. Every token in that
/// sentence is a lane the CFG gate compares.
#[test]
fn test_the_body_is_one_typed_fadd_and_a_ret_of_its_result() {
    let b0 = minted_line("ir_fa_b0");
    assert!(b0.contains("IRInst.binop IRBinOp.fadd (IRTy.float_ 64) ir_d1 ir_d2) ir_d3"));
    assert!(b0.contains("IRInst.ret (ir_nl1 ir_d3)"));
    assert!(!b0.contains("IRInst.ret (ir_nl1 ir_d1)"));
    assert_eq!(SRC_IR_FA_TF64.split(":= ").nth(1), Some("IRTy.float_ 64"));
    assert!(!b0.contains("condbr") && !b0.contains("switch") && !b0.contains("IRInst.br "));
}

/// Every registered source, so a source cannot be added and left out of
/// the two whole-set checks below.
const ALL: &[&str] = &[
    SRC_IR_FA_TF64,
    SRC_ENV_REDUCE_FLOAT_ADD,
    SRC_IR_FA_RES,
    SRC_IR_FA_MACH0,
    SRC_IR_FA_M1,
    SRC_IR_FA_ONE_STEP,
    SRC_IR_FA_SPLIT,
    SRC_IR_FA_EXACT,
    SRC_IR_FA_FUELOUT_ABSURD,
    SRC_IR_FA_RUN_SUCC,
    SRC_IR_FA_RUN_LE,
    SRC_IR_FA_CORRECT,
    SRC_IR_FA_HEAD_FLOAT,
    SRC_IR_FA_ANSWER,
    SRC_IR_FA_ANSWER_RES,
    SRC_IR_FA_SOUND_GEN,
    SRC_IR_FA_RES_IS_RET,
    SRC_IR_FA_RES_NEVER_TRAPS,
    SRC_IR_F64_ADD_ZERO_ZERO,
    SRC_W_INT_OPERAND,
    SRC_W_F32,
    SRC_W_WRAP_CONTRAST,
    SRC_W_NAN,
    SRC_W_OPPOSITE_INF,
    SRC_W_INF_PLUS_INF,
    SRC_W_MINUS_ZEROS,
    SRC_W_MIXED_ZEROS,
    SRC_W_ZERO_PLUS_FIN,
    SRC_W_FIN_PLUS_MZERO,
    SRC_W_EXACT_ZERO_SUM,
    SRC_W_SIGNED_ZERO_SUM,
    SRC_W_CORRECT_WITNESS,
    SRC_W_ONE_PLUS_TWO,
    SRC_W_TWO_PLUS_ONE,
    SRC_W_OVERFLOW,
];

/// Nothing the earlier chains registered is re-declared: a duplicate
/// elaborates cleanly in every fast gate and fails only in the full
/// `Specification::new()`.
#[test]
fn test_no_shared_declaration_is_redeclared() {
    let all = format!("{}\n{}", ALL.join("\n"), MINTED_IR_FA);
    for shared in [
        "def ir_nl3",
        "def ir_vl3",
        "def ir_option_is_some",
        "def ir_outcome_is_trap",
        "def ir_outcome_is_ret",
        "def ir_outcome_fuelout_ne_unmodelled_prop",
        "def ir_outcome_fuelout_ne_ret_prop",
        "inductive EncodesF64Val",
    ] {
        assert!(
            !all.contains(shared),
            "{shared} must be REUSED, not declared"
        );
    }
}

/// A4 is TOTAL, quantified, and goes through the refusal-tolerant
/// monotonicity rather than the ret-only one.
#[test]
fn test_a4_is_total_over_a_partial_value_domain() {
    let statement = SRC_IR_FA_CORRECT.split(":=").next().unwrap_or("");
    assert!(statement.contains("(a : Nat)") && statement.contains("(b : Nat)"));
    assert!(statement.contains("(mem : IRList IRMemSlot)"));
    assert!(statement.contains("Le ir_d2 fuel ->"));
    assert!(
        statement.contains("(ir_fa_res (env_reduce_float_add a b))"),
        "the conclusion must be the CLASSIFIED outcome, refusals included"
    );
    // A conclusion restricted to returns would throw away the half of this
    // theorem that says the emitted body's refusals are the reflected
    // function's refusals; a concrete heap would make it a witness rather
    // than a theorem; and a premise on `p` would weaken it for nothing,
    // since the body never reads the environment pointer.
    assert!(!statement.contains("IROutcome.ret"));
    assert!(!statement.contains("ir_mem0"));
    assert!(!statement.contains("EncodesF64Val p"));
    assert_eq!(SRC_IR_FA_CORRECT.matches("EncodesF64Val.rec").count(), 2);
    assert!(SRC_IR_FA_CORRECT.contains("ir_fa_run_le"));
    assert!(!SRC_IR_FA_CORRECT.contains("ir_run_le_ret"));
}

/// **A5 and the two boundary corollaries are stated at the IMAGE, and that
/// is a measured limit rather than a stylistic choice.** If one of them ever
/// mentions `env_reduce_float_add`, somebody has composed it with A4 — the
/// shape that does not elaborate here (module header, probe table) — and
/// this fails in a second instead of in twenty-five minutes.
#[test]
fn test_a5_and_the_boundary_are_stated_at_the_image() {
    for src in [
        SRC_IR_FA_SOUND_GEN,
        SRC_IR_FA_RES_IS_RET,
        SRC_IR_FA_RES_NEVER_TRAPS,
    ] {
        assert!(
            !src.contains("env_reduce_float_add") && !src.contains("ir_f64_add"),
            "this statement must quantify over the OUTCOME IMAGE, not over the add: {src}"
        );
        assert!(src.contains("(o : IROption Nat)"));
    }
    assert!(SRC_IR_FA_SOUND_GEN.contains("ir_fa_answer_res"));
    assert!(SRC_IR_FA_SOUND_GEN.contains(": @Eq (IROption Nat) o (@IROption.some Nat k)"));
    assert!(SRC_IR_FA_RES_IS_RET.contains("ir_option_is_some o"));
    assert!(SRC_IR_FA_RES_NEVER_TRAPS.contains("ir_outcome_is_trap"));
}

/// The signed-zero rule concludes about the ARGUMENTS' sign bits, with the
/// AND that addition uses and not the XOR that multiplication does.
#[test]
fn test_the_signed_zero_rule_is_the_and_of_the_sign_bits() {
    assert!(SRC_IR_F64_ADD_ZERO_ZERO.contains("(ir_f64_class b) IRF64Class.zero_"));
    assert!(SRC_IR_F64_ADD_ZERO_ZERO.contains(
        ": @Eq (IROption Nat) (ir_f64_add a b) (@IROption.some Nat (ir_f64_pack (Bool.and \
         (ir_f64_is_neg a) (ir_f64_is_neg b)) Nat.zero))"
    ));
    // The XOR is MULTIPLICATION's rule: it agrees with addition's on three
    // of the four zero pairs and differs on (-0) + (-0).
    assert!(!SRC_IR_F64_ADD_ZERO_ZERO.contains("ir_f64_xsign"));
    // …and the witness discharges both class premises by computation.
    let refls = SRC_W_SIGNED_ZERO_SUM.matches("Eq.refl IRF64Class IRF64Class.zero_");
    assert_eq!(refls.count(), 2);
}

/// **The answering witnesses, re-derived from the HARDWARE.**
///
/// Every expected bit pattern below is computed by `f64` itself rather than
/// by reading IEEE 754 a second time. A table whose arms were in the wrong
/// order, or a rounding mode that resolved ties the other way, type-checks
/// exactly as well and fails here.
#[test]
fn test_the_answering_witnesses_agree_with_real_f64() {
    for (src, a, b) in [
        (
            SRC_W_ONE_PLUS_TWO,
            4607182418800017408u64,
            4611686018427387904u64,
        ),
        (SRC_W_TWO_PLUS_ONE, 4611686018427387904, 4607182418800017408),
        (
            SRC_W_EXACT_ZERO_SUM,
            4607182418800017408,
            13830554455654793216,
        ),
        (SRC_W_OVERFLOW, 9218868437227405311, 9218868437227405311),
        (SRC_W_INF_PLUS_INF, 9218868437227405312, 9218868437227405312),
        (SRC_W_MINUS_ZEROS, 9223372036854775808, 9223372036854775808),
        (SRC_W_MIXED_ZEROS, 9223372036854775808, 0),
        (SRC_W_ZERO_PLUS_FIN, 0, 4607182418800017408),
        (
            SRC_W_FIN_PLUS_MZERO,
            4607182418800017408,
            9223372036854775808,
        ),
    ] {
        let expected = (f64::from_bits(a) + f64::from_bits(b)).to_bits();
        assert!(
            src.contains(&format!(
                "(IROutcome.ret (ir_vl1 (IRScalar.float_ {expected})))"
            )),
            "the hardware answers {expected} for {a} + {b}; the registered witness says \
             something else: {src}"
        );
        assert!(src.contains("ir_eval ir_d2 ir_fa_module"));
        assert!(src.contains(&format!("(IRScalar.float_ {a}) (IRScalar.float_ {b})")));
    }
}

/// The refusing witnesses are TAGGED refusals and never values; the two
/// answering contrasts are values. Together: the refusal set of this
/// operator is the two shapes the module doc names, and finite/finite is
/// not one of them.
#[test]
fn test_the_refusing_witnesses_are_tagged_refusals() {
    for src in [SRC_W_OPPOSITE_INF, SRC_W_NAN] {
        assert!(src.contains("ir_eval ir_d2 ir_fa_module"));
        assert!(src.contains("IROutcome.unmodelled IRFault.float_domain"));
        assert!(!src.contains("IROutcome.ret"));
    }
    assert!(SRC_W_ONE_PLUS_TWO.contains("IROutcome.ret"));
    // …and the float lane is measurably not the integer lane.
    assert!(SRC_W_WRAP_CONTRAST.contains("IRBinOp.add"));
    assert!(SRC_W_WRAP_CONTRAST.contains("IRStepResult.value (IRScalar.int_ 0)"));
    assert!(SRC_W_OVERFLOW.contains("IRScalar.float_ 9218868437227405312"));
    assert!(SRC_W_F32.contains("IRTy.float_ 32") && SRC_W_F32.contains("ir_float_fault"));
}

#[test]
fn test_sources_balanced_ascii() {
    assert_eq!(
        ALL.len() + ir_fa_module_defs().len(),
        38,
        "every registered source must be checked here"
    );
    for src in ALL.iter().chain(ir_fa_module_defs()) {
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
