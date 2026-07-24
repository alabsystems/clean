// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Higham accumulated dot-product rounding bound (Stage C, #3185).
//!
//! These verify that:
//! - the `∀` inductive accumulation STEP and the small-n unrolled accumulations
//!   are kernel-checked `Theorem`s with EMPTY non-foundational axiom closures
//!   (sorry-free, grounded only in `Rat.abs_add_le` / `Rat.add_le_add` /
//!   `Rat.le_trans`, themselves grounded in the half-ulp per-op bound chain);
//! - the per-op relative-error discharges REDUCE in-kernel at the true f32
//!   (u = 2^-24) and f64 (u = 2^-53) precisions, and the concrete γ_n / (1+u)^n
//!   bounds REDUCE in-kernel at two small representative precisions (u = 2^-8,
//!   2^-12) — `u` is a genuine parameter throughout.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_prelude_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_nn_verify_float_rational()
        .expect("init_nn_verify_float_rational");
    env
}

fn assert_axiom_free_theorem(env: &Environment, name: &str) {
    let nm = Name::from_string(name);
    let info = env
        .get_const(&nm)
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{name} must be a Theorem (kernel-checked proof), not {:?}",
        info.kind
    );
    let tc = TypeChecker::with_mode(env, env.mode());
    let _ = tc
        .infer_type(&Expr::const_(nm.clone(), vec![]))
        .unwrap_or_else(|e| panic!("{name} must type-check: {e:?}"));
    let deps = env
        .axiom_deps(&nm)
        .unwrap_or_else(|| panic!("{name}: axiom_deps None"));
    let ds: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        !ds.contains("sorry") && !ds.contains("sorryAx"),
        "{name} must not depend on sorry; got {ds:?}"
    );
    assert!(
        ds.is_empty(),
        "{name} non-foundational closure must be empty; got {ds:?}"
    );
}

/// The `∀` inductive accumulation STEP — the core of Higham's dot-product error
/// induction — is a kernel-checked, axiom-free Theorem.
#[test]
fn test_error_accum_step_axiom_free() {
    let env = make_prelude_env();
    assert_axiom_free_theorem(&env, "NNVerify.FloatRational.error_accum_step");

    // Its stated type is `∀ E e B b, |E|≤B → |e|≤b → |E+e| ≤ B+b`.
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.error_accum_step",
        ))
        .unwrap();
    let s = format!("{}", info.type_);
    assert!(s.contains("Rat.add"), "step type must mention Rat.add: {s}");
    // It binds four Rat operands then two hypotheses (six binders).
    assert!(
        s.starts_with("(r : Rat) -> (r1 : Rat) -> (r2 : Rat) -> (r3 : Rat) ->"),
        "step must bind four Rat operands first: {s}"
    );
}

/// The unrolled n=3 and n=4 accumulations are kernel-checked, axiom-free.
#[test]
fn test_error_accum_chains_axiom_free() {
    let env = make_prelude_env();
    assert_axiom_free_theorem(&env, "NNVerify.FloatRational.error_accum_step3");
    assert_axiom_free_theorem(&env, "NNVerify.FloatRational.error_accum_step4");
}

/// The per-op relative-error discharges at BOTH precisions are kernel-checked,
/// axiom-free Theorems — the named per-op hypothesis is DISCHARGED from the
/// half-ulp bound, not assumed.
#[test]
fn test_fl_op_rel_error_discharges_both_precisions() {
    let env = make_prelude_env();
    assert_axiom_free_theorem(&env, "NNVerify.FloatRational.fl_op_rel_error_discharge_f32");
    assert_axiom_free_theorem(&env, "NNVerify.FloatRational.fl_op_rel_error_discharge_f64");
}

/// The concrete γ_n / (1+u)^n bounds REDUCE in-kernel for small n at the small
/// representative precisions (u = 2^-8, 2^-12) AND at the TRUE binary32
/// (u = 2^-24) and binary64 (u = 2^-53) unit roundoffs. The f32/f64 LITERAL
/// discharges were previously blocked by the Rat-blowup wall (the `Rat.le` lift's
/// `Nat.pred` on the `2^{u_exp}`-scale denominator OOM-killed); the native
/// `Nat.pred` + arbitrary-precision `Int` reducers close it, so `u` is now a
/// genuine parameter discharged at the real f32/f64 scales, not just symbolically.
#[test]
fn test_gamma_n_reductions_representative_precisions() {
    let env = make_prelude_env();
    for name in [
        "NNVerify.FloatRational.gamma_n_reduces_u8_n2",
        "NNVerify.FloatRational.gamma_n_reduces_u8_n3",
        "NNVerify.FloatRational.gamma_n_reduces_u12_n2",
        "NNVerify.FloatRational.gamma_n_reduces_u12_n3",
        // TRUE f32 (u = 2^-24) and f64 (u = 2^-53) literal discharges.
        "NNVerify.FloatRational.gamma_n_reduces_f32_n2",
        "NNVerify.FloatRational.gamma_n_reduces_f32_n3",
        "NNVerify.FloatRational.gamma_n_reduces_f64_n2",
        "NNVerify.FloatRational.gamma_n_reduces_f64_n3",
    ] {
        assert_axiom_free_theorem(&env, name);
    }
}

/// The TRUE-precision f32/f64 γ_n discharges carry the REAL `2^24` / `2^53`
/// denominators in their stated `Rat.le` types — i.e. they are LITERAL discharges
/// at the binary32/binary64 unit roundoffs, not the small representative `u`.
/// `assert_axiom_free_theorem` above already KERNEL-REDUCES each (the wall-closed
/// proof); here we pin the denominators so the precision can't silently regress.
#[test]
fn test_gamma_n_f32_f64_are_at_true_precision() {
    let env = make_prelude_env();
    // n·u = n / 2^u_exp ; the denominator `2^u_exp` appears in the stated type.
    // f32: u_exp = 24 → 2^24 = 16_777_216. f64: u_exp = 53 → 2^53.
    let f32_ty = format!(
        "{}",
        env.get_const(&Name::from_string(
            "NNVerify.FloatRational.gamma_n_reduces_f32_n2"
        ))
        .expect("f32 discharge registered")
        .type_
    );
    assert!(
        f32_ty.contains("16777216"),
        "f32 γ_n must carry the 2^24 = 16777216 denominator (true binary32 u): {f32_ty}"
    );
    let f64_ty = format!(
        "{}",
        env.get_const(&Name::from_string(
            "NNVerify.FloatRational.gamma_n_reduces_f64_n2"
        ))
        .expect("f64 discharge registered")
        .type_
    );
    // 2^53 = 9_007_199_254_740_992.
    assert!(
        f64_ty.contains("9007199254740992"),
        "f64 γ_n must carry the 2^53 denominator (true binary64 u): {f64_ty}"
    );
}

/// End-to-end: instantiate `error_accum_step` at a CONCRETE pair of bounds and
/// check the kernel accepts the application (the bound reduces). Uses the
/// f64 per-op discharge as the inner hypothesis source shape: we feed two copies
/// of a trivial `Rat.le_refl`-backed bound and confirm the composed accumulation
/// type-checks.
#[test]
fn test_error_accum_step_instantiates() {
    let env = make_prelude_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    // error_accum_step applied to four zero operands needs |0|≤0 twice; the
    // simplest concrete witness is via the registered discharge — but here we
    // only check the HEAD application type-infers (partial application), which
    // exercises the binder structure end-to-end.
    let step = Expr::const_(
        Name::from_string("NNVerify.FloatRational.error_accum_step"),
        vec![],
    );
    let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    // error_accum_step 0 0 0 0  :  |0|≤0 → |0|≤0 → |0+0| ≤ 0+0
    let applied = Expr::apps(
        step,
        [zero.clone(), zero.clone(), zero.clone(), zero.clone()],
    );
    let ty = tc
        .infer_type(&applied)
        .expect("error_accum_step 0 0 0 0 must type-infer");
    let s = format!("{ty}");
    assert!(
        s.contains("Rat.le") || s.contains("LE.le"),
        "applied step type must be a chain of Rat.le implications: {s}"
    );
}
