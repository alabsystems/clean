// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Fourier analysis on Boolean hypercube declarations.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_fourier_boolean().expect("init_fourier_boolean");
    env
}

// =========================================================================
// Definition registration tests
// =========================================================================

#[test]
fn test_fourier_coefficient_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoolAnalysis.FourierCoefficient"))
        .is_some());
}

#[test]
fn test_fourier_spectrum_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoolAnalysis.FourierSpectrum"))
        .is_some());
}

#[test]
fn test_fourier_weight_at_level_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoolAnalysis.FourierWeightAtLevel"))
        .is_some());
}

// =========================================================================
// Theorem registration tests
// =========================================================================

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "BoolAnalysis.noise_stability_fourier_helper",
        "BoolAnalysis.noise_stability_fourier",
        "BoolAnalysis.fourier_weight_parseval_helper",
        "BoolAnalysis.fourier_weight_parseval",
        "BoolAnalysis.friedgut_boolean_helper",
        "BoolAnalysis.friedgut_boolean",
        "BoolAnalysis.fourier_coefficient_transform_helper",
        "BoolAnalysis.fourier_coefficient_transform",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

// =========================================================================
// Type-checking tests
// =========================================================================

#[test]
fn test_fourier_coefficient_type_checks() {
    let env = make_env();
    let fc = Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fc)
        .expect("infer BoolAnalysis.FourierCoefficient type");
    // Should be Pi (n : Nat), Pi (f : BoolFn n), Pi (S : HCPoint n), Rat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fourier_weight_at_level_type_checks() {
    let env = make_env();
    let fw = Expr::const_(
        Name::from_string("BoolAnalysis.FourierWeightAtLevel"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fw)
        .expect("infer BoolAnalysis.FourierWeightAtLevel type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_noise_stability_fourier_type_checks() {
    let env = make_env();
    let nsf = Expr::const_(
        Name::from_string("BoolAnalysis.noise_stability_fourier"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&nsf)
        .expect("infer BoolAnalysis.noise_stability_fourier type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_friedgut_boolean_type_checks() {
    let env = make_env();
    let fb = Expr::const_(Name::from_string("BoolAnalysis.friedgut_boolean"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fb)
        .expect("infer BoolAnalysis.friedgut_boolean type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// =========================================================================
// Idempotency test
// =========================================================================

#[test]
fn test_fourier_boolean_idempotent() {
    let mut env = Environment::new();
    env.init_fourier_boolean().expect("first init");
    env.init_fourier_boolean().expect("second init");
}

// =========================================================================
// Naming convention test
// =========================================================================

#[test]
fn test_fourier_boolean_naming_convention() {
    let env = make_env();
    for name in [
        "BoolAnalysis.FourierCoefficient",
        "BoolAnalysis.FourierSpectrum",
        "BoolAnalysis.FourierWeightAtLevel",
        "BoolAnalysis.noise_stability_fourier",
        "BoolAnalysis.fourier_weight_parseval",
        "BoolAnalysis.friedgut_boolean",
        "BoolAnalysis.fourier_coefficient_transform",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with BoolAnalysis. prefix"
        );
    }
}

// =========================================================================
// No overlap with boolean_analysis.rs declarations
// =========================================================================

#[test]
fn test_no_overlap_with_existing_boolean_analysis() {
    let env = make_env();
    // These are the NEW declarations from fourier_boolean -- verify they exist
    let new_names = [
        "BoolAnalysis.FourierCoefficient",
        "BoolAnalysis.FourierSpectrum",
        "BoolAnalysis.FourierWeightAtLevel",
        "BoolAnalysis.noise_stability_fourier",
        "BoolAnalysis.fourier_weight_parseval",
        "BoolAnalysis.friedgut_boolean",
        "BoolAnalysis.fourier_coefficient_transform",
    ];
    for name in new_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "new declaration {name} missing"
        );
    }

    // These are the EXISTING declarations from boolean_analysis.rs -- verify
    // they still exist (init_fourier_boolean calls init_boolean_analysis)
    let existing_names = [
        "BoolAnalysis.BoolFn",
        "BoolAnalysis.FourierCoeff",
        "BoolAnalysis.Influence",
        "BoolAnalysis.TotalInfluence",
        "BoolAnalysis.Variance",
        "BoolAnalysis.FourierTransform",
        "BoolAnalysis.parseval_identity",
        "BoolAnalysis.influence_fourier",
        "BoolAnalysis.total_influence_identity",
        "BoolAnalysis.bonami_beckner",
        "BoolAnalysis.kkl_inequality",
    ];
    for name in existing_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "existing declaration {name} should still be present"
        );
    }
}

// =========================================================================
// Boolean analysis dependency chain test
// =========================================================================

#[test]
fn test_fourier_boolean_initializes_boolean_analysis() {
    let mut env = Environment::new();
    // Only call init_fourier_boolean -- it should pull in boolean_analysis
    env.init_fourier_boolean()
        .expect("init_fourier_boolean should init boolean_analysis as dependency");
    assert!(env
        .get_const(&Name::from_string("BoolAnalysis.BoolFn"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("BoolAnalysis.parseval_identity"))
        .is_some());
}

// =========================================================================
// TCB-shrink Tier-0: FourierSpectrum DEFINED as FourierTransform
// =========================================================================

/// `BoolAnalysis.FourierSpectrum` is a genuine `Declaration::Definition`
/// (NOT an Axiom): the spectrum IS the Fourier transform. Pins the discharge.
#[test]
fn test_fourier_spectrum_is_definition_not_axiom() {
    use crate::env::types::ConstantKind;
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("BoolAnalysis.FourierSpectrum"))
        .expect("FourierSpectrum should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "FourierSpectrum must be DEFINED (= FourierTransform), not admitted as an axiom"
    );
    assert!(info.value.is_some(), "FourierSpectrum must retain its body");
}

/// The `FourierSpectrum` definition type-checks: `infer_type(value)` is def-eq
/// to the declared `(n) → (f : BoolFn n) → FourierCoeff n` type. This is the
/// same independent re-verification C1 of the soundness certificate performs.
#[test]
fn test_fourier_spectrum_definition_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("BoolAnalysis.FourierSpectrum"))
        .expect("FourierSpectrum registered");
    let value = info.value.clone().expect("FourierSpectrum has a value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&value, &info.type_)
        .expect("FourierSpectrum body must check against its declared type");
}

/// Definitional-correctness pin: the η-expanded `fun n f => FourierSpectrum n f`
/// is def-eq to `fun n f => FourierTransform n f` — i.e. the body is exactly the
/// transform (unfolds to it), not merely a same-typed shell.
#[test]
fn test_fourier_spectrum_equals_fourier_transform() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_fn = Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]);
    let spectrum = Expr::const_(Name::from_string("BoolAnalysis.FourierSpectrum"), vec![]);
    let transform = Expr::const_(Name::from_string("BoolAnalysis.FourierTransform"), vec![]);

    // Build `fun (n : Nat) (f : BoolFn n) => HEAD n f` for each head, fully
    // closed (no dangling fvars), then compare for definitional equality.
    let mk_eta = |head: &Expr| -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let body = Expr::apps(head.clone(), [n.clone(), f.clone()]);
        let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), body);
        let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
        b.finish(lam)
    };
    let lhs = mk_eta(&spectrum);
    let rhs = mk_eta(&transform);
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "fun n f => FourierSpectrum n f must be def-eq to fun n f => FourierTransform n f"
    );
}

// =========================================================================
// Stage-2: FourierWeightAtLevel DEFINED as Σ_{|S|=k} f̂(S)²
// =========================================================================

fn k_const(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}

fn nat_lit(n: u64) -> Expr {
    let mut e = k_const("Nat.zero");
    for _ in 0..n {
        e = Expr::app(k_const("Nat.succ"), e);
    }
    e
}

fn fin_mk(m: Expr, val: Expr) -> Expr {
    Expr::apps(k_const("Fin.mk"), [m, val, k_const("True")])
}

/// `FourierWeightAtLevel` is a genuine `Declaration::Definition` whose body
/// type-checks against `(n) → (f : BoolFn n) → (k : Nat) → Rat` (the same
/// independent re-verification C1 performs).
#[test]
fn test_fourier_weight_at_level_is_definition() {
    use crate::env::types::ConstantKind;
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("BoolAnalysis.FourierWeightAtLevel"))
        .expect("FourierWeightAtLevel registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "FourierWeightAtLevel must be DEFINED (Σ over |S|=k of f̂(S)²), not admitted"
    );
    let value = info.value.clone().expect("has body");
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&value, &info.type_)
        .expect("FourierWeightAtLevel body must check against its declared type");
}

/// The level-restriction machinery reduces correctly: the popcount of a decoded
/// subset is the number of set bits. With `n = 2`, `j = ⟨3⟩` (binary `11`), the
/// decoded indicator `S = hcDecode 2 ⟨3⟩` has both coordinates true, so
/// `Fin.sumNat 2 (fun i => indNat (S i))` ground-reduces to `2` — the popcount
/// `|S|` that the weight's `Nat.beq |S| k` gate compares against `k`.
#[test]
fn test_fourier_weight_popcount_reduces() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let n = nat_lit(2);
    // S = hcDecode 2 ⟨3⟩ : HCPoint 2  (bits 11 ⇒ both coords true).
    let s = Expr::apps(
        k_const("BoolAnalysis.hcDecode"),
        [n.clone(), fin_mk(nat_lit(4), nat_lit(3))],
    );
    // popcount = Fin.sumNat 2 (fun i => @Bool.rec (fun _=>Nat) 0 1 (S i))
    let popcount = {
        let mut b = EnvDeclBuilder::new();
        let fin_n = Expr::app(k_const("Fin"), n.clone());
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let s_i = Expr::app(s.clone(), i);
        let nat_motive = Expr::lam(BinderInfo::Default, k_const("Bool"), k_const("Nat"));
        let ind_nat = Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![crate::level::Level::succ(crate::level::Level::zero())],
            ),
            [nat_motive, nat_lit(0), nat_lit(1), s_i],
        );
        let count_fn = b.mk_lam(i_id, BinderInfo::Default, fin_n, ind_nat);
        b.finish(Expr::apps(k_const("Fin.sumNat"), [n.clone(), count_fn]))
    };
    assert!(
        tc.is_def_eq(&popcount, &nat_lit(2)),
        "popcount of hcDecode 2 ⟨3⟩ (bits 11) must reduce to 2"
    );
    // Discriminator: it is NOT 1 (a single bit) — the sum genuinely counts both.
    assert!(
        !tc.is_def_eq(&popcount, &nat_lit(1)),
        "popcount must count BOTH set bits (got 1)"
    );
}

/// Definitional-correctness pin: `fun n f k => FourierWeightAtLevel n f k` is
/// def-eq to the explicit `Σ_{j<2^n} ind(|hcDecode n j| = k) · f̂(hcDecode n j)²`
/// formula — the body is exactly the level-gated sum of squared coefficients,
/// not a same-typed shell.
#[test]
fn test_fourier_weight_equals_gated_sum_formula() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let nat = k_const("Nat");
    let bool_fn = k_const("BoolAnalysis.BoolFn");
    let weight = k_const("BoolAnalysis.FourierWeightAtLevel");

    // lhs: fun n f k => FourierWeightAtLevel n f k
    let lhs = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let (k_id, kk) = b.fresh_local(nat.clone());
        let body = Expr::apps(weight.clone(), [n.clone(), f.clone(), kk.clone()]);
        let lam = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body);
        let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), lam);
        let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
        b.finish(lam)
    };

    // rhs: the explicit gated-sum formula (mirrors register_fourier_weight_at_level).
    let rhs = {
        let two = Expr::app(
            k_const("Nat.succ"),
            Expr::app(k_const("Nat.succ"), k_const("Nat.zero")),
        );
        let pow2 = |n: &Expr| Expr::apps(k_const("Nat.pow"), [two.clone(), n.clone()]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );
        let nat_motive = Expr::lam(BinderInfo::Default, k_const("Bool"), k_const("Nat"));

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let (k_id, kk) = b.fresh_local(nat.clone());

        let summand = {
            let fin_pow = Expr::app(k_const("Fin"), pow2(&n));
            let (j_id, j) = b.fresh_local(fin_pow.clone());
            let s = Expr::apps(k_const("BoolAnalysis.hcDecode"), [n.clone(), j]);
            let popcount = {
                let fin_n = Expr::app(k_const("Fin"), n.clone());
                let (i_id, i) = b.fresh_local(fin_n.clone());
                let s_i = Expr::app(s.clone(), i);
                let ind_nat = Expr::apps(
                    bool_rec.clone(),
                    [nat_motive.clone(), nat_lit(0), nat_lit(1), s_i],
                );
                let cf = b.mk_lam(i_id, BinderInfo::Default, fin_n, ind_nat);
                Expr::apps(k_const("Fin.sumNat"), [n.clone(), cf])
            };
            let same = Expr::apps(k_const("Nat.beq"), [popcount, kk.clone()]);
            let gate = Expr::app(k_const("BoolAnalysis.ind"), same);
            let coeff = Expr::apps(
                k_const("BoolAnalysis.FourierCoefficient"),
                [n.clone(), f.clone(), s],
            );
            let coeff_sq = Expr::apps(k_const("Rat.mul"), [coeff.clone(), coeff]);
            let term = Expr::apps(k_const("Rat.mul"), [gate, coeff_sq]);
            b.mk_lam(j_id, BinderInfo::Default, fin_pow, term)
        };
        let body = Expr::apps(k_const("Fin.sum"), [pow2(&n), summand]);
        let lam = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body);
        let lam = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n.clone(), lam);
        let lam = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), lam);
        b.finish(lam)
    };
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "FourierWeightAtLevel must be def-eq to the explicit Σ over |S|=k of f̂(S)² formula"
    );
}
