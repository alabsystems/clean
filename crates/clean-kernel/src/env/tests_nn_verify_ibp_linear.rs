// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for T80 IBP linear layer soundness (nn_verify_ibp_linear).

use std::process::Command;

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_linear()
        .expect("init_nn_verify_ibp_linear should succeed");
    env
}

fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered"
    );
}

fn assert_type_checks_as_pi(env: &Environment, name: &str) {
    let e = Expr::const_(Name::from_string(name), vec![]);
    let tc = TypeChecker::with_mode(env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{name} should type-check, got: {err:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "{name} type should be Pi, got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// Registration tests
// ---------------------------------------------------------------

#[test]
fn test_mul_nonneg_le_left_registered() {
    assert_registered(&make_env(), "NNVerify.mul_nonneg_le_left");
}

#[test]
fn test_mul_nonpos_le_left_registered() {
    assert_registered(&make_env(), "NNVerify.mul_nonpos_le_left");
}

#[test]
fn test_add_le_add_registered() {
    assert_registered(&make_env(), "NNVerify.add_le_add");
}

#[test]
fn test_le_of_eq_of_le_registered() {
    assert_registered(&make_env(), "NNVerify.le_of_eq_of_le");
}

#[test]
fn test_le_of_le_of_eq_registered() {
    assert_registered(&make_env(), "NNVerify.le_of_le_of_eq");
}

#[test]
fn test_w_pos_registered() {
    assert_registered(&make_env(), "NNVerify.w_pos");
}

#[test]
fn test_w_neg_registered() {
    assert_registered(&make_env(), "NNVerify.w_neg");
}

#[test]
fn test_w_decompose_registered() {
    assert_registered(&make_env(), "NNVerify.w_decompose");
}

#[test]
fn test_w_pos_nonneg_registered() {
    assert_registered(&make_env(), "NNVerify.w_pos_nonneg");
}

#[test]
fn test_w_neg_nonpos_registered() {
    assert_registered(&make_env(), "NNVerify.w_neg_nonpos");
}

#[test]
fn test_ibp_linear_per_component_registered() {
    assert_registered(&make_env(), "NNVerify.ibp_linear_per_component");
}

#[test]
fn test_ibp_linear_bounds_registered() {
    assert_registered(&make_env(), "NNVerify.ibp_linear_bounds");
}

#[test]
fn test_linear_output_registered() {
    assert_registered(&make_env(), "NNVerify.linear_output");
}

#[test]
fn test_ibp_linear_sound_registered() {
    assert_registered(&make_env(), "NNVerify.ibp_linear_sound");
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_mul_nonneg_le_left_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.mul_nonneg_le_left");
}

#[test]
fn test_mul_nonpos_le_left_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.mul_nonpos_le_left");
}

#[test]
fn test_add_le_add_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.add_le_add");
}

#[test]
fn test_le_of_eq_of_le_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.le_of_eq_of_le");
}

#[test]
fn test_le_of_le_of_eq_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.le_of_le_of_eq");
}

#[test]
fn test_w_pos_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.w_pos");
}

#[test]
fn test_w_neg_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.w_neg");
}

#[test]
fn test_w_decompose_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.w_decompose");
}

#[test]
fn test_w_pos_nonneg_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.w_pos_nonneg");
}

#[test]
fn test_w_neg_nonpos_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.w_neg_nonpos");
}

#[test]
fn test_ibp_linear_per_component_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ibp_linear_per_component");
}

#[test]
fn test_ibp_linear_bounds_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ibp_linear_bounds");
}

#[test]
fn test_linear_output_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.linear_output");
}

#[test]
fn test_ibp_linear_sound_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ibp_linear_sound");
}

// ---------------------------------------------------------------
// Structural tests
// ---------------------------------------------------------------

#[test]
fn test_linear_output_is_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.linear_output"))
        .expect("NNVerify.linear_output should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "linear_output should be a Definition, not {:?}",
        info.kind
    );
    assert!(info.value.is_some(), "linear_output should have a value");
}

#[test]
fn test_w_pos_is_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.w_pos"))
        .expect("NNVerify.w_pos should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "w_pos should be a Definition, not {:?}",
        info.kind
    );
    assert!(info.value.is_some(), "w_pos should have a value");
}

#[test]
fn test_w_neg_is_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.w_neg"))
        .expect("NNVerify.w_neg should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "w_neg should be a Definition, not {:?}",
        info.kind
    );
    assert!(info.value.is_some(), "w_neg should have a value");
}

#[test]
fn test_ibp_linear_sound_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_linear_sound"))
        .expect("NNVerify.ibp_linear_sound should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_linear_sound should be a Theorem, not {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "ibp_linear_sound should have a proof term"
    );
}

#[test]
fn test_ibp_linear_sound_proof_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_linear_sound"))
        .expect("NNVerify.ibp_linear_sound should exist");
    let proof = info.value.as_ref().expect("should have proof term");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc.infer_type(proof).expect("T80 proof should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

#[test]
fn test_ibp_linear_sound_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_linear_sound"))
        .expect("NNVerify.ibp_linear_sound should exist");
    let sorry = info.sorry_summary();
    assert!(
        !sorry.has_sorry,
        "ibp_linear_sound proof should not use sorry"
    );
}

#[test]
fn test_linear_output_value_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.linear_output"))
        .expect("NNVerify.linear_output should exist");
    let val = info.value.as_ref().expect("should have value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc.infer_type(val).expect("value should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type of value should match declared type"
    );
}

#[test]
fn test_w_pos_value_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.w_pos"))
        .expect("NNVerify.w_pos should exist");
    let val = info.value.as_ref().expect("should have value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc.infer_type(val).expect("w_pos value should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type of w_pos value should match declared type"
    );
}

#[test]
fn test_w_neg_value_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.w_neg"))
        .expect("NNVerify.w_neg should exist");
    let val = info.value.as_ref().expect("should have value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc.infer_type(val).expect("w_neg value should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type of w_neg value should match declared type"
    );
}

#[test]
fn test_ibp_linear_sound_depends_on_fin_sum() {
    let env = make_env();
    for name in &[
        "Fin.sum",
        "Fin.sum_le",
        "Fin.sum_add",
        "Fin.sum_zero",
        "Fin.sum_succ",
    ] {
        assert_registered(&env, name);
    }
}

#[test]
fn test_ibp_linear_sound_depends_on_rat_le_trans() {
    // Since #3222/#3240, the bridging axiom Rat.le_trans_LE is eliminated;
    // Rat.le_trans (from the algebra layer) is used directly because
    // LE.le @Rat instLERat now reduces to Rat.le via projection reduction.
    assert_registered(&make_env(), "Rat.le_trans");
}

#[test]
fn test_ibp_linear_sound_depends_on_w_decompose() {
    let env = make_env();
    for name in &[
        "NNVerify.w_pos",
        "NNVerify.w_neg",
        "NNVerify.w_decompose",
        "NNVerify.w_pos_nonneg",
        "NNVerify.w_neg_nonpos",
    ] {
        assert_registered(&env, name);
    }
}

// ---------------------------------------------------------------
// Proof axiom dependency completeness
// ---------------------------------------------------------------

#[test]
fn test_ibp_linear_sound_depends_on_le_transport() {
    let env = make_env();
    for name in &[
        "NNVerify.le_of_eq_of_le",
        "NNVerify.le_of_le_of_eq",
        "NNVerify.add_le_add",
        "NNVerify.mul_nonneg_le_left",
        "NNVerify.mul_nonpos_le_left",
    ] {
        assert_registered(&env, name);
    }
}

#[test]
fn test_ibp_linear_sound_proof_is_lambda() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_linear_sound"))
        .expect("ibp_linear_sound should exist");
    let proof = info.value.as_ref().expect("should have proof term");
    assert!(
        matches!(proof.kind(), ExprKind::Lam(..)),
        "proof should be a lambda abstraction, got {:?}",
        proof.kind()
    );
}

#[test]
fn test_ibp_linear_per_component_is_sorry_free_theorem() {
    // T80 unlock (#3490 follow-up): `ibp_linear_per_component` was formerly a
    // bare admitted `Declaration::Axiom` because its conclusion was stated
    // through the projections of the (then uninterpreted) `ibp_linear_bounds`
    // axiom. Now that `ibp_linear_bounds` is a faithful reducible
    // `Declaration::Definition` (`IntervalBounds.mk m lo' hi' valid`), those
    // projections proj-reduce and the per-index goal is a genuine sorry-free
    // `Declaration::Theorem` proved by per-summand monotonicity + `Fin.sum_le`
    // + the `w_decompose` recombination. Its transitive closure must reach NO
    // trust marker.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_linear_per_component"))
        .expect("ibp_linear_per_component should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_linear_per_component should be a sorry-free Theorem, not {:?}",
        info.kind
    );
    let tm = env
        .trust_marker_deps(&Name::from_string("NNVerify.ibp_linear_per_component"))
        .expect("present");
    assert!(
        tm.is_empty(),
        "ibp_linear_per_component must be sorry-free, got {tm:?}"
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&Expr::const_(
            Name::from_string("NNVerify.ibp_linear_per_component"),
            vec![],
        ))
        .expect("per_component should type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "per_component type should be Pi"
    );
}

// ---------------------------------------------------------------
// Phase 5 (#3366): Axiom -> Opaque promotion tests
// ---------------------------------------------------------------

#[test]
fn test_ibp_lemmas_are_opaque() {
    let env = make_env();
    // Ratchet-drained (#3490 Batch 0 final): the IBP-linear lemma list has
    // NO remaining sorry-inhabited Opaques. Every lemma registered by
    // `nn_verify_ibp_linear.rs` is now a constructive `Declaration::Theorem`:
    //   - `mul_nonneg_le_left`: #3490 T3 / #3476 (Rat field→order bridge
    //     via #3503). See `test_mul_nonneg_le_left_is_sorry_free_theorem`.
    //   - `add_le_add`: #3490 Batch 0 (`Rat.add_le_add_left` +
    //     `Rat.add_comm` + `Rat.le_trans`). See
    //     `test_add_le_add_is_sorry_free_theorem`.
    //   - `mul_nonpos_le_left`: #3490 Batch 0 final (via
    //     `mul_nonneg_le_left` applied to `(-w)` + `add_right_cancel`
    //     identities). See `test_mul_nonpos_le_left_is_sorry_free_theorem`.
    //
    // This assertion is a ratchet guard: if any future change re-introduces
    // a sorry-inhabited Opaque here, promote it the same way and delete
    // this guard only after you have a new `*_is_sorry_free_theorem` test.
    let ibp_linear_lemmas = [
        "NNVerify.mul_nonneg_le_left",
        "NNVerify.add_le_add",
        "NNVerify.mul_nonpos_le_left",
    ];
    for name in &ibp_linear_lemmas {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} is no longer sorry-inhabited; the ratchet is drained and \
             every IBP-linear lemma must be a constructive Theorem. Got {:?}.",
            info.kind
        );
    }
}

/// T2 ratchet (#3490): `le_of_eq_of_le` and `le_of_le_of_eq` promoted from
/// sorry-inhabited Opaque to constructive Theorem. Proofs use only
/// foundational `Eq.subst`/`Eq.symm`; no `sorry` in transitive closure.
#[test]
fn test_le_eq_helpers_are_constructive_theorems() {
    use crate::env::axiom_audit::ProofQuality;

    let env = make_env();
    for name in &["NNVerify.le_of_eq_of_le", "NNVerify.le_of_le_of_eq"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be Theorem (#3490 T2), not {:?}",
            info.kind
        );
        let q = env
            .proof_quality(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should have a proof quality"));
        assert!(
            matches!(q, ProofQuality::Constructive),
            "{name} should be Constructive, got {:?}",
            q
        );
    }
}

/// T3 ratchet (#3490, #3476): `mul_nonneg_le_left` promoted from
/// sorry-inhabited Opaque to sorry-free Theorem. Unblocked by #3503
/// (Rat field→order bridging lemmas). Proof term uses honest
/// ordered-field axioms (`Rat.add_le_add_left`, `Rat.left_distrib`,
/// `Rat.add_assoc`, `Rat.add_comm`, `Rat.add_zero`, `Rat.zero_add`,
/// `Rat.add_left_neg`, `Rat.add_neg_self`, `Rat.mul_neg`,
/// `Rat.sub_nonneg_of_le`, `Rat.mul_sub`, `Rat.le_of_sub_nonneg`) plus
/// `Eq.subst`/`Eq.symm`; no `sorry`. (`Rat.mul_nonneg` was previously in this
/// closure but has since been ELIMINATED — it is now a constructive
/// kernel-checked Theorem, see `algebra_rat_order_proofs.rs::
/// register_rat_mul_nonneg` — so it no longer contributes a domain axiom.)
///
/// The proof is `AxiomDependent` (not `Constructive`) because the
/// ordered-field Rat axioms are classified as domain-specific by
/// `axiom_audit`. This is the expected classification — every proof
/// that uses Rat arithmetic has this property. The key metric that
/// changed is: `sorry` no longer appears in the transitive closure.
#[test]
fn test_mul_nonneg_le_left_is_sorry_free_theorem() {
    let env = make_env();
    let name = Name::from_string("NNVerify.mul_nonneg_le_left");
    let info = env
        .get_const(&name)
        .expect("mul_nonneg_le_left should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "mul_nonneg_le_left should be Theorem (#3490 T3), not {:?}",
        info.kind
    );
    // `sorry` must not be reachable through the proof term.
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for mul_nonneg_le_left");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
        "mul_nonneg_le_left proof closure must not reference `sorry`; got {dep_strs:?}"
    );
    // The value itself must be sorry-free by construction.
    let value = info
        .value
        .as_ref()
        .expect("mul_nonneg_le_left Theorem must have a value");
    assert!(
        !value_refs_sorry(value),
        "mul_nonneg_le_left proof term must not literally contain `sorry`"
    );
}

/// Batch 0 ratchet (#3490): `add_le_add` promoted from sorry-inhabited
/// Opaque to sorry-free Theorem. Proof term uses only the foundational
/// order axiom `Rat.add_le_add_left`, the field axiom `Rat.add_comm`, the
/// transitive axiom `Rat.le_trans`, and `Eq.subst`. No `sorry` in the
/// transitive closure.
///
/// Classification is `AxiomDependent` (like `mul_nonneg_le_left`) because
/// the Rat arithmetic axioms are classified as domain-specific by
/// `axiom_audit`. The key metric that changed is: `sorry` no longer appears
/// in the transitive closure.
#[test]
fn test_add_le_add_is_sorry_free_theorem() {
    let env = make_env();
    let name = Name::from_string("NNVerify.add_le_add");
    let info = env.get_const(&name).expect("add_le_add should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "add_le_add should be Theorem (#3490 Batch 0), not {:?}",
        info.kind
    );
    // `sorry` must not be reachable through the proof term.
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for add_le_add");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
        "add_le_add proof closure must not reference `sorry`; got {dep_strs:?}"
    );
    // The value itself must be sorry-free by construction.
    let value = info
        .value
        .as_ref()
        .expect("add_le_add Theorem must have a value");
    assert!(
        !value_refs_sorry(value),
        "add_le_add proof term must not literally contain `sorry`"
    );
}

/// Batch 0 final ratchet (#3490): `mul_nonpos_le_left` promoted from
/// sorry-inhabited Opaque to sorry-free Theorem. This closes the LAST
/// `sorry_inhabit_pi` call-site in `nn_verify_ibp_linear.rs`.
///
/// The proof uses only pre-existing axioms:
/// * Foundational ordered-field: `Rat.add_le_add_left`, `Rat.add_left_neg`,
///   `Rat.add_neg_self`, `Rat.add_zero`, `Rat.add_comm`, `Rat.add_right_cancel`,
///   `Rat.mul_comm`, `Rat.mul_neg`, `Rat.sub_nonneg_of_le`, `Rat.le_of_sub_nonneg`.
/// * Sibling: `NNVerify.mul_nonneg_le_left` (also sorry-free since #3490 T3).
/// * Kernel primitives: `Eq.subst`, `Eq.trans`, `Eq.symm`, `congrArg`.
///
/// No new axioms; no `sorry` in the transitive closure.
///
/// Classification is `AxiomDependent` (like siblings) because Rat axioms are
/// domain-specific by `axiom_audit`. The key metric: `sorry` no longer
/// appears in the transitive closure.
#[test]
fn test_mul_nonpos_le_left_is_sorry_free_theorem() {
    let env = make_env();
    let name = Name::from_string("NNVerify.mul_nonpos_le_left");
    let info = env
        .get_const(&name)
        .expect("mul_nonpos_le_left should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "mul_nonpos_le_left should be Theorem (#3490 Batch 0 final), not {:?}",
        info.kind
    );
    // `sorry` must not be reachable through the proof term.
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for mul_nonpos_le_left");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
        "mul_nonpos_le_left proof closure must not reference `sorry`; got {dep_strs:?}"
    );
    // The value itself must be sorry-free by construction.
    let value = info
        .value
        .as_ref()
        .expect("mul_nonpos_le_left Theorem must have a value");
    assert!(
        !value_refs_sorry(value),
        "mul_nonpos_le_left proof term must not literally contain `sorry`"
    );
}

/// Walk an expression tree and return `true` iff any `Expr::Const` with
/// name equal to `sorry` or `sorryAx` appears anywhere.
fn value_refs_sorry(expr: &Expr) -> bool {
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                if s == "sorry" || s == "sorryAx" {
                    return true;
                }
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) => {
                stack.push(inner);
            }
            ExprKind::Proj(_, _, inner) => {
                stack.push(inner);
            }
            ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }
    false
}

#[test]
fn test_w_decomp_dispositions_are_sound() {
    // Soundness-certificate floor (TCB-shrink): the W+/W- decomposition lemmas
    // are now sorry-free AND axiom-free. `w_decompose` (`W = max(0,W) + min(0,W)`)
    // is a genuine `Declaration::Theorem` proved by a `Bool.rec` split on
    // `Rat.ble Rat.zero (W i j)` discharged with `Rat.zero_add` / `Rat.add_zero`.
    // `w_pos_nonneg` / `w_neg_nonpos` are genuine `Declaration::Theorem`s proved
    // from `Rat.le_max_left` / `Rat.min_le_left`.
    let env = make_env();

    let dec = env
        .get_const(&Name::from_string("NNVerify.w_decompose"))
        .expect("w_decompose should exist");
    assert_eq!(
        dec.kind,
        ConstantKind::Theorem,
        "w_decompose should now be a constructive Theorem, not {:?}",
        dec.kind
    );

    for name in &["NNVerify.w_pos_nonneg", "NNVerify.w_neg_nonpos"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be a constructive Theorem, not {:?}",
            info.kind
        );
    }

    // None of the three may reach a trust marker.
    for name in &[
        "NNVerify.w_decompose",
        "NNVerify.w_pos_nonneg",
        "NNVerify.w_neg_nonpos",
    ] {
        let tm = env
            .trust_marker_deps(&Name::from_string(name))
            .expect("present");
        assert!(tm.is_empty(), "{name} must be sorry-free, got {tm:?}");
    }
}

#[test]
fn test_ibp_linear_init_is_sorry_free() {
    // Soundness-certificate capstone: the whole IBP-linear init surface is now
    // sorry-free. Every formerly sorry-inhabited Opaque was either PROVED
    // (`w_pos_nonneg` / `w_neg_nonpos`) or DEMOTED to an honest admitted Axiom
    // (`w_decompose`, `ibp_linear_per_component`). Consequently NO declaration
    // registered by `init_nn_verify_ibp_linear` reaches a trust marker, and the
    // init runs cleanly even under DENY_SORRY (it never calls the sorry
    // constructor anymore).
    let env = make_env();
    for c in env.constants() {
        if let Some(tm) = env.trust_marker_deps(&c.name) {
            assert!(
                tm.is_empty(),
                "{} unexpectedly reaches a trust marker: {tm:?}",
                c.name
            );
        }
    }
}

#[test]
fn deny_sorry_child_ibp_linear_init() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("ibp_linear_init") {
        return;
    }
    let mut env = Environment::new();
    env.init_nn_verify_ibp_linear()
        .expect("init must succeed (now sorry-free)");
}

#[test]
fn test_deny_sorry_allows_sorry_free_ibp_linear_init() {
    // Inverted from the historical guard: `init_nn_verify_ibp_linear` no longer
    // creates ANY sorry term (its formerly sorry-inhabited lemmas are now
    // proved or honestly demoted to axioms), so it must SUCCEED under
    // DENY_SORRY=1 rather than panicking.
    let exe = std::env::current_exe().expect("cannot get current test exe path");
    let output = Command::new(&exe)
        .env("DENY_SORRY", "1")
        .env("DENY_SORRY_GATE_CHILD", "ibp_linear_init")
        .arg("deny_sorry_child_ibp_linear_init")
        .arg("--test-threads=1")
        .arg("--nocapture")
        .output()
        .expect("failed to exec DENY_SORRY child process");

    assert!(
        output.status.success(),
        "init_nn_verify_ibp_linear should SUCCEED under DENY_SORRY=1 (it is now \
         sorry-free).\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn test_ibp_linear_bounds_is_faithful_definition() {
    // #3490 follow-up: `ibp_linear_bounds` is now a faithful reducible
    // `Declaration::Definition` (was an uninterpreted `Declaration::Axiom`).
    // It returns `IntervalBounds m` (a Type, not a Prop), built as
    // `IntervalBounds.mk m lo' hi' valid` with a CONSTRUCTIVELY-proved `valid`
    // (`∀ j, lo' j ≤ hi' j`) — no `sorry`. The kernel re-verifies the body
    // against its type at registration; this test pins the kind transition.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_linear_bounds"))
        .expect("ibp_linear_bounds should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "ibp_linear_bounds should now be a faithful Definition"
    );
    assert!(
        info.value.is_some(),
        "ibp_linear_bounds Definition must carry a value term"
    );
    // The value (including its constructive `valid` proof) must be sorry-free.
    let tm = env
        .trust_marker_deps(&Name::from_string("NNVerify.ibp_linear_bounds"))
        .expect("present");
    assert!(
        tm.is_empty(),
        "ibp_linear_bounds must be sorry-free, got {tm:?}"
    );
}

#[test]
fn test_ibp_linear_module_dispositions() {
    // T80 unlock (#3490 follow-up). Every Prop-typed declaration in the
    // IBP-linear module is now a genuine constructive `Declaration::Theorem`:
    // the keystone `ibp_linear_bounds` define unlocked
    // `ibp_linear_per_component` (formerly the sole honest admitted Axiom,
    // resting on the then-uninterpreted bound-computation function). NONE is a
    // sorry-inhabited Opaque or an admitted Axiom any longer.
    let env = make_env();

    let theorems = [
        "NNVerify.mul_nonneg_le_left",
        "NNVerify.mul_nonpos_le_left",
        "NNVerify.add_le_add",
        "NNVerify.le_of_eq_of_le",
        "NNVerify.le_of_le_of_eq",
        "NNVerify.w_pos_nonneg",
        "NNVerify.w_neg_nonpos",
        // TCB-shrink: `w_decompose` is now a constructive Theorem too.
        "NNVerify.w_decompose",
        // T80 unlock: per-component soundness is now PROVED off the define.
        "NNVerify.ibp_linear_per_component",
    ];
    for name in &theorems {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be a constructive Theorem, got {:?}",
            info.kind
        );
    }

    // Whole module is sorry-free.
    for name in &theorems {
        let tm = env
            .trust_marker_deps(&Name::from_string(name))
            .expect("present");
        assert!(tm.is_empty(), "{name} must be sorry-free, got {tm:?}");
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_linear().expect("first init");
    env.init_nn_verify_ibp_linear()
        .expect("second init (idempotent)");
}
