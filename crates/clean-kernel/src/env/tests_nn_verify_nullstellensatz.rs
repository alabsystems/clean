// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C028: Neural Nullstellensatz — SoS certificates for NN verification.
//!
//! Validates that all definitions and theorems are properly registered
//! in the kernel and pass type checking. Includes proof quality tests
//! to verify the constructive completeness proof (#3377).

use super::*;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_nullstellensatz()
        .expect("init_nn_verify_nullstellensatz");
    env
}

// =============================================================================
// Registration tests
// =============================================================================

#[test]
fn test_type_axioms_registered() {
    let env = make_env();
    let type_names = [
        "NNVerify.C028.ReLUNetwork",
        "NNVerify.C028.Polynomial",
        "NNVerify.C028.SoSCertificate",
        "NNVerify.C028.PiecewiseLinear",
    ];
    for name in &type_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_function_axioms_registered() {
    let env = make_env();
    let fn_names = [
        "NNVerify.C028.relu_to_pwl",
        "NNVerify.C028.sos_certifies",
        "NNVerify.C028.sos_degree",
        "NNVerify.C028.network_depth",
        "NNVerify.C028.network_width",
        "NNVerify.C028.property_polynomial",
        "NNVerify.C028.property_holds_on_region",
    ];
    for name in &fn_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_theorems_registered() {
    let env = make_env();
    // Post-#3567: sos_existence is an honest Axiom (Branch A demotion);
    // sos_existence_core is no longer registered (was backing the now-deleted
    // constructive proof term). degree_bound_core remains a sorry-based Opaque.
    let thm_names = [
        "NNVerify.C028.sos_existence",
        "NNVerify.C028.degree_bound",
        "NNVerify.C028.degree_bound_core",
        // C028c is constructive — no completeness_core needed (#3377)
        "NNVerify.C028.completeness",
    ];
    for name in &thm_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
    // Verify completeness_core does NOT exist (eliminated by #3377)
    assert!(
        env.get_const(&Name::from_string("NNVerify.C028.completeness_core"))
            .is_none(),
        "completeness_core should not exist — eliminated by constructive proof (#3377)",
    );
    // Verify sos_existence_core does NOT exist (eliminated by #3567 Branch A demotion)
    assert!(
        env.get_const(&Name::from_string("NNVerify.C028.sos_existence_core"))
            .is_none(),
        "sos_existence_core should not exist — eliminated by sos_existence \
         demotion to Declaration::Axiom (#3567 Branch A)",
    );
}

// =============================================================================
// Type checking tests
// =============================================================================

#[test]
fn test_polynomial_type_checks() {
    let env = make_env();
    let poly = Expr::const_(Name::from_string("NNVerify.C028.Polynomial"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&poly).expect("infer Polynomial type");
    // Polynomial : Nat -> Type, so its type is a Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_sos_certificate_type_checks() {
    let env = make_env();
    let sos = Expr::const_(Name::from_string("NNVerify.C028.SoSCertificate"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&sos).expect("infer SoSCertificate type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_relu_network_type_checks() {
    let env = make_env();
    let net = Expr::const_(Name::from_string("NNVerify.C028.ReLUNetwork"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&net).expect("infer ReLUNetwork type");
    // ReLUNetwork : Type, so its type is Sort(1+)
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_piecewise_linear_type_checks() {
    let env = make_env();
    let pwl = Expr::const_(Name::from_string("NNVerify.C028.PiecewiseLinear"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&pwl).expect("infer PiecewiseLinear type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_relu_to_pwl_type_checks() {
    let env = make_env();
    let r = Expr::const_(Name::from_string("NNVerify.C028.relu_to_pwl"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&r).expect("infer relu_to_pwl type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_sos_existence_theorem_type_checks() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C028.sos_existence"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer sos_existence type");
    // Theorem type is a forall (Pi)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_degree_bound_theorem_type_checks() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C028.degree_bound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer degree_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_completeness_theorem_type_checks() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C028.completeness"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer completeness type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// =============================================================================
// Idempotency and naming
// =============================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_nullstellensatz().expect("first init");
    env.init_nn_verify_nullstellensatz().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    let all_names = [
        "NNVerify.C028.ReLUNetwork",
        "NNVerify.C028.Polynomial",
        "NNVerify.C028.SoSCertificate",
        "NNVerify.C028.PiecewiseLinear",
        "NNVerify.C028.relu_to_pwl",
        "NNVerify.C028.sos_certifies", // local-evidence projection Definition
        "NNVerify.C028.sos_degree",
        "NNVerify.C028.network_depth",
        "NNVerify.C028.network_width",
        "NNVerify.C028.property_polynomial",
        "NNVerify.C028.property_holds_on_region",
        "NNVerify.C028.sos_existence", // hypothesis-wrapped theorem
        // sos_existence_core eliminated by #3567 Branch A demotion
        "NNVerify.C028.degree_bound",
        "NNVerify.C028.degree_bound_core", // Opaque (sorry-based, not Axiom)
        // completeness_core eliminated by constructive proof (#3377)
        "NNVerify.C028.completeness",
    ];
    for name in &all_names {
        assert!(
            name.starts_with("NNVerify.C028."),
            "All C028 names must use NNVerify.C028. prefix: {name}",
        );
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_network_depth_width_type_checks() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for name in ["NNVerify.C028.network_depth", "NNVerify.C028.network_width"] {
        let c = Expr::const_(Name::from_string(name), vec![]);
        let ty = tc.infer_type(&c).unwrap_or_else(|e| {
            panic!("{name} should type-check: {e:?}");
        });
        // ReLUNetwork -> Nat, so type is a Pi
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "{name} type should be Pi, got {:?}",
            ty.kind(),
        );
    }
}

#[test]
fn test_sos_certifies_type_checks() {
    let env = make_env();
    let c = Expr::const_(Name::from_string("NNVerify.C028.sos_certifies"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&c).expect("infer sos_certifies type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_property_polynomial_type_checks() {
    let env = make_env();
    let c = Expr::const_(
        Name::from_string("NNVerify.C028.property_polynomial"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&c).expect("infer property_polynomial type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_property_holds_type_checks() {
    let env = make_env();
    let c = Expr::const_(
        Name::from_string("NNVerify.C028.property_holds_on_region"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&c)
        .expect("infer property_holds_on_region type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// =============================================================================
// Proof quality tests (#3377)
// =============================================================================

/// Post-2026-04-27 hypothesis-wrapped retirement, the C028 axiom set is
/// empty. `sos_existence` returns an explicit local SoS-existence hypothesis,
/// and `sos_certifies` projects predicate evidence from the certificate.
const C028_EXPECTED_AXIOMS: &[&str] = &[];

#[test]
fn test_c028_completeness_depends_on_demoted_axioms() {
    let env = make_env();

    // Post-2026-04-27: `completeness` is hypothesis-wrapped over local
    // SoS-existence evidence and must not reference any C028 global axiom.
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.C028.completeness"))
        .expect("completeness axiom_deps should be defined");
    let c028_axiom_deps: std::collections::BTreeSet<String> = deps
        .iter()
        .map(|n| n.to_string())
        .filter(|s| s.starts_with("NNVerify.C028."))
        .collect();
    assert_eq!(
        c028_axiom_deps,
        std::collections::BTreeSet::new(),
        "completeness should not transitively depend on any C028 axiom after \
         sos_certifies retirement; found: {c028_axiom_deps:?}",
    );
}

#[test]
fn test_c028_axiom_set_post_3567_branch_a() {
    let env = make_env();

    // Enumerate all C028-prefixed domain axioms via the env soundness report.
    let report = env.soundness_report();
    let c028_axioms: std::collections::BTreeSet<String> = report
        .domain_axioms
        .iter()
        .map(|n| n.to_string())
        .filter(|s| s.starts_with("NNVerify.C028."))
        .collect();

    let expected: std::collections::BTreeSet<String> = C028_EXPECTED_AXIOMS
        .iter()
        .map(|s| (*s).to_string())
        .collect();

    assert_eq!(
        c028_axioms, expected,
        "Post-2026-04-27: C028 domain axiom set should be empty. \
         Found: {c028_axioms:?}",
    );
}

#[test]
fn test_c028_core_opaques_not_axioms() {
    let env = make_env();

    // Post-#3567: only `degree_bound_core` remains as a sorry-based Opaque.
    // `sos_existence_core` was deleted when `sos_existence` became an Axiom.
    let name_str = "NNVerify.C028.degree_bound_core";
    let name = Name::from_string(name_str);
    let ci = env
        .get_const(&name)
        .unwrap_or_else(|| panic!("{name_str} should be registered"));
    assert_eq!(
        ci.kind,
        ConstantKind::Opaque,
        "{name_str} should be ConstantKind::Opaque (sorry-based), got {:?}",
        ci.kind,
    );

    // Verify completeness_core does NOT exist
    assert!(
        env.get_const(&Name::from_string("NNVerify.C028.completeness_core"))
            .is_none(),
        "completeness_core should not exist — eliminated by constructive proof",
    );
    // Verify sos_existence_core does NOT exist (post-#3567)
    assert!(
        env.get_const(&Name::from_string("NNVerify.C028.sos_existence_core"))
            .is_none(),
        "sos_existence_core should not exist — eliminated by #3567 Branch A demotion",
    );
}

// =============================================================================
// 2026-04-27: sos_existence and sos_certifies hypothesis-wrapped retirement
// =============================================================================

/// Post-2026-04-27: `NNVerify.C028.sos_existence` is a hypothesis-wrapped
/// `Declaration::Theorem`. The former constructive proof term
/// `fun d_in d_out net C P _h => @Exists.intro (SoSCertificate d_in) pred
/// Nat.zero True.intro` depended on the reducible
/// `sos_certifies = fun _ _ _ _ => True` carrier to delta-collapse the
/// existential's predicate into `True`. That is MASQUERADE Rule M2
/// (argument-discarding carrier) + Rule M4 (trivial witness/`True.intro`
/// proof) per `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
///
/// This guard pins the honest hypothesis-wrapped state and the local-evidence
/// predicate definition so a future reversion back to the MASQUERADE pattern
/// or a global C028 axiom is forced to explicitly update this test.
///
/// Keys pinned:
/// 1. `ConstantKind::Theorem` with a proof term.
/// 2. The proof returns its innermost local hypothesis.
/// 3. `sos_certifies` is a reducible projection `Definition`, not an axiom.
/// 4. No `sos_existence_core` Opaque remains.
#[test]
fn test_c028_sos_existence_is_hypothesis_wrapped_theorem() {
    let env = make_env();

    // (1) Theorem kind.
    let thm_ci = env
        .get_const(&Name::from_string("NNVerify.C028.sos_existence"))
        .expect("sos_existence should be registered");
    assert_eq!(
        thm_ci.kind,
        ConstantKind::Theorem,
        "sos_existence should be a hypothesis-wrapped theorem after \
         2026-04-27 retirement, got {:?}",
        thm_ci.kind,
    );

    // (2) The theorem proof is exactly the local hypothesis wrapper.
    let value = thm_ci
        .value
        .clone()
        .expect("hypothesis-wrapped sos_existence should carry a proof value");
    let mut cursor = &value;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        cursor = body;
    }
    assert!(
        matches!(cursor.kind(), ExprKind::BVar(0)),
        "sos_existence proof should return its innermost local hypothesis; \
         got {:?}",
        cursor.kind(),
    );

    // (3) sos_certifies is a local-evidence projection definition (was
    //     reducible Definition with body `fun _ _ _ _ => True` — Rule M2
    //     argument-discarding carrier enabling the Exists.intro+True.intro
    //     proof; then an honest Branch-A axiom).
    let cert_ci = env
        .get_const(&Name::from_string("NNVerify.C028.sos_certifies"))
        .expect("sos_certifies should be registered");
    assert_eq!(
        cert_ci.kind,
        ConstantKind::Definition,
        "sos_certifies should be a local-evidence projection Definition \
         after 2026-04-27 retirement, got {:?}",
        cert_ci.kind,
    );
    let cert_value = cert_ci
        .value
        .clone()
        .expect("sos_certifies Definition should carry a projection body");
    let mut cursor = &cert_value;
    let mut lam_count = 0;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        lam_count += 1;
        cursor = body;
    }
    assert_eq!(
        lam_count, 4,
        "sos_certifies projection should abstract d, sigma, poly, region",
    );
    assert!(
        matches!(cursor.kind(), ExprKind::App(_, _)),
        "sos_certifies body should apply local certificate evidence, got {:?}",
        cursor.kind(),
    );

    // (4) sos_existence_core Opaque no longer exists.
    assert!(
        env.get_const(&Name::from_string("NNVerify.C028.sos_existence_core"))
            .is_none(),
        "sos_existence_core should not exist — eliminated by #3567 \
         Branch A demotion (was backing the now-deleted constructive proof)",
    );
}

/// Verifies the `sos_existence` theorem const type-checks through the full
/// kernel `add_decl` pipeline (via `init_nn_verify_nullstellensatz` on a
/// fresh Environment) AND that `tc.infer_type(&sos_existence)` returns
/// the declared Pi type.
///
/// Post-2026-04-27: `sos_existence` is a hypothesis-wrapped theorem, so
/// both its type and proof value are checked by `add_decl`.
#[test]
fn test_c028_sos_existence_kernel_validates_via_add_decl() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C028.sos_existence"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("sos_existence theorem const should infer a type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "sos_existence type should be Pi, got {:?}",
        ty.kind(),
    );

    let thm_ci = env
        .get_const(&Name::from_string("NNVerify.C028.sos_existence"))
        .expect("sos_existence should be registered");
    assert!(
        thm_ci.value.is_some(),
        "sos_existence theorem should carry the local-hypothesis proof value",
    );
}

/// Verifies the C028 `sorry_inhabit_pi` site count.
///
/// Lineage:
/// - Before #3466: 2 sites (sos_existence_core, degree_bound_core).
/// - After  #3466: 1 site (degree_bound_core only); sos_existence became
///   a constructive proof over a reducible `True` carrier — MASQUERADE.
/// - After  #3567 Branch A: still 1 site; sos_existence_core deleted
///   outright when sos_existence demoted to Axiom.
/// - After  2026-04-27: still 1 site; sos_existence is
///   hypothesis-wrapped and does not use sorry-based inhabitation.
///
/// A sorry-inhabited value has the shape `fun .. .. => <synthetic sorry>` —
/// a nested lambda whose innermost body is the canonical synthetic sorry term.
#[test]
fn test_c028_sorry_inhabit_pi_site_count_after_3567() {
    let env = make_env();

    fn innermost_body_is_synthetic_sorry(env_value: &Expr) -> bool {
        let mut cursor = env_value;
        while let ExprKind::Lam(_, _, body) = cursor.kind() {
            cursor = body;
        }
        cursor.is_synthetic_sorry()
    }

    // sos_existence_core no longer exists post-#3567 Branch A.
    assert!(
        env.get_const(&Name::from_string("NNVerify.C028.sos_existence_core"))
            .is_none(),
        "sos_existence_core should not exist post-#3567 Branch A",
    );

    // degree_bound_core remains a sorry-inhabited Opaque (pending
    // substantive C028 carrier work, Branch B).
    let degree_bound_core = env
        .get_const(&Name::from_string("NNVerify.C028.degree_bound_core"))
        .and_then(|ci| ci.value.clone())
        .expect("degree_bound_core should have a value");
    assert!(
        innermost_body_is_synthetic_sorry(&degree_bound_core),
        "degree_bound_core should still be sorry-inhabited (pending \
         Branch B substantive carrier work)",
    );
}
