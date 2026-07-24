// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C010 robustness-generalization bounds formalization.
//!
//! Part of #3262.

use crate::env::{ConstantKind, Environment};
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_robustness_gen()
        .expect("init_nn_verify_robustness_gen");
    env
}

#[test]
fn test_certified_robust_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certified_robust"
        ))
        .is_some());
}

#[test]
fn test_lipschitz_local_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.RobustnessGen.lipschitz_local"))
        .is_some());
}

#[test]
fn test_utility_functions_registered() {
    let env = make_env();
    for name in &[
        "NNVerify.RobustnessGen.nat_to_rat",
        "NNVerify.RobustnessGen.sqrt",
        "NNVerify.RobustnessGen.ln",
        "NNVerify.RobustnessGen.rademacher_complexity",
        "NNVerify.RobustnessGen.generalization_gap",
        "NNVerify.RobustnessGen.gen_bound",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
    }
}

#[test]
fn test_certified_implies_lipschitz_local_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certified_implies_lipschitz_local"
        ))
        .is_some());
    // Post-#3578 Branch A demasquerade: the `_axiom` backing Opaque has
    // been removed. The primary declaration is now itself the axiom.
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certified_implies_lipschitz_local_axiom"
        ))
        .is_none(),
        "After #3578, the `_axiom` backing Opaque must be removed; the \
         primary `certified_implies_lipschitz_local` declaration is now \
         itself a `Declaration::Axiom`.",
    );
}

#[test]
fn test_lipschitz_rademacher_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.lipschitz_rademacher_bound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.lipschitz_rademacher_bound_axiom"
        ))
        .is_some());
}

#[test]
fn test_rademacher_gen_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.rademacher_gen_bound"
        ))
        .is_some());
}

#[test]
fn test_certificate_gen_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certificate_gen_bound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certificate_gen_bound_axiom"
        ))
        .is_some());
}

#[test]
fn test_tighter_cert_better_gen_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.tighter_cert_better_gen"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.tighter_cert_better_gen_axiom"
        ))
        .is_some());
}

#[test]
fn test_certified_robust_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.RobustnessGen.certified_robust"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer certified_robust type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_certificate_gen_bound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.RobustnessGen.certificate_gen_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer certificate_gen_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_tighter_cert_better_gen_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.RobustnessGen.tighter_cert_better_gen"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer tighter_cert_better_gen type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_robustness_gen().expect("first init");
    env.init_nn_verify_robustness_gen().expect("second init");
}

/// Verify the exact set of domain axioms for C010 RobustnessGen.
///
/// After #3571 (Branch A demasquerade), the four PAC-generalization bounds
/// are honest `Declaration::Axiom` entries. After #3578 (Branch A
/// demasquerade of `certified_implies_lipschitz_local`), the fifth axiom
/// is the bare-primary `certified_implies_lipschitz_local` itself — the
/// `_axiom` Opaque backing was removed entirely, so the allow-list names
/// the primary declaration rather than an auxiliary `_axiom` wrapper.
/// The set is pinned here so any future unexpected growth (or accidental
/// reintroduction of the sorry-Opaque masquerade pattern) is caught by
/// the guard.
#[test]
fn test_robustness_gen_exact_domain_axiom_set() {
    let env = make_env();
    let report = env.soundness_report();
    let mut rg_axioms: Vec<String> = report
        .domain_axioms
        .iter()
        .filter(|n| n.to_string().starts_with("NNVerify.RobustnessGen."))
        .map(|n| n.to_string())
        .collect();
    rg_axioms.sort();

    let expected: Vec<String> = [
        "NNVerify.RobustnessGen.certificate_gen_bound_axiom",
        "NNVerify.RobustnessGen.certified_implies_lipschitz_local",
        "NNVerify.RobustnessGen.lipschitz_rademacher_bound_axiom",
        "NNVerify.RobustnessGen.rademacher_gen_bound_axiom",
        "NNVerify.RobustnessGen.tighter_cert_better_gen_axiom",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect();

    assert_eq!(
        rg_axioms, expected,
        "C010 RobustnessGen domain axioms drifted. \
         Expected exactly the 4 #3571 PAC-bound axioms + the #3578 \
         `certified_implies_lipschitz_local` bare-primary axiom; got \
         {rg_axioms:?}",
    );
}

// =============================================================================
// #3578 Branch A demasquerade guards — C010 certified_implies_lipschitz_local
// demoted from True.intro-closed Theorem to Declaration::Axiom, and
// lipschitz_local reverted from reducible Definition to Declaration::Opaque.
// =============================================================================
//
// Prior #3463 configuration (MASQUERADE under
// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2 + M4):
//   `lipschitz_local` := reducible Declaration::Definition (body `True`)
//   `certified_implies_lipschitz_local` := Declaration::Theorem carrying
//       `fun d f eps _h1 _h2 => True.intro` — type-checked only because
//       delta-unfolding `lipschitz_local d f eps (1/eps)` collapsed to
//       `True`, closed by `True.intro` under five discarded binders.
//
// Post-#3578 (Branch A demasquerade):
//   `lipschitz_local` := Declaration::Opaque (no delta-unfolding).
//   `certified_implies_lipschitz_local` := Declaration::Axiom (no stored
//       value; honest primitive posit).
//   Backing `certified_implies_lipschitz_local_axiom` Opaque: DELETED.
//   Constructive-proof builder: DELETED.

/// Returns true iff the innermost body (after stripping lambdas) is the
/// canonical synthetic sorry term.
///
/// Retained post-#3578 because the sorry-pi audit test
/// (`test_c010_sorry_inhabit_pi_site_count_after_3578`) still walks the
/// PAC-bound axiom wrappers' Theorem values to confirm they are plain
/// axiom references and not sorry-inhabited.
fn innermost_body_is_synthetic_sorry(env_value: &Expr) -> bool {
    let mut cursor = env_value;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        cursor = body;
    }
    cursor.is_synthetic_sorry()
}

/// #3578 pins: `certified_implies_lipschitz_local` is a honest
/// `Declaration::Axiom` with no stored value. The five-binder
/// `True.intro`-closed proof and the backing `_axiom` Opaque are both
/// gone. Guards against any future refactor that silently reintroduces
/// either half of the #3463 masquerade (reducible `True`-carrier OR
/// `True.intro`-valued Opaque/Theorem).
#[test]
fn test_c010_certified_implies_lipschitz_local_is_axiom_honest_demotion_3578() {
    let env = make_env();

    // (1) Primary declaration: ConstantKind::Axiom, value == None.
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certified_implies_lipschitz_local",
        ))
        .expect("certified_implies_lipschitz_local should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Axiom,
        "Post-#3578: certified_implies_lipschitz_local must be \
         ConstantKind::Axiom (was Theorem in #3463 with True.intro \
         masquerade proof). Got {:?}.",
        ci.kind,
    );
    assert!(
        ci.value.is_none(),
        "Post-#3578: certified_implies_lipschitz_local is a \
         Declaration::Axiom — ci.value must be None. If this fires, \
         Branch A regressed to the #3463 True.intro-Theorem pattern.",
    );

    // (2) Type is still a Pi (the honest universally-quantified
    // certificate-to-Lipschitz claim). Type-checks through add_decl.
    assert!(
        matches!(ci.type_.kind(), ExprKind::Pi(..)),
        "certified_implies_lipschitz_local type must remain a Pi \
         (the universally-quantified claim over d, f, eps, _h1, _h2). \
         Got {:?}.",
        ci.type_.kind(),
    );

    // (3) Backing `_axiom` Opaque is removed entirely.
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certified_implies_lipschitz_local_axiom"
        ))
        .is_none(),
        "Post-#3578: certified_implies_lipschitz_local_axiom Opaque \
         must be removed. The primary declaration is now itself the \
         axiom — no auxiliary `_axiom` wrapper.",
    );
}

/// #3578 pins: `lipschitz_local` is reverted from a reducible
/// `Declaration::Definition` (the #3463 promotion that enabled the
/// `True.intro` masquerade) back to `Declaration::Opaque`. Opaques are
/// NOT delta-unfolded by kernel `def_eq`, so `lipschitz_local d f eps L`
/// can no longer collapse to `True` during proof type-checking.
/// Guards the companion half of the #3578 Branch A demotion — flipping
/// `lipschitz_local` back to a reducible `True`-Definition and adding a
/// `True.intro`-valued Opaque for `certified_implies_lipschitz_local`
/// would re-enable the masquerade; this test fences that path.
#[test]
fn test_c010_lipschitz_local_is_opaque_not_reducible_definition_3578() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.RobustnessGen.lipschitz_local"))
        .expect("lipschitz_local should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Opaque,
        "Post-#3578: lipschitz_local must be Declaration::Opaque \
         (reverted from the #3463 reducible Definition). Opaques are not \
         delta-unfolded by kernel def_eq, closing the reduction path that \
         let `lipschitz_local d f eps L` collapse to `True`. Got {:?}.",
        ci.kind,
    );
    // Opaques ignore the is_reducible flag; assert it's false for
    // belt-and-braces (matches EnvDeclBuilder::add_decl default).
    assert!(
        !ci.is_reducible,
        "lipschitz_local Opaque should have is_reducible=false; \
         is_reducible=true on an Opaque has no kernel effect but would \
         confuse future readers.",
    );
}

/// #3578: `certified_implies_lipschitz_local` still type-checks through
/// the kernel `add_decl` pipeline — the Pi type is valid (a real
/// universally-quantified claim over the vacuous `lipschitz_local`
/// placeholder). Demotion from Theorem to Axiom removes the proof term
/// but preserves the type.
#[test]
fn test_c010_certified_implies_lipschitz_local_type_still_type_checks_3578() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.RobustnessGen.certified_implies_lipschitz_local"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("certified_implies_lipschitz_local should infer a type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "certified_implies_lipschitz_local type should still be Pi after \
         #3578 demotion; got {:?}",
        ty.kind(),
    );
}

/// Verifies the C010 RobustnessGen `sorry_inhabit_pi` site count after
/// the full #3463 + #3571 + #3578 remediation sequence.
///
/// Before #3463: 5 RobustnessGen claim Opaques sorry-inhabited.
/// After #3463: 4 sorry-pi sites (the 4 PAC bounds) + 1 True.intro
///   masquerade (`certified_implies_lipschitz_local`).
/// After #3571 (Branch A): 0 sorry-pi sites in the four PAC bounds;
///   they are honest `Declaration::Axiom` with `ci.value == None`.
///   The `certified_implies_lipschitz_local` masquerade survived.
/// After #3578 (Branch A): the masquerade is gone too —
///   `certified_implies_lipschitz_local` is itself `Declaration::Axiom`
///   with `ci.value == None`.  Total domain axioms in C010: 5. Total
///   sorry-inhabited RobustnessGen value terms: 0.
#[test]
fn test_c010_sorry_inhabit_pi_site_count_after_3578() {
    let env = make_env();

    // #3578: certified_implies_lipschitz_local is now an Axiom with no
    // value. No term to be sorry-inhabited.
    let thm_ci = env
        .get_const(&Name::from_string(
            "NNVerify.RobustnessGen.certified_implies_lipschitz_local",
        ))
        .expect("certified_implies_lipschitz_local should be registered");
    assert_eq!(thm_ci.kind, ConstantKind::Axiom);
    assert!(
        thm_ci.value.is_none(),
        "certified_implies_lipschitz_local must be a bare Axiom post-#3578.",
    );

    // #3571: The four PAC-bound `_axiom` entries are honest Axioms; no
    // value to sorry-inhabit.
    for axiom_name in &[
        "NNVerify.RobustnessGen.lipschitz_rademacher_bound_axiom",
        "NNVerify.RobustnessGen.rademacher_gen_bound_axiom",
        "NNVerify.RobustnessGen.certificate_gen_bound_axiom",
        "NNVerify.RobustnessGen.tighter_cert_better_gen_axiom",
    ] {
        let ci = env
            .get_const(&Name::from_string(axiom_name))
            .unwrap_or_else(|| panic!("{axiom_name} should be registered"));
        assert_eq!(
            ci.kind,
            ConstantKind::Axiom,
            "{axiom_name} should be ConstantKind::Axiom after #3571 \
             Branch A, got {:?}",
            ci.kind,
        );
        assert!(
            ci.value.is_none(),
            "{axiom_name} is a Declaration::Axiom — ci.value must be \
             None. If this fires, Branch A regressed to the old \
             sorry-Opaque pattern.",
        );
    }

    // The four PAC-bound Theorem wrappers reference their `_axiom` by
    // name. Ensure their value terms are not sorry-inhabited.
    for thm_name in &[
        "NNVerify.RobustnessGen.lipschitz_rademacher_bound",
        "NNVerify.RobustnessGen.rademacher_gen_bound",
        "NNVerify.RobustnessGen.certificate_gen_bound",
        "NNVerify.RobustnessGen.tighter_cert_better_gen",
    ] {
        let value = env
            .get_const(&Name::from_string(thm_name))
            .and_then(|ci| ci.value.clone())
            .unwrap_or_else(|| panic!("{thm_name} should have a value"));
        assert!(
            !innermost_body_is_synthetic_sorry(&value),
            "{thm_name} Theorem wrapper value should not be \
             sorry-inhabited after #3571 Branch A",
        );
    }
}

/// #3571: Each of the four PAC-bound Theorem wrappers must reference its
/// `_axiom` so `axiom_deps(theorem)` returns the correct transitive
/// closure under the honest-axiom proof_mechanism. Guards against a
/// future refactor silently inlining the axiom value and dropping the
/// dependency.
#[test]
fn test_c010_branch_a_axiom_wrapper_closure_3571() {
    let env = make_env();
    let pairs = [
        (
            "NNVerify.RobustnessGen.lipschitz_rademacher_bound",
            "NNVerify.RobustnessGen.lipschitz_rademacher_bound_axiom",
        ),
        (
            "NNVerify.RobustnessGen.rademacher_gen_bound",
            "NNVerify.RobustnessGen.rademacher_gen_bound_axiom",
        ),
        (
            "NNVerify.RobustnessGen.certificate_gen_bound",
            "NNVerify.RobustnessGen.certificate_gen_bound_axiom",
        ),
        (
            "NNVerify.RobustnessGen.tighter_cert_better_gen",
            "NNVerify.RobustnessGen.tighter_cert_better_gen_axiom",
        ),
    ];
    for (thm_name, axiom_name) in &pairs {
        let thm_ci = env
            .get_const(&Name::from_string(thm_name))
            .unwrap_or_else(|| panic!("{thm_name} should be registered"));
        assert_eq!(
            thm_ci.kind,
            ConstantKind::Theorem,
            "{thm_name} should be ConstantKind::Theorem, got {:?}",
            thm_ci.kind,
        );
        let deps = env
            .axiom_deps(&Name::from_string(thm_name))
            .unwrap_or_else(|| panic!("{thm_name} should resolve axiom_deps"));
        let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            dep_names.iter().any(|n| n == axiom_name),
            "{thm_name}'s axiom_deps closure must contain {axiom_name}; \
             got {dep_names:?}",
        );
    }
}

// NOTE (#3578): the prior `test_c010_lipschitz_local_is_reducible_definition`
// guard was deleted during Branch A demasquerade. That test pinned
// `lipschitz_local` as a reducible Declaration::Definition — the exact
// configuration the #3463 masquerade required. The replacement guard
// (`test_c010_lipschitz_local_is_opaque_not_reducible_definition_3578`,
// above) pins the post-demotion Declaration::Opaque shape. A future
// refactor that re-promotes `lipschitz_local` to a reducible Definition
// MUST either (a) land Branch B (faithful Lipschitz predicate body) or
// (b) keep `certified_implies_lipschitz_local` as a Declaration::Axiom
// so the M2+M4 masquerade cannot recur.

/// Verify all declarations use the `NNVerify.RobustnessGen.` prefix.
///
/// Post-#3578: the `certified_implies_lipschitz_local_axiom` backing
/// Opaque is removed. The primary declaration is now itself the axiom.
#[test]
fn test_nn_verify_robustness_gen_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.RobustnessGen.certified_robust",
        "NNVerify.RobustnessGen.lipschitz_local",
        "NNVerify.RobustnessGen.nat_to_rat",
        "NNVerify.RobustnessGen.sqrt",
        "NNVerify.RobustnessGen.ln",
        "NNVerify.RobustnessGen.rademacher_complexity",
        "NNVerify.RobustnessGen.generalization_gap",
        "NNVerify.RobustnessGen.gen_bound",
        "NNVerify.RobustnessGen.certified_implies_lipschitz_local",
        // NOTE (#3578): certified_implies_lipschitz_local_axiom removed.
        "NNVerify.RobustnessGen.lipschitz_rademacher_bound",
        "NNVerify.RobustnessGen.lipschitz_rademacher_bound_axiom",
        "NNVerify.RobustnessGen.rademacher_gen_bound",
        "NNVerify.RobustnessGen.rademacher_gen_bound_axiom",
        "NNVerify.RobustnessGen.certificate_gen_bound",
        "NNVerify.RobustnessGen.certificate_gen_bound_axiom",
        "NNVerify.RobustnessGen.tighter_cert_better_gen",
        "NNVerify.RobustnessGen.tighter_cert_better_gen_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify.RobustnessGen."),
            "{} must use NNVerify.RobustnessGen. prefix",
            name,
        );
    }
}
