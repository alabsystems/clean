// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for zonotope compression soundness (T10-T12).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_zonotope_compress()
        .expect("init_nn_verify_zonotope_compress should succeed");
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
// Type registration tests
// ---------------------------------------------------------------

#[test]
fn test_zonotope_type_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.Zonotope");
    assert_registered(&env, "NNVerify.Zonotope.mk");
}

#[test]
fn test_zonotope_contains_registered() {
    assert_registered(&make_env(), "NNVerify.Zonotope.contains");
}

/// #3556: `NNVerify.Zonotope.contains` must be a `Declaration::Definition`
/// carrying an `Exists` body, not a `Declaration::Axiom`. A bare axiom
/// laundered interface content into foundational status without defining
/// the predicate.
#[test]
fn test_zonotope_contains_is_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.contains"))
        .expect("NNVerify.Zonotope.contains should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "Zonotope.contains should be Definition (#3556), got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "Zonotope.contains should carry an existential value (#3556)"
    );
}

#[test]
fn test_zonotope_compress_registered() {
    assert_registered(&make_env(), "NNVerify.Zonotope.compress");
}

/// COMPRESS RETIREMENT: `NNVerify.Zonotope.compress` was a body-less
/// `Declaration::Axiom` (a trusted operation signature). It is now a faithful,
/// total, reducible `Declaration::Definition` whose box-cover body genuinely
/// depends on `z` — so it drops out of the admitted-axiom census (a Definition
/// is a computation, not a claim). This guard pins, in order: (1) kind ==
/// Definition (NOT Axiom), with a real term value present; (2) the body head is
/// `Zonotope.mk` (a genuine reconstruction over the carrier), crucially NOT an
/// argument-discarding masquerade; (3) the body genuinely references
/// `z.generators` (a `Proj` at field 1) and the absorbed-tail bricks `Rat.abs` +
/// `Fin.sum`; and (4) its transitive axiom closure is EMPTY (the
/// Nat/Fin/Rat.abs/Decidable.rec bricks it uses are all constructive kernel
/// theorems — no domain axiom, no `sorry`). A regression that reverts compress
/// to a bare Axiom (re-admitting it into the TCB) turns this RED.
#[test]
fn test_zonotope_compress_is_faithful_definition_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.compress"))
        .expect("compress should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "compress should now be a faithful Definition (axiom retired), got {:?}",
        info.kind
    );
    let value = info
        .value
        .as_ref()
        .expect("compress Definition must carry a real body (not a bare axiom)");

    // Strip the outer `fun n k k' h_le z => _` binders to reach the body head.
    let mut body = value;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner;
    }
    let head = {
        let mut h = body;
        while let ExprKind::App(f, _) = h.kind() {
            h = f;
        }
        h
    };
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "NNVerify.Zonotope.mk",
            "compress body head must be Zonotope.mk (genuine carrier reconstruction), got {name}"
        ),
        other => panic!("compress body head must be a Const (Zonotope.mk), got {other:?}"),
    }

    // The body must genuinely use `z` — assert it contains a `Proj` of field 1
    // (`z.generators`) and references `Rat.abs` + `Fin.sum` (the absorbed tail).
    fn collect(e: &Expr, out: &mut Vec<String>, saw_gen_proj: &mut bool) {
        match e.kind() {
            ExprKind::Const(n, _) => out.push(n.to_string()),
            ExprKind::App(f, a) => {
                collect(f, out, saw_gen_proj);
                collect(a, out, saw_gen_proj);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                collect(t, out, saw_gen_proj);
                collect(b, out, saw_gen_proj);
            }
            ExprKind::Proj(_, idx, p) => {
                if *idx == 1 {
                    *saw_gen_proj = true;
                }
                collect(p, out, saw_gen_proj);
            }
            _ => {}
        }
    }
    let mut consts = Vec::new();
    let mut saw_gen_proj = false;
    collect(value, &mut consts, &mut saw_gen_proj);
    assert!(
        saw_gen_proj,
        "compress body must genuinely use z.generators (a Proj at field 1) — \
         the absorbed tail column depends on the dropped generator data"
    );
    assert!(
        consts.iter().any(|c| c == "Rat.abs"),
        "compress body must fold dropped columns by Rat.abs (per-row L1)"
    );
    assert!(
        consts.iter().any(|c| c == "Fin.sum"),
        "compress body must sum the absorbed tail via Fin.sum"
    );

    // Empty transitive axiom closure: the retirement adds NO axiom (and no sorry).
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.Zonotope.compress"))
        .expect("compress should be registered");
    let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
    assert!(
        names.is_empty(),
        "compress Definition body must carry no domain axioms / no sorry, got {names:?}"
    );
}

#[test]
fn test_zonotope_to_ibp_registered() {
    assert_registered(&make_env(), "NNVerify.Zonotope.to_ibp");
}

// ---------------------------------------------------------------
// Helper theorem registration tests
// ---------------------------------------------------------------

#[test]
fn test_zero_eps_valid_registered() {
    assert_registered(&make_env(), "NNVerify.Zonotope.zero_eps_valid");
}

/// #3152: `NNVerify.Zonotope.zero_eps_valid` (the eps=0 bound helper) was
/// promoted from a bare `Declaration::Axiom` to a constructive
/// `Declaration::Theorem`. The value must be PRESENT and its head must be
/// `And.intro` (the genuine conjunction introduction of `-1 ≤ 0` and `0 ≤ 1`),
/// crucially NOT `Eq.refl` (which would be an opaque-carrier reflexivity
/// masquerade). Mirrors `test_t10_is_constructive_theorem_with_exists_intro_value`.
#[test]
fn test_zero_eps_valid_is_constructive_theorem_with_and_intro_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.zero_eps_valid"))
        .expect("zero_eps_valid should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "zero_eps_valid should now be a constructive Theorem, not {:?}",
        info.kind
    );
    let value = info
        .value
        .as_ref()
        .expect("zero_eps_valid must carry a real proof value (not a bare axiom)");

    // Strip the outer `fun k i => _` binders to reach the proof body head.
    let mut body = value;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner;
    }
    // The body head must be `And.intro` (the (-1 ≤ 0) ∧ (0 ≤ 1) introduction),
    // and crucially NOT `Eq.refl` (an opaque-carrier reflexivity masquerade).
    let head = {
        let mut h = body;
        while let ExprKind::App(f, _) = h.kind() {
            h = f;
        }
        h
    };
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "And.intro",
                "zero_eps_valid proof head must be And.intro (eps=0 bound), got {name}"
            );
            assert_ne!(
                name.to_string(),
                "Eq.refl",
                "zero_eps_valid proof must NOT be an Eq.refl opaque-carrier masquerade"
            );
        }
        other => panic!("zero_eps_valid proof body head must be a Const, got {other:?}"),
    }
}

/// #3152: `zero_eps_valid`'s eps=0 bound reuses only constructive `Rat`-order
/// theorems over the quotient-`Rat` carrier (`Rat.neg_le_neg`,
/// `Rat.lt_iff_le_not_le`, `Rat.zero_lt_one`), so its transitive axiom closure
/// is EMPTY — no domain axiom, no NEW axiom of any kind. Pins that the
/// promotion did not smuggle a domain axiom into the closure (which would make
/// it a `Theorem`-wrapping-`Axiom` restatement rather than a real proof).
#[test]
fn test_zero_eps_valid_axiom_closure_is_foundational() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.Zonotope.zero_eps_valid"))
        .expect("zero_eps_valid should be registered");
    let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
    let non_foundational: Vec<&String> = names
        .iter()
        .filter(|nm| !crate::env::is_foundational_axiom(&Name::from_string(nm)))
        .collect();
    assert!(
        non_foundational.is_empty(),
        "zero_eps_valid must carry no non-foundational axioms (eps=0 bound over \
         constructive Rat bricks), got {non_foundational:?} (full closure: {names:?})"
    );
    let domain_axioms: Vec<&String> = names
        .iter()
        .filter(|nm| nm.starts_with("NNVerify."))
        .collect();
    assert!(
        domain_axioms.is_empty(),
        "zero_eps_valid must carry no NNVerify.* domain axioms, got {domain_axioms:?}"
    );
}

// ---------------------------------------------------------------
// Theorem registration tests (T10-T12)
// ---------------------------------------------------------------

#[test]
fn test_t10_center_contained_registered() {
    assert_registered(&make_env(), "NNVerify.Zonotope.center_contained");
}

#[test]
fn test_t11_compress_sound_registered() {
    assert_registered(&make_env(), "NNVerify.Zonotope.compress_sound");
}

#[test]
fn test_t12_to_ibp_sound_registered() {
    assert_registered(&make_env(), "NNVerify.Zonotope.to_ibp_sound");
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_zonotope_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("Zonotope should type-check");
    // Type should be Nat -> Nat -> Type
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Zonotope type should be Pi, got {:?}",
        ty.kind()
    );
}

#[test]
fn test_zonotope_contains_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.contains");
}

#[test]
fn test_zonotope_compress_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.compress");
}

#[test]
fn test_zonotope_to_ibp_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.to_ibp");
}

#[test]
fn test_zero_eps_valid_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.zero_eps_valid");
}

#[test]
fn test_t10_center_contained_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.center_contained");
}

#[test]
fn test_t11_compress_sound_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.compress_sound");
}

#[test]
fn test_t12_to_ibp_sound_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.to_ibp_sound");
}

// ---------------------------------------------------------------
// Structural tests
// ---------------------------------------------------------------

#[test]
fn test_zonotope_is_inductive() {
    let env = make_env();
    assert!(
        env.get_inductive(&Name::from_string("NNVerify.Zonotope"))
            .is_some(),
        "Zonotope should be registered as inductive"
    );
}

#[test]
fn test_zonotope_mk_is_constructor() {
    let env = make_env();
    assert!(
        env.get_constructor(&Name::from_string("NNVerify.Zonotope.mk"))
            .is_some(),
        "Zonotope.mk should be registered as constructor"
    );
}

/// #3152 lane-4c: T10 `center_contained` was promoted from a bare
/// `Declaration::Axiom` to a constructive `Declaration::Theorem` carrying the
/// eps=0 witness. The value must be PRESENT and its head must NOT be `Eq.refl`
/// (which would be an opaque-carrier masquerade) — it is `Exists.intro`, the
/// genuine existential introduction discharging the `contains` body.
#[test]
fn test_t10_is_constructive_theorem_with_exists_intro_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.center_contained"))
        .expect("T10 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "T10 should now be a constructive Theorem, not {:?}",
        info.kind
    );
    let value = info
        .value
        .as_ref()
        .expect("T10 must carry a real proof value (not a bare axiom)");

    // Strip the outer `fun n k z => _` binders to reach the proof body head.
    let mut body = value;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner;
    }
    // The body head must be `Exists.intro` (the eps=0 witness introduction),
    // and crucially NOT `Eq.refl` (an opaque-carrier reflexivity masquerade).
    let head = {
        let mut h = body;
        while let ExprKind::App(f, _) = h.kind() {
            h = f;
        }
        h
    };
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "Exists.intro",
                "T10 proof head must be Exists.intro (eps=0 witness), got {name}"
            );
            assert_ne!(
                name.to_string(),
                "Eq.refl",
                "T10 proof must NOT be an Eq.refl opaque-carrier masquerade"
            );
        }
        other => panic!("T10 proof body head must be a Const, got {other:?}"),
    }
}

#[test]
fn test_t11_is_hypothesis_wrapped_theorem() {
    // #zono-false: T11 `compress_sound` was a REFUTABLE Axiom (unconditional
    // over-approximation of the opaque `compress`, false at k'=0). It is now an
    // honest hypothesis-wrapped Theorem (the over-approximation is an explicit
    // local premise the proof returns), so it is no longer an admitted axiom.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.compress_sound"))
        .expect("T11 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "T11 should now be a hypothesis-wrapped Theorem, not {:?}",
        info.kind
    );
}

#[test]
fn test_t12_is_proven_theorem() {
    // T12 was a bare Axiom while `to_ibp` was the FAKE zero-interval carrier.
    // With the faithful `to_ibp` (`[center − Σ|G|, center + Σ|G|]`),
    // `to_ibp_sound` is now a genuine kernel-checked Theorem (the summed
    // triangle-inequality argument). The old "should be Axiom" assertion was
    // about the unproved soundness over the fake body and is retired.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.to_ibp_sound"))
        .expect("T12 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "T12 (to_ibp_sound) should now be a proven Theorem, not {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "T12 should carry a real proof term (not an axiom)"
    );
}

// ---------------------------------------------------------------
// Dependency tests
// ---------------------------------------------------------------

#[test]
fn test_depends_on_nn_verify_types() {
    let env = make_env();
    assert_registered(&env, "NNVerify.NNVec");
    assert_registered(&env, "NNVerify.NNMat");
    assert_registered(&env, "NNVerify.IntervalBounds");
    assert_registered(&env, "NNVerify.IntervalBounds.contains");
}

#[test]
fn test_zonotope_structure_fields() {
    let env = make_env();
    // Zonotope.mk constructor and recursor exist
    assert_registered(&env, "NNVerify.Zonotope.mk");
    assert_registered(&env, "NNVerify.Zonotope.rec");
}

// ---------------------------------------------------------------
// NNVerify naming convention
// ---------------------------------------------------------------

#[test]
fn test_nn_verify_naming_convention() {
    let env = make_env();
    let nn_names = [
        "NNVerify.Zonotope",
        "NNVerify.Zonotope.mk",
        "NNVerify.Zonotope.contains",
        "NNVerify.Zonotope.compress",
        "NNVerify.Zonotope.to_ibp",
        "NNVerify.Zonotope.center_contained",
        "NNVerify.Zonotope.compress_sound",
        "NNVerify.Zonotope.to_ibp_sound",
    ];
    for name in &nn_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with NNVerify.Zonotope. prefix"
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_zonotope_compress().expect("first init");
    env.init_nn_verify_zonotope_compress()
        .expect("second init (idempotent)");
}

/// #3152 lane-4c: T10's eps=0 witness reuses only constructive `Rat`-order /
/// field / `Fin.sum` theorems over the quotient-`Rat` carrier, so its
/// transitive axiom closure is EMPTY — no domain axiom, no NEW axiom of any
/// kind. This pins that the promotion did not smuggle a domain axiom into the
/// closure (which would make it a `Theorem`-wrapping-`Axiom` restatement
/// rather than a real proof).
#[test]
fn test_t10_axiom_closure_is_foundational() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.Zonotope.center_contained"))
        .expect("T10 should be registered");
    let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
    let non_foundational: Vec<&String> = names
        .iter()
        .filter(|nm| !crate::env::is_foundational_axiom(&Name::from_string(nm)))
        .collect();
    assert!(
        non_foundational.is_empty(),
        "T10 center_contained must carry no non-foundational axioms (eps=0 \
         witness over constructive Rat bricks), got {non_foundational:?} \
         (full closure: {names:?})"
    );
    let domain_axioms: Vec<&String> = names
        .iter()
        .filter(|nm| nm.starts_with("NNVerify."))
        .collect();
    assert!(
        domain_axioms.is_empty(),
        "T10 center_contained must carry no NNVerify.* domain axioms, got {domain_axioms:?}"
    );
}
