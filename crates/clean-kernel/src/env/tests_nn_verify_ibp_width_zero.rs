// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for T4 sub-lemmas (#3490 T4, #3476).
//!
//! Guards:
//! - `NNVerify.rat_max_zero_zero` is a `Declaration::Theorem` (not Opaque).
//! - The theorem type-checks under the kernel.
//! - No `sorry`/`sorryAx` appears in the proof value.
//! - Transitive axiom deps are a subset of the expected set.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_width_zero()
        .expect("init_nn_verify_ibp_width_zero should succeed");
    env
}

const TARGET: &str = "NNVerify.rat_max_zero_zero";

#[test]
fn test_ibp_width_zero_rat_max_zero_zero_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(TARGET)).is_some(),
        "{TARGET} should be registered"
    );
}

#[test]
fn test_ibp_width_zero_rat_max_zero_zero_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET))
        .expect("target must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{TARGET} should be a Declaration::Theorem, got {:?}",
        info.kind
    );
}

#[test]
fn test_ibp_width_zero_rat_max_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check, got: {err:?}"));
}

#[test]
fn test_ibp_width_zero_rat_max_zero_zero_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET))
        .expect("target must be registered");
    let value = info
        .value
        .as_ref()
        .expect("target should have a value (Theorem)");
    let mut stack: Vec<&Expr> = vec![value];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                assert_ne!(s, "sorry", "{TARGET} value contains sorry");
                assert_ne!(s, "sorryAx", "{TARGET} value contains sorryAx");
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
            ExprKind::Proj(_, _, src) => stack.push(src),
            ExprKind::MData(_, body) => stack.push(body),
            _ => {}
        }
    }
}

#[test]
fn test_ibp_width_zero_rat_max_zero_zero_axiom_closure() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("target should have axiom_deps");
    let deps: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    // #integrity-audit (2026-06): the `Rat.*` ordered-field / lattice facts
    // (`Rat.max`, `Rat.max_def`, `Rat.le_refl`, …) were previously whitelisted
    // as `FOUNDATIONAL_AXIOMS`, so `axiom_deps` filtered them out and reported
    // an EMPTY closure (`ProofQuality::Constructive`). That overstated the
    // proof: those are unproved-in-Clean DOMAIN assumptions
    // (`ADMITTED_DOMAIN_AXIOMS`), not logical foundations. They are now
    // excluded from `is_foundational_axiom`, so `axiom_deps` honestly RETURNS
    // them. The proof of `@Rat.max_def Rat.zero Rat.zero (Rat.le_refl
    // Rat.zero)` (type `Eq (Rat.max 0 0) 0`) genuinely rests on those admitted
    // domain axioms, so the closure is NON-EMPTY — and the theorem is
    // `AxiomDependent`, not `Constructive`. `sorry`/`sorryAx` must STILL never
    // appear, and no non-admitted/rogue axiom may sneak in.
    assert!(
        !deps.contains("sorry"),
        "{TARGET} axiom closure must not contain sorry; got {deps:?}"
    );
    assert!(
        !deps.contains("sorryAx"),
        "{TARGET} axiom closure must not contain sorryAx; got {deps:?}"
    );
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET} is now FULLY CONSTRUCTIVE — `Rat.max` / `Rat.max_def` / \
         `Rat.le_refl` are kernel-checked over the quotient carrier, so its \
         axiom closure is EMPTY; got {deps:?}"
    );
    let admitted: std::collections::HashSet<&str> = crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .collect();
    for a in &deps {
        assert!(
            admitted.contains(a.as_str()),
            "unexpected non-admitted axiom in {TARGET} closure: {a}; full closure {deps:?}"
        );
    }
}

// -----------------------------------------------------------------------------
// `NNVerify.ibp_width_zero_at_zero` — n=0 specialization of ibp_width_zero.
// -----------------------------------------------------------------------------

const TARGET_AT_ZERO: &str = "NNVerify.ibp_width_zero_at_zero";

#[test]
fn test_ibp_width_zero_at_zero_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(TARGET_AT_ZERO)).is_some(),
        "{TARGET_AT_ZERO} should be registered"
    );
}

#[test]
fn test_ibp_width_zero_at_zero_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET_AT_ZERO))
        .expect("target must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{TARGET_AT_ZERO} should be a Declaration::Theorem, got {:?}",
        info.kind
    );
}

#[test]
fn test_ibp_width_zero_at_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET_AT_ZERO), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET_AT_ZERO} should type-check, got: {err:?}"));
}

#[test]
fn test_ibp_width_zero_at_zero_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET_AT_ZERO))
        .expect("target must be registered");
    let value = info
        .value
        .as_ref()
        .expect("target should have a value (Theorem)");
    let mut stack: Vec<&Expr> = vec![value];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                assert_ne!(s, "sorry", "{TARGET_AT_ZERO} value contains sorry");
                assert_ne!(s, "sorryAx", "{TARGET_AT_ZERO} value contains sorryAx");
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
            ExprKind::Proj(_, _, src) => stack.push(src),
            ExprKind::MData(_, body) => stack.push(body),
            _ => {}
        }
    }
}

/// Verify the proof VALUE — the lambda body — contains only `Eq.refl`
/// applied to `Rat` and `Rat.zero`, i.e. does not secretly pull in
/// domain axioms through the proof term itself. (The theorem's *type*
/// pulls `Rat.max` through `ibp_width`'s definition body, which is
/// documented and expected.)
#[test]
fn test_ibp_width_zero_at_zero_proof_value_is_eq_refl() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET_AT_ZERO))
        .expect("target must be registered");
    let value = info
        .value
        .as_ref()
        .expect("target should have a value (Theorem)");
    // Expect: Lam(_, _, App(App(Const("Eq.refl"), Const("Rat")), Const("Rat.zero")))
    let body = match value.kind() {
        ExprKind::Lam(_, _, body) => body.as_ref(),
        other => panic!("{TARGET_AT_ZERO} value should be a lambda, got {other:?}"),
    };
    // Walk the body and confirm `Eq.refl`, `Rat`, `Rat.zero` appear and
    // nothing else that's a domain axiom.
    let mut stack: Vec<&Expr> = vec![body];
    let mut saw_eq_refl = false;
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                if s == "Eq.refl" {
                    saw_eq_refl = true;
                }
                // The proof body should only reference these three.
                assert!(
                    matches!(s.as_str(), "Eq.refl" | "Rat" | "Rat.zero"),
                    "{TARGET_AT_ZERO} proof body should reference only Eq.refl/Rat/Rat.zero, got {s}"
                );
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
            ExprKind::Proj(_, _, src) => stack.push(src),
            ExprKind::MData(_, body) => stack.push(body),
            _ => {}
        }
    }
    assert!(
        saw_eq_refl,
        "{TARGET_AT_ZERO} proof body should reference Eq.refl"
    );
}

#[test]
fn test_ibp_width_zero_at_zero_axiom_closure_no_sorry() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET_AT_ZERO))
        .expect("target should have axiom_deps");
    let deps: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    // Key soundness check: no `sorry` anywhere in the closure.
    assert!(
        !deps.contains("sorry"),
        "{TARGET_AT_ZERO} axiom closure must not contain sorry; got {deps:?}"
    );
    assert!(
        !deps.contains("sorryAx"),
        "{TARGET_AT_ZERO} axiom closure must not contain sorryAx; got {deps:?}"
    );
    // #integrity-audit (2026-06): this theorem's TYPE references
    // `NNVerify.ibp_width`, whose definition body references `Rat.max` /
    // `Rat.max_def` / `Rat.max_def'`. Those Rat lattice facts were dishonestly
    // whitelisted as `FOUNDATIONAL_AXIOMS`, which made `axiom_deps` filter them
    // out and report an EMPTY closure (`ProofQuality::Constructive`). They are
    // really unproved-in-Clean DOMAIN assumptions (`ADMITTED_DOMAIN_AXIOMS`),
    // now excluded from `is_foundational_axiom`, so `axiom_deps` honestly
    // RETURNS them. The remaining `ibp_width` body operations (`Rat.sub`,
    // `Rat.neg`, `Rat.abs`, `Rat.add`, `Rat.mul`, `Rat.zero`, `Rat.one`,
    // `Rat.le`) are `Declaration::Definition`s, not axioms, so they do NOT
    // enter the closure. Honest state: closure is NON-EMPTY, containing ONLY
    // admitted Rat domain axioms — this theorem is `AxiomDependent`, not
    // `Constructive`.
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET_AT_ZERO} is now FULLY CONSTRUCTIVE — the `Rat.max` lattice \
         axioms it inherited via `ibp_width` are kernel-checked over the quotient \
         carrier, so its axiom closure is EMPTY; got {deps:?}"
    );
    let admitted: std::collections::HashSet<&str> = crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .collect();
    for a in &deps {
        assert!(
            admitted.contains(a.as_str()),
            "unexpected non-admitted axiom in {TARGET_AT_ZERO} closure: {a}; full closure {deps:?}"
        );
    }
}

// -----------------------------------------------------------------------------
// `NNVerify.ibp_width_zero` — full `∀ n bnd, ... → ibp_width n bnd = 0`
// theorem (#3490 T4 completion).
// -----------------------------------------------------------------------------

const TARGET_FULL: &str = "NNVerify.ibp_width_zero";

#[test]
fn test_ibp_width_zero_full_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(TARGET_FULL)).is_some(),
        "{TARGET_FULL} should be registered"
    );
}

#[test]
fn test_ibp_width_zero_full_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET_FULL))
        .expect("target must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{TARGET_FULL} should be a Declaration::Theorem, got {:?}",
        info.kind
    );
}

#[test]
fn test_ibp_width_zero_full_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET_FULL), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET_FULL} should type-check, got: {err:?}"));
}

#[test]
fn test_ibp_width_zero_full_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET_FULL))
        .expect("target must be registered");
    let value = info
        .value
        .as_ref()
        .expect("target should have a value (Theorem)");
    let mut stack: Vec<&Expr> = vec![value];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                assert_ne!(s, "sorry", "{TARGET_FULL} value contains sorry");
                assert_ne!(s, "sorryAx", "{TARGET_FULL} value contains sorryAx");
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
            ExprKind::Proj(_, _, src) => stack.push(src),
            ExprKind::MData(_, body) => stack.push(body),
            _ => {}
        }
    }
}

#[test]
fn test_ibp_width_zero_full_axiom_closure_no_sorry() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET_FULL))
        .expect("target should have axiom_deps");
    let deps: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    // Key soundness check: no `sorry` anywhere in the closure.
    assert!(
        !deps.contains("sorry"),
        "{TARGET_FULL} axiom closure must not contain sorry; got {deps:?}"
    );
    assert!(
        !deps.contains("sorryAx"),
        "{TARGET_FULL} axiom closure must not contain sorryAx; got {deps:?}"
    );
}

// =============================================================================
// T5: NNVerify.eps_ball_width_is_zero (#3490 T5)
// =============================================================================

const TARGET_EPS_BALL: &str = "NNVerify.eps_ball_width_is_zero";

#[test]
fn test_eps_ball_width_is_zero_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(TARGET_EPS_BALL)).is_some(),
        "{TARGET_EPS_BALL} should be registered"
    );
}

#[test]
fn test_eps_ball_width_is_zero_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET_EPS_BALL))
        .expect("target must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{TARGET_EPS_BALL} should be a Declaration::Theorem, got {:?}",
        info.kind
    );
}

#[test]
fn test_eps_ball_width_is_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET_EPS_BALL), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET_EPS_BALL} should type-check, got: {err:?}"));
}

#[test]
fn test_eps_ball_width_is_zero_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET_EPS_BALL))
        .expect("target must be registered");
    let value = info
        .value
        .as_ref()
        .expect("target should have a value (Theorem)");
    let mut stack: Vec<&Expr> = vec![value];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                assert_ne!(s, "sorry", "{TARGET_EPS_BALL} value contains sorry");
                assert_ne!(s, "sorryAx", "{TARGET_EPS_BALL} value contains sorryAx");
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
            ExprKind::Proj(_, _, src) => stack.push(src),
            ExprKind::MData(_, body) => stack.push(body),
            _ => {}
        }
    }
}

#[test]
fn test_eps_ball_width_is_zero_axiom_closure_no_sorry() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET_EPS_BALL))
        .expect("target should have axiom_deps");
    let deps: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    // Key soundness check: no `sorry` anywhere in the closure.
    assert!(
        !deps.contains("sorry"),
        "{TARGET_EPS_BALL} axiom closure must not contain sorry; got {deps:?}"
    );
    assert!(
        !deps.contains("sorryAx"),
        "{TARGET_EPS_BALL} axiom closure must not contain sorryAx; got {deps:?}"
    );
    // #integrity-audit (2026-06): this proof composes `NNVerify.ibp_width_zero`
    // (whose `ibp_width` body rests on `Rat.max` / `Rat.max_def` /
    // `Rat.max_def'`) with `Eq.refl`, so it inherits those Rat lattice
    // dependencies. Those facts were dishonestly whitelisted as
    // `FOUNDATIONAL_AXIOMS`, masking the closure as EMPTY
    // (`ProofQuality::Constructive`). They are really unproved-in-Clean DOMAIN
    // assumptions (`ADMITTED_DOMAIN_AXIOMS`), now excluded from
    // `is_foundational_axiom`, so `axiom_deps` honestly RETURNS them. Honest
    // state: closure is NON-EMPTY, containing ONLY admitted Rat domain axioms —
    // this theorem is `AxiomDependent`, not `Constructive`.
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET_EPS_BALL} is now FULLY CONSTRUCTIVE — the `Rat.max` lattice \
         axioms it inherited from `ibp_width_zero` are kernel-checked over the \
         quotient carrier, so its axiom closure is EMPTY; got {deps:?}"
    );
    let admitted: std::collections::HashSet<&str> = crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .collect();
    for a in &deps {
        assert!(
            admitted.contains(a.as_str()),
            "unexpected non-admitted axiom in {TARGET_EPS_BALL} closure: {a}; full closure {deps:?}"
        );
    }
}
