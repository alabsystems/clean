// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additional coverage tests for proof-producing WHNF reduction.
//!
//! Part of #685.

use super::*;
use crate::expr::BinderInfo;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::tc::whnf_proof::WhnfProofStep;

fn env_with_eq() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("invariant: init_nat");
    env.init_eq().expect("invariant: init_eq");
    env
}

fn assert_eq_proof(tc: &TypeChecker, proof: &Expr, type_: Expr, lhs: Expr, rhs: Expr) {
    let ty = tc.infer_type(proof).expect("proof must type-check");
    let u1 = Level::succ(Level::zero());
    let expected = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [type_, lhs, rhs],
    );
    assert!(tc.is_def_eq(&ty, &expected), "proof type mismatch: {ty:?}");
}

fn add_point_inductive(env: &mut Environment) -> Name {
    let point_name = Name::from_string("Point");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let point_mk_type = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::const_(point_name.clone(), vec![]),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: point_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Point.mk"),
                type_: point_mk_type,
            }],
        }],
    })
    .expect("invariant: add Point inductive");

    point_name
}

#[test]
fn test_fvar_proof_typechecks() {
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let value = Expr::nat_lit(7);
    let fvar_id = tc
        .ctx
        .borrow_mut()
        .push_let(Name::from_string("x"), nat.clone(), value.clone());
    let fvar = Expr::fvar(fvar_id);

    let wp = tc.whnf_with_proof(&fvar, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, value);
    assert!(
        matches!(wp.steps.as_slice(), [WhnfProofStep::Zeta]),
        "let-bound FVar reduction should record one zeta step, got {:?}",
        wp.steps
    );
    assert_eq_proof(
        &tc,
        &wp.proof.expect("let-bound FVar reduction needs proof"),
        nat,
        fvar,
        Expr::nat_lit(7),
    );
}

#[test]
fn test_proj_proof_typechecks() {
    let mut env = env_with_eq();
    let point_name = add_point_inductive(&mut env);
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let point = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Point.mk"), vec![]),
            Expr::nat_lit(1),
        ),
        Expr::nat_lit(2),
    );
    let proj = Expr::proj(point_name.clone(), 0, point);
    let reduced = Expr::nat_lit(1);

    let wp = tc.whnf_with_proof(&proj, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, reduced);
    assert!(
        matches!(
            wp.steps.as_slice(),
            [WhnfProofStep::Proj { struct_name, idx }]
                if struct_name == &point_name && *idx == 0
        ),
        "projection reduction should record one proj step, got {:?}",
        wp.steps
    );
    assert_eq_proof(
        &tc,
        &wp.proof.expect("projection reduction needs proof"),
        nat,
        proj,
        Expr::nat_lit(1),
    );
}

/// Regression: Proj on a let-bound FVar exercises the multi-step Eq.refl
/// shortcut in whnf_proof.rs (Proj case delegates to self.whnf(e) which
/// performs FVar zeta + projection reduction, then uses Eq.refl for the
/// full chain). Confirms the kernel accepts Eq.refl for non-trivial
/// definitional reduction paths.
///
/// Re: #685, #2456
#[test]
fn test_proj_let_bound_fvar_proof_typechecks() {
    let mut env = env_with_eq();
    let point_name = add_point_inductive(&mut env);
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let point_type = Expr::const_(point_name.clone(), vec![]);
    let point_val = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Point.mk"), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(4),
    );

    // let p : Point := Point.mk 3 4
    let fvar_id = tc
        .ctx
        .borrow_mut()
        .push_let(Name::from_string("p"), point_type, point_val);
    let fvar = Expr::fvar(fvar_id);

    // Proj(Point, 0, p) — requires zeta (FVar → Point.mk 3 4) then projection
    let proj = Expr::proj(point_name.clone(), 0, fvar.clone());
    let reduced = Expr::nat_lit(3);

    let wp = tc.whnf_with_proof(&proj, &nat, Level::succ(Level::zero()));
    assert_eq!(
        wp.result, reduced,
        "Proj on let-bound FVar should reduce to field 0"
    );
    assert!(
        wp.steps
            .iter()
            .any(|s| matches!(s, WhnfProofStep::Proj { .. })),
        "step trace should include a Proj step, got {:?}",
        wp.steps
    );
    assert_eq_proof(
        &tc,
        &wp.proof.expect("Proj on let-bound FVar needs proof"),
        nat,
        proj,
        Expr::nat_lit(3),
    );
}
