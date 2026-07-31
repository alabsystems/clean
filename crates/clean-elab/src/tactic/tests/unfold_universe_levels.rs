// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-level instantiation in `unfold` / `delta` (RC-E.2).
//!
//! `substitute_const` replaced a `Const(name, levels)` node with the
//! declaration's stored value and DISCARDED `levels`, so unfolding a
//! universe-polymorphic definition left the declaration's own `Level::Param`
//! dangling in the goal or hypothesis. Observed symptom under real `import
//! Init`: `unfold id at hid` failing with
//! `TypeMismatch { expected: Sort(Param(u)), inferred: Sort(Succ(Zero)) }`,
//! while the monomorphic local-def spelling passed.
//!
//! Every polymorphic test here is paired with a MONOMORPHIC control, so the fix
//! cannot silently trade one class of definition for another.

use super::*;

/// Collect every `Level::Param` name reachable from `expr` (Sort levels and
/// `Const` level arguments). A term built from a level-0 goal by substituting a
/// correctly instantiated definition body must have none.
fn level_params_in(expr: &Expr) -> Vec<String> {
    fn from_level(level: &Level, out: &mut Vec<String>) {
        match level {
            Level::Param(n) => out.push(n.to_string()),
            Level::Succ(inner) => from_level(inner, out),
            Level::Max(a, b) | Level::IMax(a, b) => {
                from_level(a, out);
                from_level(b, out);
            }
            Level::Zero => {}
        }
    }
    fn go(expr: &Expr, out: &mut Vec<String>) {
        match expr.kind() {
            ExprKind::Sort(level) => from_level(level, out),
            ExprKind::Const(_, levels) => {
                for level in levels.iter() {
                    from_level(level, out);
                }
            }
            ExprKind::App(f, a) => {
                go(f, out);
                go(a, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                go(ty, out);
                go(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                go(ty, out);
                go(val, out);
                go(body, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => go(inner, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(expr, &mut out);
    out
}

fn u() -> Name {
    Name::from_string("u")
}

fn type_u() -> Expr {
    Expr::sort(Level::succ(Level::param(u())))
}

fn n_ty() -> Expr {
    Expr::const_(Name::from_string("N"), vec![])
}

/// `@Eq.{lvl} ty lhs rhs`
fn eq_at(lvl: Level, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![lvl]), ty),
            lhs,
        ),
        rhs,
    )
}

/// Env with `Eq`, `N : Type 0`, `n : N`, and the two definitions under test:
///
/// * `MyId.{u} : {α : Type u} → α → α := fun {α} x => x`
/// * `MyIdN : N → N := fun x => x`   (monomorphic control)
fn setup_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init Eq");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("register N");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: n_ty(),
    })
    .expect("register n");

    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyId"),
        level_params: vec![u()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            type_u(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
        value: Expr::lam(
            BinderInfo::Implicit,
            type_u(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
        is_reducible: false,
    })
    .expect("register MyId");

    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyIdN"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty(), n_ty()),
        value: Expr::lam(BinderInfo::Default, n_ty(), Expr::bvar(0)),
        is_reducible: false,
    })
    .expect("register MyIdN");

    env
}

/// `@MyId.{0} N arg`
fn my_id_at_zero(arg: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("MyId"), vec![Level::zero()]),
            n_ty(),
        ),
        arg,
    )
}

fn n_const() -> Expr {
    Expr::const_(Name::from_string("n"), vec![])
}

/// RC-E.2 — `unfold` in the goal must instantiate the definition's level params
/// with the `Const` node's level arguments. Before the fix the substituted body
/// kept `Sort (Param u)` from the declaration, leaving a dangling level param in
/// the goal that the kernel later rejects.
#[test]
fn test_unfold_goal_instantiates_definition_levels() {
    let env = setup_env();
    let target = eq_at(
        Level::succ(Level::zero()),
        n_ty(),
        my_id_at_zero(n_const()),
        n_const(),
    );
    let mut state = ProofState::new(env, target);

    unfold(&mut state, "MyId").expect("unfold must accept a universe-polymorphic definition");

    let new_target = state
        .current_goal()
        .expect("unfold keeps one goal")
        .target
        .clone();
    assert!(
        level_params_in(&new_target).is_empty(),
        "RC-E.2: unfolding `@MyId.{{0}}` must substitute u := 0 into the body; \
         dangling level params {:?} in {new_target:?}",
        level_params_in(&new_target)
    );
    let tc = TypeChecker::new(state.env());
    assert!(
        tc.infer_type(&new_target).is_ok(),
        "the unfolded target must still be kernel-well-typed; got {:?}",
        tc.infer_type(&new_target)
    );
}

/// RC-E.2 — the reported symptom shape: `unfold MyId at hid`.
#[test]
fn test_unfold_at_hypothesis_instantiates_definition_levels() {
    let env = setup_env();
    let hyp_ty = eq_at(
        Level::succ(Level::zero()),
        n_ty(),
        my_id_at_zero(n_const()),
        n_const(),
    );
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        hyp_ty,
        eq_at(Level::succ(Level::zero()), n_ty(), n_const(), n_const()),
    );
    let mut state = ProofState::new(env, goal_ty);
    intro(&mut state, "hid").expect("intro the hypothesis");

    unfold_at(&mut state, "MyId", "hid")
        .expect("unfold at h must accept a universe-polymorphic definition");

    let goal = state.current_goal().expect("unfold_at keeps one goal");
    let hyp = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "hid")
        .expect("hid survives the rewrite");
    assert!(
        level_params_in(&hyp.ty).is_empty(),
        "RC-E.2: `unfold MyId at hid` must substitute u := 0 into the body; \
         dangling level params {:?} in {:?}",
        level_params_in(&hyp.ty),
        hyp.ty
    );
    let tc = TypeChecker::new(state.env());
    assert!(
        tc.infer_type(&hyp.ty).is_ok(),
        "the unfolded hypothesis type must still be kernel-well-typed; got {:?}",
        tc.infer_type(&hyp.ty)
    );
}

/// RC-E.2 — `delta` shares `substitute_const`, so it inherits the same fix.
#[test]
fn test_delta_instantiates_definition_levels() {
    let env = setup_env();
    let target = eq_at(
        Level::succ(Level::zero()),
        n_ty(),
        my_id_at_zero(n_const()),
        n_const(),
    );
    let mut state = ProofState::new(env, target);

    delta(&mut state).expect("delta must accept a universe-polymorphic definition");

    let new_target = state
        .current_goal()
        .expect("delta keeps one goal")
        .target
        .clone();
    assert!(
        level_params_in(&new_target).is_empty(),
        "RC-E.2: delta must substitute u := 0 into the body; dangling level \
         params {:?} in {new_target:?}",
        level_params_in(&new_target)
    );
}

/// RC-E.2 control — a MONOMORPHIC definition unfolds exactly as before.
#[test]
fn test_unfold_monomorphic_definition_unchanged() {
    let env = setup_env();
    let my_id_n = Expr::app(Expr::const_(Name::from_string("MyIdN"), vec![]), n_const());
    let target = eq_at(Level::succ(Level::zero()), n_ty(), my_id_n, n_const());
    let mut state = ProofState::new(env, target);

    unfold(&mut state, "MyIdN").expect("unfold must keep working on a monomorphic definition");
    let new_target = state
        .current_goal()
        .expect("unfold keeps one goal")
        .target
        .clone();
    assert!(
        level_params_in(&new_target).is_empty(),
        "monomorphic unfold introduces no level params"
    );
    let tc = TypeChecker::new(state.env());
    assert!(
        tc.infer_type(&new_target).is_ok(),
        "the monomorphic unfolded target must stay kernel-well-typed"
    );
}

/// RC-E.2 control — `unfold at h` on a monomorphic definition.
#[test]
fn test_unfold_at_monomorphic_definition_unchanged() {
    let env = setup_env();
    let my_id_n = Expr::app(Expr::const_(Name::from_string("MyIdN"), vec![]), n_const());
    let hyp_ty = eq_at(Level::succ(Level::zero()), n_ty(), my_id_n, n_const());
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        hyp_ty,
        eq_at(Level::succ(Level::zero()), n_ty(), n_const(), n_const()),
    );
    let mut state = ProofState::new(env, goal_ty);
    intro(&mut state, "hid").expect("intro the hypothesis");

    unfold_at(&mut state, "MyIdN", "hid")
        .expect("unfold at h must keep working on a monomorphic definition");
    let goal = state.current_goal().expect("unfold_at keeps one goal");
    let hyp = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "hid")
        .expect("hid survives the rewrite");
    assert!(
        level_params_in(&hyp.ty).is_empty(),
        "monomorphic unfold at h introduces no level params"
    );
}
