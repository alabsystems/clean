// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_elab::tactic::{LocalDecl, ProofState};
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, Name};
use clean_parser::SurfaceName;

fn local(id: u64, name: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        fvar: FVarId::new(id),
        name: SurfaceName::from_name(Name::from_string(name)),
        ty,
        value: None,
        binder_info: BinderInfo::Default.into(),
    }
}

#[test]
fn sibling_dependency_closure_reaches_transitive_locals_and_excludes_unused_ones() {
    let proposition = Expr::sort(Level::zero());
    let a = local(101, "a", proposition.clone());
    let b = local(
        102,
        "b",
        Expr::let_named(
            Name::from_string("p"),
            proposition.clone(),
            Expr::fvar(a.fvar),
            proposition.clone(),
            true,
        ),
    );
    let h = local(
        103,
        "h",
        Expr::arrow(Expr::fvar(b.fvar), Expr::fvar(b.fvar)),
    );
    let dead = local(104, "dead", proposition.clone());
    let state = ProofState::with_context(
        Environment::with_prelude(),
        Expr::const_str("True"),
        vec![a.clone(), b.clone(), h.clone(), dead.clone()],
    );

    let mut goal = state.current_goal().expect("active goal").clone();
    goal.local_ctx = vec![h];
    assert_eq!(
        state.infer_type(&goal, &Expr::fvar(a.fvar)).unwrap(),
        proposition
    );
    assert_eq!(state.infer_type(&goal, &Expr::fvar(b.fvar)).unwrap(), b.ty);
    assert!(state.infer_type(&goal, &Expr::fvar(dead.fvar)).is_err());
}

#[test]
fn a_complete_goal_retains_its_local_types_and_refuses_foreign_variables() {
    let proposition = Expr::sort(Level::zero());
    let a = local(201, "a", proposition.clone());
    let state = ProofState::with_context(
        Environment::with_prelude(),
        Expr::const_str("True"),
        vec![a.clone()],
    );
    let goal = state.current_goal().expect("active goal");
    assert_eq!(
        state.infer_type(goal, &Expr::fvar(a.fvar)).unwrap(),
        proposition
    );
    assert!(state
        .infer_type(goal, &Expr::fvar(FVarId::new(202)))
        .is_err());
}

#[test]
fn instantiation_skips_only_ids_outside_the_reserved_metavariable_range() {
    use clean_elab::{MetaState, Unifier, UnifyResult};
    use clean_kernel::expr::{ExprKind, ZFCSetExpr};
    use std::sync::Arc;

    let tag = 1_u64 << 63;
    let mut metas = MetaState::new();
    let assigned = metas.fresh(Expr::const_str("Nat"));
    let unresolved = metas.fresh(Expr::const_str("Nat"));
    let tagged = |id: clean_elab::MetaId| FVarId::new(tag | id.as_u64());
    let known = Expr::fvar(tagged(assigned));
    let unknown = Expr::fvar(tagged(unresolved));
    assert_eq!(MetaState::from_fvar(tagged(assigned)), Some(assigned));
    assert!(matches!(
        Unifier::new(&mut metas).unify(&known, &Expr::const_str("Nat.zero")),
        UnifyResult::Success
    ));

    let local = Expr::fvar(FVarId::new(tag - 1));
    let floor = FVarId::new(tag);
    assert!(!local.may_contain_fvar_at_or_above(floor));
    assert!(known.may_contain_fvar_at_or_above(floor));
    let tree = |leaf| {
        Expr::app(
            Expr::app(local.clone(), leaf),
            Expr::app(unknown.clone(), local.clone()),
        )
    };
    assert_eq!(
        metas.instantiate(&tree(known.clone())),
        tree(Expr::const_str("Nat.zero"))
    );
    let payload = |expr| Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(expr))));
    assert!(payload(local).may_contain_fvar_at_or_above(floor));
    assert_eq!(
        metas.instantiate(&payload(known)),
        payload(Expr::const_str("Nat.zero"))
    );
}
