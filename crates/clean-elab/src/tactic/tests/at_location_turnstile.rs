// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::infer::ElabCtx;
use crate::tactic::builtins::register_builtin_tactics;
use crate::tactic::builtins_phase3d_rewrite::register_phase3d_rewrite;
use crate::tactic::registry::{ElaboratedRefine, TacticEval, TacticRegistry};
use crate::unify::MetaState;
use clean_kernel::env::Declaration;
use clean_parser::{Span, SurfaceExpr, SurfaceRwRule, SurfaceTactic, SurfaceTacticLocation};

struct NoopTacticEval {
    metas: MetaState,
}

impl TacticEval for NoopTacticEval {
    fn eval(&mut self, _ps: &mut ProofState, _tac: &SurfaceTactic) -> Result<(), TacticError> {
        Ok(())
    }

    fn eval_seq(
        &mut self,
        _ps: &mut ProofState,
        _tacs: &[SurfaceTactic],
    ) -> Result<(), TacticError> {
        Ok(())
    }

    fn elaborate(&mut self, _expr: &SurfaceExpr) -> Result<Expr, TacticError> {
        panic!("NoopTacticEval::elaborate should not be called in turnstile tests")
    }

    fn infer_type(&mut self, _expr: &Expr) -> Result<Expr, TacticError> {
        panic!("NoopTacticEval::infer_type should not be called in turnstile tests")
    }

    fn elaborate_refine(
        &mut self,
        _ps: &ProofState,
        _expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, TacticError> {
        panic!("NoopTacticEval::elaborate_refine should not be called in turnstile tests")
    }

    fn metas(&self) -> &MetaState {
        &self.metas
    }
}

fn rw_rule(name: &str) -> SurfaceRwRule {
    SurfaceRwRule {
        span: Span::dummy(),
        reverse: false,
        term: SurfaceExpr::Ident(Span::dummy(), name.to_string()),
    }
}

fn find_local_decl<'a>(goal: &'a Goal, name: &str) -> &'a LocalDecl {
    goal.local_ctx
        .iter()
        .find(|decl| decl.name == name)
        .unwrap_or_else(|| panic!("expected local declaration '{name}'"))
}

/// Build an env with N:Type, a b:N, P Q:N→Prop and init_eq.
/// Uses distinct predicates so simp cannot close the goal via assumption.
fn setup_simp_turnstile_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    for (name, ty) in [
        ("N", Expr::type_()),
        ("a", n_ty.clone()),
        ("b", n_ty.clone()),
        (
            "P",
            Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
        ),
        ("Q", Expr::pi(BinderInfo::Default, n_ty, Expr::prop())),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .unwrap();
    }
    env
}

fn make_beta_reducible(pred: &str, arg: &Expr, base_ty: &Expr) -> Expr {
    let family = Expr::lam(
        BinderInfo::Default,
        base_ty.clone(),
        Expr::app(Expr::const_(Name::from_string(pred), vec![]), Expr::bvar(0)),
    );
    Expr::app(family, arg.clone())
}

#[test]
fn test_simp_turnstile_location_modifies_hypothesis_and_goal() {
    let env = setup_simp_turnstile_env();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let goal_reducible = make_beta_reducible("P", &a, &n_ty);
    let hyp_reducible = make_beta_reducible("Q", &b, &n_ty);

    let mut state = ProofState::with_context(
        env,
        goal_reducible,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_reducible,
            value: None,
        }],
    );

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    register_phase3d_rewrite(&mut registry);
    let simp = registry
        .get_compound("simp")
        .expect("simp should be registered as a compound tactic");
    let tactic = SurfaceTactic::Simp {
        span: Span::dummy(),
        only: false,
        lemmas: vec![],
        location: SurfaceTacticLocation::HypsAndGoal(vec!["h".to_string()]),
    };
    let mut eval = NoopTacticEval {
        metas: MetaState::new(),
    };

    (simp.handler)(&mut eval, &mut state, &tactic)
        .expect("simp at h ⊢ should simplify both hypothesis and goal");

    let expected_goal = Expr::app(Expr::const_(Name::from_string("P"), vec![]), a);
    let expected_hyp = Expr::app(Expr::const_(Name::from_string("Q"), vec![]), b);
    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, expected_goal,
        "should simplify the goal target"
    );
    let h = find_local_decl(goal, "h");
    assert_eq!(h.ty, expected_hyp, "should simplify the named hypothesis");
}

#[test]
fn test_dsimp_turnstile_arg_modifies_hypothesis_and_goal() {
    let mut env = setup_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::type_(),
        ),
    })
    .unwrap();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);

    let family = Expr::lam(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::app(p.clone(), Expr::bvar(0)),
    );
    let reducible = Expr::app(family, a.clone());

    let mut state = ProofState::with_context(
        env,
        reducible.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: reducible,
            value: None,
        }],
    );

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let dsimp = registry
        .get("dsimp")
        .expect("dsimp should be registered in the production registry");

    (dsimp.handler)(
        &mut state,
        &[
            Expr::const_(Name::from_string("h"), vec![]),
            Expr::const_(Name::from_string("⊢"), vec![]),
        ],
    )
    .expect("dsimp at h ⊢ should simplify both hypothesis and goal");

    let expected = Expr::app(p, a);
    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, expected,
        "turnstile arg should simplify the goal target"
    );
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("hypothesis should remain visible");
    assert_eq!(
        h.ty, expected,
        "turnstile arg should simplify the named hypothesis"
    );
}

#[test]
fn test_rw_turnstile_location_modifies_hypothesis_and_goal() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let target = make_p(x.clone());
    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h_eq".to_string(),
                ty: make_eq_n(x.clone(), y.clone()),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_target".to_string(),
                ty: make_p(x.clone()),
                value: None,
            },
        ],
    );

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    register_phase3d_rewrite(&mut registry);
    let rw = registry
        .get_compound("rw")
        .expect("rw should be registered as a compound tactic");
    let tactic = SurfaceTactic::Rw(
        Span::dummy(),
        vec![rw_rule("h_eq")],
        SurfaceTacticLocation::HypsAndGoal(vec!["h_target".to_string()]),
    );
    let mut eval = NoopTacticEval {
        metas: MetaState::new(),
    };

    (rw.handler)(&mut eval, &mut state, &tactic)
        .expect("rw [h_eq] at h_target ⊢ should rewrite both hypothesis and goal");

    let expected = make_p(y);
    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, expected,
        "turnstile location should rewrite the goal target"
    );
    let h_target = find_local_decl(goal, "h_target");
    assert_eq!(
        h_target.ty, expected,
        "turnstile location should rewrite the named hypothesis"
    );
}

#[test]
fn test_push_neg_turnstile_arg_modifies_hypothesis_and_goal() {
    let mut env = setup_env_with_prop_ext();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("A"), vec![]);
    let not_not_p = make_not(&make_not(&p));
    let mut state = ProofState::with_context(
        env,
        not_not_p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: not_not_p,
            value: None,
        }],
    );

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let push_neg = registry
        .get("push_neg")
        .expect("push_neg should be registered in the production registry");

    (push_neg.handler)(
        &mut state,
        &[
            Expr::const_(Name::from_string("h"), vec![]),
            Expr::const_(Name::from_string("⊢"), vec![]),
        ],
    )
    .expect("push_neg at h ⊢ should simplify both hypothesis and goal");

    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, p,
        "turnstile arg should simplify the goal target"
    );
    let h = find_local_decl(goal, "h");
    assert_eq!(
        h.ty, p,
        "turnstile arg should simplify the named hypothesis"
    );
}

#[test]
fn test_unfold_turnstile_arg_modifies_hypothesis_and_goal() {
    let mut env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
        value: a.clone(),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::prop(),
        ),
    })
    .unwrap();

    let mydef = Expr::const_(Name::from_string("mydef"), vec![]);
    let target = Expr::app(Expr::const_(Name::from_string("P"), vec![]), mydef.clone());
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: target,
            value: None,
        }],
    );

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let unfold = registry
        .get("unfold")
        .expect("unfold should be registered in the production registry");

    (unfold.handler)(
        &mut state,
        &[
            Expr::const_(Name::from_string("mydef"), vec![]),
            Expr::const_(Name::from_string("h"), vec![]),
            Expr::const_(Name::from_string("⊢"), vec![]),
        ],
    )
    .expect("unfold mydef at h ⊢ should expand both hypothesis and goal");

    let expected = Expr::app(Expr::const_(Name::from_string("P"), vec![]), a);
    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, expected,
        "turnstile arg should unfold the goal target"
    );
    let h = find_local_decl(goal, "h");
    assert_eq!(
        h.ty, expected,
        "turnstile arg should unfold the named hypothesis"
    );
}

#[test]
fn test_conv_turnstile_location_modifies_hypothesis_and_goal() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = make_eq(Expr::prop(), make_p(x.clone()), make_p(x.clone()));
    let mut state = ProofState::with_context(
        env.clone(),
        target.clone(),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h_eq".to_string(),
                ty: make_eq_n(x.clone(), y.clone()),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_target".to_string(),
                ty: target,
                value: None,
            },
        ],
    );
    let mut ctx = ElabCtx::new(&env);

    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::HypsAndGoal(vec!["h_target".into()]),
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule("h_eq")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv at h_target ⊢ should rewrite both hypothesis and goal");

    let expected = make_eq(Expr::prop(), make_p(y), make_p(x));
    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, expected,
        "turnstile location should rewrite the goal target through conv"
    );
    let h_target = find_local_decl(goal, "h_target");
    assert_eq!(
        h_target.ty, expected,
        "turnstile location should rewrite the named hypothesis through conv"
    );
}
