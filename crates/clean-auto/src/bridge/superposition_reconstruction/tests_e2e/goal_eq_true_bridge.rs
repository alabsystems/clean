// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end goal-wrapper tests for the `P = True` bridge.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, FVarId, Level, LocalContext, TypeChecker,
};

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_prop_env(names: &[&str]) -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");
    env.init_iff().expect("init_iff");
    env.init_propext().expect("init_propext");

    for name in names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("add axiom to env");
    }
    env
}

fn mk_eq_true(p: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::prop(),
            ),
            p.clone(),
        ),
        prop("True"),
    )
}

fn mk_not(expr: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr.clone())
}

fn mk_and(left: &Expr, right: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), left.clone()),
        right.clone(),
    )
}

fn assert_proof_has_type(
    env: &Environment,
    ctx: LocalContext,
    proof: &Expr,
    goal: &Expr,
    msg: &str,
) {
    let tc = TypeChecker::with_context(env, ctx);
    let inferred = tc.infer_type(proof).expect("type-check should succeed");
    assert!(
        tc.is_def_eq(&inferred, goal),
        "{msg}: inferred type should equal goal, inferred={inferred:?}, goal={goal:?}"
    );
}

#[test]
fn test_reconstruct_goal_atomic_prop_by_contradiction_type_checks() {
    let env = mk_prop_env(&["P"]);
    let p = prop("P");

    let h_p_id = FVarId::new(100);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_p_id,
        Name::from_string("hP"),
        p.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, p.clone(), Expr::prop());
    map.add_symbol(1, prop("True"), Expr::prop());
    map.add_input_clause(0, FVarId::new(0), mk_not(&p));
    map.add_input_clause(1, h_p_id, p.clone());
    map.set_goal_info(p.clone(), 1);

    let c0 = mk_input_neq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_eq(1, Term::Const(0), Term::Const(1));
    let c2 = Clause {
        literals: vec![mk_lit(Term::Const(1), Term::Const(1), false)],
        id: 2,
        parents: vec![1, 0],
        inference: Inference::Superposition(1, 0, Position::root()),
    };
    let c3 = Clause {
        literals: vec![],
        id: 3,
        parents: vec![2],
        inference: Inference::EqualityResolution(2),
    };
    let trace = ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c0, c1, c2, c3],
    };

    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let (proof, _) = reconstructor
        .reconstruct_goal()
        .expect("atomic byContradiction reconstruction should succeed");

    assert_proof_has_type(
        &env,
        ctx,
        &proof,
        &p,
        "atomic byContradiction proof should type-check",
    );
}

#[test]
fn test_reconstruct_goal_atomic_and_type_checks() {
    let env = mk_prop_env(&["P", "Q"]);
    let p = prop("P");
    let q = prop("Q");
    let goal = mk_and(&p, &q);

    let h_p_id = FVarId::new(100);
    let h_q_id = FVarId::new(101);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_p_id,
        Name::from_string("hP"),
        p.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_q_id,
        Name::from_string("hQ"),
        q.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, p.clone(), Expr::prop());
    map.add_symbol(1, q.clone(), Expr::prop());
    map.add_symbol(2, prop("True"), Expr::prop());
    map.add_input_clause(0, FVarId::new(0), mk_not(&goal));
    map.add_input_clause(1, h_p_id, p.clone());
    map.add_input_clause(2, h_q_id, q.clone());
    map.set_goal_info(goal.clone(), 1);

    let c0 = Clause {
        literals: vec![
            mk_lit(Term::Const(0), Term::Const(2), false),
            mk_lit(Term::Const(1), Term::Const(2), false),
        ],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let c1 = mk_input_eq(1, Term::Const(0), Term::Const(2));
    let c2 = mk_input_eq(2, Term::Const(1), Term::Const(2));
    let c3 = Clause {
        literals: vec![
            mk_lit(Term::Const(2), Term::Const(2), false),
            mk_lit(Term::Const(1), Term::Const(2), false),
        ],
        id: 3,
        parents: vec![1, 0],
        inference: Inference::Superposition(1, 0, Position::root()),
    };
    let c4 = Clause {
        literals: vec![mk_lit(Term::Const(1), Term::Const(2), false)],
        id: 4,
        parents: vec![3],
        inference: Inference::EqualityResolution(3),
    };
    let c5 = Clause {
        literals: vec![mk_lit(Term::Const(2), Term::Const(2), false)],
        id: 5,
        parents: vec![2, 4],
        inference: Inference::Superposition(2, 4, Position::root()),
    };
    let c6 = Clause {
        literals: vec![],
        id: 6,
        parents: vec![5],
        inference: Inference::EqualityResolution(5),
    };
    let trace = ProofTrace {
        empty_clause: c6.clone(),
        clauses: vec![c0, c1, c2, c3, c4, c5, c6],
    };

    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let (proof, _) = reconstructor
        .reconstruct_goal()
        .expect("atomic And reconstruction should succeed");

    assert_proof_has_type(
        &env,
        ctx,
        &proof,
        &goal,
        "atomic And proof should type-check",
    );
}

#[test]
fn test_reconstruct_goal_atomic_or_type_checks() {
    let env = mk_prop_env(&["P", "Q"]);
    let p = prop("P");
    let q = prop("Q");
    let goal = mk_or(&p, &q);

    let h_p_id = FVarId::new(100);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_p_id,
        Name::from_string("hP"),
        p.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, p.clone(), Expr::prop());
    map.add_symbol(1, q.clone(), Expr::prop());
    map.add_symbol(2, prop("True"), Expr::prop());
    map.add_input_clause(0, FVarId::new(0), mk_not(&p));
    map.add_input_clause(1, FVarId::new(1), mk_not(&q));
    map.add_input_clause(2, h_p_id, p.clone());
    map.set_goal_info(goal.clone(), 2);

    let c0 = mk_input_neq(0, Term::Const(0), Term::Const(2));
    let c1 = mk_input_neq(1, Term::Const(1), Term::Const(2));
    let c2 = mk_input_eq(2, Term::Const(0), Term::Const(2));
    let c3 = Clause {
        literals: vec![mk_lit(Term::Const(2), Term::Const(2), false)],
        id: 3,
        parents: vec![2, 0],
        inference: Inference::Superposition(2, 0, Position::root()),
    };
    let c4 = Clause {
        literals: vec![],
        id: 4,
        parents: vec![3],
        inference: Inference::EqualityResolution(3),
    };
    let trace = ProofTrace {
        empty_clause: c4.clone(),
        clauses: vec![c0, c1, c2, c3, c4],
    };

    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let (proof, _) = reconstructor
        .reconstruct_goal()
        .expect("atomic Or reconstruction should succeed");

    assert_proof_has_type(
        &env,
        ctx,
        &proof,
        &goal,
        "atomic Or proof should type-check",
    );
}

#[test]
fn test_reconstruct_goal_atomic_not_type_checks() {
    let env = mk_prop_env(&["P"]);
    let p = prop("P");
    let goal = mk_not(&p);

    let h_np_id = FVarId::new(100);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_np_id,
        Name::from_string("hnP"),
        goal.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, p.clone(), Expr::prop());
    map.add_symbol(1, prop("True"), Expr::prop());
    map.add_input_clause(0, FVarId::new(0), mk_not(&goal));
    map.add_input_clause(1, h_np_id, goal.clone());
    map.set_goal_info(goal.clone(), 1);

    let c0 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_neq(1, Term::Const(0), Term::Const(1));
    let c2 = Clause {
        literals: vec![mk_lit(Term::Const(1), Term::Const(1), false)],
        id: 2,
        parents: vec![0, 1],
        inference: Inference::Superposition(0, 1, Position::root()),
    };
    let c3 = Clause {
        literals: vec![],
        id: 3,
        parents: vec![2],
        inference: Inference::EqualityResolution(2),
    };
    let trace = ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c0, c1, c2, c3],
    };

    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let (proof, _) = reconstructor
        .reconstruct_goal()
        .expect("atomic Not reconstruction should succeed");

    assert_proof_has_type(
        &env,
        ctx,
        &proof,
        &goal,
        "atomic Not proof should type-check",
    );
}

#[test]
fn test_reconstruct_goal_atomic_implies_type_checks() {
    let env = mk_prop_env(&["P"]);
    let p = prop("P");
    let goal = Expr::pi(BinderInfo::Default, p.clone(), p.clone());

    let mut map = SymbolMap::new();
    map.add_symbol(0, p.clone(), Expr::prop());
    map.add_symbol(1, prop("True"), Expr::prop());
    map.add_input_clause(0, FVarId::new(0), mk_eq_true(&p));
    map.add_input_clause(1, FVarId::new(1), mk_not(&mk_eq_true(&p)));
    map.set_goal_info(goal.clone(), 2);

    let c0 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_neq(1, Term::Const(0), Term::Const(1));
    let c2 = Clause {
        literals: vec![mk_lit(Term::Const(1), Term::Const(1), false)],
        id: 2,
        parents: vec![0, 1],
        inference: Inference::Superposition(0, 1, Position::root()),
    };
    let c3 = Clause {
        literals: vec![],
        id: 3,
        parents: vec![2],
        inference: Inference::EqualityResolution(2),
    };
    let trace = ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c0, c1, c2, c3],
    };

    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let (proof, _) = reconstructor
        .reconstruct_goal()
        .expect("atomic Implies reconstruction should succeed");

    assert_proof_has_type(
        &env,
        LocalContext::new(),
        &proof,
        &goal,
        "atomic Implies proof should type-check",
    );
}

#[test]
fn test_reconstruct_goal_atomic_iff_type_checks() {
    let env = mk_prop_env(&["P", "Q"]);
    let p = prop("P");
    let q = prop("Q");
    let goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p.clone()),
        q.clone(),
    );

    let h_p_id = FVarId::new(100);
    let h_q_id = FVarId::new(101);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_p_id,
        Name::from_string("hP"),
        p.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_q_id,
        Name::from_string("hQ"),
        q.clone(),
        BinderInfo::Default,
    );

    let clause_1_prop = mk_or(&mk_eq_true(&p), &mk_eq_true(&q));
    let clause_2_prop = mk_or(&mk_not(&mk_eq_true(&q)), &mk_not(&mk_eq_true(&p)));

    let mut map = SymbolMap::new();
    map.add_symbol(0, p.clone(), Expr::prop());
    map.add_symbol(1, q.clone(), Expr::prop());
    map.add_symbol(2, prop("True"), Expr::prop());
    map.add_input_clause(1, FVarId::new(1), clause_1_prop);
    map.add_input_clause(2, FVarId::new(2), clause_2_prop);
    map.add_input_clause(4, h_p_id, p.clone());
    map.add_input_clause(5, h_q_id, q.clone());
    map.set_goal_info(goal.clone(), 4);

    let c1 = Clause {
        literals: vec![
            mk_lit(Term::Const(0), Term::Const(2), true),
            mk_lit(Term::Const(1), Term::Const(2), true),
        ],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    let c2 = Clause {
        literals: vec![
            mk_lit(Term::Const(1), Term::Const(2), false),
            mk_lit(Term::Const(0), Term::Const(2), false),
        ],
        id: 2,
        parents: vec![],
        inference: Inference::Input,
    };
    let c4 = mk_input_eq(4, Term::Const(0), Term::Const(2));
    let c5 = mk_input_eq(5, Term::Const(1), Term::Const(2));
    let c6 = Clause {
        literals: vec![
            mk_lit(Term::Const(1), Term::Const(2), false),
            mk_lit(Term::Const(2), Term::Const(2), false),
        ],
        id: 6,
        parents: vec![4, 2],
        inference: Inference::Superposition(4, 2, Position::root()),
    };
    let c7 = Clause {
        literals: vec![mk_lit(Term::Const(1), Term::Const(2), false)],
        id: 7,
        parents: vec![6],
        inference: Inference::EqualityResolution(6),
    };
    let c8 = Clause {
        literals: vec![mk_lit(Term::Const(2), Term::Const(2), false)],
        id: 8,
        parents: vec![5, 7],
        inference: Inference::Superposition(5, 7, Position::root()),
    };
    let c9 = Clause {
        literals: vec![],
        id: 9,
        parents: vec![8],
        inference: Inference::EqualityResolution(8),
    };
    let trace = ProofTrace {
        empty_clause: c9.clone(),
        clauses: vec![c1, c2, c4, c5, c6, c7, c8, c9],
    };

    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let (proof, _) = reconstructor
        .reconstruct_goal()
        .expect("atomic Iff reconstruction should succeed");

    assert_proof_has_type(
        &env,
        ctx,
        &proof,
        &goal,
        "atomic Iff proof should type-check",
    );
}
