// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel type-check coverage for Ge/Gt arithmetic reconstruction (#2442).

use super::super::*;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, LocalContext, TypeChecker};

fn setup_arith_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_smt_bridge_nat_order_lemmas()
        .expect("SMT bridge Nat order lemmas should initialize");
    define_nat_gt(&mut env);
    env
}

fn setup_env_with_nat_consts(names: &[&str]) -> Environment {
    let mut env = setup_arith_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add Nat test constant {name}: {e}"));
    }
    env
}

fn define_nat_gt(env: &mut Environment) {
    let nat_gt_name = Name::from_string("Nat.gt");
    if env.get_const(&nat_gt_name).is_some() {
        return;
    }

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_gt_type = Expr::pi(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::pi(BinderInfo::Default, nat_ty.clone(), Expr::prop()),
    );
    let nat_gt_value = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ty,
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.lt"), vec![]),
                    Expr::bvar(0),
                ),
                Expr::bvar(1),
            ),
        ),
    );

    env.add_decl(Declaration::Definition {
        name: nat_gt_name,
        level_params: vec![],
        type_: nat_gt_type,
        value: nat_gt_value,
        is_reducible: true,
    })
    .expect("Nat.gt test definition should be valid");
}

fn make_nat_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

fn make_nat_lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), lhs),
        rhs,
    )
}

fn make_nat_ge(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.ge"), vec![]), lhs),
        rhs,
    )
}

fn make_nat_gt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.gt"), vec![]), lhs),
        rhs,
    )
}

fn assert_proof_type_checks_to_goal(
    env: &Environment,
    ctx: LocalContext,
    proof: &Expr,
    goal: &Expr,
    msg: &str,
) {
    let tc = TypeChecker::with_context(env, ctx);
    tc.check_type(proof, goal)
        .unwrap_or_else(|e| panic!("{msg}: proof should check against goal {goal:?}: {e:?}"));
}

#[test]
fn test_direct_nat_ge_proof_type_checks_against_original_goal() {
    let env = setup_arith_env();
    let mut bridge = SmtBridge::new(&env);
    let goal = make_nat_ge(Expr::nat_lit(3), Expr::nat_lit(0));

    let proof_result = bridge
        .prove(&goal)
        .expect("ground Nat >= goal should solve")
        .verified()
        .expect("ground Nat >= goal should be verified");

    assert!(
        matches!(proof_result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_le")
    );
    assert_proof_type_checks_to_goal(
        &env,
        LocalContext::new(),
        proof_result.proof_term(),
        &goal,
        "ground Nat.ge goal",
    );
}

#[test]
fn test_direct_nat_gt_proof_type_checks_against_original_goal() {
    let env = setup_arith_env();
    let mut bridge = SmtBridge::new(&env);
    let goal = make_nat_gt(Expr::nat_lit(5), Expr::nat_lit(2));

    let proof_result = bridge
        .prove(&goal)
        .expect("ground Nat > goal should solve")
        .verified()
        .expect("ground Nat > goal should be verified");

    assert!(
        matches!(proof_result.proof_step(), ProofStep::Propositional(s) if s == "arith.nat_ground_lt")
    );
    assert_proof_type_checks_to_goal(
        &env,
        LocalContext::new(),
        proof_result.proof_term(),
        &goal,
        "ground Nat.gt goal",
    );
}

#[test]
fn test_reflexive_nat_ge_proof_type_checks_against_original_goal() {
    let env = setup_env_with_nat_consts(&["n"]);
    let mut bridge = SmtBridge::new(&env);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let goal = make_nat_ge(n.clone(), n);

    let proof_result = bridge
        .prove(&goal)
        .expect("reflexive Nat >= goal should solve")
        .verified()
        .expect("reflexive Nat >= goal should be verified");

    assert!(
        matches!(proof_result.proof_step(), ProofStep::Propositional(s) if s == "arith.le_refl")
    );
    assert_proof_type_checks_to_goal(
        &env,
        LocalContext::new(),
        proof_result.proof_term(),
        &goal,
        "reflexive Nat.ge goal",
    );
}

#[test]
fn test_nat_ge_chain_proof_type_checks_against_original_goal() {
    let env = setup_env_with_nat_consts(&["x", "y", "z"]);
    let mut bridge = SmtBridge::new(&env);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    let h_xy_id = FVarId::new(960);
    let h_yz_id = FVarId::new(961);
    let h_xy = make_nat_le(x.clone(), y.clone());
    let h_yz = make_nat_le(y.clone(), z.clone());

    bridge
        .add_hypothesis_with_fvar(&h_xy, Some(h_xy_id))
        .expect("x <= y hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&h_yz, Some(h_yz_id))
        .expect("y <= z hypothesis should assert");

    let goal = make_nat_ge(z.clone(), x.clone());
    let proof_result = bridge
        .prove(&goal)
        .expect("Nat.ge chain goal should solve")
        .verified()
        .expect("Nat.ge chain goal should be verified");

    assert!(
        matches!(proof_result.proof_step(), ProofStep::Trans(_, _)),
        "expected transitivity proof step, got {:?}",
        proof_result.proof_step()
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_xy_id,
        Name::from_string("h_xy"),
        h_xy,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_yz_id,
        Name::from_string("h_yz"),
        h_yz,
        BinderInfo::Default,
    );
    assert_proof_type_checks_to_goal(
        &env,
        ctx,
        proof_result.proof_term(),
        &goal,
        "Nat.ge chain goal",
    );
}

#[test]
fn test_nat_gt_chain_proof_type_checks_against_original_goal() {
    let env = setup_env_with_nat_consts(&["x", "y", "z"]);
    let mut bridge = SmtBridge::new(&env);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    let h_xy_id = FVarId::new(962);
    let h_yz_id = FVarId::new(963);
    let h_xy = make_nat_lt(x.clone(), y.clone());
    let h_yz = make_nat_le(y.clone(), z.clone());

    bridge
        .add_hypothesis_with_fvar(&h_xy, Some(h_xy_id))
        .expect("x < y hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&h_yz, Some(h_yz_id))
        .expect("y <= z hypothesis should assert");

    let goal = make_nat_gt(z.clone(), x.clone());
    let proof_result = bridge
        .prove(&goal)
        .expect("Nat.gt chain goal should solve")
        .verified()
        .expect("Nat.gt chain goal should be verified");

    assert!(
        matches!(proof_result.proof_step(), ProofStep::Trans(_, _)),
        "expected transitivity proof step, got {:?}",
        proof_result.proof_step()
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_xy_id,
        Name::from_string("h_xy"),
        h_xy,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_yz_id,
        Name::from_string("h_yz"),
        h_yz,
        BinderInfo::Default,
    );
    assert_proof_type_checks_to_goal(
        &env,
        ctx,
        proof_result.proof_term(),
        &goal,
        "Nat.gt chain goal",
    );
}
