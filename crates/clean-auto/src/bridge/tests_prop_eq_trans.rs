// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Eq.trans from And-assumptions and mixed And-goal under Or (#2442 Phase 2).
//!
//! Covers bridge-local Eq.trans chaining from And(Eq(a,b), Eq(b,c)) assumptions
//! inside Or.elim branches, and And-goal construction under Or with mixed conjuncts.

use super::super::*;
use super::test_helpers::{make_eq, setup_env};
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use clean_kernel::Level;
use ntest::timeout;

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

fn setup_eq_prop_env() -> Environment {
    let mut env = setup_env();
    // Add propositional constructors needed by proof reconstruction
    for (name, type_) in [
        (
            "And",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        (
            "Or",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        ("True", Expr::prop()),
        ("False", Expr::prop()),
    ] {
        // Ignore errors from duplicate declarations (setup_env may already have some)
        let _ = env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        });
    }
    // Add Eq.trans : {α : Sort u} → {a b c : α} → a = b → b = c → a = c
    let _ = env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.trans"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0), // a : α
                Expr::pi(
                    BinderInfo::Implicit,
                    Expr::bvar(1), // b : α
                    Expr::pi(
                        BinderInfo::Implicit,
                        Expr::bvar(2), // c : α
                        Expr::pi(
                            BinderInfo::Default,
                            make_eq(Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)), // a = b
                            Expr::pi(
                                BinderInfo::Default,
                                make_eq(Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)), // b = c
                                make_eq(Expr::bvar(5), Expr::bvar(4), Expr::bvar(1)), // a = c
                            ),
                        ),
                    ),
                ),
            ),
        ),
    });
    env
}

// ========================================================================
// Eq.trans from And-assumption tests
// ========================================================================

#[test]
#[timeout(30000)]
fn test_or_elim_and_eq_trans_basic() {
    // Or.elim where assumption is And(Eq(a,b), Eq(b,c)) and goal is Eq(a,c).
    // h1 : Or(And(Eq(A,a,b), Eq(A,b,c)), P), h2 : P → Eq(A,a,c), goal: Eq(A,a,c)
    // Left branch:  assumption = And(Eq(a,b), Eq(b,c)) → Eq.trans (And.left bvar(0)) (And.right bvar(0))
    // Right branch: assumption = P → modus ponens with h2
    let env = setup_eq_prop_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let p = prop("P");

    let eq_ab = make_eq(a_ty.clone(), a.clone(), b.clone());
    let eq_bc = make_eq(a_ty.clone(), b.clone(), c.clone());
    let eq_ac = make_eq(a_ty.clone(), a.clone(), c.clone());
    let and_eqs = mk_and(&eq_ab, &eq_bc);
    let or_and_p = mk_or(&and_eqs, &p);
    let implies_p_eq = Expr::pi(BinderInfo::Default, p.clone(), eq_ac.clone());

    bridge.prop_hypotheses.push((FVarId::new(500), or_and_p));
    bridge
        .prop_hypotheses
        .push((FVarId::new(501), implies_p_eq));

    // Add P as a declared Prop for the environment
    let goal_class = bridge.classify_prop(&eq_ac);
    let result = bridge.build_propositional_proof(&goal_class, &eq_ac);
    assert!(
        result.is_ok(),
        "Or.elim with And(Eq,Eq) assumption should build Eq.trans: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_and_eq_trans_swapped_order() {
    // And(Eq(b,c), Eq(a,b)) with goal Eq(a,c) — components in reversed order.
    // Should still build Eq.trans by swapping: Eq.trans (And.right h) (And.left h)
    let env = setup_eq_prop_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let p = prop("P");

    let eq_ab = make_eq(a_ty.clone(), a.clone(), b.clone());
    let eq_bc = make_eq(a_ty.clone(), b.clone(), c.clone());
    let eq_ac = make_eq(a_ty.clone(), a.clone(), c.clone());
    // Swapped: Eq(b,c) first, then Eq(a,b)
    let and_eqs_swapped = mk_and(&eq_bc, &eq_ab);
    let or_and_p = mk_or(&and_eqs_swapped, &p);
    let implies_p_eq = Expr::pi(BinderInfo::Default, p.clone(), eq_ac.clone());

    bridge.prop_hypotheses.push((FVarId::new(510), or_and_p));
    bridge
        .prop_hypotheses
        .push((FVarId::new(511), implies_p_eq));

    let goal_class = bridge.classify_prop(&eq_ac);
    let result = bridge.build_propositional_proof(&goal_class, &eq_ac);
    assert!(
        result.is_ok(),
        "Or.elim with swapped And(Eq,Eq) should still build Eq.trans: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

// ========================================================================
// And-goal under Or with mixed conjuncts
// ========================================================================

#[test]
#[timeout(30000)]
fn test_or_elim_and_goal_mixed_conjuncts() {
    // Or(P, Q) with goal And(P, R) where h2 : R exists and h3 : Q → P exists.
    // Left branch:  assumption P → And(P, R): And.intro(bvar(0), h2)
    // Right branch: assumption Q → And(P, R): And.intro(h3 (bvar 0), h2)
    let env = setup_eq_prop_env();
    let mut bridge = SmtBridge::new(&env);

    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let or_pq = mk_or(&p, &q);
    let and_pr = mk_and(&p, &r);
    let implies_qp = Expr::pi(BinderInfo::Default, q.clone(), p.clone());

    bridge.prop_hypotheses.push((FVarId::new(520), or_pq));
    bridge.prop_hypotheses.push((FVarId::new(521), r.clone()));
    bridge.prop_hypotheses.push((FVarId::new(522), implies_qp));

    let goal_class = bridge.classify_prop(&and_pr);
    let result = bridge.build_propositional_proof(&goal_class, &and_pr);
    assert!(
        result.is_ok(),
        "Or.elim with mixed And goal should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_and_goal_assumption_provides_one_conjunct() {
    // Or(P, R) with goal And(P, Q) where h2 : Q and h3 : R → P exist.
    // Left branch:  assumption P → And(P, Q): And.intro(bvar(0), h2)
    // Right branch: assumption R → And(P, Q): And.intro(h3(bvar 0), h2)
    let env = setup_eq_prop_env();
    let mut bridge = SmtBridge::new(&env);

    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let or_pr = mk_or(&p, &r);
    let and_pq = mk_and(&p, &q);
    let implies_rp = Expr::pi(BinderInfo::Default, r.clone(), p.clone());

    bridge.prop_hypotheses.push((FVarId::new(530), or_pr));
    bridge.prop_hypotheses.push((FVarId::new(531), q.clone()));
    bridge.prop_hypotheses.push((FVarId::new(532), implies_rp));

    let goal_class = bridge.classify_prop(&and_pq);
    let result = bridge.build_propositional_proof(&goal_class, &and_pq);
    assert!(
        result.is_ok(),
        "Or.elim with assumption providing one And conjunct should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_and_goal_both_conjuncts_from_hypotheses() {
    // Or(P, Q) with goal And(R, S) where h2 : R, h3 : S exist.
    // Both branches succeed because And.intro uses hypothesis proofs, not the assumption.
    let env = setup_eq_prop_env();
    let mut bridge = SmtBridge::new(&env);

    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let s = Expr::const_(Name::from_string("S"), vec![]);
    let or_pq = mk_or(&p, &q);
    let and_rs = mk_and(&r, &s);

    bridge.prop_hypotheses.push((FVarId::new(540), or_pq));
    bridge.prop_hypotheses.push((FVarId::new(541), r.clone()));
    bridge.prop_hypotheses.push((FVarId::new(542), s.clone()));

    let goal_class = bridge.classify_prop(&and_rs);
    let result = bridge.build_propositional_proof(&goal_class, &and_rs);
    // Succeeds because both conjuncts R, S are provable from hypotheses directly.
    // May go through Or.elim (each branch proves And(R,S) from hypotheses with
    // assumption unused) or And.intro depending on strategy ordering.
    assert!(
        result.is_ok(),
        "And goal with both conjuncts from hypotheses should succeed: {:?}",
        result.err()
    );
}
