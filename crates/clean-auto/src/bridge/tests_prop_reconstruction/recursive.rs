// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursive Or.elim and nested-assumption coverage for propositional proofs.

use super::*;

#[test]
#[timeout(30000)]
fn test_or_elim_with_recursive_and_goal() {
    // Or.elim where the goal requires recursive And decomposition (#2442 Phase 2).
    // h1 : P ∨ P, goal: P ∧ P
    // Left branch:  assumption P -> And(P, P) -> recursive: And.intro(bvar 0, bvar 0)
    // Right branch: assumption P -> And(P, P) -> recursive: And.intro(bvar 0, bvar 0)
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let or_pp = mk_or(&p, &p);
    let and_pp = mk_and(&p, &p);

    bridge.prop_hypotheses.push((FVarId::new(210), or_pp));

    let goal_class = bridge.classify_prop(&and_pp);
    let result = bridge.build_propositional_proof(&goal_class, &and_pp);
    assert!(
        result.is_ok(),
        "Or.elim with recursive And goal should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("recursive And goal should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_recursive_or_goal() {
    // Or.elim where the goal requires recursive Or decomposition (#2442 Phase 2).
    // h1 : P ∨ Q, goal: Q ∨ P (swap disjuncts)
    // Left branch:  assumption P -> Or(Q, P) -> recursive: Or.inr(bvar 0)
    // Right branch: assumption Q -> Or(Q, P) -> recursive: Or.inl(bvar 0)
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let or_pq = mk_or(&p, &q);
    let or_qp = mk_or(&q, &p);

    bridge.prop_hypotheses.push((FVarId::new(220), or_pq));

    let goal_class = bridge.classify_prop(&or_qp);
    let result = bridge.build_propositional_proof(&goal_class, &or_qp);
    assert!(
        result.is_ok(),
        "Or.elim with recursive Or goal (disjunct swap) should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("recursive Or goal should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_and_decomposition_assumption() {
    // Or.elim where assumption is A ∧ B and goal matches a conjunct.
    // Setup: h1 : Or(And(P, Q), R), goal: P
    // Left branch:  assumption = P ∧ Q -> And.left (bvar 0) -> P
    // Right branch: assumption = R -> no match -> fall through to absurd etc.
    // For right branch to work, add h2 : R -> P
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let and_pq = mk_and(&p, &q);
    let or_andpq_r = mk_or(&and_pq, &r);
    let implies_rp = Expr::pi(BinderInfo::Default, r.clone(), p.clone());

    bridge.prop_hypotheses.push((FVarId::new(110), or_andpq_r));
    bridge.prop_hypotheses.push((FVarId::new(111), implies_rp));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Or.elim with And decomposition assumption should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("And decomposition branch should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_nested_or_assumption_decomposition() {
    // Or.elim where the assumption itself is Or(A, B), requiring nested Or.rec (#2442 Phase 2).
    // h1 : Or(Or(P, Q), R), h2 : R -> P, h3 : Q -> P, goal: P
    //
    // Outer Or.elim on h1:
    //   Left branch: assumption = Or(P, Q)
    //     -> Inner Or.rec on assumption:
    //       Left inner:  assumption P -> goal P -> bvar(0) (direct match)
    //       Right inner: assumption Q -> goal P -> assumption_modus_ponens with h3
    //   Right branch: assumption = R
    //     -> assumption_modus_ponens with h2
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let or_pq = mk_or(&p, &q);
    let or_orpq_r = mk_or(&or_pq, &r);
    let implies_rp = Expr::pi(BinderInfo::Default, r.clone(), p.clone());
    let implies_qp = Expr::pi(BinderInfo::Default, q.clone(), p.clone());

    bridge.prop_hypotheses.push((FVarId::new(300), or_orpq_r));
    bridge.prop_hypotheses.push((FVarId::new(301), implies_rp));
    bridge.prop_hypotheses.push((FVarId::new(302), implies_qp));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Or.elim with nested Or assumption decomposition should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("nested Or assumption should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}
