// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the implication Tseitin rule handlers
//! (`implies`, `implies_pos`, `implies_neg1`, `implies_neg2`,
//! `not_implies1`, `not_implies2`).
//!
//! ay desugars `(=> a b)` to `(or (not a) b)` at term construction (and
//! `mk_or` sorts its arguments canonically), so these tests build the
//! implication with `TermStore::mk_implies` and derive the expected kernel
//! proposition from the stored term — whichever argument order it ended up in.
//! Every proof term is type-checked through the clean kernel; the premised
//! rules are additionally driven through resolution to `False`.

use super::{attempt_reconstruction, VariableMapping};
use ay::Sort;
use ay_core::{AletheRule, Proof, ProofId, Symbol, TermData, TermId, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker,
};

fn mk_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");

    let prop = Expr::sort(Level::zero());
    for name in ["testP", "testQ"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

struct Fixture {
    terms: TermStore,
    map: VariableMapping,
    p: TermId,
    q: TermId,
    /// `(=> p q)` as stored by ay (desugared `or`).
    imp: TermId,
    /// Imported/native `(=> p q)` retained as an application.
    native_imp: TermId,
    not_p: TermId,
    not_q: TermId,
    not_imp: TermId,
    not_native_imp: TermId,
}

fn mk_fixture() -> Fixture {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let prop = Expr::sort(Level::zero());

    let p = terms.mk_var("fvar_p", Sort::Bool);
    let q = terms.mk_var("fvar_q", Sort::Bool);
    map.register_var(
        "fvar_p",
        Expr::const_(Name::from_string("testP"), vec![]),
        prop.clone(),
    );
    map.register_var(
        "fvar_q",
        Expr::const_(Name::from_string("testQ"), vec![]),
        prop,
    );

    let imp = terms.mk_implies(p, q);
    let native_imp = terms.mk_app(Symbol::named("=>"), vec![p, q], Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    // Raw negation: `mk_not` would De Morgan the `or` away.
    let not_imp = terms.mk_not_raw(imp);
    let not_native_imp = terms.mk_not_raw(native_imp);
    Fixture {
        terms,
        map,
        p,
        q,
        imp,
        native_imp,
        not_p,
        not_q,
        not_imp,
        not_native_imp,
    }
}

fn const_(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

fn mk_not(e: Expr) -> Expr {
    Expr::app(const_("Not"), e)
}

fn mk_or(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(const_("Or"), a), b)
}

/// Kernel proposition for an ay Bool term over the fixture's atoms.
fn prop_of(terms: &TermStore, t: TermId) -> Expr {
    match terms.get(t) {
        TermData::Var(name, _) if name == "fvar_p" => const_("testP"),
        TermData::Var(name, _) if name == "fvar_q" => const_("testQ"),
        TermData::Not(inner) => mk_not(prop_of(terms, *inner)),
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
            mk_or(prop_of(terms, args[0]), prop_of(terms, args[1]))
        }
        TermData::App(Symbol::Named(name), args)
            if (name == "=>" || name == "implies") && args.len() == 2 =>
        {
            Expr::pi(
                BinderInfo::Default,
                prop_of(terms, args[0]),
                prop_of(terms, args[1]).lift(1),
            )
        }
        other => panic!("unexpected fixture term {other:?}"),
    }
}

fn or_chain(props: Vec<Expr>) -> Expr {
    let mut it = props.into_iter().rev();
    let last = it.next().expect("non-empty clause");
    it.fold(last, |acc, p| mk_or(p, acc))
}

fn assert_premiseless_type_checks(
    fx: &Fixture,
    rule: AletheRule,
    clause: Vec<TermId>,
    label: &str,
) {
    let env = mk_env();
    let expected = or_chain(clause.iter().map(|&t| prop_of(&fx.terms, t)).collect());

    let mut proof = Proof::new();
    proof.add_rule_step(rule, clause, vec![], vec![]);

    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &const_("False"));
    let proof_term = result.proof_term.unwrap_or_else(|| {
        panic!(
            "{label} should produce a proof term, stats: {:?}, error: {:?}",
            result.stats.rule_attempts, result.stats.error,
        )
    });
    assert_eq!(
        result.trust_subterm_count, 0,
        "{label} proof should have no trust sub-terms"
    );

    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let ty = tc
        .infer_type(&proof_term)
        .unwrap_or_else(|e| panic!("{label} proof term should type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "{label} proof type should be def-eq to the clause disjunction"
    );
}

/// `implies_neg1`: ⊢ {(=> p q), p}.
#[test]
fn test_implies_neg1_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesNeg1,
        vec![fx.imp, fx.p],
        "implies_neg1",
    );
}

/// `implies_neg1` with the atom before the implication literal.
#[test]
fn test_implies_neg1_atom_first_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesNeg1,
        vec![fx.p, fx.imp],
        "implies_neg1 (atom first)",
    );
}

/// `implies_neg2`: ⊢ {(=> p q), ¬q}.
#[test]
fn test_implies_neg2_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesNeg2,
        vec![fx.imp, fx.not_q],
        "implies_neg2",
    );
}

/// `implies_neg2` with the atom before the implication literal.
#[test]
fn test_implies_neg2_atom_first_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesNeg2,
        vec![fx.not_q, fx.imp],
        "implies_neg2 (atom first)",
    );
}

#[test]
fn test_implies_pos_desugared_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesPos,
        vec![fx.not_imp, fx.not_p, fx.q],
        "implies_pos (desugared)",
    );
}

#[test]
fn test_implies_pos_native_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesPos,
        vec![fx.not_native_imp, fx.not_p, fx.q],
        "implies_pos (native)",
    );
}

#[test]
fn test_implies_pos_native_word_spelling_type_checks() {
    let mut fx = mk_fixture();
    let native = fx
        .terms
        .mk_app(Symbol::named("implies"), vec![fx.p, fx.q], Sort::Bool);
    let not_native = fx.terms.mk_not_raw(native);
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesPos,
        vec![not_native, fx.not_p, fx.q],
        "implies_pos (native word spelling)",
    );
}

/// AY canonicalizes the complement of antecedent `not p` to `p`. The bridge
/// must discharge `Not (Not p) -> p` with an explicit classical kernel term,
/// not by treating the TermId simplification as definitional equality.
#[test]
fn test_implies_pos_native_double_negation_type_checks() {
    let mut fx = mk_fixture();
    let native = fx
        .terms
        .mk_app(Symbol::named("=>"), vec![fx.not_p, fx.q], Sort::Bool);
    let not_native = fx.terms.mk_not_raw(native);
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesPos,
        vec![not_native, fx.p, fx.q],
        "implies_pos native double-negation",
    );
}

#[test]
fn test_implies_neg1_native_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesNeg1,
        vec![fx.native_imp, fx.p],
        "implies_neg1 (native)",
    );
}

#[test]
fn test_implies_neg2_native_type_checks() {
    let fx = mk_fixture();
    assert_premiseless_type_checks(
        &fx,
        AletheRule::ImpliesNeg2,
        vec![fx.native_imp, fx.not_q],
        "implies_neg2 (native)",
    );
}

fn assert_rule_fails_closed(
    fx: &Fixture,
    rule: AletheRule,
    clause: Vec<TermId>,
    premises: Vec<ProofId>,
    label: &str,
) {
    let mut proof = Proof::new();
    proof.add_rule_step(rule, clause, premises, vec![]);
    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &const_("False"));
    assert!(
        result.proof_term.is_none() || result.trust_subterm_count > 0,
        "{label} must not enter the trust-free proof cache"
    );
}

/// Mutation: semantic antecedent/consequent positions are exchanged. Clause
/// order itself is free, but these are not the source implication's disjuncts.
#[test]
fn test_implies_pos_swapped_semantics_fails_closed() {
    let fx = mk_fixture();
    assert_rule_fails_closed(
        &fx,
        AletheRule::ImpliesPos,
        vec![fx.not_native_imp, fx.not_q, fx.p],
        vec![],
        "swapped-semantics implies_pos",
    );
}

/// Mutation: `implies_neg2` must use the consequent's complement, not the
/// antecedent (which would be the distinct `implies_neg1` rule).
#[test]
fn test_implies_neg2_non_complement_fails_closed() {
    let fx = mk_fixture();
    assert_rule_fails_closed(
        &fx,
        AletheRule::ImpliesNeg2,
        vec![fx.imp, fx.p],
        vec![],
        "non-consequent implies_neg2",
    );
}

/// A self-premise is absent from the prior-step cache and must become a local
/// trusted gap rather than borrowing its own asserted clause.
#[test]
fn test_implies_self_premise_cycle_fails_closed() {
    let fx = mk_fixture();
    assert_rule_fails_closed(
        &fx,
        AletheRule::Implies,
        vec![fx.not_p, fx.q],
        vec![ProofId(0)],
        "self-premise implies",
    );
}

/// A premiseless implies tautology whose clause carries no implication literal
/// must fail closed rather than fabricate a proof.
#[test]
fn test_implies_neg1_without_implication_literal_fails_closed() {
    let fx = mk_fixture();
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::ImpliesNeg1, vec![fx.p, fx.q], vec![], vec![]);
    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &const_("False"));
    assert!(
        result.proof_term.is_none() || result.trust_subterm_count > 0,
        "implies_neg1 on {{p, q}} must not yield a trust-free proof"
    );
}

/// Drive a premised proof to the empty clause and kernel-check it to `False`.
///
/// `hyps` are (fvar id, proposition) pairs registered both as ay hypotheses
/// and in the kernel local context; `neg_goal` is the negated goal the final
/// `assume` matches (its sentinel is substituted by a fresh context fvar).
fn assert_refutation_type_checks(
    fx: &mut Fixture,
    proof: &Proof,
    hyps: &[(u64, &str, Expr)],
    neg_goal: &Expr,
    label: &str,
) {
    let env = mk_env();
    let mut ctx = LocalContext::new();
    for (id, name, prop) in hyps {
        let fvar = FVarId::new(*id);
        fx.map
            .register_hypothesis(name, fvar, Expr::fvar(fvar), prop.clone());
        ctx.push_with_id(
            fvar,
            Name::from_string(name),
            prop.clone(),
            BinderInfo::Default,
        );
    }

    let result = attempt_reconstruction(proof, &fx.terms, &fx.map, neg_goal);
    let mut proof_term = result.proof_term.unwrap_or_else(|| {
        panic!(
            "{label} should produce a proof term, stats: {:?}, error: {:?}",
            result.stats.rule_attempts, result.stats.error,
        )
    });
    assert_eq!(
        result.trust_subterm_count, 0,
        "{label} proof should have no trust sub-terms"
    );
    assert!(
        result.derives_empty_clause,
        "{label} should derive the empty clause"
    );
    if let Some(sentinel_id) = result.negated_goal_fvar {
        let neg_id = FVarId::new(99);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(neg_id));
        ctx.push_with_id(
            neg_id,
            Name::from_string("h_neg_goal"),
            neg_goal.clone(),
            BinderInfo::Default,
        );
    }

    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .unwrap_or_else(|e| panic!("{label}: type-check failed: {e:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
        "{label}: expected type False, got {ty:?}"
    );
}

/// `implies`: (=> p q), p, ¬q ⊢ ⊥ via `implies` + two resolutions.
#[test]
fn test_implies_e2e_refutation_type_checks() {
    let mut fx = mk_fixture();
    let imp_prop = prop_of(&fx.terms, fx.imp);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(fx.imp, None);
    let s1 = proof.add_rule_step(AletheRule::Implies, vec![fx.not_p, fx.q], vec![s0], vec![]);
    let s2 = proof.add_assume(fx.p, None);
    let s3 = proof.add_resolution(vec![fx.q], fx.p, s1, s2);
    let s4 = proof.add_assume(fx.not_q, None);
    proof.add_resolution(vec![], fx.q, s3, s4);

    let neg_goal = mk_not(const_("testQ"));
    assert_refutation_type_checks(
        &mut fx,
        &proof,
        &[(10, "h_imp", imp_prop), (11, "h_p", const_("testP"))],
        &neg_goal,
        "implies e2e",
    );
}

#[test]
fn test_implies_native_e2e_refutation_type_checks() {
    let mut fx = mk_fixture();
    let imp_prop = prop_of(&fx.terms, fx.native_imp);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(fx.native_imp, None);
    let s1 = proof.add_rule_step(AletheRule::Implies, vec![fx.not_p, fx.q], vec![s0], vec![]);
    let s2 = proof.add_assume(fx.p, None);
    let s3 = proof.add_resolution(vec![fx.q], fx.p, s1, s2);
    let s4 = proof.add_assume(fx.not_q, None);
    proof.add_resolution(vec![], fx.q, s3, s4);

    let neg_goal = mk_not(const_("testQ"));
    assert_refutation_type_checks(
        &mut fx,
        &proof,
        &[(10, "h_native_imp", imp_prop), (11, "h_p", const_("testP"))],
        &neg_goal,
        "implies native e2e",
    );
}

/// `not_implies1`: ¬(=> p q), ¬p ⊢ ⊥.
#[test]
fn test_not_implies1_e2e_refutation_type_checks() {
    let mut fx = mk_fixture();
    let not_imp_prop = prop_of(&fx.terms, fx.not_imp);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(fx.not_imp, None);
    let s1 = proof.add_rule_step(AletheRule::NotImplies1, vec![fx.p], vec![s0], vec![]);
    let s2 = proof.add_assume(fx.not_p, None);
    proof.add_resolution(vec![], fx.p, s1, s2);

    let neg_goal = mk_not(const_("testP"));
    assert_refutation_type_checks(
        &mut fx,
        &proof,
        &[(10, "h_not_imp", not_imp_prop)],
        &neg_goal,
        "not_implies1 e2e",
    );
}

#[test]
fn test_not_implies1_native_e2e_refutation_type_checks() {
    let mut fx = mk_fixture();
    let not_imp_prop = prop_of(&fx.terms, fx.not_native_imp);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(fx.not_native_imp, None);
    let s1 = proof.add_rule_step(AletheRule::NotImplies1, vec![fx.p], vec![s0], vec![]);
    let s2 = proof.add_assume(fx.not_p, None);
    proof.add_resolution(vec![], fx.p, s1, s2);

    let neg_goal = mk_not(const_("testP"));
    assert_refutation_type_checks(
        &mut fx,
        &proof,
        &[(10, "h_not_native_imp", not_imp_prop)],
        &neg_goal,
        "not_implies1 native e2e",
    );
}

/// `not_implies2`: ¬(=> p q), q ⊢ ⊥.
#[test]
fn test_not_implies2_e2e_refutation_type_checks() {
    let mut fx = mk_fixture();
    let not_imp_prop = prop_of(&fx.terms, fx.not_imp);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(fx.not_imp, None);
    let s1 = proof.add_rule_step(AletheRule::NotImplies2, vec![fx.not_q], vec![s0], vec![]);
    let s2 = proof.add_assume(fx.q, None);
    proof.add_resolution(vec![], fx.q, s2, s1);

    let neg_goal = const_("testQ");
    assert_refutation_type_checks(
        &mut fx,
        &proof,
        &[(10, "h_not_imp", not_imp_prop)],
        &neg_goal,
        "not_implies2 e2e",
    );
}

#[test]
fn test_not_implies2_native_e2e_refutation_type_checks() {
    let mut fx = mk_fixture();
    let not_imp_prop = prop_of(&fx.terms, fx.not_native_imp);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(fx.not_native_imp, None);
    let s1 = proof.add_rule_step(AletheRule::NotImplies2, vec![fx.not_q], vec![s0], vec![]);
    let s2 = proof.add_assume(fx.q, None);
    proof.add_resolution(vec![], fx.q, s2, s1);

    let neg_goal = const_("testQ");
    assert_refutation_type_checks(
        &mut fx,
        &proof,
        &[(10, "h_not_native_imp", not_imp_prop)],
        &neg_goal,
        "not_implies2 native e2e",
    );
}
