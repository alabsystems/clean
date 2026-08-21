// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the bounded, all-edges-used `eq_transitive` tautology handler.
//!
//! `eq_transitive` clause: {¬(a = b), ¬(b = c), (a = c)}. Reconstructs via
//! nested `Classical.em` + `Eq.trans` (with `Eq.symm` to align orientations).
//! Each proof term is type-checked through the clean kernel; one variant is
//! driven through resolution to `False`.

use super::{attempt_reconstruction, VariableMapping};
use ay::Sort;
use ay_core::{AletheRule, Proof, Symbol, TermData, TermId, TermStore};
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
    env.init_classical().expect("init_classical");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testA", "testB", "testC", "testD"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

struct Fixture {
    terms: TermStore,
    map: VariableMapping,
    a: TermId,
    b: TermId,
    c: TermId,
    d: TermId,
}

fn mk_fixture() -> Fixture {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let mut mk = |terms: &mut TermStore, var: &str, konst: &str| {
        let t = terms.mk_var(var, Sort::Int);
        map.register_var(
            var,
            Expr::const_(Name::from_string(konst), vec![]),
            int_ty.clone(),
        );
        t
    };
    let a = mk(&mut terms, "fvar_a", "testA");
    let b = mk(&mut terms, "fvar_b", "testB");
    let c = mk(&mut terms, "fvar_c", "testC");
    let d = mk(&mut terms, "fvar_d", "testD");
    Fixture {
        terms,
        map,
        a,
        b,
        c,
        d,
    }
}

/// Raw `(= l r)` with the given orientation (no `mk_eq` canonicalisation).
fn raw_eq(terms: &mut TermStore, l: TermId, r: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![l, r], Sort::Bool)
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

/// Kernel proposition for an ay term over the fixture's Int atoms.
fn prop_of(terms: &TermStore, t: TermId) -> Expr {
    match terms.get(t) {
        TermData::Var(name, _) => const_(&format!("test{}", name["fvar_".len()..].to_uppercase())),
        TermData::Not(inner) => mk_not(prop_of(terms, *inner)),
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            let u1 = Level::succ(Level::zero());
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![u1]),
                        const_("Int"),
                    ),
                    prop_of(terms, args[0]),
                ),
                prop_of(terms, args[1]),
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

fn assert_tautology_type_checks(fx: &Fixture, clause: Vec<TermId>, label: &str) {
    let env = mk_env();
    let expected = or_chain(clause.iter().map(|&t| prop_of(&fx.terms, t)).collect());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::EqTransitive, clause, vec![], vec![]);

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

/// Aligned orientation: {¬(a=b), ¬(b=c), (a=c)}.
#[test]
fn test_eq_transitive_aligned_type_checks() {
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_bc = raw_eq(&mut fx.terms, fx.b, fx.c);
    let eq_ac = raw_eq(&mut fx.terms, fx.a, fx.c);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    assert_tautology_type_checks(&fx, vec![n_ab, n_bc, eq_ac], "eq_transitive aligned");
}

/// AY permits the minimum one-edge transitivity/symmetry clause.
#[test]
fn test_eq_transitive_single_edge_type_checks() {
    let mut fx = mk_fixture();
    let eq_ba = raw_eq(&mut fx.terms, fx.b, fx.a);
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let n_ba = fx.terms.mk_not_raw(eq_ba);
    assert_tautology_type_checks(
        &fx,
        vec![n_ba, eq_ab],
        "eq_transitive single symmetric edge",
    );
}

/// Both hypotheses flipped: {¬(b=a), ¬(c=b), (a=c)} — exercises the `Eq.symm` edges.
#[test]
fn test_eq_transitive_flipped_hypotheses_type_checks() {
    let mut fx = mk_fixture();
    let eq_ba = raw_eq(&mut fx.terms, fx.b, fx.a);
    let eq_cb = raw_eq(&mut fx.terms, fx.c, fx.b);
    let eq_ac = raw_eq(&mut fx.terms, fx.a, fx.c);
    let n_ba = fx.terms.mk_not_raw(eq_ba);
    let n_cb = fx.terms.mk_not_raw(eq_cb);
    assert_tautology_type_checks(&fx, vec![n_ba, n_cb, eq_ac], "eq_transitive flipped");
}

/// Hypotheses in swapped order: {¬(b=c), ¬(a=b), (a=c)}.
#[test]
fn test_eq_transitive_swapped_hypotheses_type_checks() {
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_bc = raw_eq(&mut fx.terms, fx.b, fx.c);
    let eq_ac = raw_eq(&mut fx.terms, fx.a, fx.c);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    assert_tautology_type_checks(&fx, vec![n_bc, n_ab, eq_ac], "eq_transitive swapped");
}

/// Canonicalised `mk_eq` terms (whatever orientation ay picks) still chain.
#[test]
fn test_eq_transitive_mk_eq_terms_type_checks() {
    let mut fx = mk_fixture();
    let eq_ab = fx.terms.mk_eq(fx.a, fx.b);
    let eq_bc = fx.terms.mk_eq(fx.b, fx.c);
    let eq_ac = fx.terms.mk_eq(fx.a, fx.c);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    assert_tautology_type_checks(&fx, vec![n_ab, n_bc, eq_ac], "eq_transitive mk_eq");
}

/// Hypotheses that do not chain into the conclusion fail closed.
#[test]
fn test_eq_transitive_non_chaining_fails_closed() {
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_cd = raw_eq(&mut fx.terms, fx.c, fx.d);
    let eq_ad = raw_eq(&mut fx.terms, fx.a, fx.d);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_cd = fx.terms.mk_not_raw(eq_cd);

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqTransitive,
        vec![n_ab, n_cd, eq_ad],
        vec![],
        vec![],
    );
    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &const_("False"));
    assert!(
        result.proof_term.is_none() || result.trust_subterm_count > 0,
        "non-chaining eq_transitive must not yield a trust-free proof"
    );
}

/// A three-edge chain exercises the general (non-binary) path reconstruction.
#[test]
fn test_eq_transitive_ternary_chain_type_checks() {
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_bc = raw_eq(&mut fx.terms, fx.b, fx.c);
    let eq_cd = raw_eq(&mut fx.terms, fx.c, fx.d);
    let eq_ad = raw_eq(&mut fx.terms, fx.a, fx.d);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    let n_cd = fx.terms.mk_not_raw(eq_cd);

    assert_tautology_type_checks(
        &fx,
        vec![n_ab, n_bc, n_cd, eq_ad],
        "eq_transitive three-edge chain",
    );
}

/// A longer chain may arrive scrambled and oppositely oriented; the exact path
/// order, not clause order, determines the de Bruijn proof indices.
#[test]
fn test_eq_transitive_ternary_scrambled_type_checks() {
    let mut fx = mk_fixture();
    let eq_dc = raw_eq(&mut fx.terms, fx.d, fx.c);
    let eq_ba = raw_eq(&mut fx.terms, fx.b, fx.a);
    let eq_cb = raw_eq(&mut fx.terms, fx.c, fx.b);
    let eq_ad = raw_eq(&mut fx.terms, fx.a, fx.d);
    let n_dc = fx.terms.mk_not_raw(eq_dc);
    let n_ba = fx.terms.mk_not_raw(eq_ba);
    let n_cb = fx.terms.mk_not_raw(eq_cb);
    assert_tautology_type_checks(
        &fx,
        vec![n_dc, n_ba, n_cb, eq_ad],
        "eq_transitive scrambled three-edge chain",
    );
}

/// The strict AY rule puts its sole positive equality last. A positive literal
/// in a premise position must not enter the trust-free reconstruction cache.
#[test]
fn test_eq_transitive_positive_not_last_fails_closed() {
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_bc = raw_eq(&mut fx.terms, fx.b, fx.c);
    let eq_ac = raw_eq(&mut fx.terms, fx.a, fx.c);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqTransitive,
        vec![eq_ac, n_ab, n_bc],
        vec![],
        vec![],
    );
    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &const_("False"));
    assert!(
        result.proof_term.is_none() || result.trust_subterm_count > 0,
        "positive-not-last eq_transitive must not yield a trust-free proof"
    );
}

/// A duplicate edge is not part of AY's exact all-edges-used path authority.
#[test]
fn test_eq_transitive_duplicate_edge_fails_closed() {
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_bc = raw_eq(&mut fx.terms, fx.b, fx.c);
    let eq_ac = raw_eq(&mut fx.terms, fx.a, fx.c);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqTransitive,
        vec![n_ab, n_ab, n_bc, eq_ac],
        vec![],
        vec![],
    );
    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &const_("False"));
    assert!(
        result.proof_term.is_none() || result.trust_subterm_count > 0,
        "duplicate-edge eq_transitive must not yield a trust-free proof"
    );
}

/// A cycle has an edge outside the shortest conclusion path and is rejected.
#[test]
fn test_eq_transitive_cycle_fails_closed() {
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_bc = raw_eq(&mut fx.terms, fx.b, fx.c);
    let eq_ca = raw_eq(&mut fx.terms, fx.c, fx.a);
    let eq_ac = raw_eq(&mut fx.terms, fx.a, fx.c);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    let n_ca = fx.terms.mk_not_raw(eq_ca);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqTransitive,
        vec![n_ab, n_bc, n_ca, eq_ac],
        vec![],
        vec![],
    );
    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &const_("False"));
    assert!(
        result.proof_term.is_none() || result.trust_subterm_count > 0,
        "cyclic eq_transitive must not yield a trust-free proof"
    );
}

/// E2E: eq_transitive + assumes + resolution → kernel type-checks to `False`.
#[test]
fn test_eq_transitive_e2e_refutation_type_checks() {
    let env = mk_env();
    let mut fx = mk_fixture();
    let eq_ab = raw_eq(&mut fx.terms, fx.a, fx.b);
    let eq_bc = raw_eq(&mut fx.terms, fx.b, fx.c);
    let eq_ac = raw_eq(&mut fx.terms, fx.a, fx.c);
    let n_ab = fx.terms.mk_not_raw(eq_ab);
    let n_bc = fx.terms.mk_not_raw(eq_bc);
    let n_ac = fx.terms.mk_not_raw(eq_ac);

    let h_ab = FVarId::new(10);
    let h_bc = FVarId::new(11);
    let ab_prop = prop_of(&fx.terms, eq_ab);
    let bc_prop = prop_of(&fx.terms, eq_bc);
    let neg_goal = prop_of(&fx.terms, n_ac);
    fx.map
        .register_hypothesis("h_ab", h_ab, Expr::fvar(h_ab), ab_prop.clone());
    fx.map
        .register_hypothesis("h_bc", h_bc, Expr::fvar(h_bc), bc_prop.clone());

    let mut proof = Proof::new();
    let s0 = proof.add_rule_step(
        AletheRule::EqTransitive,
        vec![n_ab, n_bc, eq_ac],
        vec![],
        vec![],
    );
    let s1 = proof.add_assume(eq_ab, None);
    let s2 = proof.add_resolution(vec![n_bc, eq_ac], eq_ab, s0, s1);
    let s3 = proof.add_assume(eq_bc, None);
    let s4 = proof.add_resolution(vec![eq_ac], eq_bc, s2, s3);
    let s5 = proof.add_assume(n_ac, None);
    proof.add_resolution(vec![], eq_ac, s4, s5);

    let result = attempt_reconstruction(&proof, &fx.terms, &fx.map, &neg_goal);
    let mut proof_term = result.proof_term.unwrap_or_else(|| {
        panic!(
            "eq_transitive e2e should produce a proof term, stats: {:?}, error: {:?}",
            result.stats.rule_attempts, result.stats.error,
        )
    });
    assert_eq!(result.trust_subterm_count, 0, "no trust sub-terms expected");
    assert!(
        result.derives_empty_clause,
        "should derive the empty clause"
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_ab,
        Name::from_string("h_ab"),
        ab_prop,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_bc,
        Name::from_string("h_bc"),
        bc_prop,
        BinderInfo::Default,
    );
    if let Some(sentinel_id) = result.negated_goal_fvar {
        let neg_id = FVarId::new(99);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(neg_id));
        ctx.push_with_id(
            neg_id,
            Name::from_string("h_neg_goal"),
            neg_goal,
            BinderInfo::Default,
        );
    }
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .unwrap_or_else(|e| panic!("eq_transitive e2e: type-check failed: {e:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
        "eq_transitive e2e: expected type False, got {ty:?}"
    );
}
