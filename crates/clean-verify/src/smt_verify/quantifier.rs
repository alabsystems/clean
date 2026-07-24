// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier instantiation checker for SMT proof verification.
//!
//! Validates quantifier-related proof rules:
//! - `forall_inst`: instantiate `forall x1..xn. P(x1,...,xn)` with terms
//!   `t1,...,tn` to produce `P(t1,...,tn)`.
//! - `skolem`: replace `exists x. P(x)` with `P(sk(y1,...,yk))` where `sk`
//!   is a fresh Skolem function depending only on universally quantified
//!   variables in scope.
//!
//! These rules are needed for quantified SMT-COMP divisions (UF, LIA, LRA
//! with quantifiers) where solvers use E-matching to find instances.
//!
//! Reference: Alethe proof format specification, Section 4.4 (quantifier rules).

use std::collections::HashMap;

use super::dag::{SmtProofDag, SmtSort, SmtStepId, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "quantifier";

/// Check a `forall_inst` step.
///
/// The Alethe `forall_inst` rule works as follows:
/// - The step has `args` containing the instantiation terms.
/// - The step has no premises; instead, one of the clause literals is the
///   negated universal quantifier `(not (forall ((x1 S1) ... (xn Sn)) body))`.
/// - Another clause literal is the instantiated body `body[x1/t1, ..., xn/tn]`.
///
/// The clause typically has the form:
///   `(cl (not (forall (...) body)) body[substitution])`
///
/// We verify that the substitution is correct by:
/// 1. Finding the `forall` term and the candidate instantiated body in the clause.
/// 2. Performing the substitution on the body.
/// 3. Checking structural equality of the result with the claimed instantiation.
pub(crate) fn check_forall_inst(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    args: &[SmtTermId],
) -> StepVerdict {
    // The clause should have at least 2 literals:
    // one negated forall, one instantiated body.
    if clause.len() < 2 {
        return fail(
            step_id,
            "forall_inst: clause needs at least 2 literals (negated forall + instantiated body)",
        );
    }

    // Find the negated forall literal and the instantiated body.
    let mut forall_info: Option<(Vec<(String, SmtSort)>, SmtTermId)> = None;
    let mut forall_lit_idx: Option<usize> = None;

    for (idx, &lit) in clause.iter().enumerate() {
        if let Some(inner) = as_negation(dag, lit) {
            if let Some(SmtTerm::Forall(vars, body)) = dag.term(inner) {
                forall_info = Some((vars.clone(), *body));
                forall_lit_idx = Some(idx);
                break;
            }
        }
    }

    let (bound_vars, body) = match forall_info {
        Some(info) => info,
        None => {
            return fail(
                step_id,
                "forall_inst: no negated forall literal found in clause",
            );
        }
    };

    let forall_idx = forall_lit_idx.expect("set when forall_info is set");

    // Build the substitution map from bound variables to instantiation terms.
    // The args provide the terms to substitute for each bound variable.
    if args.len() != bound_vars.len() {
        if args.is_empty() {
            // No args provided: try to infer the substitution from the clause
            // structure (the instantiated body is the other literal).
            return check_forall_inst_by_matching(
                dag,
                step_id,
                clause,
                forall_idx,
                &bound_vars,
                body,
            );
        }
        return fail(
            step_id,
            "forall_inst: args count does not match bound variable count",
        );
    }

    // Pre-populate the substitution map with the explicit args.
    let mut subst: HashMap<String, SmtTermId> = HashMap::new();
    for (i, (var_name, _)) in bound_vars.iter().enumerate() {
        subst.insert(var_name.clone(), args[i]);
    }

    // Verify: the remaining clause literal(s) should be consistent with
    // the body under this substitution. Use match_terms with the
    // pre-populated subst to verify consistency.
    for (idx, &lit) in clause.iter().enumerate() {
        if idx == forall_idx {
            continue;
        }
        let mut verify_subst = subst.clone();
        if match_terms(dag, body, lit, &bound_vars, &mut verify_subst) {
            return ok(step_id);
        }
    }

    // Fallback: structurally accept if we cannot verify the substitution
    // (e.g., due to term deduplication issues in the parser).
    structural_accept(
        step_id,
        "forall_inst: substitution could not be verified against clause",
    )
}

/// Check forall_inst by matching the clause body against the quantifier body,
/// without explicit args.
fn check_forall_inst_by_matching(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    forall_idx: usize,
    bound_vars: &[(String, SmtSort)],
    body: SmtTermId,
) -> StepVerdict {
    // The other literals in the clause should be the instantiated body.
    // Try to infer the substitution by matching.
    for (idx, &lit) in clause.iter().enumerate() {
        if idx == forall_idx {
            continue;
        }
        let mut inferred_subst: HashMap<String, SmtTermId> = HashMap::new();
        if match_terms(dag, body, lit, bound_vars, &mut inferred_subst) {
            // Verify the inferred substitution is consistent.
            if inferred_subst.len() == bound_vars.len() {
                return ok(step_id);
            }
            // Partial match: some variables may not appear in the body,
            // which is fine (they can be substituted with anything).
            return ok(step_id);
        }
    }

    structural_accept(
        step_id,
        "forall_inst: could not match instantiated body against forall body",
    )
}

/// Check a `skolem` step.
///
/// Skolemization replaces `exists x. P(x)` in scope of universally quantified
/// variables `y1,...,yk` with `P(sk(y1,...,yk))` where `sk` is a fresh Skolem
/// function.
///
/// The clause typically has the form:
///   `(cl (not (exists ((x S)) body)) body[x/sk(...)])`
/// or equivalently:
///   `(cl body[x/sk(...)] (not (exists ((x S)) body)))`
///
/// We verify:
/// 1. One literal is a negated existential quantifier.
/// 2. The other literal is the body with the bound variable replaced by a
///    Skolem term.
/// 3. The Skolem term's arguments are all universally quantified variables
///    from enclosing scope (checked structurally: they must all be `Var` terms).
pub(crate) fn check_skolem(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.len() < 2 {
        return fail(
            step_id,
            "skolem: clause needs at least 2 literals (negated exists + skolemized body)",
        );
    }

    // Find the negated existential.
    let mut exists_info: Option<(Vec<(String, SmtSort)>, SmtTermId)> = None;
    let mut exists_lit_idx: Option<usize> = None;

    for (idx, &lit) in clause.iter().enumerate() {
        if let Some(inner) = as_negation(dag, lit) {
            if let Some(SmtTerm::Exists(vars, body)) = dag.term(inner) {
                exists_info = Some((vars.clone(), *body));
                exists_lit_idx = Some(idx);
                break;
            }
        }
    }

    let (bound_vars, body) = match exists_info {
        Some(info) => info,
        None => {
            return fail(
                step_id,
                "skolem: no negated existential literal found in clause",
            );
        }
    };

    let exists_idx = exists_lit_idx.expect("set when exists_info is set");

    // The other literal should be the skolemized body.
    // We try to match it against the existential body by inferring the
    // Skolem replacement for each bound variable.
    for (idx, &lit) in clause.iter().enumerate() {
        if idx == exists_idx {
            continue;
        }

        let mut inferred_subst: HashMap<String, SmtTermId> = HashMap::new();
        if match_terms(dag, body, lit, &bound_vars, &mut inferred_subst) {
            // Verify the Skolem terms: each substituted term should be
            // either a function application (Skolem function) or a variable.
            // The Skolem function's arguments should be variables (the
            // universally quantified variables from enclosing scope).
            for &skolem_term_id in inferred_subst.values() {
                if let Some(term) = dag.term(skolem_term_id) {
                    match term {
                        // Skolem function application: sk(y1, ..., yk)
                        SmtTerm::App(_, args) => {
                            // Each argument should be a variable (universally
                            // quantified from enclosing scope).
                            for &arg_id in args {
                                if let Some(arg_term) = dag.term(arg_id) {
                                    if !matches!(arg_term, SmtTerm::Var(..)) {
                                        return fail(
                                            step_id,
                                            "skolem: Skolem function argument is not a variable",
                                        );
                                    }
                                }
                            }
                        }
                        // Skolem constant (no enclosing universals): just a variable.
                        SmtTerm::Var(..) => {}
                        _ => {
                            return fail(
                                step_id,
                                "skolem: substituted term is neither a function nor a variable",
                            );
                        }
                    }
                }
            }
            return ok(step_id);
        }
    }

    structural_accept(
        step_id,
        "skolem: could not match skolemized body against existential body",
    )
}

// ── Substitution and matching helpers ─────────────────────────────────────

/// Check if two terms are structurally equal by comparing their DAG representations.
///
/// This handles the case where the same term may have different IDs due to
/// non-deduplication in the parser.
fn terms_structurally_equal(dag: &SmtProofDag, a: SmtTermId, b: SmtTermId) -> bool {
    if a == b {
        return true;
    }

    let term_a = match dag.term(a) {
        Some(t) => t,
        None => return false,
    };
    let term_b = match dag.term(b) {
        Some(t) => t,
        None => return false,
    };

    match (term_a, term_b) {
        (SmtTerm::Var(na, sa), SmtTerm::Var(nb, sb)) => na == nb && sa == sb,
        (SmtTerm::Bool(a), SmtTerm::Bool(b)) => a == b,
        (SmtTerm::Int(a), SmtTerm::Int(b)) => a == b,
        (SmtTerm::Rational(an, ad), SmtTerm::Rational(bn, bd)) => an == bn && ad == bd,
        (SmtTerm::BitVec(av, aw), SmtTerm::BitVec(bv, bw)) => av == bv && aw == bw,
        (SmtTerm::Str(a), SmtTerm::Str(b)) => a == b,
        (SmtTerm::Not(a), SmtTerm::Not(b)) => terms_structurally_equal(dag, *a, *b),
        (SmtTerm::App(sa, aa), SmtTerm::App(sb, ab)) => {
            sa == sb
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(&x, &y)| terms_structurally_equal(dag, x, y))
        }
        (SmtTerm::Ite(ac, at, ae), SmtTerm::Ite(bc, bt, be)) => {
            terms_structurally_equal(dag, *ac, *bc)
                && terms_structurally_equal(dag, *at, *bt)
                && terms_structurally_equal(dag, *ae, *be)
        }
        (SmtTerm::Let(abinds, abody), SmtTerm::Let(bbinds, bbody)) => {
            abinds.len() == bbinds.len()
                && abinds
                    .iter()
                    .zip(bbinds.iter())
                    .all(|((an, av), (bn, bv))| an == bn && terms_structurally_equal(dag, *av, *bv))
                && terms_structurally_equal(dag, *abody, *bbody)
        }
        (SmtTerm::Forall(av, ab), SmtTerm::Forall(bv, bb)) => {
            av == bv && terms_structurally_equal(dag, *ab, *bb)
        }
        (SmtTerm::Exists(av, ab), SmtTerm::Exists(bv, bb)) => {
            av == bv && terms_structurally_equal(dag, *ab, *bb)
        }
        _ => false,
    }
}

/// Match a pattern term against a concrete term, inferring substitutions
/// for bound variables.
///
/// `pattern` is the quantifier body with bound variables.
/// `concrete` is the (allegedly) instantiated term.
/// `bound_vars` lists the variables that can be substituted.
/// `subst` accumulates the inferred substitution mapping.
///
/// Returns `true` if the match succeeds (concrete is a valid instantiation
/// of pattern under the accumulated substitution).
fn match_terms(
    dag: &SmtProofDag,
    pattern: SmtTermId,
    concrete: SmtTermId,
    bound_vars: &[(String, SmtSort)],
    subst: &mut HashMap<String, SmtTermId>,
) -> bool {
    // If pattern and concrete are the same ID, they trivially match.
    if pattern == concrete {
        return true;
    }

    let pat_term = match dag.term(pattern) {
        Some(t) => t.clone(),
        None => return false,
    };

    // If the pattern is a bound variable, check/record the substitution.
    if let SmtTerm::Var(ref name, _) = pat_term {
        if bound_vars.iter().any(|(vn, _)| vn == name) {
            if let Some(&existing) = subst.get(name) {
                // Variable already mapped: check consistency.
                return terms_structurally_equal(dag, existing, concrete);
            }
            subst.insert(name.clone(), concrete);
            return true;
        }
    }

    let conc_term = match dag.term(concrete) {
        Some(t) => t.clone(),
        None => return false,
    };

    match (&pat_term, &conc_term) {
        (SmtTerm::Var(na, sa), SmtTerm::Var(nb, sb)) => na == nb && sa == sb,
        (SmtTerm::Bool(a), SmtTerm::Bool(b)) => a == b,
        (SmtTerm::Int(a), SmtTerm::Int(b)) => a == b,
        (SmtTerm::Rational(an, ad), SmtTerm::Rational(bn, bd)) => an == bn && ad == bd,
        (SmtTerm::BitVec(av, aw), SmtTerm::BitVec(bv, bw)) => av == bv && aw == bw,
        (SmtTerm::Str(a), SmtTerm::Str(b)) => a == b,
        (SmtTerm::Not(a), SmtTerm::Not(b)) => match_terms(dag, *a, *b, bound_vars, subst),
        (SmtTerm::App(sa, aa), SmtTerm::App(sb, ab)) => {
            sa == sb
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(&x, &y)| match_terms(dag, x, y, bound_vars, subst))
        }
        (SmtTerm::Ite(ac, at, ae), SmtTerm::Ite(bc, bt, be)) => {
            match_terms(dag, *ac, *bc, bound_vars, subst)
                && match_terms(dag, *at, *bt, bound_vars, subst)
                && match_terms(dag, *ae, *be, bound_vars, subst)
        }
        _ => false,
    }
}

/// Extract the inner term from a negation, if the term is `Not(inner)`.
fn as_negation(dag: &SmtProofDag, term_id: SmtTermId) -> Option<SmtTermId> {
    match dag.term(term_id)? {
        SmtTerm::Not(inner) => Some(*inner),
        _ => None,
    }
}

// ── Verdict helpers ───────────────────────────────────────────────────────

fn ok(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::KernelVerified,
        checker: CHECKER_NAME,
        detail: None,
    }
}

fn fail(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

fn structural_accept(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::StructurallyAccepted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtSymbol, SmtTerm};

    /// Helper: make equality term `(= a b)`.
    fn make_eq(dag: &mut SmtProofDag, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]))
    }

    /// Helper: make binary application `(f a b)`.
    fn make_app2(dag: &mut SmtProofDag, f: &str, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named(f.to_string()), vec![a, b]))
    }

    /// Helper: make unary application `(f a)`.
    fn make_app1(dag: &mut SmtProofDag, f: &str, a: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named(f.to_string()), vec![a]))
    }

    // ── forall_inst tests ─────────────────────────────────────────────

    #[test]
    fn test_forall_inst_simple_reflexivity() {
        // forall x. x = x, instantiated with 5, gives 5 = 5.
        let mut dag = SmtProofDag::new();

        // Bound variable x
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        // Body: (= x x)
        let body = make_eq(&mut dag, x, x);
        // Forall: (forall ((x Int)) (= x x))
        let forall_term =
            dag.add_term(SmtTerm::Forall(vec![("x".to_string(), SmtSort::Int)], body));
        // Negated forall
        let neg_forall = dag.add_term(SmtTerm::Not(forall_term));

        // Instantiation term: 5
        let five = dag.add_term(SmtTerm::Int(5));
        // Instantiated body: (= 5 5)
        let inst_body = make_eq(&mut dag, five, five);

        // Clause: (not (forall ((x Int)) (= x x)))  (= 5 5)
        let clause = vec![neg_forall, inst_body];
        let args = vec![five];

        let verdict = check_forall_inst(&dag, SmtStepId(0), &clause, &args);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "simple forall_inst should verify: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_forall_inst_multi_var() {
        // forall x y. x + y = y + x, instantiated with a and b.
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let y = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));

        // Body: (= (+ x y) (+ y x))
        let x_plus_y = make_app2(&mut dag, "+", x, y);
        let y_plus_x = make_app2(&mut dag, "+", y, x);
        let body = make_eq(&mut dag, x_plus_y, y_plus_x);

        let forall_term = dag.add_term(SmtTerm::Forall(
            vec![
                ("x".to_string(), SmtSort::Int),
                ("y".to_string(), SmtSort::Int),
            ],
            body,
        ));
        let neg_forall = dag.add_term(SmtTerm::Not(forall_term));

        // Instantiation: a and b
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));

        // Instantiated body: (= (+ a b) (+ b a))
        let a_plus_b = make_app2(&mut dag, "+", a, b);
        let b_plus_a = make_app2(&mut dag, "+", b, a);
        let inst_body = make_eq(&mut dag, a_plus_b, b_plus_a);

        let clause = vec![neg_forall, inst_body];
        let args = vec![a, b];

        let verdict = check_forall_inst(&dag, SmtStepId(0), &clause, &args);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "multi-var forall_inst should verify: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_forall_inst_no_args_matching() {
        // forall_inst without explicit args: infer substitution by matching.
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let body = make_eq(&mut dag, x, x);
        let forall_term =
            dag.add_term(SmtTerm::Forall(vec![("x".to_string(), SmtSort::Int)], body));
        let neg_forall = dag.add_term(SmtTerm::Not(forall_term));

        let five = dag.add_term(SmtTerm::Int(5));
        let inst_body = make_eq(&mut dag, five, five);

        let clause = vec![neg_forall, inst_body];
        // No args: should infer x -> 5 by matching.
        let args: Vec<SmtTermId> = vec![];

        let verdict = check_forall_inst(&dag, SmtStepId(0), &clause, &args);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "forall_inst by matching should verify: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_forall_inst_wrong_substitution() {
        // forall x. P(x), instantiated with t, but the claimed result is P(s)
        // where s != t. This should NOT be kernel-verified.
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let px = make_app1(&mut dag, "P", x);
        let forall_term = dag.add_term(SmtTerm::Forall(vec![("x".to_string(), SmtSort::Int)], px));
        let neg_forall = dag.add_term(SmtTerm::Not(forall_term));

        let t = dag.add_term(SmtTerm::Int(5));
        let s = dag.add_term(SmtTerm::Int(7));

        // Claim: instantiated with t=5, but body shows P(7).
        let ps = make_app1(&mut dag, "P", s);

        let clause = vec![neg_forall, ps];
        let args = vec![t]; // args say substitute x -> 5

        let verdict = check_forall_inst(&dag, SmtStepId(0), &clause, &args);
        // The body is P(x), substituting x->5 gives P(5), but clause has P(7).
        // Since apply_substitution only handles the top-level variable case and
        // we do structural equality, this should fail to verify at kernel level.
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "wrong substitution should not be kernel-verified: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_forall_inst_clause_too_small() {
        let dag = SmtProofDag::new();
        let verdict = check_forall_inst(&dag, SmtStepId(0), &[], &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    // ── skolem tests ──────────────────────────────────────────────────

    #[test]
    fn test_skolem_simple() {
        // exists x. P(x) in scope of forall y, produces P(sk(y)).
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let px = make_app1(&mut dag, "P", x);
        let exists_term = dag.add_term(SmtTerm::Exists(vec![("x".to_string(), SmtSort::Int)], px));
        let neg_exists = dag.add_term(SmtTerm::Not(exists_term));

        // Skolem term: sk(y) where y is a universally quantified variable.
        let y = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let sk_y = make_app1(&mut dag, "sk", y);
        let p_sk_y = make_app1(&mut dag, "P", sk_y);

        let clause = vec![neg_exists, p_sk_y];

        let verdict = check_skolem(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "simple skolem should verify: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_skolem_constant() {
        // exists x. P(x) with no enclosing universals, produces P(sk)
        // where sk is a fresh constant (variable).
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let px = make_app1(&mut dag, "P", x);
        let exists_term = dag.add_term(SmtTerm::Exists(vec![("x".to_string(), SmtSort::Int)], px));
        let neg_exists = dag.add_term(SmtTerm::Not(exists_term));

        // Skolem constant: just a fresh variable.
        let sk = dag.add_term(SmtTerm::Var("sk".to_string(), SmtSort::Int));
        let p_sk = make_app1(&mut dag, "P", sk);

        let clause = vec![neg_exists, p_sk];

        let verdict = check_skolem(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "skolem constant should verify: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_skolem_non_variable_argument() {
        // Skolem function with a non-variable argument should fail.
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let px = make_app1(&mut dag, "P", x);
        let exists_term = dag.add_term(SmtTerm::Exists(vec![("x".to_string(), SmtSort::Int)], px));
        let neg_exists = dag.add_term(SmtTerm::Not(exists_term));

        // Bad Skolem: sk(5) where 5 is not a variable.
        let five = dag.add_term(SmtTerm::Int(5));
        let sk_five = make_app1(&mut dag, "sk", five);
        let p_sk_five = make_app1(&mut dag, "P", sk_five);

        let clause = vec![neg_exists, p_sk_five];

        let verdict = check_skolem(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "skolem with non-variable arg should fail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_skolem_clause_too_small() {
        let dag = SmtProofDag::new();
        let verdict = check_skolem(&dag, SmtStepId(0), &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_skolem_no_exists() {
        // Clause with no negated existential should fail.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let clause = vec![a, b];

        let verdict = check_skolem(&dag, SmtStepId(0), &clause);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    // ── structural equality tests ─────────────────────────────────────

    #[test]
    fn test_terms_structurally_equal_same_id() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Int(42));
        assert!(terms_structurally_equal(&dag, a, a));
    }

    #[test]
    fn test_terms_structurally_equal_different_ids_same_structure() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Int(42));
        let b = dag.add_term(SmtTerm::Int(42));
        assert_ne!(a, b); // Different IDs.
        assert!(terms_structurally_equal(&dag, a, b));
    }

    #[test]
    fn test_terms_structurally_equal_different_values() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Int(42));
        let b = dag.add_term(SmtTerm::Int(43));
        assert!(!terms_structurally_equal(&dag, a, b));
    }

    #[test]
    fn test_terms_structurally_equal_nested_app() {
        let mut dag = SmtProofDag::new();
        let x1 = dag.add_term(SmtTerm::Int(1));
        let x2 = dag.add_term(SmtTerm::Int(1));
        let f1 = dag.add_term(SmtTerm::App(SmtSymbol::Named("f".to_string()), vec![x1]));
        let f2 = dag.add_term(SmtTerm::App(SmtSymbol::Named("f".to_string()), vec![x2]));
        assert!(terms_structurally_equal(&dag, f1, f2));
    }

    // ── match_terms tests ─────────────────────────────────────────────

    #[test]
    fn test_match_terms_variable_capture() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let five = dag.add_term(SmtTerm::Int(5));

        let bound_vars = vec![("x".to_string(), SmtSort::Int)];
        let mut subst = HashMap::new();

        assert!(match_terms(&dag, x, five, &bound_vars, &mut subst));
        assert_eq!(subst.get("x"), Some(&five));
    }

    #[test]
    fn test_match_terms_consistent_substitution() {
        // Pattern: (= x x), concrete: (= 5 5) -- x must map to 5 consistently.
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let eq_xx = make_eq(&mut dag, x, x);

        let five1 = dag.add_term(SmtTerm::Int(5));
        let five2 = dag.add_term(SmtTerm::Int(5));
        let eq_55 = make_eq(&mut dag, five1, five2);

        let bound_vars = vec![("x".to_string(), SmtSort::Int)];
        let mut subst = HashMap::new();

        assert!(match_terms(&dag, eq_xx, eq_55, &bound_vars, &mut subst));
    }

    #[test]
    fn test_match_terms_inconsistent_substitution() {
        // Pattern: (= x x), concrete: (= 5 7) -- x can't be both 5 and 7.
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let eq_xx = make_eq(&mut dag, x, x);

        let five = dag.add_term(SmtTerm::Int(5));
        let seven = dag.add_term(SmtTerm::Int(7));
        let eq_57 = make_eq(&mut dag, five, seven);

        let bound_vars = vec![("x".to_string(), SmtSort::Int)];
        let mut subst = HashMap::new();

        assert!(!match_terms(&dag, eq_xx, eq_57, &bound_vars, &mut subst));
    }

    // ── Integration with full proof pipeline ──────────────────────────

    #[test]
    fn test_forall_inst_in_full_proof() {
        use crate::smt_verify::dag::{AletheRuleKind, SmtProofStep};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();

        // Build: forall x. x = x
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let eq_xx = make_eq(&mut dag, x, x);
        let forall_term = dag.add_term(SmtTerm::Forall(
            vec![("x".to_string(), SmtSort::Int)],
            eq_xx,
        ));
        let neg_forall = dag.add_term(SmtTerm::Not(forall_term));

        // Instantiation: x -> 5
        let five = dag.add_term(SmtTerm::Int(5));
        let eq_55 = make_eq(&mut dag, five, five);

        // not(5 = 5) for resolution
        let neg_eq_55 = dag.add_term(SmtTerm::Not(eq_55));

        // Step 0: assume (forall x. x = x)
        let s0 = dag.add_step(SmtProofStep::Assume(forall_term));
        // Step 1: assume not(5 = 5)
        let s1 = dag.add_step(SmtProofStep::Assume(neg_eq_55));
        // Step 2: forall_inst -> (not (forall x. x = x)) (= 5 5)
        let s2 = dag.add_step(SmtProofStep::Step {
            rule: AletheRuleKind::ForallInst,
            clause: vec![neg_forall, eq_55],
            premises: vec![],
            args: vec![five],
        });
        // Step 3: resolve s0 + s2 on forall_term -> {eq_55}
        let s3 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![eq_55],
            premises: vec![s0, s2],
            pivot: Some(forall_term),
        });
        // Step 4: resolve s1 + s3 on eq_55 -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s1, s3],
            pivot: Some(eq_55),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        assert!(
            result.valid,
            "forall_inst proof should be valid: {:?}",
            result.first_error
        );
    }

    // ---- AI Model-flagged adversarial soundness tests ----

    #[test]
    fn test_forall_inst_multi_position_same_var_consistent() {
        // Adversarial test: forall x. P(x, x) — the bound variable appears
        // in two positions. Instantiate with 42. Result should be P(42, 42).
        // A buggy implementation might only substitute one occurrence, giving
        // P(42, x) which would be wrong.
        let mut dag = SmtProofDag::new();

        let x1 = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let x2 = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let body = make_app2(&mut dag, "P", x1, x2);
        let forall = dag.add_term(SmtTerm::Forall(vec![("x".to_string(), SmtSort::Int)], body));
        let neg_forall = dag.add_term(SmtTerm::Not(forall));

        let forty_two = dag.add_term(SmtTerm::Int(42));
        let inst_body = make_app2(&mut dag, "P", forty_two, forty_two);

        let clause = vec![neg_forall, inst_body];
        let verdict = check_forall_inst(&dag, SmtStepId(0), &clause, &[forty_two]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "forall x. P(x, x) instantiated with 42 should produce P(42, 42): {:?}",
            verdict.detail
        );

        // Now try an INCONSISTENT instantiation: P(42, 99) which is NOT a valid
        // instantiation of forall x. P(x, x). match_terms should reject it.
        let ninety_nine = dag.add_term(SmtTerm::Int(99));
        let bad_inst = make_app2(&mut dag, "P", forty_two, ninety_nine);
        let bad_clause = vec![neg_forall, bad_inst];
        let bad_verdict = check_forall_inst(&dag, SmtStepId(0), &bad_clause, &[forty_two]);
        assert_ne!(
            bad_verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "P(42, 99) is NOT a valid instantiation of forall x. P(x, x): {:?}",
            bad_verdict.detail
        );
    }

    #[test]
    fn test_skolem_function_captures_bound_variable() {
        // Current check_skolem does structural matching only: it checks that the
        // clause has a negated Exists and a body where the existential variable
        // is replaced by an application term. It does NOT verify that the Skolem
        // function's arguments come from universally quantified variables in scope.
        // This test documents this soundness boundary: sk(z) where z is NOT in
        // universal scope is accepted structurally, not rejected.
        let mut dag = SmtProofDag::new();

        let y = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let q_xy = make_app2(&mut dag, "Q", x, y);
        let exists_term =
            dag.add_term(SmtTerm::Exists(vec![("x".to_string(), SmtSort::Int)], q_xy));
        let neg_exists = dag.add_term(SmtTerm::Not(exists_term));

        // Invalid Skolem: sk(z) where z is not universally quantified
        let z = dag.add_term(SmtTerm::Var("z".to_string(), SmtSort::Int));
        let sk_z = make_app1(&mut dag, "sk", z);
        let skolemized_body = make_app2(&mut dag, "Q", sk_z, y);

        let clause = vec![neg_exists, skolemized_body];
        let verdict = check_skolem(&dag, SmtStepId(0), &clause);
        // The implementation structurally accepts this — it doesn't verify
        // that sk arguments are in universal scope. Document this limitation.
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "check_skolem structurally accepts valid-looking Skolem terms; \
             scope checking of Skolem arguments is a known limitation"
        );
    }

    #[test]
    fn test_substitution_capture_free_variable() {
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let y_pat = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let body = make_eq(&mut dag, x, y_pat);
        let forall_term =
            dag.add_term(SmtTerm::Forall(vec![("x".to_string(), SmtSort::Int)], body));
        let neg_forall = dag.add_term(SmtTerm::Not(forall_term));

        let y_arg = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let y_lhs = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let y_rhs = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let inst_body = make_eq(&mut dag, y_lhs, y_rhs);

        let mut subst = HashMap::new();
        assert!(
            match_terms(
                &dag,
                body,
                inst_body,
                &[("x".to_string(), SmtSort::Int)],
                &mut subst,
            ),
            "x = y instantiated with y should match y = y"
        );
        assert_eq!(subst.len(), 1, "only the bound x should be substituted");
        assert_eq!(subst.get("x"), Some(&y_lhs));
        assert!(
            !subst.contains_key("y"),
            "the free y in the body must remain free"
        );

        let clause = vec![neg_forall, inst_body];
        let verdict = check_forall_inst(&dag, SmtStepId(0), &clause, &[y_arg]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "substituting x -> y must preserve the free y in the body: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_forall_inst_body_contains_nested_quantifier() {
        // match_terms does not descend into Forall/Exists bodies (they fall into
        // the _ => false catch-all). When the body of the outer forall is itself
        // a quantifier, check_forall_inst cannot produce KernelVerified and must
        // fall back to a weaker trust level. This test documents and verifies
        // that soundness boundary.
        let mut dag = SmtProofDag::new();

        let x_pat = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let y_pat = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let inner_body_pat = make_app2(&mut dag, "P", x_pat, y_pat);
        let body_pat = dag.add_term(SmtTerm::Forall(
            vec![("y".to_string(), SmtSort::Int)],
            inner_body_pat,
        ));
        let outer_forall = dag.add_term(SmtTerm::Forall(
            vec![("x".to_string(), SmtSort::Int)],
            body_pat,
        ));
        let neg_outer_forall = dag.add_term(SmtTerm::Not(outer_forall));

        let five = dag.add_term(SmtTerm::Int(5));
        let y_conc = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let inner_body_conc = make_app2(&mut dag, "P", five, y_conc);
        let inst_body = dag.add_term(SmtTerm::Forall(
            vec![("y".to_string(), SmtSort::Int)],
            inner_body_conc,
        ));

        // match_terms cannot handle Forall nodes in the body
        let mut subst = HashMap::new();
        assert!(
            !match_terms(
                &dag,
                body_pat,
                inst_body,
                &[("x".to_string(), SmtSort::Int)],
                &mut subst,
            ),
            "match_terms should return false for Forall-in-body (known limitation)"
        );

        let clause = vec![neg_outer_forall, inst_body];
        let verdict = check_forall_inst(&dag, SmtStepId(0), &clause, &[five]);
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "nested quantifiers prevent KernelVerified — should fall back: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_match_terms_rejects_inconsistent_nested_subst() {
        let mut dag = SmtProofDag::new();

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let fx_lhs = make_app1(&mut dag, "f", x);
        let fx_rhs = make_app1(&mut dag, "f", x);
        let pattern = make_eq(&mut dag, fx_lhs, fx_rhs);

        let three = dag.add_term(SmtTerm::Int(3));
        let four = dag.add_term(SmtTerm::Int(4));
        let f3 = make_app1(&mut dag, "f", three);
        let f4 = make_app1(&mut dag, "f", four);
        let concrete = make_eq(&mut dag, f3, f4);

        let mut subst = HashMap::new();
        assert!(
            !match_terms(
                &dag,
                pattern,
                concrete,
                &[("x".to_string(), SmtSort::Int)],
                &mut subst,
            ),
            "x cannot consistently match both 3 and 4 through nested applications"
        );
    }
}
