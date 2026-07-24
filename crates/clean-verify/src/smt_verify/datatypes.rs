// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Datatypes theory checker for SMT proof verification.
//!
//! Validates algebraic datatype axiom applications:
//! - **Constructor injectivity**: `cons(a, b) = cons(c, d) -> a = c /\ b = d`
//! - **Constructor distinctness**: `cons(x, y) != nil` (different constructors never equal)
//! - **Selector reduction**: `head(cons(a, b)) = a`, `tail(cons(a, b)) = b`
//! - **Tester reduction**: `is_cons(cons(a, b)) = true`, `is_cons(nil) = false`
//! - **Acyclicity**: No term equals a proper subterm of itself
//!
//! Datatype operations are encoded as function applications in `SmtTerm`:
//! - Constructor: `App("cons", [head, tail])`, `App("nil", [])`
//! - Selector: `App("head", [term])`, `App("tail", [term])`
//! - Tester: `App("is_cons", [term])`, `App("is_nil", [term])`
//!
//! The checker works on blocking clauses (disjunctions). The conjunction of
//! the negations of clause literals forms the conflict. For the lemma to be
//! valid, this conflict must be unsatisfiable under the theory of datatypes.
//!
//! Reference: SMT-LIB Theory of Datatypes (QF_DT, QF_DTLIA divisions).

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "datatypes";

/// Check a datatypes theory lemma (blocking clause).
///
/// Tries the following axiom schemas in order:
/// 1. Constructor injectivity
/// 2. Constructor distinctness
/// 3. Selector reduction
/// 4. Tester reduction
/// 5. Acyclicity
///
/// Falls back to structural acceptance if no axiom schema matches.
pub(crate) fn check_datatypes_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "datatypes: empty clause");
    }

    // Try constructor injectivity.
    if let Some(verdict) = try_injectivity(dag, step_id, clause) {
        return verdict;
    }

    // Try constructor distinctness.
    if let Some(verdict) = try_distinctness(dag, step_id, clause) {
        return verdict;
    }

    // Try selector reduction.
    if let Some(verdict) = try_selector(dag, step_id, clause) {
        return verdict;
    }

    // Try tester reduction.
    if let Some(verdict) = try_tester(dag, step_id, clause) {
        return verdict;
    }

    // Try acyclicity.
    if let Some(verdict) = try_acyclicity(dag, step_id, clause) {
        return verdict;
    }

    // No axiom matched; structurally accept.
    structural_accept(step_id)
}

// ── Constructor Injectivity ────────────────────────────────────────────

/// Try to verify the clause as a constructor injectivity axiom.
///
/// Injectivity: if `C(a1, ..., an) = C(b1, ..., bn)`, then `ai = bi` for all i.
///
/// Blocking clause pattern:
///   `(not (= C(a1..an) C(b1..bn)))  \/  (= a1 b1)  \/  ...  \/  (= ak bk)`
///
/// The clause says: either the constructors are not equal, or the listed
/// argument equalities hold. By injectivity, if constructors are equal then
/// ALL arguments are equal, so any subset is justified. The clause need not
/// cover every argument position.
///
/// Conflict: `C(a1..an) = C(b1..bn)`, `ai != bi` for each `(= ai bi)` in clause.
/// By injectivity, `ai = bi`. Contradiction.
fn try_injectivity(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    // Look for a negated equality between two same-constructor applications.
    for &lit in clause {
        let (ctor_a, args_a, ctor_b, args_b) = match extract_negated_constructor_equality(dag, lit)
        {
            Some(x) => x,
            None => continue,
        };

        // Same constructor, same arity.
        if ctor_a != ctor_b || args_a.len() != args_b.len() {
            continue;
        }

        // At least one positive equality in the clause must pair corresponding
        // constructor argument positions. The clause need not cover all positions.
        let has_arg_eq = clause.iter().any(|&other_lit| {
            if let Some((lhs, rhs)) = dag.as_equality(other_lit) {
                (0..args_a.len()).any(|i| {
                    (lhs == args_a[i] && rhs == args_b[i]) || (lhs == args_b[i] && rhs == args_a[i])
                })
            } else {
                false
            }
        });

        if has_arg_eq {
            return Some(ok(step_id));
        }
    }

    None
}

/// Extract a negated equality between two constructor applications.
///
/// Given `not (= C(a1..an) C(b1..bn))`, returns
/// `Some((ctor_name_a, args_a, ctor_name_b, args_b))`.
fn extract_negated_constructor_equality(
    dag: &SmtProofDag,
    lit: SmtTermId,
) -> Option<(String, Vec<SmtTermId>, String, Vec<SmtTermId>)> {
    let (lhs, rhs) = dag.as_negated_equality(lit)?;
    let (name_a, args_a) = as_constructor(dag, lhs)?;
    let (name_b, args_b) = as_constructor(dag, rhs)?;
    Some((name_a, args_a, name_b, args_b))
}

// ── Constructor Distinctness ───────────────────────────────────────────

/// Try to verify the clause as a constructor distinctness axiom.
///
/// Distinctness: different constructors `C1` and `C2` are never equal.
///
/// Blocking clause pattern:
///   `(not (= C1(a1..an) C2(b1..bm)))` -- tautology by distinctness
///
/// Conflict: `C1(...) = C2(...)`. By distinctness, impossible. Contradiction.
fn try_distinctness(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_negated_equality(lit) {
            if are_distinct_constructors(dag, lhs, rhs) {
                return Some(ok(step_id));
            }
        }
    }

    None
}

/// Check if two terms are applications of different constructors.
///
/// Returns true if both are `App(name, ...)` with different names AND
/// both look like constructors (we use a heuristic: any application
/// that is not a known operator like `=`, `select`, `store`, etc.).
fn are_distinct_constructors(dag: &SmtProofDag, a: SmtTermId, b: SmtTermId) -> bool {
    let (name_a, _) = match as_constructor(dag, a) {
        Some(x) => x,
        None => return false,
    };
    let (name_b, _) = match as_constructor(dag, b) {
        Some(x) => x,
        None => return false,
    };
    name_a != name_b
}

// ── Selector Reduction ─────────────────────────────────────────────────

/// Try to verify the clause as a selector reduction axiom.
///
/// Selector reduction: `sel_i(C(a1, ..., an)) = ai` where `sel_i` is the
/// i-th selector for constructor `C`.
///
/// Blocking clause pattern:
///   `(= sel_i(C(a1..an)) ai)` -- tautology
///
/// Conflict: `sel_i(C(a1..an)) != ai`. By the selector axiom, this is
/// impossible. Contradiction.
fn try_selector(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if check_selector_reduction(dag, lhs, rhs) || check_selector_reduction(dag, rhs, lhs) {
                return Some(ok(step_id));
            }
        }
    }

    None
}

/// Check if `sel_side` is a selector applied to a constructor, and
/// `arg_side` is the corresponding constructor argument.
///
/// Validates: `sel(C(a0, a1, ..., an)) = ai` for some argument position i.
/// A selector is any non-builtin unary function applied to a constructor term.
fn check_selector_reduction(dag: &SmtProofDag, sel_side: SmtTermId, arg_side: SmtTermId) -> bool {
    // sel_side should be App(selector_name, [constructor_term]).
    let (_sel_name, sel_args) = match as_named_app(dag, sel_side) {
        Some(x) => x,
        None => return false,
    };

    // Selector takes exactly one argument (the datatype term).
    if sel_args.len() != 1 {
        return false;
    }

    // That argument should be a constructor application.
    let (_ctor_name, ctor_args) = match as_constructor(dag, sel_args[0]) {
        Some(x) => x,
        None => return false,
    };

    // Check if arg_side is one of the constructor arguments.
    ctor_args.contains(&arg_side)
}

// ── Tester Reduction ───────────────────────────────────────────────────

/// Try to verify the clause as a tester reduction axiom.
///
/// Tester reduction:
/// - `is_C(C(...)) = true`  (tester on matching constructor)
/// - `is_C(D(...)) = false`  (tester on different constructor)
///
/// Blocking clause patterns:
///
/// Positive tester on matching constructor:
///   Clause: `(is_C(C(...)))` -- always true, tautology
///   Conflict: `not is_C(C(...))` -- UNSAT
///
/// Negative tester on different constructor:
///   Clause: `(not (is_C(D(..))))` -- always true (D is not C)
///   Conflict: `is_C(D(..))` -- UNSAT
///
/// The clause may also contain `is_C(t)` or `not is_C(t)` combined
/// with equalities showing what `t` is.
fn try_tester(dag: &SmtProofDag, step_id: SmtStepId, clause: &[SmtTermId]) -> Option<StepVerdict> {
    for &lit in clause {
        // Case 1: Positive tester `is_C(C(...))` -- tautology.
        if let Some((tester_name, tested_term)) = as_tester(dag, lit) {
            if let Some((ctor_name, _)) = as_constructor(dag, tested_term) {
                let expected_ctor = tester_name.strip_prefix("is_").unwrap_or(&tester_name);
                if expected_ctor == ctor_name {
                    return Some(ok(step_id));
                }
            }
        }

        // Case 2: Negated tester `not is_C(D(...))` where C != D -- tautology.
        if let Some(inner) = as_negation(dag, lit) {
            if let Some((tester_name, tested_term)) = as_tester(dag, inner) {
                if let Some((ctor_name, _)) = as_constructor(dag, tested_term) {
                    let expected_ctor = tester_name.strip_prefix("is_").unwrap_or(&tester_name);
                    if expected_ctor != ctor_name {
                        return Some(ok(step_id));
                    }
                }
            }
        }

        // Case 3: Tester as equality with boolean constants.
        // `(= (is_C(C(...))) true)` or `(= (is_C(D(...))) false)`
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if check_tester_eq_bool(dag, lhs, rhs) || check_tester_eq_bool(dag, rhs, lhs) {
                return Some(ok(step_id));
            }
        }
    }

    None
}

/// Check if `tester_side = (is_C(term))` and `bool_side` is the expected
/// boolean constant for that tester-constructor combination.
fn check_tester_eq_bool(dag: &SmtProofDag, tester_side: SmtTermId, bool_side: SmtTermId) -> bool {
    let (tester_name, tested_term) = match as_tester(dag, tester_side) {
        Some(x) => x,
        None => return false,
    };

    let (ctor_name, _) = match as_constructor(dag, tested_term) {
        Some(x) => x,
        None => return false,
    };

    let expected_ctor = tester_name.strip_prefix("is_").unwrap_or(&tester_name);
    let expected_bool = expected_ctor == ctor_name;

    match dag.term(bool_side) {
        Some(SmtTerm::Bool(b)) => *b == expected_bool,
        _ => false,
    }
}

// ── Acyclicity ─────────────────────────────────────────────────────────

/// Try to verify the clause as an acyclicity axiom.
///
/// Acyclicity: no datatype term equals a proper subterm of itself.
/// `t != C(... t ...)` for any constructor C where t appears as an argument.
///
/// Blocking clause pattern:
///   `(not (= t C(... t ...)))` -- tautology by acyclicity
///
/// Conflict: `t = C(... t ...)` -- UNSAT because t would be a proper subterm
/// of itself, violating well-foundedness.
fn try_acyclicity(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_negated_equality(lit) {
            if is_proper_subterm(dag, lhs, rhs) || is_proper_subterm(dag, rhs, lhs) {
                return Some(ok(step_id));
            }
        }
    }

    None
}

/// Check if `needle` appears as a proper subterm of `haystack`.
///
/// A term `t` is a proper subterm of `C(a1, ..., an)` if `t` is `ai` for
/// some i, or `t` is a proper subterm of some `ai`.
fn is_proper_subterm(dag: &SmtProofDag, needle: SmtTermId, haystack: SmtTermId) -> bool {
    if needle == haystack {
        return false; // Not a *proper* subterm.
    }

    let term = match dag.term(haystack) {
        Some(t) => t,
        None => return false,
    };

    match term {
        SmtTerm::App(SmtSymbol::Named(name), args) if !is_builtin_op(name) => {
            for &arg in args {
                if arg == needle {
                    return true;
                }
                if is_proper_subterm(dag, needle, arg) {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

// ── Term Recognition Helpers ───────────────────────────────────────────

/// Known built-in SMT-LIB operator names that are NOT constructors.
const BUILTIN_OPS: &[&str] = &[
    "=", "distinct", "ite", "and", "or", "not", "=>", "xor", "+", "-", "*", "/", "div", "mod",
    "abs", "<", "<=", ">", ">=", "select", "store", "concat", "extract", "bvadd", "bvsub", "bvmul",
    "bvand", "bvor", "bvxor", "bvnot", "bvshl", "bvlshr", "bvashr", "bvult", "bvslt", "to_real",
    "to_int", "is_int",
];

/// Check if a name is a known built-in operator.
fn is_builtin_op(name: &str) -> bool {
    BUILTIN_OPS.contains(&name)
}

/// Decompose a term as a named function application.
///
/// Returns `Some((name, args))` for `App(Named(name), args)`.
fn as_named_app(dag: &SmtProofDag, id: SmtTermId) -> Option<(String, Vec<SmtTermId>)> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) => Some((name.clone(), args.clone())),
        _ => None,
    }
}

/// Decompose a term as a constructor application.
///
/// Returns `Some((ctor_name, args))` if the term is `App(name, args)` where
/// `name` is not a known built-in operator. This is a heuristic: we treat
/// any non-builtin application as a potential constructor.
fn as_constructor(dag: &SmtProofDag, id: SmtTermId) -> Option<(String, Vec<SmtTermId>)> {
    let (name, args) = as_named_app(dag, id)?;
    if is_builtin_op(&name) {
        return None;
    }
    Some((name, args))
}

/// Decompose a term as a tester application (`is_X(term)`).
///
/// Returns `Some((tester_name, tested_term))` if the term is
/// `App("is_X", [term])` where the name starts with "is_".
fn as_tester(dag: &SmtProofDag, id: SmtTermId) -> Option<(String, SmtTermId)> {
    let (name, args) = as_named_app(dag, id)?;
    if !name.starts_with("is_") || args.len() != 1 {
        return None;
    }
    Some((name, args[0]))
}

/// Extract the inner term from a negation.
fn as_negation(dag: &SmtProofDag, id: SmtTermId) -> Option<SmtTermId> {
    match dag.term(id)? {
        SmtTerm::Not(inner) => Some(*inner),
        _ => None,
    }
}

// ── Verdict Helpers ────────────────────────────────────────────────────

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

fn structural_accept(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::StructurallyAccepted,
        checker: CHECKER_NAME,
        detail: Some("datatypes: no axiom schema matched, structurally accepted".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtTerm};

    // ── Test helpers ────────────────────────────────────────────────────

    fn make_var(dag: &mut SmtProofDag, name: &str, sort: SmtSort) -> SmtTermId {
        dag.add_term(SmtTerm::Var(name.to_string(), sort))
    }

    fn make_int_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
        make_var(dag, name, SmtSort::Int)
    }

    fn make_dt_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
        make_var(dag, name, SmtSort::Named("ListType".to_string()))
    }

    fn make_app(dag: &mut SmtProofDag, name: &str, args: Vec<SmtTermId>) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named(name.to_string()), args))
    }

    fn make_cons(dag: &mut SmtProofDag, head: SmtTermId, tail: SmtTermId) -> SmtTermId {
        make_app(dag, "cons", vec![head, tail])
    }

    fn make_nil(dag: &mut SmtProofDag) -> SmtTermId {
        make_app(dag, "nil", vec![])
    }

    fn make_head(dag: &mut SmtProofDag, list: SmtTermId) -> SmtTermId {
        make_app(dag, "head", vec![list])
    }

    fn make_tail(dag: &mut SmtProofDag, list: SmtTermId) -> SmtTermId {
        make_app(dag, "tail", vec![list])
    }

    fn make_is_cons(dag: &mut SmtProofDag, term: SmtTermId) -> SmtTermId {
        make_app(dag, "is_cons", vec![term])
    }

    fn make_is_nil(dag: &mut SmtProofDag, term: SmtTermId) -> SmtTermId {
        make_app(dag, "is_nil", vec![term])
    }

    fn make_eq(dag: &mut SmtProofDag, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]))
    }

    fn make_not(dag: &mut SmtProofDag, inner: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::Not(inner))
    }

    fn make_bool(dag: &mut SmtProofDag, val: bool) -> SmtTermId {
        dag.add_term(SmtTerm::Bool(val))
    }

    fn make_int(dag: &mut SmtProofDag, val: i64) -> SmtTermId {
        dag.add_term(SmtTerm::Int(val))
    }

    // ── Constructor Injectivity Tests ───────────────────────────────────

    #[test]
    fn test_dt_injectivity_valid() {
        // cons(a, b) = cons(c, d), a != c -> contradiction
        // Blocking clause: not(= cons(a,b) cons(c,d)), (= a c)
        // Conflict: cons(a,b) = cons(c,d), a != c
        // By injectivity: a = c. Contradiction.
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");
        let c = make_int_var(&mut dag, "c");
        let d = make_dt_var(&mut dag, "d");

        let cons_ab = make_cons(&mut dag, a, b);
        let cons_cd = make_cons(&mut dag, c, d);

        let eq_cons = make_eq(&mut dag, cons_ab, cons_cd);
        let neq_cons = make_not(&mut dag, eq_cons);
        let eq_ac = make_eq(&mut dag, a, c);

        let clause = vec![neq_cons, eq_ac];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "injectivity should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_injectivity_both_args_valid() {
        // cons(a, b) = cons(c, d) -> a = c AND b = d
        // Blocking clause: not(= cons(a,b) cons(c,d)), (= a c), (= b d)
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");
        let c = make_int_var(&mut dag, "c");
        let d = make_dt_var(&mut dag, "d");

        let cons_ab = make_cons(&mut dag, a, b);
        let cons_cd = make_cons(&mut dag, c, d);

        let eq_cons = make_eq(&mut dag, cons_ab, cons_cd);
        let neq_cons = make_not(&mut dag, eq_cons);
        let eq_ac = make_eq(&mut dag, a, c);
        let eq_bd = make_eq(&mut dag, b, d);

        let clause = vec![neq_cons, eq_ac, eq_bd];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "injectivity (both args) should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_injectivity_invalid_missing_arg_eq() {
        // cons(a, b) = cons(c, d) but clause only provides (= a c), not (= b d)
        // and b != d syntactically.
        // This is still valid because injectivity gives BOTH equalities.
        // The clause only needs to cover the arguments where IDs differ.
        //
        // Actually, if the clause is: not(= cons(a,b) cons(c,d)), (= a c)
        // and b != d (different term IDs), then the injectivity check needs
        // (= b d) as well. Without it, the clause is NOT a valid injectivity
        // lemma for BOTH arguments.
        //
        // But wait -- the blocking clause is a disjunction. The injectivity
        // lemma for the FIRST argument only needs: not(= cons(a,b) cons(c,d)) \/ (= a c).
        // This is valid! It says: either the constructors differ, or a = c.
        // By injectivity, if constructors are equal then a = c. So this is valid
        // regardless of the second argument.
        //
        // Let me test the case where it genuinely shouldn't validate:
        // cons(a, b) = cons(c, d) alone (no equality disjuncts).
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");
        let c = make_int_var(&mut dag, "c");
        let d = make_dt_var(&mut dag, "d");

        let cons_ab = make_cons(&mut dag, a, b);
        let cons_cd = make_cons(&mut dag, c, d);
        let eq_cons = make_eq(&mut dag, cons_ab, cons_cd);

        // Just a positive equality -- not valid on its own.
        let clause = vec![eq_cons];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "single constructor equality should not be kernel-verified by injectivity"
        );
    }

    // ── Constructor Distinctness Tests ──────────────────────────────────

    #[test]
    fn test_dt_distinctness_valid() {
        // nil = cons(a, b) is impossible.
        // Blocking clause: not(= nil cons(a, b))
        // Conflict: nil = cons(a, b) -- UNSAT by distinctness.
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let nil = make_nil(&mut dag);
        let cons_ab = make_cons(&mut dag, a, b);

        let eq = make_eq(&mut dag, nil, cons_ab);
        let neq = make_not(&mut dag, eq);

        let clause = vec![neq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "distinctness should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_distinctness_valid_swapped() {
        // cons(a, b) = nil -- same thing, swapped.
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let cons_ab = make_cons(&mut dag, a, b);
        let nil = make_nil(&mut dag);

        let eq = make_eq(&mut dag, cons_ab, nil);
        let neq = make_not(&mut dag, eq);

        let clause = vec![neq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "distinctness (swapped) should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_distinctness_invalid_same_constructor() {
        // not(= cons(a,b) cons(c,d)) -- same constructor, not a distinctness axiom.
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");
        let c = make_int_var(&mut dag, "c");
        let d = make_dt_var(&mut dag, "d");

        let cons_ab = make_cons(&mut dag, a, b);
        let cons_cd = make_cons(&mut dag, c, d);

        let eq = make_eq(&mut dag, cons_ab, cons_cd);
        let neq = make_not(&mut dag, eq);

        // This alone is not valid by distinctness (same constructor).
        // It might be checked by injectivity if argument equalities are present.
        let clause = vec![neq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        // Should not be kernel-verified by distinctness alone.
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "same constructor should not pass distinctness"
        );
    }

    // ── Selector Reduction Tests ───────────────────────────────────────

    #[test]
    fn test_dt_selector_head_valid() {
        // head(cons(5, xs)) = 5
        // Blocking clause: (= (head (cons 5 xs)) 5)
        let mut dag = SmtProofDag::new();
        let five = make_int(&mut dag, 5);
        let xs = make_dt_var(&mut dag, "xs");

        let cons_5_xs = make_cons(&mut dag, five, xs);
        let head_cons = make_head(&mut dag, cons_5_xs);
        let eq = make_eq(&mut dag, head_cons, five);

        let clause = vec![eq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "selector head reduction should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_selector_tail_valid() {
        // tail(cons(5, xs)) = xs
        let mut dag = SmtProofDag::new();
        let five = make_int(&mut dag, 5);
        let xs = make_dt_var(&mut dag, "xs");

        let cons_5_xs = make_cons(&mut dag, five, xs);
        let tail_cons = make_tail(&mut dag, cons_5_xs);
        let eq = make_eq(&mut dag, tail_cons, xs);

        let clause = vec![eq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "selector tail reduction should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_selector_swapped_valid() {
        // 5 = head(cons(5, xs)) -- swapped sides
        let mut dag = SmtProofDag::new();
        let five = make_int(&mut dag, 5);
        let xs = make_dt_var(&mut dag, "xs");

        let cons_5_xs = make_cons(&mut dag, five, xs);
        let head_cons = make_head(&mut dag, cons_5_xs);
        let eq = make_eq(&mut dag, five, head_cons);

        let clause = vec![eq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "selector (swapped) should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_selector_invalid_wrong_arg() {
        // head(cons(5, xs)) = 7 -- wrong value
        let mut dag = SmtProofDag::new();
        let five = make_int(&mut dag, 5);
        let seven = make_int(&mut dag, 7);
        let xs = make_dt_var(&mut dag, "xs");

        let cons_5_xs = make_cons(&mut dag, five, xs);
        let head_cons = make_head(&mut dag, cons_5_xs);
        let eq = make_eq(&mut dag, head_cons, seven);

        let clause = vec![eq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "wrong selector value should not be kernel-verified"
        );
    }

    // ── Tester Reduction Tests ─────────────────────────────────────────

    #[test]
    fn test_dt_tester_positive_match_valid() {
        // is_cons(cons(a, b)) -- tautology
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let cons_ab = make_cons(&mut dag, a, b);
        let is_cons = make_is_cons(&mut dag, cons_ab);

        let clause = vec![is_cons];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "tester positive match should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_tester_negative_mismatch_valid() {
        // not is_cons(nil) -- tautology (nil is not cons)
        // But this is `not is_nil(cons(a, b))` to be more precise.
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let cons_ab = make_cons(&mut dag, a, b);
        let is_nil = make_is_nil(&mut dag, cons_ab);
        let not_is_nil = make_not(&mut dag, is_nil);

        let clause = vec![not_is_nil];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "tester negative mismatch should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_tester_eq_true_valid() {
        // (= (is_cons (cons a b)) true) -- tautology
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let cons_ab = make_cons(&mut dag, a, b);
        let is_cons = make_is_cons(&mut dag, cons_ab);
        let true_val = make_bool(&mut dag, true);
        let eq = make_eq(&mut dag, is_cons, true_val);

        let clause = vec![eq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "tester = true should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_tester_eq_false_valid() {
        // (= (is_nil (cons a b)) false) -- tautology (cons is not nil)
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let cons_ab = make_cons(&mut dag, a, b);
        let is_nil = make_is_nil(&mut dag, cons_ab);
        let false_val = make_bool(&mut dag, false);
        let eq = make_eq(&mut dag, is_nil, false_val);

        let clause = vec![eq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "tester = false (mismatch) should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_tester_eq_true_wrong_ctor_invalid() {
        // (= (is_nil (cons a b)) true) -- is_nil on cons is false, not true
        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let cons_ab = make_cons(&mut dag, a, b);
        let is_nil = make_is_nil(&mut dag, cons_ab);
        let true_val = make_bool(&mut dag, true);
        let eq = make_eq(&mut dag, is_nil, true_val);

        let clause = vec![eq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "wrong tester=true should not be kernel-verified"
        );
    }

    // ── Acyclicity Tests ───────────────────────────────────────────────

    #[test]
    fn test_dt_acyclicity_valid() {
        // not(= x cons(a, x)) -- x cannot equal a term containing x
        let mut dag = SmtProofDag::new();
        let x = make_dt_var(&mut dag, "x");
        let a = make_int_var(&mut dag, "a");

        let cons_a_x = make_cons(&mut dag, a, x);
        let eq = make_eq(&mut dag, x, cons_a_x);
        let neq = make_not(&mut dag, eq);

        let clause = vec![neq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "acyclicity should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_dt_acyclicity_valid_swapped() {
        // not(= cons(a, x) x) -- swapped sides
        let mut dag = SmtProofDag::new();
        let x = make_dt_var(&mut dag, "x");
        let a = make_int_var(&mut dag, "a");

        let cons_a_x = make_cons(&mut dag, a, x);
        let eq = make_eq(&mut dag, cons_a_x, x);
        let neq = make_not(&mut dag, eq);

        let clause = vec![neq];
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "acyclicity (swapped) should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Empty clause test ──────────────────────────────────────────────

    #[test]
    fn test_dt_empty_clause_fails() {
        let dag = SmtProofDag::new();
        let verdict = check_datatypes_lemma(&dag, SmtStepId(0), &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    // ── Full pipeline integration tests ────────────────────────────────

    #[test]
    fn test_dt_injectivity_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");
        let c = make_int_var(&mut dag, "c");
        let d = make_dt_var(&mut dag, "d");

        let cons_ab = make_cons(&mut dag, a, b);
        let cons_cd = make_cons(&mut dag, c, d);

        // Assume: cons(a,b) = cons(c,d)
        let eq_cons = make_eq(&mut dag, cons_ab, cons_cd);
        let s0 = dag.add_step(SmtProofStep::Assume(eq_cons));

        // Assume: a != c
        let eq_ac = make_eq(&mut dag, a, c);
        let neq_ac = make_not(&mut dag, eq_ac);
        let s1 = dag.add_step(SmtProofStep::Assume(neq_ac));

        // DT injectivity lemma: not(= cons(a,b) cons(c,d)), (= a c)
        let neq_cons = make_not(&mut dag, eq_cons);
        let s2 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Datatypes,
            kind: TheoryLemmaDetail::DatatypesInjectivity,
            clause: vec![neq_cons, eq_ac],
        });

        // Resolve s0 + s2 on eq_cons -> {eq_ac}
        let s3 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![eq_ac],
            premises: vec![s0, s2],
            pivot: Some(eq_cons),
        });

        // Resolve s1 + s3 on eq_ac -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s1, s3],
            pivot: Some(eq_ac),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "DT injectivity proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Datatypes),
            Some(&1)
        );
    }

    #[test]
    fn test_dt_distinctness_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let nil = make_nil(&mut dag);
        let cons_ab = make_cons(&mut dag, a, b);

        // Assume: nil = cons(a, b)
        let eq = make_eq(&mut dag, nil, cons_ab);
        let s0 = dag.add_step(SmtProofStep::Assume(eq));

        // DT distinctness lemma: not(= nil cons(a,b))
        let neq = make_not(&mut dag, eq);
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Datatypes,
            kind: TheoryLemmaDetail::DatatypesDistinctness,
            clause: vec![neq],
        });

        // Resolve s0 + s1 on eq -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(eq),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "DT distinctness proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Datatypes),
            Some(&1)
        );
    }

    #[test]
    fn test_dt_selector_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let five = make_int(&mut dag, 5);
        let xs = make_dt_var(&mut dag, "xs");

        let cons_5_xs = make_cons(&mut dag, five, xs);
        let head_cons = make_head(&mut dag, cons_5_xs);

        // Assume: head(cons(5, xs)) != 5
        let eq = make_eq(&mut dag, head_cons, five);
        let neq = make_not(&mut dag, eq);
        let s0 = dag.add_step(SmtProofStep::Assume(neq));

        // DT selector lemma: (= head(cons(5, xs)) 5)
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Datatypes,
            kind: TheoryLemmaDetail::DatatypesSelector,
            clause: vec![eq],
        });

        // Resolve s0 + s1 on eq -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(eq),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "DT selector proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Datatypes),
            Some(&1)
        );
    }

    #[test]
    fn test_dt_tester_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let a = make_int_var(&mut dag, "a");
        let b = make_dt_var(&mut dag, "b");

        let cons_ab = make_cons(&mut dag, a, b);
        let is_nil = make_is_nil(&mut dag, cons_ab);

        // Assume: is_nil(cons(a, b))  (this is false)
        let s0 = dag.add_step(SmtProofStep::Assume(is_nil));

        // DT tester lemma: not(is_nil(cons(a, b))) -- tautology (cons is not nil)
        let not_is_nil = make_not(&mut dag, is_nil);
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Datatypes,
            kind: TheoryLemmaDetail::DatatypesTester,
            clause: vec![not_is_nil],
        });

        // Resolve s0 + s1 on is_nil -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(is_nil),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "DT tester proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Datatypes),
            Some(&1)
        );
    }
}
