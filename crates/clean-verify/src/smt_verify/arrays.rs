// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arrays theory checker for SMT proof verification.
//!
//! Validates array axiom applications:
//! - **Read-over-write (select-store)**: `select(store(a, i, v), i) = v`
//! - **Read-over-write-other**: `i != j -> select(store(a, i, v), j) = select(a, j)`
//! - **Extensionality**: `(forall i. select(a, i) = select(b, i)) -> a = b`
//!
//! Array operations are encoded as `App("select", [array, index])` and
//! `App("store", [array, index, value])` in the `SmtTerm` representation.
//!
//! Reference: SMT-LIB Theory of Arrays (QF_AX, QF_ALIA, QF_ABV divisions).

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "arrays";

/// Check an array theory lemma (blocking clause).
///
/// The clause is a valid disjunction (blocking clause). For the lemma to be
/// valid, the conjunction of the negations of the clause literals must be
/// unsatisfiable under the theory of arrays.
///
/// Tries the following axiom schemas in order:
/// 1. Read-over-write (same index): `select(store(a, i, v), i) = v`
/// 2. Read-over-write (different index): `i != j -> select(store(a, i, v), j) = select(a, j)`
/// 3. Extensionality: `a != b -> exists k. select(a, k) != select(b, k)`
///
/// Falls back to structural acceptance if no axiom schema matches.
pub(crate) fn check_arrays_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "arrays: empty clause");
    }

    // Try read-over-write (same index).
    if let Some(verdict) = try_read_over_write_same(dag, step_id, clause) {
        return verdict;
    }

    // Try read-over-write (different index).
    if let Some(verdict) = try_read_over_write_other(dag, step_id, clause) {
        return verdict;
    }

    // Try extensionality.
    if let Some(verdict) = try_extensionality(dag, step_id, clause) {
        return verdict;
    }

    // No axiom matched; structurally accept.
    structural_accept(step_id)
}

/// Check a `ReadOverWritePos` rule step (same-index read-over-write).
///
/// Expected clause form:
///   `(cl (not (= i j)) (= (select (store a i v) j) v))`
/// or the single-literal form when index equality is asserted:
///   `(cl (= (select (store a i v) i) v))`
pub(crate) fn check_read_over_write_pos(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "row_pos: empty clause");
    }

    // Try the common form: single literal (= (select (store a i v) i) v).
    if clause.len() == 1 {
        if let Some((lhs, rhs)) = dag.as_equality(clause[0]) {
            if check_select_store_same_index(dag, lhs, rhs)
                || check_select_store_same_index(dag, rhs, lhs)
            {
                return ok(step_id);
            }
        }
    }

    // Two-literal form: (not (= i j)), (= (select (store a i v) j) v).
    if clause.len() == 2 {
        // Find the negated equality (index condition) and the positive equality.
        let (neg_eq_lit, pos_eq_lit) = if dag.as_negated_equality(clause[0]).is_some() {
            (clause[0], clause[1])
        } else if dag.as_negated_equality(clause[1]).is_some() {
            (clause[1], clause[0])
        } else {
            return fail(step_id, "row_pos: expected negated equality literal");
        };

        if let Some((i, j)) = dag.as_negated_equality(neg_eq_lit) {
            if let Some((lhs, rhs)) = dag.as_equality(pos_eq_lit) {
                // Check: select(store(a, i, v), j) = v with i, j from the negated eq.
                if check_select_store_with_indices(dag, lhs, rhs, i, j)
                    || check_select_store_with_indices(dag, rhs, lhs, i, j)
                    || check_select_store_with_indices(dag, lhs, rhs, j, i)
                    || check_select_store_with_indices(dag, rhs, lhs, j, i)
                {
                    return ok(step_id);
                }
            }
        }
    }

    // Didn't match expected pattern; try generic check.
    if let Some(verdict) = try_read_over_write_same(dag, step_id, clause) {
        return verdict;
    }

    structural_accept(step_id)
}

/// Check a `ReadOverWriteNeg` rule step (different-index read-over-write).
///
/// Expected clause form:
///   `(cl (= i j) (= (select (store a i v) j) (select a j)))`
pub(crate) fn check_read_over_write_neg(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "row_neg: empty clause");
    }

    // Two-literal form: (= i j), (= (select (store a i v) j) (select a j)).
    if clause.len() == 2 {
        let (eq_lit, other_lit) = if dag.as_equality(clause[0]).is_some()
            && !is_select_or_store_equality(dag, clause[0])
        {
            (clause[0], clause[1])
        } else if dag.as_equality(clause[1]).is_some()
            && !is_select_or_store_equality(dag, clause[1])
        {
            (clause[1], clause[0])
        } else {
            // Both might be array equalities; try generic.
            if let Some(verdict) = try_read_over_write_other(dag, step_id, clause) {
                return verdict;
            }
            return structural_accept(step_id);
        };

        if let Some((i, j)) = dag.as_equality(eq_lit) {
            if let Some((lhs, rhs)) = dag.as_equality(other_lit) {
                if check_row_other_with_indices(dag, lhs, rhs, i, j)
                    || check_row_other_with_indices(dag, rhs, lhs, i, j)
                    || check_row_other_with_indices(dag, lhs, rhs, j, i)
                    || check_row_other_with_indices(dag, rhs, lhs, j, i)
                {
                    return ok(step_id);
                }
            }
        }
    }

    // Try generic different-index check.
    if let Some(verdict) = try_read_over_write_other(dag, step_id, clause) {
        return verdict;
    }

    structural_accept(step_id)
}

/// Check an extensionality rule step.
///
/// Expected clause form:
///   `(cl (= a b) (not (= (select a k) (select b k))))`
/// meaning: either the arrays are equal, or there exists a witness index k
/// where they differ.
pub(crate) fn check_extensionality(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.len() != 2 {
        return fail(step_id, "extensionality: expected exactly 2 literals");
    }

    // Find the array equality and the negated select equality.
    for perm in &[(0, 1), (1, 0)] {
        let arr_eq_lit = clause[perm.0];
        let sel_neq_lit = clause[perm.1];

        if let Some((a, b)) = dag.as_equality(arr_eq_lit) {
            if let Some((sel_a, sel_b)) = dag.as_negated_equality(sel_neq_lit) {
                // Check: sel_a = select(a, k), sel_b = select(b, k)
                // (or vice versa).
                if check_ext_witness(dag, a, b, sel_a, sel_b)
                    || check_ext_witness(dag, a, b, sel_b, sel_a)
                    || check_ext_witness(dag, b, a, sel_a, sel_b)
                    || check_ext_witness(dag, b, a, sel_b, sel_a)
                {
                    return ok(step_id);
                }
            }
        }
    }

    // Try the generic extensionality check.
    if let Some(verdict) = try_extensionality(dag, step_id, clause) {
        return verdict;
    }

    structural_accept(step_id)
}

// ── Array term recognition helpers ──────────────────────────────────────

/// Decompose `select(array, index)` from a term.
///
/// Returns `Some((array, index))` if the term is `App("select", [array, index])`.
fn as_select(dag: &SmtProofDag, id: SmtTermId) -> Option<(SmtTermId, SmtTermId)> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Decompose `store(array, index, value)` from a term.
///
/// Returns `Some((array, index, value))` if the term is
/// `App("store", [array, index, value])`.
fn as_store(dag: &SmtProofDag, id: SmtTermId) -> Option<(SmtTermId, SmtTermId, SmtTermId)> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "store" && args.len() == 3 => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

/// Check if an equality literal involves select or store terms.
fn is_select_or_store_equality(dag: &SmtProofDag, lit: SmtTermId) -> bool {
    if let Some((lhs, rhs)) = dag.as_equality(lit) {
        as_select(dag, lhs).is_some()
            || as_select(dag, rhs).is_some()
            || as_store(dag, lhs).is_some()
            || as_store(dag, rhs).is_some()
    } else {
        false
    }
}

// ── Read-over-write (same index) ────────────────────────────────────────

/// Check: `lhs = select(store(a, i, v), i)` and `rhs = v`.
fn check_select_store_same_index(
    dag: &SmtProofDag,
    select_side: SmtTermId,
    value_side: SmtTermId,
) -> bool {
    if let Some((store_term, sel_idx)) = as_select(dag, select_side) {
        if let Some((_arr, store_idx, store_val)) = as_store(dag, store_term) {
            return sel_idx == store_idx && value_side == store_val;
        }
    }
    false
}

/// Check select(store(a, i, v), j) = v where i and j are known equal.
fn check_select_store_with_indices(
    dag: &SmtProofDag,
    select_side: SmtTermId,
    value_side: SmtTermId,
    store_idx: SmtTermId,
    sel_idx: SmtTermId,
) -> bool {
    if let Some((store_term, actual_sel_idx)) = as_select(dag, select_side) {
        if let Some((_arr, actual_store_idx, store_val)) = as_store(dag, store_term) {
            // The indices from the negated equality should match the actual indices.
            let idx_match = (actual_store_idx == store_idx && actual_sel_idx == sel_idx)
                || (actual_store_idx == sel_idx && actual_sel_idx == store_idx);
            return idx_match && value_side == store_val;
        }
    }
    false
}

/// Try to verify the clause as a read-over-write-same-index axiom instance.
///
/// Blocking clause pattern:
///   `(= (select (store a i v) i) v)` -- single positive equality
/// or
///   `(not (= i j)) (= (select (store a i v) j) v)` -- with index disequality premise
///
/// In blocking clause semantics:
///   Conflict = negations of literals
///   Positive `(= X Y)` in clause -> disequality `X != Y` in conflict
///   Negative `(not (= X Y))` in clause -> equality `X = Y` in conflict
fn try_read_over_write_same(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    // Look for a positive equality literal involving select(store(...), ...).
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            // Check if either side is select(store(a, i, v), j).
            if check_row_same_from_equality(dag, lhs, rhs, clause)
                || check_row_same_from_equality(dag, rhs, lhs, clause)
            {
                return Some(ok(step_id));
            }
        }
    }
    None
}

/// Helper: given `select_side = select(store(a, i, v), j)` and `value_side`,
/// check that `value_side == v` and that either `i == j` syntactically, or
/// the clause contains `(not (= i j))` (meaning i = j in the conflict).
fn check_row_same_from_equality(
    dag: &SmtProofDag,
    select_side: SmtTermId,
    value_side: SmtTermId,
    clause: &[SmtTermId],
) -> bool {
    let (store_term, sel_idx) = match as_select(dag, select_side) {
        Some(x) => x,
        None => return false,
    };
    let (_arr, store_idx, store_val) = match as_store(dag, store_term) {
        Some(x) => x,
        None => return false,
    };

    if value_side != store_val {
        return false;
    }

    // Same index syntactically.
    if sel_idx == store_idx {
        return true;
    }

    // Check for index equality in clause premises (negated equality in clause
    // = equality in conflict).
    clause.iter().any(|&other_lit| {
        if let Some((a, b)) = dag.as_negated_equality(other_lit) {
            (a == sel_idx && b == store_idx) || (a == store_idx && b == sel_idx)
        } else {
            false
        }
    })
}

// ── Read-over-write (different index) ───────────────────────────────────

/// Helper for row-other: check `select(store(a, i, v), j) = select(a, j)`
/// where i and j are from the index equality literal.
fn check_row_other_with_indices(
    dag: &SmtProofDag,
    select_store_side: SmtTermId,
    select_plain_side: SmtTermId,
    idx_a: SmtTermId,
    idx_b: SmtTermId,
) -> bool {
    let (store_term, sel_idx) = match as_select(dag, select_store_side) {
        Some(x) => x,
        None => return false,
    };
    let (arr, store_idx, _store_val) = match as_store(dag, store_term) {
        Some(x) => x,
        None => return false,
    };
    let (plain_arr, plain_idx) = match as_select(dag, select_plain_side) {
        Some(x) => x,
        None => return false,
    };

    // Arrays must match.
    if arr != plain_arr {
        return false;
    }

    // Select indices must match.
    if sel_idx != plain_idx {
        return false;
    }

    // The store index and select index correspond to the equality literal's
    // indices (in either order), and they must be different terms.
    let indices_match =
        (store_idx == idx_a && sel_idx == idx_b) || (store_idx == idx_b && sel_idx == idx_a);

    indices_match && store_idx != sel_idx
}

/// Try to verify the clause as a read-over-write-other axiom instance.
///
/// Blocking clause pattern:
///   `(= i j) (= (select (store a i v) j) (select a j))`
///
/// In the conflict: i != j (from positive `(= i j)` in blocking clause),
/// and `select(store(a, i, v), j) != select(a, j)`. Since i != j, by the
/// read-over-write-other axiom, `select(store(a, i, v), j) = select(a, j)`,
/// contradicting the disequality.
fn try_read_over_write_other(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    // Look for a positive equality between select(store(a, i, v), j) and select(a, j).
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if check_row_other_from_equality(dag, lhs, rhs, clause)
                || check_row_other_from_equality(dag, rhs, lhs, clause)
            {
                return Some(ok(step_id));
            }
        }
    }
    None
}

/// Helper: check `select(store(a, i, v), j) = select(a, j)` pattern,
/// where some other literal in the clause asserts `(= i j)` (meaning
/// i != j in the conflict, giving us the different-index condition).
fn check_row_other_from_equality(
    dag: &SmtProofDag,
    select_store_side: SmtTermId,
    select_plain_side: SmtTermId,
    clause: &[SmtTermId],
) -> bool {
    let (store_term, sel_idx) = match as_select(dag, select_store_side) {
        Some(x) => x,
        None => return false,
    };
    let (arr, store_idx, _store_val) = match as_store(dag, store_term) {
        Some(x) => x,
        None => return false,
    };
    let (plain_arr, plain_idx) = match as_select(dag, select_plain_side) {
        Some(x) => x,
        None => return false,
    };

    // Arrays must match, select indices must match.
    if arr != plain_arr || sel_idx != plain_idx {
        return false;
    }

    // Store index and select index must be different (syntactically).
    if store_idx == sel_idx {
        return false;
    }

    // Check that clause contains `(= store_idx sel_idx)` (positive equality,
    // meaning index disequality in the conflict).
    clause.iter().any(|&other_lit| {
        if let Some((a, b)) = dag.as_equality(other_lit) {
            // Must be a "bare" index equality, not a select/store equality.
            let is_index_eq = (a == store_idx && b == sel_idx) || (a == sel_idx && b == store_idx);
            is_index_eq
                && as_select(dag, a).is_none()
                && as_store(dag, a).is_none()
                && as_select(dag, b).is_none()
                && as_store(dag, b).is_none()
        } else {
            false
        }
    })
}

// ── Extensionality ──────────────────────────────────────────────────────

/// Check extensionality witness: `sel_a = select(arr_a, k)` and
/// `sel_b = select(arr_b, k)` for the same witness index `k`.
fn check_ext_witness(
    dag: &SmtProofDag,
    arr_a: SmtTermId,
    arr_b: SmtTermId,
    sel_a: SmtTermId,
    sel_b: SmtTermId,
) -> bool {
    let (a_arr, a_idx) = match as_select(dag, sel_a) {
        Some(x) => x,
        None => return false,
    };
    let (b_arr, b_idx) = match as_select(dag, sel_b) {
        Some(x) => x,
        None => return false,
    };

    // Same witness index.
    if a_idx != b_idx {
        return false;
    }

    // Arrays match the extensionality operands.
    (a_arr == arr_a && b_arr == arr_b) || (a_arr == arr_b && b_arr == arr_a)
}

/// Try to verify the clause as an extensionality axiom instance.
///
/// Blocking clause pattern:
///   `(= a b) (not (= (select a k) (select b k)))`
///
/// Conflict: a != b, select(a, k) = select(b, k). If all indices agree,
/// extensionality gives a = b, contradicting a != b.
///
/// Also handles the contrapositive direction:
///   `(not (= a b)) (= (select a k) (select b k))`
/// Conflict: a = b, select(a, k) != select(b, k). By congruence on select,
/// a = b implies select(a, k) = select(b, k), contradiction.
fn try_extensionality(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    // Standard form: (= a b) and (not (= (select a k) (select b k))).
    for (i, &lit_eq) in clause.iter().enumerate() {
        if let Some((a, b)) = dag.as_equality(lit_eq) {
            for (j, &lit_neq) in clause.iter().enumerate() {
                if i == j {
                    continue;
                }
                if let Some((sel_a, sel_b)) = dag.as_negated_equality(lit_neq) {
                    if check_ext_witness(dag, a, b, sel_a, sel_b)
                        || check_ext_witness(dag, a, b, sel_b, sel_a)
                    {
                        return Some(ok(step_id));
                    }
                }
            }
        }
    }

    None
}

// ── Verdict helpers ─────────────────────────────────────────────────────

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
        detail: Some("arrays: no axiom schema matched, structurally accepted".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtSymbol, SmtTerm};

    // ── Test helpers ────────────────────────────────────────────────────

    fn make_var(dag: &mut SmtProofDag, name: &str, sort: SmtSort) -> SmtTermId {
        dag.add_term(SmtTerm::Var(name.to_string(), sort))
    }

    fn make_int_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
        make_var(dag, name, SmtSort::Int)
    }

    fn make_array_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
        make_var(
            dag,
            name,
            SmtSort::Array(Box::new(SmtSort::Int), Box::new(SmtSort::Int)),
        )
    }

    fn make_select(dag: &mut SmtProofDag, array: SmtTermId, index: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named("select".to_string()),
            vec![array, index],
        ))
    }

    fn make_store(
        dag: &mut SmtProofDag,
        array: SmtTermId,
        index: SmtTermId,
        value: SmtTermId,
    ) -> SmtTermId {
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named("store".to_string()),
            vec![array, index, value],
        ))
    }

    fn make_eq(dag: &mut SmtProofDag, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]))
    }

    fn make_not(dag: &mut SmtProofDag, inner: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::Not(inner))
    }

    // ── Read-over-write (same index) tests ──────────────────────────────

    #[test]
    fn test_arrays_row_same_valid() {
        // select(store(a, 0, 5), 0) = 5
        // Blocking clause: (= (select (store a 0 5) 0) 5)
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let idx = dag.add_term(SmtTerm::Int(0));
        let val = dag.add_term(SmtTerm::Int(5));

        let store_a = make_store(&mut dag, a, idx, val);
        let sel = make_select(&mut dag, store_a, idx);
        let eq = make_eq(&mut dag, sel, val);

        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "read-over-write same index should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_row_same_valid_swapped() {
        // 5 = select(store(a, 0, 5), 0)  (swapped sides)
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let idx = dag.add_term(SmtTerm::Int(0));
        let val = dag.add_term(SmtTerm::Int(5));

        let store_a = make_store(&mut dag, a, idx, val);
        let sel = make_select(&mut dag, store_a, idx);
        let eq = make_eq(&mut dag, val, sel);

        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "swapped read-over-write same index should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_row_same_with_index_premise() {
        // (not (= i j)) (= (select (store a i v) j) v)
        // Conflict: i = j, select(store(a, i, v), j) != v
        // By ROW: since i = j, select(store(a, i, v), j) = v. Contradiction.
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let i = make_int_var(&mut dag, "i");
        let j = make_int_var(&mut dag, "j");
        let v = make_int_var(&mut dag, "v");

        let store_a = make_store(&mut dag, a, i, v);
        let sel = make_select(&mut dag, store_a, j);
        let eq_sel_v = make_eq(&mut dag, sel, v);
        let eq_ij = make_eq(&mut dag, i, j);
        let neq_ij = make_not(&mut dag, eq_ij);

        let clause = vec![neq_ij, eq_sel_v];
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "ROW with index premise should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_row_same_invalid_different_value() {
        // select(store(a, 0, 5), 0) = 7  -- NOT valid (value mismatch)
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let idx = dag.add_term(SmtTerm::Int(0));
        let val5 = dag.add_term(SmtTerm::Int(5));
        let val7 = dag.add_term(SmtTerm::Int(7));

        let store_a = make_store(&mut dag, a, idx, val5);
        let sel = make_select(&mut dag, store_a, idx);
        let eq = make_eq(&mut dag, sel, val7);

        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &[eq]);
        // Should NOT be KernelVerified since 7 != 5.
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "value mismatch should not be kernel-verified"
        );
    }

    // ── Read-over-write (different index) tests ─────────────────────────

    #[test]
    fn test_arrays_row_other_valid() {
        // (= i j) (= (select (store a i v) j) (select a j))
        // Conflict: i != j, select(store(a, i, v), j) != select(a, j)
        // By ROW-other: i != j implies select(store(a, i, v), j) = select(a, j).
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let i = make_int_var(&mut dag, "i");
        let j = make_int_var(&mut dag, "j");
        let v = make_int_var(&mut dag, "v");

        let store_a = make_store(&mut dag, a, i, v);
        let sel_store = make_select(&mut dag, store_a, j);
        let sel_plain = make_select(&mut dag, a, j);

        let eq_ij = make_eq(&mut dag, i, j);
        let eq_sels = make_eq(&mut dag, sel_store, sel_plain);

        let clause = vec![eq_ij, eq_sels];
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "ROW-other should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_row_other_valid_swapped_eq() {
        // (= j i) instead of (= i j)
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let i = make_int_var(&mut dag, "i");
        let j = make_int_var(&mut dag, "j");
        let v = make_int_var(&mut dag, "v");

        let store_a = make_store(&mut dag, a, i, v);
        let sel_store = make_select(&mut dag, store_a, j);
        let sel_plain = make_select(&mut dag, a, j);

        let eq_ji = make_eq(&mut dag, j, i); // swapped
        let eq_sels = make_eq(&mut dag, sel_store, sel_plain);

        let clause = vec![eq_ji, eq_sels];
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "ROW-other with swapped index eq should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_row_other_invalid_same_index() {
        // store(a, i, v)[i] != a[i]  -- NOT valid for row-other (same index)
        // This would be a row-same instance: store(a, i, v)[i] = v, not a[i].
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let i = make_int_var(&mut dag, "i");
        let v = make_int_var(&mut dag, "v");

        let store_a = make_store(&mut dag, a, i, v);
        let sel_store = make_select(&mut dag, store_a, i);
        let sel_plain = make_select(&mut dag, a, i);

        // (= i i) -- trivially true index equality
        let eq_ii = make_eq(&mut dag, i, i);
        let eq_sels = make_eq(&mut dag, sel_store, sel_plain);

        let clause = vec![eq_ii, eq_sels];
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &clause);
        // Should NOT be kernel-verified as row-other because store_idx == sel_idx.
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "same-index should not pass row-other check"
        );
    }

    // ── Extensionality tests ────────────────────────────────────────────

    #[test]
    fn test_arrays_extensionality_valid() {
        // (= a b) (not (= (select a k) (select b k)))
        // Conflict: a != b, select(a, k) = select(b, k)
        // Extensionality: if for all k, select(a, k) = select(b, k), then a = b.
        // The witness k shows where they agree, supporting the extensionality claim.
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let b = make_array_var(&mut dag, "b");
        let k = make_int_var(&mut dag, "k");

        let sel_a = make_select(&mut dag, a, k);
        let sel_b = make_select(&mut dag, b, k);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_sels = make_eq(&mut dag, sel_a, sel_b);
        let neq_sels = make_not(&mut dag, eq_sels);

        let clause = vec![eq_ab, neq_sels];
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "extensionality should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_extensionality_valid_swapped_order() {
        // (not (= (select a k) (select b k))) (= a b) -- swapped literal order
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let b = make_array_var(&mut dag, "b");
        let k = make_int_var(&mut dag, "k");

        let sel_a = make_select(&mut dag, a, k);
        let sel_b = make_select(&mut dag, b, k);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_sels = make_eq(&mut dag, sel_a, sel_b);
        let neq_sels = make_not(&mut dag, eq_sels);

        let clause = vec![neq_sels, eq_ab]; // swapped
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "extensionality with swapped order should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_extensionality_invalid_different_witness() {
        // (= a b) (not (= (select a k1) (select b k2)))  -- different indices
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let b = make_array_var(&mut dag, "b");
        let k1 = make_int_var(&mut dag, "k1");
        let k2 = make_int_var(&mut dag, "k2");

        let sel_a = make_select(&mut dag, a, k1);
        let sel_b = make_select(&mut dag, b, k2);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_sels = make_eq(&mut dag, sel_a, sel_b);
        let neq_sels = make_not(&mut dag, eq_sels);

        let clause = vec![eq_ab, neq_sels];
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &clause);
        // Should not be kernel-verified: witness indices don't match.
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "different witness indices should not be kernel-verified"
        );
    }

    // ── Rule step entry point tests ─────────────────────────────────────

    #[test]
    fn test_arrays_row_pos_single_literal() {
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let idx = dag.add_term(SmtTerm::Int(0));
        let val = dag.add_term(SmtTerm::Int(5));

        let store_a = make_store(&mut dag, a, idx, val);
        let sel = make_select(&mut dag, store_a, idx);
        let eq = make_eq(&mut dag, sel, val);

        let verdict = check_read_over_write_pos(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "ROW pos single literal: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_row_neg_two_literals() {
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let i = make_int_var(&mut dag, "i");
        let j = make_int_var(&mut dag, "j");
        let v = make_int_var(&mut dag, "v");

        let store_a = make_store(&mut dag, a, i, v);
        let sel_store = make_select(&mut dag, store_a, j);
        let sel_plain = make_select(&mut dag, a, j);

        let eq_ij = make_eq(&mut dag, i, j);
        let eq_sels = make_eq(&mut dag, sel_store, sel_plain);

        let clause = vec![eq_ij, eq_sels];
        let verdict = check_read_over_write_neg(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "ROW neg two literals: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_extensionality_rule() {
        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let b = make_array_var(&mut dag, "b");
        let k = make_int_var(&mut dag, "k");

        let sel_a = make_select(&mut dag, a, k);
        let sel_b = make_select(&mut dag, b, k);

        let eq_ab = make_eq(&mut dag, a, b);
        let eq_sels = make_eq(&mut dag, sel_a, sel_b);
        let neq_sels = make_not(&mut dag, eq_sels);

        let clause = vec![eq_ab, neq_sels];
        let verdict = check_extensionality(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "extensionality rule: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_arrays_empty_clause_fails() {
        let dag = SmtProofDag::new();
        let verdict = check_arrays_lemma(&dag, SmtStepId(0), &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    // ── Full pipeline integration test ──────────────────────────────────

    #[test]
    fn test_arrays_lemma_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let idx = dag.add_term(SmtTerm::Int(0));
        let val = dag.add_term(SmtTerm::Int(5));

        // store(a, 0, 5)
        let store_a = make_store(&mut dag, a, idx, val);
        // select(store(a, 0, 5), 0)
        let sel = make_select(&mut dag, store_a, idx);

        // assume: select(store(a, 0, 5), 0) != 5
        let eq_sel_val = make_eq(&mut dag, sel, val);
        let neq_sel_val = make_not(&mut dag, eq_sel_val);

        let s0 = dag.add_step(SmtProofStep::Assume(neq_sel_val));

        // Array theory lemma: (= (select (store a 0 5) 0) 5)
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Arrays,
            kind: TheoryLemmaDetail::ArraySelectStore { index_eq: true },
            clause: vec![eq_sel_val],
        });

        // Resolve: s0 (neq) + s1 (eq) -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(eq_sel_val),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "arrays proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Arrays),
            Some(&1)
        );
    }

    #[test]
    fn test_arrays_row_other_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let i = make_int_var(&mut dag, "i");
        let j = make_int_var(&mut dag, "j");
        let v = make_int_var(&mut dag, "v");

        let store_a = make_store(&mut dag, a, i, v);
        let sel_store = make_select(&mut dag, store_a, j);
        let sel_plain = make_select(&mut dag, a, j);

        // Assume: i != j
        let eq_ij = make_eq(&mut dag, i, j);
        let neq_ij = make_not(&mut dag, eq_ij);
        let s0 = dag.add_step(SmtProofStep::Assume(neq_ij));

        // Assume: select(store(a, i, v), j) != select(a, j)
        let eq_sels = make_eq(&mut dag, sel_store, sel_plain);
        let neq_sels = make_not(&mut dag, eq_sels);
        let s1 = dag.add_step(SmtProofStep::Assume(neq_sels));

        // Array theory lemma: (= i j) (= (select (store a i v) j) (select a j))
        let s2 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Arrays,
            kind: TheoryLemmaDetail::ArraySelectStore { index_eq: false },
            clause: vec![eq_ij, eq_sels],
        });

        // Resolve s0 + s2 on eq_ij -> {eq_sels}
        let s3 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![eq_sels],
            premises: vec![s0, s2],
            pivot: Some(eq_ij),
        });

        // Resolve s1 + s3 on eq_sels -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s1, s3],
            pivot: Some(eq_sels),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "arrays ROW-other proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Arrays),
            Some(&1)
        );
    }

    #[test]
    fn test_arrays_extensionality_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let a = make_array_var(&mut dag, "a");
        let b = make_array_var(&mut dag, "b");
        let k = make_int_var(&mut dag, "k");

        let sel_a = make_select(&mut dag, a, k);
        let sel_b = make_select(&mut dag, b, k);

        // Assume: a != b
        let eq_ab = make_eq(&mut dag, a, b);
        let neq_ab = make_not(&mut dag, eq_ab);
        let s0 = dag.add_step(SmtProofStep::Assume(neq_ab));

        // Assume: select(a, k) = select(b, k)
        let eq_sels = make_eq(&mut dag, sel_a, sel_b);
        let s1 = dag.add_step(SmtProofStep::Assume(eq_sels));

        // Extensionality lemma: (= a b) (not (= (select a k) (select b k)))
        let neq_sels = make_not(&mut dag, eq_sels);
        let s2 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Arrays,
            kind: TheoryLemmaDetail::ArrayExtensionality,
            clause: vec![eq_ab, neq_sels],
        });

        // Resolve s0 + s2 on eq_ab -> {neq_sels}
        let s3 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![neq_sels],
            premises: vec![s0, s2],
            pivot: Some(eq_ab),
        });

        // Resolve s1 + s3 on eq_sels -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s1, s3],
            pivot: Some(eq_sels),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "arrays extensionality proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Arrays),
            Some(&1)
        );
    }
}
