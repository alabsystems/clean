// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strings theory checker for SMT proof verification.
//!
//! Validates string axiom applications for the QF_S (quantifier-free strings)
//! SMT-COMP division:
//!
//! - **Concatenation associativity**: `str.++ (str.++ a b) c = str.++ a (str.++ b c)`
//! - **Length of concatenation**: `str.len (str.++ a b) = (+ (str.len a) (str.len b))`
//! - **Empty string identity**: `str.++ "" a = a`, `str.++ a "" = a`
//! - **Length of empty**: `str.len "" = 0`
//! - **Contains implication**: `str.contains a b` implies decomposition
//! - **Prefix/suffix**: `str.prefixof a b -> str.contains b a`
//! - **Concrete evaluation**: direct evaluation on string literals
//!
//! String operations are encoded as function applications in `SmtTerm`:
//! - Concatenation: `App("str.++", [a, b, ...])`
//! - Length: `App("str.len", [s])`
//! - Contains: `App("str.contains", [s, t])`
//! - Prefix: `App("str.prefixof", [pre, s])`
//! - Suffix: `App("str.suffixof", [suf, s])`
//! - Substr: `App("str.substr", [s, i, n])`
//! - Replace: `App("str.replace", [s, from, to])`
//! - At: `App("str.at", [s, i])`
//! - IndexOf: `App("str.indexof", [s, t, i])`
//!
//! Reference: SMT-LIB Theory of Strings (QF_S, QF_SLIA divisions).

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "strings";

/// Check a strings theory lemma (blocking clause).
///
/// Tries the following axiom schemas in order:
/// 1. Concrete string evaluation (ground terms)
/// 2. Empty string identity (`str.++ "" a = a`)
/// 3. Length of concatenation (`str.len(str.++(a, b)) = str.len(a) + str.len(b)`)
/// 4. Length of empty (`str.len("") = 0`)
/// 5. Contains contradictions (concrete)
/// 6. Concatenation associativity
/// 7. Prefix/suffix implication
///
/// Falls back to structural acceptance if no axiom schema matches.
pub(crate) fn check_strings_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "strings: empty clause");
    }

    // Try concrete string evaluation.
    if let Some(verdict) = try_concrete_eval(dag, step_id, clause) {
        return verdict;
    }

    // Try empty string identity.
    if let Some(verdict) = try_empty_concat(dag, step_id, clause) {
        return verdict;
    }

    // Try length of concatenation.
    if let Some(verdict) = try_length_concat(dag, step_id, clause) {
        return verdict;
    }

    // Try length of empty string.
    if let Some(verdict) = try_length_empty(dag, step_id, clause) {
        return verdict;
    }

    // Try contains contradiction (concrete).
    if let Some(verdict) = try_contains_concrete(dag, step_id, clause) {
        return verdict;
    }

    // Try concatenation associativity.
    if let Some(verdict) = try_concat_assoc(dag, step_id, clause) {
        return verdict;
    }

    // Try prefix/suffix implications.
    if let Some(verdict) = try_prefix_suffix(dag, step_id, clause) {
        return verdict;
    }

    // No axiom matched; structurally accept.
    structural_accept(step_id)
}

// ── Concrete String Evaluation ────────────────────────────────────────

/// Try to verify the clause by evaluating concrete string operations.
///
/// If all terms in the clause are ground (no variables), we can evaluate
/// each literal and check that the clause (disjunction) is a tautology.
///
/// Common pattern: a single-literal clause `(not (= (str.len "abc") 3))`
/// is valid because the negation `str.len("abc") = 3` evaluates to true,
/// making the clause tautologically true (the disjunction contains a true literal).
///
/// Actually, for blocking clauses: a single literal `(= (str.len "abc") 3)`
/// evaluates to true, making the clause valid.
/// A single literal `(not (= (str.contains "hello" "ell") true))` is also
/// valid because str.contains("hello", "ell") = true contradicts the literal.
fn try_concrete_eval(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if eval_literal_true(dag, lit) {
            return Some(ok(step_id));
        }
    }
    None
}

/// Evaluate whether a literal is true under concrete string semantics.
///
/// Returns `true` if the literal can be shown to be always true by
/// concrete evaluation.
fn eval_literal_true(dag: &SmtProofDag, lit: SmtTermId) -> bool {
    let term = match dag.term(lit) {
        Some(t) => t,
        None => return false,
    };

    match term {
        // Equality: check if both sides evaluate to the same concrete value.
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "=" && args.len() == 2 => {
            match (eval_to_string(dag, args[0]), eval_to_string(dag, args[1])) {
                (Some(a), Some(b)) => a == b,
                _ => match (eval_to_int(dag, args[0]), eval_to_int(dag, args[1])) {
                    (Some(a), Some(b)) => a == b,
                    _ => match (eval_to_bool(dag, args[0]), eval_to_bool(dag, args[1])) {
                        (Some(a), Some(b)) => a == b,
                        _ => false,
                    },
                },
            }
        }

        // Negated equality: check if both sides evaluate to different values.
        SmtTerm::Not(inner) => {
            let inner_term = match dag.term(*inner) {
                Some(t) => t,
                None => return false,
            };
            match inner_term {
                SmtTerm::App(SmtSymbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    match (eval_to_string(dag, args[0]), eval_to_string(dag, args[1])) {
                        (Some(a), Some(b)) => a != b,
                        _ => match (eval_to_int(dag, args[0]), eval_to_int(dag, args[1])) {
                            (Some(a), Some(b)) => a != b,
                            _ => match (eval_to_bool(dag, args[0]), eval_to_bool(dag, args[1])) {
                                (Some(a), Some(b)) => a != b,
                                _ => false,
                            },
                        },
                    }
                }
                _ => false,
            }
        }

        // Boolean application: str.contains, str.prefixof, str.suffixof.
        SmtTerm::App(SmtSymbol::Named(name), args) => match name.as_str() {
            "str.contains" if args.len() == 2 => {
                match (eval_to_string(dag, args[0]), eval_to_string(dag, args[1])) {
                    (Some(haystack), Some(needle)) => haystack.contains(&*needle),
                    _ => false,
                }
            }
            "str.prefixof" if args.len() == 2 => {
                match (eval_to_string(dag, args[0]), eval_to_string(dag, args[1])) {
                    (Some(prefix), Some(s)) => s.starts_with(&*prefix),
                    _ => false,
                }
            }
            "str.suffixof" if args.len() == 2 => {
                match (eval_to_string(dag, args[0]), eval_to_string(dag, args[1])) {
                    (Some(suffix), Some(s)) => s.ends_with(&*suffix),
                    _ => false,
                }
            }
            _ => false,
        },

        _ => false,
    }
}

/// Try to evaluate a term to a concrete string value.
fn eval_to_string(dag: &SmtProofDag, id: SmtTermId) -> Option<String> {
    let term = dag.term(id)?;
    match term {
        SmtTerm::Str(s) => Some(s.clone()),

        SmtTerm::App(SmtSymbol::Named(name), args) => match name.as_str() {
            "str.++" => {
                let mut result = String::new();
                for &arg in args {
                    result.push_str(&eval_to_string(dag, arg)?);
                }
                Some(result)
            }
            "str.substr" if args.len() == 3 => {
                let s = eval_to_string(dag, args[0])?;
                let i = eval_to_int(dag, args[1])?;
                let n = eval_to_int(dag, args[2])?;
                Some(str_substr(&s, i, n))
            }
            "str.replace" if args.len() == 3 => {
                let s = eval_to_string(dag, args[0])?;
                let from = eval_to_string(dag, args[1])?;
                let to = eval_to_string(dag, args[2])?;
                // SMT-LIB str.replace replaces the first occurrence.
                Some(str_replace_first(&s, &from, &to))
            }
            "str.at" if args.len() == 2 => {
                let s = eval_to_string(dag, args[0])?;
                let i = eval_to_int(dag, args[1])?;
                Some(str_at(&s, i))
            }
            _ => None,
        },

        _ => None,
    }
}

/// Try to evaluate a term to a concrete integer value.
fn eval_to_int(dag: &SmtProofDag, id: SmtTermId) -> Option<i64> {
    let term = dag.term(id)?;
    match term {
        SmtTerm::Int(n) => Some(*n),

        SmtTerm::App(SmtSymbol::Named(name), args) => match name.as_str() {
            "str.len" if args.len() == 1 => {
                let s = eval_to_string(dag, args[0])?;
                Some(s.len() as i64)
            }
            "str.indexof" if args.len() == 3 => {
                let s = eval_to_string(dag, args[0])?;
                let t = eval_to_string(dag, args[1])?;
                let start = eval_to_int(dag, args[2])?;
                Some(str_indexof(&s, &t, start))
            }
            "+" if args.len() == 2 => {
                let a = eval_to_int(dag, args[0])?;
                let b = eval_to_int(dag, args[1])?;
                Some(a + b)
            }
            "-" if args.len() == 2 => {
                let a = eval_to_int(dag, args[0])?;
                let b = eval_to_int(dag, args[1])?;
                Some(a - b)
            }
            _ => None,
        },

        _ => None,
    }
}

/// Try to evaluate a term to a concrete boolean value.
fn eval_to_bool(dag: &SmtProofDag, id: SmtTermId) -> Option<bool> {
    let term = dag.term(id)?;
    match term {
        SmtTerm::Bool(b) => Some(*b),

        SmtTerm::App(SmtSymbol::Named(name), args) => match name.as_str() {
            "str.contains" if args.len() == 2 => {
                let s = eval_to_string(dag, args[0])?;
                let t = eval_to_string(dag, args[1])?;
                Some(s.contains(&*t))
            }
            "str.prefixof" if args.len() == 2 => {
                let pre = eval_to_string(dag, args[0])?;
                let s = eval_to_string(dag, args[1])?;
                Some(s.starts_with(&*pre))
            }
            "str.suffixof" if args.len() == 2 => {
                let suf = eval_to_string(dag, args[0])?;
                let s = eval_to_string(dag, args[1])?;
                Some(s.ends_with(&*suf))
            }
            "=" if args.len() == 2 => {
                // Equality of strings.
                match (eval_to_string(dag, args[0]), eval_to_string(dag, args[1])) {
                    (Some(a), Some(b)) => Some(a == b),
                    _ => match (eval_to_int(dag, args[0]), eval_to_int(dag, args[1])) {
                        (Some(a), Some(b)) => Some(a == b),
                        _ => None,
                    },
                }
            }
            _ => None,
        },

        SmtTerm::Not(inner) => {
            let b = eval_to_bool(dag, *inner)?;
            Some(!b)
        }

        _ => None,
    }
}

// ── SMT-LIB String Operation Semantics ────────────────────────────────

/// `str.substr(s, i, n)`: extract substring starting at position `i` with
/// length at most `n`. Returns "" if `i < 0`, `n < 0`, or `i >= |s|`.
fn str_substr(s: &str, i: i64, n: i64) -> String {
    if i < 0 || n < 0 || i >= s.len() as i64 {
        return String::new();
    }
    let start = i as usize;
    let len = n.min(s.len() as i64 - i) as usize;
    s[start..start + len].to_string()
}

/// `str.replace(s, from, to)`: replace first occurrence of `from` in `s` with `to`.
/// If `from` is empty, prepends `to` to `s`.
fn str_replace_first(s: &str, from: &str, to: &str) -> String {
    if from.is_empty() {
        return format!("{to}{s}");
    }
    if let Some(pos) = s.find(from) {
        format!("{}{to}{}", &s[..pos], &s[pos + from.len()..])
    } else {
        s.to_string()
    }
}

/// `str.at(s, i)`: character at position `i`, or "" if out of bounds.
fn str_at(s: &str, i: i64) -> String {
    if i < 0 || i >= s.len() as i64 {
        return String::new();
    }
    s[i as usize..i as usize + 1].to_string()
}

/// `str.indexof(s, t, start)`: first position of `t` in `s` starting at `start`,
/// or -1 if not found. Returns -1 if `start < 0`.
fn str_indexof(s: &str, t: &str, start: i64) -> i64 {
    if start < 0 || start > s.len() as i64 {
        return -1;
    }
    let from = start as usize;
    s[from..].find(t).map_or(-1, |pos| (from + pos) as i64)
}

// ── Empty String Concatenation Identity ───────────────────────────────

/// Try to verify the clause as an empty string concatenation identity.
///
/// Axioms:
/// - `str.++ "" a = a` (left identity)
/// - `str.++ a "" = a` (right identity)
///
/// Blocking clause pattern (single literal):
///   `(= (str.++ "" a) a)` or `(= (str.++ a "") a)` or their negations
///   forming a tautology.
///
/// Also handles the negated form: `(not (= (str.++ "" a) b))` where
/// `a != b` in the conflict (so `a = b` must hold by the identity axiom).
fn try_empty_concat(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if check_empty_concat_eq(dag, lhs, rhs) || check_empty_concat_eq(dag, rhs, lhs) {
                return Some(ok(step_id));
            }
        }
    }
    None
}

/// Check if `concat_side = str.++(args)` simplifies to `other_side`
/// by removing empty string arguments.
fn check_empty_concat_eq(dag: &SmtProofDag, concat_side: SmtTermId, other_side: SmtTermId) -> bool {
    let args = match as_str_concat(dag, concat_side) {
        Some(a) => a,
        None => return false,
    };

    // Collect non-empty arguments.
    let non_empty: Vec<SmtTermId> = args
        .iter()
        .copied()
        .filter(|&a| !is_empty_string(dag, a))
        .collect();

    match non_empty.len() {
        0 => {
            // All arguments are empty: str.++("", "") = ""
            is_empty_string(dag, other_side)
        }
        1 => {
            // Single non-empty argument: str.++("", a) = a
            non_empty[0] == other_side
        }
        _ => false,
    }
}

// ── Length of Concatenation ───────────────────────────────────────────

/// Try to verify the clause as a length-of-concatenation axiom.
///
/// Axiom: `str.len(str.++(a, b)) = str.len(a) + str.len(b)`
///
/// Blocking clause pattern:
///   `(= (str.len (str.++ a b)) (+ (str.len a) (str.len b)))`
fn try_length_concat(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if check_length_concat_eq(dag, lhs, rhs) || check_length_concat_eq(dag, rhs, lhs) {
                return Some(ok(step_id));
            }
        }
    }
    None
}

/// Check: `len_side = str.len(str.++(a1, ..., an))` and
/// `sum_side = (+ (str.len a1) (+ (str.len a2) ... (str.len an) ...))`.
fn check_length_concat_eq(dag: &SmtProofDag, len_side: SmtTermId, sum_side: SmtTermId) -> bool {
    // len_side should be str.len(concat_term)
    let concat_arg = match as_str_len(dag, len_side) {
        Some(arg) => arg,
        None => return false,
    };

    let concat_args = match as_str_concat(dag, concat_arg) {
        Some(a) => a,
        None => return false,
    };

    // Collect the individual str.len terms from the sum.
    let sum_len_args = collect_sum_terms(dag, sum_side);

    if sum_len_args.len() != concat_args.len() {
        return false;
    }

    // Each sum term should be str.len of the corresponding concat argument.
    for sum_term in &sum_len_args {
        let inner = match as_str_len(dag, *sum_term) {
            Some(a) => a,
            None => return false,
        };
        if !concat_args.contains(&inner) {
            return false;
        }
    }

    true
}

/// Collect flat addition operands from a nested `(+ a (+ b c))` structure.
fn collect_sum_terms(dag: &SmtProofDag, id: SmtTermId) -> Vec<SmtTermId> {
    let term = match dag.term(id) {
        Some(t) => t,
        None => return vec![id],
    };

    match term {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "+" && args.len() == 2 => {
            let mut result = collect_sum_terms(dag, args[0]);
            result.extend(collect_sum_terms(dag, args[1]));
            result
        }
        _ => vec![id],
    }
}

// ── Length of Empty String ────────────────────────────────────────────

/// Try to verify the clause as `str.len("") = 0`.
fn try_length_empty(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if check_length_empty(dag, lhs, rhs) || check_length_empty(dag, rhs, lhs) {
                return Some(ok(step_id));
            }
        }
    }
    None
}

/// Check: `len_side = str.len("")` and `zero_side = 0`.
fn check_length_empty(dag: &SmtProofDag, len_side: SmtTermId, zero_side: SmtTermId) -> bool {
    let arg = match as_str_len(dag, len_side) {
        Some(a) => a,
        None => return false,
    };

    if !is_empty_string(dag, arg) {
        return false;
    }

    matches!(dag.term(zero_side), Some(SmtTerm::Int(0)))
}

// ── Contains Contradiction (Concrete) ─────────────────────────────────

/// Try to verify the clause when it involves concrete string contains.
///
/// Pattern: `(not (= (str.contains "hello" "ell") true))` is valid
/// because `str.contains("hello", "ell")` evaluates to `true`.
///
/// Also: `(= (str.contains "hello" "xyz") false)` is valid because
/// `str.contains("hello", "xyz")` evaluates to `false`.
fn try_contains_concrete(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        // Negated contains with boolean: not(= (str.contains s t) b)
        // where the evaluation contradicts b.
        if let Some(inner) = as_negation(dag, lit) {
            if let Some((lhs, rhs)) = dag.as_equality(inner) {
                if check_contains_eq_bool_contradiction(dag, lhs, rhs)
                    || check_contains_eq_bool_contradiction(dag, rhs, lhs)
                {
                    return Some(ok(step_id));
                }
            }
        }

        // Positive contains = bool: (= (str.contains s t) b)
        // where the evaluation agrees with b.
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            if check_contains_eq_bool_agreement(dag, lhs, rhs)
                || check_contains_eq_bool_agreement(dag, rhs, lhs)
            {
                return Some(ok(step_id));
            }
        }
    }
    None
}

/// Check: `contains_side = str.contains(s, t)` evaluates to some value,
/// and `bool_side` is the opposite boolean. This makes the negated equality
/// (from the clause's negation) satisfiable but the clause literal true.
fn check_contains_eq_bool_contradiction(
    dag: &SmtProofDag,
    contains_side: SmtTermId,
    bool_side: SmtTermId,
) -> bool {
    let val = match eval_to_bool(dag, contains_side) {
        Some(v) => v,
        None => return false,
    };

    match dag.term(bool_side) {
        Some(SmtTerm::Bool(b)) => val != *b,
        _ => false,
    }
}

/// Check: `contains_side = str.contains(s, t)` evaluates to some value,
/// and `bool_side` is the same boolean. The equality holds, making the
/// clause literal true.
fn check_contains_eq_bool_agreement(
    dag: &SmtProofDag,
    contains_side: SmtTermId,
    bool_side: SmtTermId,
) -> bool {
    let val = match eval_to_bool(dag, contains_side) {
        Some(v) => v,
        None => return false,
    };

    match dag.term(bool_side) {
        Some(SmtTerm::Bool(b)) => val == *b,
        _ => false,
    }
}

// ── Concatenation Associativity ──────────────────────────────────────

/// Try to verify the clause as a concatenation associativity axiom.
///
/// Axiom: `str.++ (str.++ a b) c = str.++ a (str.++ b c)`
///
/// Blocking clause:
///   `(= (str.++ (str.++ a b) c) (str.++ a (str.++ b c)))`
fn try_concat_assoc(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    for &lit in clause {
        if let Some((lhs, rhs)) = dag.as_equality(lit) {
            let lhs_flat = flatten_concat(dag, lhs);
            let rhs_flat = flatten_concat(dag, rhs);
            if !lhs_flat.is_empty() && lhs_flat == rhs_flat {
                // Both sides flatten to the same sequence of leaf terms,
                // meaning they differ only in associativity.
                return Some(ok(step_id));
            }
        }
    }
    None
}

/// Flatten nested `str.++` into a list of leaf (non-concat) term IDs.
fn flatten_concat(dag: &SmtProofDag, id: SmtTermId) -> Vec<SmtTermId> {
    match as_str_concat(dag, id) {
        Some(args) => {
            let mut result = Vec::new();
            for &arg in &args {
                result.extend(flatten_concat(dag, arg));
            }
            result
        }
        None => vec![id],
    }
}

// ── Prefix / Suffix Implications ─────────────────────────────────────

/// Try to verify prefix/suffix implication axioms.
///
/// Axioms:
/// - `str.prefixof a b -> str.contains b a`
/// - `str.suffixof a b -> str.contains b a`
///
/// Blocking clause pattern:
///   `(not (str.prefixof a b)) (str.contains b a)` -- if prefix, then contains
fn try_prefix_suffix(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> Option<StepVerdict> {
    // Look for pattern: (not (str.prefixof a b)) and (str.contains b a) both in clause.
    for &lit in clause {
        if let Some(inner) = as_negation(dag, lit) {
            // (not (str.prefixof a b)) -- check for matching contains.
            if let Some((pre, s)) = as_str_prefixof(dag, inner) {
                if clause.iter().any(|&other| {
                    as_str_contains(dag, other)
                        .is_some_and(|(haystack, needle)| haystack == s && needle == pre)
                }) {
                    return Some(ok(step_id));
                }
            }

            // (not (str.suffixof a b)) -- check for matching contains.
            if let Some((suf, s)) = as_str_suffixof(dag, inner) {
                if clause.iter().any(|&other| {
                    as_str_contains(dag, other)
                        .is_some_and(|(haystack, needle)| haystack == s && needle == suf)
                }) {
                    return Some(ok(step_id));
                }
            }
        }
    }
    None
}

// ── Term Recognition Helpers ─────────────────────────────────────────

/// Decompose `str.++(args)` from a term.
fn as_str_concat(dag: &SmtProofDag, id: SmtTermId) -> Option<Vec<SmtTermId>> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "str.++" && !args.is_empty() => {
            Some(args.clone())
        }
        _ => None,
    }
}

/// Decompose `str.len(s)` from a term.
fn as_str_len(dag: &SmtProofDag, id: SmtTermId) -> Option<SmtTermId> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "str.len" && args.len() == 1 => {
            Some(args[0])
        }
        _ => None,
    }
}

/// Decompose `str.contains(s, t)` from a term.
fn as_str_contains(dag: &SmtProofDag, id: SmtTermId) -> Option<(SmtTermId, SmtTermId)> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "str.contains" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Decompose `str.prefixof(pre, s)` from a term.
fn as_str_prefixof(dag: &SmtProofDag, id: SmtTermId) -> Option<(SmtTermId, SmtTermId)> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "str.prefixof" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Decompose `str.suffixof(suf, s)` from a term.
fn as_str_suffixof(dag: &SmtProofDag, id: SmtTermId) -> Option<(SmtTermId, SmtTermId)> {
    match dag.term(id)? {
        SmtTerm::App(SmtSymbol::Named(name), args) if name == "str.suffixof" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Check if a term is the empty string literal `""`.
fn is_empty_string(dag: &SmtProofDag, id: SmtTermId) -> bool {
    matches!(dag.term(id), Some(SmtTerm::Str(s)) if s.is_empty())
}

/// Extract the inner term from a negation.
fn as_negation(dag: &SmtProofDag, id: SmtTermId) -> Option<SmtTermId> {
    match dag.term(id)? {
        SmtTerm::Not(inner) => Some(*inner),
        _ => None,
    }
}

// ── Verdict Helpers ──────────────────────────────────────────────────

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
        detail: Some("strings: no axiom schema matched, structurally accepted".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtSymbol, SmtTerm};

    // ── Test helpers ────────────────────────────────────────────────────

    fn make_str_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
        dag.add_term(SmtTerm::Var(name.to_string(), SmtSort::String))
    }

    fn make_str(dag: &mut SmtProofDag, s: &str) -> SmtTermId {
        dag.add_term(SmtTerm::Str(s.to_string()))
    }

    fn make_int(dag: &mut SmtProofDag, n: i64) -> SmtTermId {
        dag.add_term(SmtTerm::Int(n))
    }

    fn make_bool(dag: &mut SmtProofDag, b: bool) -> SmtTermId {
        dag.add_term(SmtTerm::Bool(b))
    }

    fn make_app(dag: &mut SmtProofDag, name: &str, args: Vec<SmtTermId>) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named(name.to_string()), args))
    }

    fn make_concat(dag: &mut SmtProofDag, args: Vec<SmtTermId>) -> SmtTermId {
        make_app(dag, "str.++", args)
    }

    fn make_strlen(dag: &mut SmtProofDag, s: SmtTermId) -> SmtTermId {
        make_app(dag, "str.len", vec![s])
    }

    fn make_contains(dag: &mut SmtProofDag, s: SmtTermId, t: SmtTermId) -> SmtTermId {
        make_app(dag, "str.contains", vec![s, t])
    }

    fn make_prefixof(dag: &mut SmtProofDag, pre: SmtTermId, s: SmtTermId) -> SmtTermId {
        make_app(dag, "str.prefixof", vec![pre, s])
    }

    fn make_suffixof(dag: &mut SmtProofDag, suf: SmtTermId, s: SmtTermId) -> SmtTermId {
        make_app(dag, "str.suffixof", vec![suf, s])
    }

    fn make_plus(dag: &mut SmtProofDag, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        make_app(dag, "+", vec![a, b])
    }

    fn make_eq(dag: &mut SmtProofDag, a: SmtTermId, b: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]))
    }

    fn make_not(dag: &mut SmtProofDag, inner: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::Not(inner))
    }

    // ── Concrete Evaluation Tests ──────────────────────────────────────

    #[test]
    fn test_strings_concrete_strlen_eq() {
        // (= (str.len "abc") 3) -- tautology
        let mut dag = SmtProofDag::new();
        let abc = make_str(&mut dag, "abc");
        let len_abc = make_strlen(&mut dag, abc);
        let three = make_int(&mut dag, 3);
        let eq = make_eq(&mut dag, len_abc, three);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.len(\"abc\") = 3 should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_concrete_strlen_neq() {
        // (not (= (str.len "abc") 3)) -- contradiction: str.len("abc") IS 3
        // As a blocking clause literal, this is the NEGATION in the conflict.
        // Conflict: str.len("abc") = 3. Since that's true, contradiction.
        // But wait -- the blocking clause literal (not (= str.len("abc") 3))
        // is FALSE (str.len("abc") = 3), so the clause has a false literal.
        // For the clause to be valid, we need some literal that's TRUE.
        //
        // Actually: a single-literal clause (not (= (str.len "abc") 3)) is
        // NOT valid because str.len("abc") = 3 is true, making the negation false.
        // The clause should NOT be kernel-verified.
        let mut dag = SmtProofDag::new();
        let abc = make_str(&mut dag, "abc");
        let len_abc = make_strlen(&mut dag, abc);
        let three = make_int(&mut dag, 3);
        let eq = make_eq(&mut dag, len_abc, three);
        let neq = make_not(&mut dag, eq);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[neq]);
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "not(str.len(\"abc\") = 3) should NOT be valid"
        );
    }

    #[test]
    fn test_strings_concrete_strlen_wrong_value() {
        // (not (= (str.len "abc") 5)) -- valid: str.len("abc") = 3 != 5
        let mut dag = SmtProofDag::new();
        let abc = make_str(&mut dag, "abc");
        let len_abc = make_strlen(&mut dag, abc);
        let five = make_int(&mut dag, 5);
        let eq = make_eq(&mut dag, len_abc, five);
        let neq = make_not(&mut dag, eq);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[neq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "not(str.len(\"abc\") = 5) should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_concrete_empty_strlen() {
        // (= (str.len "") 0) -- tautology
        let mut dag = SmtProofDag::new();
        let empty = make_str(&mut dag, "");
        let len_empty = make_strlen(&mut dag, empty);
        let zero = make_int(&mut dag, 0);
        let eq = make_eq(&mut dag, len_empty, zero);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.len(\"\") = 0 should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Empty Concatenation Identity Tests ─────────────────────────────

    #[test]
    fn test_strings_empty_concat_left() {
        // (= (str.++ "" a) a) -- tautology
        let mut dag = SmtProofDag::new();
        let empty = make_str(&mut dag, "");
        let a = make_str_var(&mut dag, "a");
        let concat = make_concat(&mut dag, vec![empty, a]);
        let eq = make_eq(&mut dag, concat, a);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.++(\"\", a) = a should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_empty_concat_right() {
        // (= (str.++ a "") a) -- tautology
        let mut dag = SmtProofDag::new();
        let a = make_str_var(&mut dag, "a");
        let empty = make_str(&mut dag, "");
        let concat = make_concat(&mut dag, vec![a, empty]);
        let eq = make_eq(&mut dag, concat, a);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.++(a, \"\") = a should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_empty_concat_swapped() {
        // (= a (str.++ "" a)) -- swapped sides
        let mut dag = SmtProofDag::new();
        let empty = make_str(&mut dag, "");
        let a = make_str_var(&mut dag, "a");
        let concat = make_concat(&mut dag, vec![empty, a]);
        let eq = make_eq(&mut dag, a, concat);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "a = str.++(\"\", a) should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Length of Concatenation Tests ──────────────────────────────────

    #[test]
    fn test_strings_length_concat() {
        // (= (str.len (str.++ a b)) (+ (str.len a) (str.len b)))
        let mut dag = SmtProofDag::new();
        let a = make_str_var(&mut dag, "a");
        let b = make_str_var(&mut dag, "b");
        let concat = make_concat(&mut dag, vec![a, b]);
        let len_concat = make_strlen(&mut dag, concat);
        let len_a = make_strlen(&mut dag, a);
        let len_b = make_strlen(&mut dag, b);
        let sum = make_plus(&mut dag, len_a, len_b);
        let eq = make_eq(&mut dag, len_concat, sum);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.len(str.++(a, b)) = str.len(a) + str.len(b) should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_length_concat_swapped() {
        // (= (+ (str.len a) (str.len b)) (str.len (str.++ a b)))
        let mut dag = SmtProofDag::new();
        let a = make_str_var(&mut dag, "a");
        let b = make_str_var(&mut dag, "b");
        let concat = make_concat(&mut dag, vec![a, b]);
        let len_concat = make_strlen(&mut dag, concat);
        let len_a = make_strlen(&mut dag, a);
        let len_b = make_strlen(&mut dag, b);
        let sum = make_plus(&mut dag, len_a, len_b);
        let eq = make_eq(&mut dag, sum, len_concat);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "swapped length concat should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Contains Tests ────────────────────────────────────────────────

    #[test]
    fn test_strings_contains_concrete_true() {
        // (= (str.contains "hello" "ell") true) -- tautology
        let mut dag = SmtProofDag::new();
        let hello = make_str(&mut dag, "hello");
        let ell = make_str(&mut dag, "ell");
        let contains = make_contains(&mut dag, hello, ell);
        let true_val = make_bool(&mut dag, true);
        let eq = make_eq(&mut dag, contains, true_val);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.contains(\"hello\", \"ell\") = true should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_contains_concrete_false() {
        // (= (str.contains "hello" "xyz") false) -- tautology
        let mut dag = SmtProofDag::new();
        let hello = make_str(&mut dag, "hello");
        let xyz = make_str(&mut dag, "xyz");
        let contains = make_contains(&mut dag, hello, xyz);
        let false_val = make_bool(&mut dag, false);
        let eq = make_eq(&mut dag, contains, false_val);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.contains(\"hello\", \"xyz\") = false should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_contains_contradiction() {
        // (not (= (str.contains "hello" "ell") false)) -- valid
        // str.contains("hello", "ell") = true, so (= ... false) is false,
        // and the negation is true.
        let mut dag = SmtProofDag::new();
        let hello = make_str(&mut dag, "hello");
        let ell = make_str(&mut dag, "ell");
        let contains = make_contains(&mut dag, hello, ell);
        let false_val = make_bool(&mut dag, false);
        let eq = make_eq(&mut dag, contains, false_val);
        let neq = make_not(&mut dag, eq);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[neq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "not(str.contains(\"hello\", \"ell\") = false) should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Concatenation Associativity Tests ─────────────────────────────

    #[test]
    fn test_strings_concat_assoc() {
        // (= (str.++ (str.++ a b) c) (str.++ a (str.++ b c)))
        let mut dag = SmtProofDag::new();
        let a = make_str_var(&mut dag, "a");
        let b = make_str_var(&mut dag, "b");
        let c = make_str_var(&mut dag, "c");
        let ab = make_concat(&mut dag, vec![a, b]);
        let ab_c = make_concat(&mut dag, vec![ab, c]);
        let bc = make_concat(&mut dag, vec![b, c]);
        let a_bc = make_concat(&mut dag, vec![a, bc]);
        let eq = make_eq(&mut dag, ab_c, a_bc);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "concat associativity should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Prefix/Suffix Tests ──────────────────────────────────────────

    #[test]
    fn test_strings_prefix_implies_contains() {
        // (not (str.prefixof a b)) (str.contains b a) -- valid
        // "If a is a prefix of b, then b contains a."
        let mut dag = SmtProofDag::new();
        let a = make_str_var(&mut dag, "a");
        let b = make_str_var(&mut dag, "b");
        let prefix = make_prefixof(&mut dag, a, b);
        let not_prefix = make_not(&mut dag, prefix);
        let contains = make_contains(&mut dag, b, a);

        let clause = vec![not_prefix, contains];
        let verdict = check_strings_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "prefix implies contains should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_suffix_implies_contains() {
        // (not (str.suffixof a b)) (str.contains b a) -- valid
        let mut dag = SmtProofDag::new();
        let a = make_str_var(&mut dag, "a");
        let b = make_str_var(&mut dag, "b");
        let suffix = make_suffixof(&mut dag, a, b);
        let not_suffix = make_not(&mut dag, suffix);
        let contains = make_contains(&mut dag, b, a);

        let clause = vec![not_suffix, contains];
        let verdict = check_strings_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "suffix implies contains should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Concrete String Operation Tests ──────────────────────────────

    #[test]
    fn test_strings_concrete_concat() {
        // (= (str.++ "ab" "cd") "abcd") -- tautology
        let mut dag = SmtProofDag::new();
        let ab = make_str(&mut dag, "ab");
        let cd = make_str(&mut dag, "cd");
        let concat = make_concat(&mut dag, vec![ab, cd]);
        let abcd = make_str(&mut dag, "abcd");
        let eq = make_eq(&mut dag, concat, abcd);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[eq]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.++(\"ab\", \"cd\") = \"abcd\" should be valid: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_strings_concrete_prefix() {
        // (str.prefixof "hel" "hello") -- tautology
        let mut dag = SmtProofDag::new();
        let hel = make_str(&mut dag, "hel");
        let hello = make_str(&mut dag, "hello");
        let prefix = make_prefixof(&mut dag, hel, hello);

        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[prefix]);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "str.prefixof(\"hel\", \"hello\") should be valid: {:?}",
            verdict.detail
        );
    }

    // ── Empty Clause Tests ───────────────────────────────────────────

    #[test]
    fn test_strings_empty_clause_fails() {
        let dag = SmtProofDag::new();
        let verdict = check_strings_lemma(&dag, SmtStepId(0), &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    // ── SMT-LIB String Operation Semantics Tests ─────────────────────

    #[test]
    fn test_str_substr_normal() {
        assert_eq!(str_substr("hello", 1, 3), "ell");
    }

    #[test]
    fn test_str_substr_out_of_bounds() {
        assert_eq!(str_substr("hello", -1, 3), "");
        assert_eq!(str_substr("hello", 10, 3), "");
        assert_eq!(str_substr("hello", 0, -1), "");
    }

    #[test]
    fn test_str_substr_clamped() {
        assert_eq!(str_substr("hello", 3, 100), "lo");
    }

    #[test]
    fn test_str_replace_first_found() {
        assert_eq!(str_replace_first("abcabc", "bc", "XY"), "aXYabc");
    }

    #[test]
    fn test_str_replace_first_not_found() {
        assert_eq!(str_replace_first("hello", "xyz", "ABC"), "hello");
    }

    #[test]
    fn test_str_replace_first_empty_pattern() {
        assert_eq!(str_replace_first("hello", "", "X"), "Xhello");
    }

    #[test]
    fn test_str_at_valid() {
        assert_eq!(str_at("hello", 1), "e");
    }

    #[test]
    fn test_str_at_out_of_bounds() {
        assert_eq!(str_at("hello", -1), "");
        assert_eq!(str_at("hello", 10), "");
    }

    #[test]
    fn test_str_indexof_found() {
        assert_eq!(str_indexof("hello", "ell", 0), 1);
    }

    #[test]
    fn test_str_indexof_not_found() {
        assert_eq!(str_indexof("hello", "xyz", 0), -1);
    }

    #[test]
    fn test_str_indexof_with_offset() {
        assert_eq!(str_indexof("abcabc", "abc", 1), 3);
    }

    #[test]
    fn test_str_indexof_negative_start() {
        assert_eq!(str_indexof("hello", "h", -1), -1);
    }

    // ── Full Pipeline Integration Tests ──────────────────────────────

    #[test]
    fn test_strings_strlen_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let abc = make_str(&mut dag, "abc");
        let len_abc = make_strlen(&mut dag, abc);
        let three = make_int(&mut dag, 3);

        // Assume: str.len("abc") != 3
        let eq = make_eq(&mut dag, len_abc, three);
        let neq = make_not(&mut dag, eq);

        let s0 = dag.add_step(SmtProofStep::Assume(neq));

        // String theory lemma: (= (str.len "abc") 3)
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Strings,
            kind: TheoryLemmaDetail::StringLength,
            clause: vec![eq],
        });

        // Resolve: s0 (neq) + s1 (eq) -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(eq),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "strings strlen proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Strings),
            Some(&1)
        );
    }

    #[test]
    fn test_strings_empty_concat_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let empty = make_str(&mut dag, "");
        let a = make_str_var(&mut dag, "a");
        let concat = make_concat(&mut dag, vec![empty, a]);

        // Assume: str.++("", a) != a
        let eq = make_eq(&mut dag, concat, a);
        let neq = make_not(&mut dag, eq);

        let s0 = dag.add_step(SmtProofStep::Assume(neq));

        // String theory lemma: (= (str.++ "" a) a)
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Strings,
            kind: TheoryLemmaDetail::StringNormalForm,
            clause: vec![eq],
        });

        // Resolve: s0 + s1 -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(eq),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "strings empty concat proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
    }

    #[test]
    fn test_strings_contains_in_full_proof_pipeline() {
        use crate::smt_verify::dag::{SmtProofStep, SmtTheory, TheoryLemmaDetail};
        use crate::smt_verify::{verify_smt_proof, VerifyMode};

        let mut dag = SmtProofDag::new();
        let hello = make_str(&mut dag, "hello");
        let ell = make_str(&mut dag, "ell");
        let contains = make_contains(&mut dag, hello, ell);
        let false_val = make_bool(&mut dag, false);

        // Assume: str.contains("hello", "ell") = false
        let eq = make_eq(&mut dag, contains, false_val);
        let s0 = dag.add_step(SmtProofStep::Assume(eq));

        // String theory lemma: (not (= (str.contains "hello" "ell") false))
        // Valid because str.contains("hello", "ell") = true != false.
        let neq = make_not(&mut dag, eq);
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Strings,
            kind: TheoryLemmaDetail::StringContent,
            clause: vec![neq],
        });

        // Resolve: s0 + s1 -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(eq),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "strings contains proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
    }
}
