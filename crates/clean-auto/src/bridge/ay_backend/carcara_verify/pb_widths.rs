// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Require complete pseudo-Boolean expansions before the pinned checker runs.
//!
//! Upstream Carcara d62d45cf accepts truncated bit sums in comparison/equality
//! rules. Dropping a high bit can certify equality of distinct words. This
//! adapter checks exact expansion lengths on the parsed DAG, including nested
//! proofs and expanded definitions, then runs the independent rule checker.
//!
//! The vendored copy in `third-party/carcara` now requires exact lengths
//! itself. This guard stays as defense in depth: it only refuses, and never
//! accepts, a step.

use super::VerifyError;
use carcara::ast::{pool::TermPool, Operator, ProofCommand, ProofStep, Rc, Sort, Term};
use std::time::Instant;

/// Parses under Clean's Alethe dialect, `Config::clean_dialect()`
/// (`third-party/carcara/DOWNSTREAM.md` § Dialect), which is the only place the
/// adapter's parser options come from.
#[cfg(test)]
pub(super) fn check(problem: &str, proof: &str) -> Result<bool, VerifyError> {
    check_until(problem, proof, None)
}

/// [`check`], refused once `deadline` passes: the vendored parser polls it as it reads
/// (`parse_instance_until`), the vendored checker reads it before and after every command, and the
/// adapter before each reading of the problem and after parsing it. A reading stopped by the
/// deadline is not retried.
pub(super) fn check_until(
    problem: &str,
    proof: &str,
    deadline: Option<Instant>,
) -> Result<bool, VerifyError> {
    let ordinary = check_with_parser_until(
        problem,
        proof,
        carcara::parser::Config::clean_dialect(),
        deadline,
    );
    if ordinary.is_ok()
        || matches!(ordinary, Err(VerifyError::CarcaraDeadline(_)))
        || !problem.contains("(define-fun")
    {
        return ordinary;
    }
    // Alethe producers use either defining assertions or macro expansion for
    // SMT-LIB define-fun. Carcara supports both interpretations of the same
    // original input. Reparse the entire problem and proof together; every
    // adapter guard and the unchanged independent checker run again. Holes
    // are never repaired, and no assertion is removed or invented here.
    match check_with_parser_until(
        problem,
        proof,
        carcara::parser::Config::clean_dialect().apply_function_defs(true),
        deadline,
    ) {
        Ok(verified) => Ok(verified),
        Err(deadline @ VerifyError::CarcaraDeadline(_)) => Err(deadline),
        // Both readings fail. Report both, so a refusal under the macro reading (the one a
        // producer that expands definitions meant) is not hidden behind the ordinary reading's.
        Err(VerifyError::CarcaraError(macro_error)) => match ordinary {
            Err(VerifyError::CarcaraError(ordinary_error)) => Err(VerifyError::CarcaraError(
                format!("{ordinary_error}; with define-fun expanded as macros: {macro_error}"),
            )),
            other => other,
        },
        Err(_) => ordinary,
    }
}

#[cfg(test)]
pub(super) fn check_with_parser(
    problem: &str,
    proof: &str,
    config: carcara::parser::Config,
) -> Result<bool, VerifyError> {
    check_with_parser_until(problem, proof, config, None)
}

fn check_with_parser_until(
    problem: &str,
    proof: &str,
    config: carcara::parser::Config,
    deadline: Option<Instant>,
) -> Result<bool, VerifyError> {
    let passed = || deadline.is_some_and(|deadline| Instant::now() >= deadline);
    if passed() {
        return Err(super::diagnostics::deadline_passed("before parsing"));
    }
    let (problem, proof, rules, mut pool) =
        carcara::parser::parse_instance_until(problem, proof, None, config, deadline)
            .map_err(super::diagnostics::failure)?;
    if passed() {
        return Err(super::diagnostics::deadline_passed("after parsing"));
    }
    for command in proof.iter() {
        if let ProofCommand::Step(step) = command {
            if !super::ashr::safe_shift(step, &mut pool) {
                return Err(VerifyError::CarcaraError(format!(
                    "step '{}' with rule '{}': arithmetic shift may overshift a negative operand",
                    step.id, step.rule
                )));
            }
            if !complete_expansion(step, &mut pool) {
                return Err(VerifyError::CarcaraError(format!(
                    "step '{}' with rule '{}': incomplete or invalid pseudo-Boolean bit expansion",
                    step.id, step.rule
                )));
            }
        }
    }
    // The production adapter explicitly consumes Clean's parser AND rule
    // dialect. A standalone/default checker retains the upstream contract.
    // The new wire name is a separately versioned capability. Older
    // `clean_dialect()` users retain the immediate scalar rule contract.
    let config = carcara::checker::Config::clean_dialect()
        .with_bv_offset_spines_v1()
        .with_bv_reconstruct_v1()
        .deadline(deadline);
    carcara::checker::ProofChecker::new(&mut pool, &rules, config)
        .check(&problem, &proof)
        .map(|is_holey| !is_holey)
        .map_err(super::diagnostics::failure)
}

fn binary(term: &Rc<Term>, op: Operator) -> Option<(&Rc<Term>, &Rc<Term>)> {
    let Term::Op(actual, args) = term.as_ref() else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    (*actual == op).then_some((left, right))
}

fn width(term: &Rc<Term>, pool: &mut dyn TermPool) -> Option<usize> {
    let Sort::BitVec(width) = pool.sort(term).as_ref().clone() else {
        return None;
    };
    (width > 0).then_some(width)
}

fn sum_len(term: &Rc<Term>) -> usize {
    match term.as_ref() {
        Term::Op(Operator::Add, args) => args.len(),
        _ => 1,
    }
}

fn complete_expansion(step: &ProofStep, pool: &mut dyn TermPool) -> bool {
    let signed = matches!(
        step.rule.as_str(),
        "pbblast_bvslt" | "pbblast_bvsgt" | "pbblast_bvsle" | "pbblast_bvsge"
    );
    let unsigned = matches!(
        step.rule.as_str(),
        "pbblast_bveq" | "pbblast_bvult" | "pbblast_bvugt" | "pbblast_bvule" | "pbblast_bvuge"
    );
    let word = matches!(step.rule.as_str(), "pbblast_pbbvar" | "pbblast_pbbconst");
    if !signed && !unsigned && !word {
        return true;
    }
    let result = (|| {
        let [clause] = step.clause.as_slice() else {
            return None;
        };
        let (source, target) = binary(clause, Operator::Equals)?;
        if word {
            return word_expansion(source, target, step.rule == "pbblast_pbbconst", pool);
        }
        let Term::Op(_, operands) = source.as_ref() else {
            return None;
        };
        let [left, right] = operands.as_slice() else {
            return None;
        };
        let width = width(left, pool)?;
        if self::width(right, pool)? != width {
            return None;
        }
        let target_op = if step.rule == "pbblast_bveq" {
            Operator::Equals
        } else {
            Operator::GreaterEq
        };
        let (difference, _) = binary(target, target_op)?;
        let (sum_left, sum_right) = if signed {
            let (left, right) = binary(difference, Operator::Add)?;
            let (lower_left, _) = binary(left, Operator::Sub)?;
            let (_, lower_right) = binary(right, Operator::Sub)?;
            (lower_left, lower_right)
        } else {
            binary(difference, Operator::Sub)?
        };
        let expected = width - usize::from(signed);
        Some(sum_len(sum_left) == expected && sum_len(sum_right) == expected)
    })();
    result == Some(true)
}

fn word_expansion(
    source: &Rc<Term>,
    target: &Rc<Term>,
    constant: bool,
    pool: &mut dyn TermPool,
) -> Option<bool> {
    let Term::Op(Operator::BvPBbTerm, bits) = target.as_ref() else {
        return None;
    };
    if bits.len() != width(source, pool)? {
        return Some(false);
    }
    if constant {
        // The upstream constant rule truncates arbitrary integers to i32.
        // Check the actual integer before it can be mistaken for a zero/one bit.
        for bit in bits {
            let value = bit.as_integer()?;
            if value != 0 && value != 1 {
                return Some(false);
            }
        }
    }
    Some(true)
}

#[cfg(test)]
mod tests;
