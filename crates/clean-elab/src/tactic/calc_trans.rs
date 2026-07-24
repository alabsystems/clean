// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Transitivity resolution helpers for mixed-relation `calc` chains.
//!
//! Goal matching and relation expression builders are in `calc_trans_match`.

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::calc::{CalcRel, CalcStep};
use super::tc_app::rel_inst_for_type;
use super::{ProofState, TacticError};

/// Metadata for a supported calc transitivity lemma.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) struct CalcTransRule {
    /// Left relation in the chain.
    pub rel_a: CalcRel,
    /// Right relation in the chain.
    pub rel_b: CalcRel,
    /// Result relation after transitivity.
    pub result_rel: CalcRel,
    /// Lean constant name implementing the step.
    pub lemma_name: &'static str,
    /// Metadata arity for the rule table.
    #[cfg_attr(not(test), allow(dead_code))]
    pub arg_count: usize,
}

const CALC_TRANS_RULES: [CalcTransRule; 20] = [
    // -- Equality --------------------------------------------------------
    CalcTransRule {
        rel_a: CalcRel::Eq,
        rel_b: CalcRel::Eq,
        result_rel: CalcRel::Eq,
        lemma_name: "Eq.trans",
        arg_count: 6,
    },
    // -- Le/Lt family (ascending order) ----------------------------------
    CalcTransRule {
        rel_a: CalcRel::Le,
        rel_b: CalcRel::Le,
        result_rel: CalcRel::Le,
        lemma_name: "le_trans",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Lt,
        rel_b: CalcRel::Lt,
        result_rel: CalcRel::Lt,
        lemma_name: "lt_trans",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Le,
        rel_b: CalcRel::Lt,
        result_rel: CalcRel::Lt,
        lemma_name: "lt_of_le_of_lt",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Lt,
        rel_b: CalcRel::Le,
        result_rel: CalcRel::Lt,
        lemma_name: "lt_of_lt_of_le",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Le,
        rel_b: CalcRel::Eq,
        result_rel: CalcRel::Le,
        lemma_name: "le_of_le_of_eq",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Eq,
        rel_b: CalcRel::Le,
        result_rel: CalcRel::Le,
        lemma_name: "le_of_eq_of_le",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Lt,
        rel_b: CalcRel::Eq,
        result_rel: CalcRel::Lt,
        lemma_name: "lt_of_lt_of_eq",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Eq,
        rel_b: CalcRel::Lt,
        result_rel: CalcRel::Lt,
        lemma_name: "lt_of_eq_of_lt",
        arg_count: 6,
    },
    // -- Ge/Gt family (descending order) ---------------------------------
    CalcTransRule {
        rel_a: CalcRel::Ge,
        rel_b: CalcRel::Ge,
        result_rel: CalcRel::Ge,
        lemma_name: "ge_trans",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Gt,
        rel_b: CalcRel::Gt,
        result_rel: CalcRel::Gt,
        lemma_name: "gt_trans",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Ge,
        rel_b: CalcRel::Gt,
        result_rel: CalcRel::Gt,
        lemma_name: "gt_of_ge_of_gt",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Gt,
        rel_b: CalcRel::Ge,
        result_rel: CalcRel::Gt,
        lemma_name: "gt_of_gt_of_ge",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Ge,
        rel_b: CalcRel::Eq,
        result_rel: CalcRel::Ge,
        lemma_name: "ge_of_ge_of_eq",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Eq,
        rel_b: CalcRel::Ge,
        result_rel: CalcRel::Ge,
        lemma_name: "ge_of_eq_of_ge",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Gt,
        rel_b: CalcRel::Eq,
        result_rel: CalcRel::Gt,
        lemma_name: "gt_of_gt_of_eq",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Eq,
        rel_b: CalcRel::Gt,
        result_rel: CalcRel::Gt,
        lemma_name: "gt_of_eq_of_gt",
        arg_count: 6,
    },
    // -- Iff (propositional equivalence) ---------------------------------
    CalcTransRule {
        rel_a: CalcRel::Iff,
        rel_b: CalcRel::Iff,
        result_rel: CalcRel::Iff,
        lemma_name: "Iff.trans",
        arg_count: 4,
    },
    // -- Ne (disequality) ------------------------------------------------
    CalcTransRule {
        rel_a: CalcRel::Eq,
        rel_b: CalcRel::Ne,
        result_rel: CalcRel::Ne,
        lemma_name: "ne_of_eq_of_ne",
        arg_count: 6,
    },
    CalcTransRule {
        rel_a: CalcRel::Ne,
        rel_b: CalcRel::Eq,
        result_rel: CalcRel::Ne,
        lemma_name: "ne_of_ne_of_eq",
        arg_count: 6,
    },
];

#[must_use]
pub(crate) fn rel_const_name(rel: CalcRel) -> &'static str {
    match rel {
        CalcRel::Eq => "Eq",
        CalcRel::Le => "LE.le",
        CalcRel::Lt => "LT.lt",
        CalcRel::Ge => "GE.ge",
        CalcRel::Gt => "GT.gt",
        CalcRel::Ne => "Ne",
        CalcRel::Iff => "Iff",
    }
}

fn apply_apps(mut head: Expr, args: &[Expr]) -> Expr {
    for arg in args {
        head = Expr::app(head, arg.clone());
    }
    head
}

fn apply_trans_rule(
    state: &mut ProofState,
    rule: &CalcTransRule,
    ty: &Expr,
    levels: &[Level],
    lhs: &Expr,
    mid: &Expr,
    rhs: &Expr,
    left_proof: &Expr,
    right_proof: &Expr,
) -> Result<Expr, TacticError> {
    let const_name = Name::from_string(rule.lemma_name);
    if state.env.get_const(&const_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: rule.lemma_name.to_string(),
        });
    }

    let lemma = if matches!(rule.result_rel, CalcRel::Eq) {
        Expr::const_(const_name, levels.to_vec())
    } else if matches!(rule.result_rel, CalcRel::Iff) {
        Expr::const_(const_name, vec![])
    } else {
        state.mk_const_str(rule.lemma_name)
    };

    let proof = match rule.result_rel {
        CalcRel::Eq => apply_apps(
            lemma,
            &[
                ty.clone(),
                lhs.clone(),
                mid.clone(),
                rhs.clone(),
                left_proof.clone(),
                right_proof.clone(),
            ],
        ),
        CalcRel::Iff => apply_apps(
            lemma,
            &[
                lhs.clone(),
                mid.clone(),
                rhs.clone(),
                left_proof.clone(),
                right_proof.clone(),
            ],
        ),
        CalcRel::Ne => {
            // Ne lemmas take the same shape as Eq: @lemma.{u} ty a b c h1 h2
            apply_apps(
                lemma,
                &[
                    ty.clone(),
                    lhs.clone(),
                    mid.clone(),
                    rhs.clone(),
                    left_proof.clone(),
                    right_proof.clone(),
                ],
            )
        }
        CalcRel::Le | CalcRel::Lt | CalcRel::Ge | CalcRel::Gt => {
            let inst = rel_inst_for_type(ty, rel_const_name(rule.result_rel));
            apply_apps(
                lemma,
                &[
                    ty.clone(),
                    inst,
                    lhs.clone(),
                    mid.clone(),
                    rhs.clone(),
                    left_proof.clone(),
                    right_proof.clone(),
                ],
            )
        }
    };

    Ok(proof)
}

/// Return the supported calc transitivity rules.
///
/// REQUIRES: none.
/// ENSURES: Returns a stable slice containing all mixed-relation calc
/// transitivity rules supported by this module.
#[must_use]
pub(crate) fn calc_trans_rules() -> &'static [CalcTransRule] {
    &CALC_TRANS_RULES
}

/// Look up the transitivity rule for two consecutive calc relations.
///
/// REQUIRES: `rel_a` and `rel_b` are valid calc relation tags.
/// ENSURES: Returns `Some(rule)` iff the relation pair is supported.
#[must_use]
pub(crate) fn lookup_trans_rule(rel_a: CalcRel, rel_b: CalcRel) -> Option<&'static CalcTransRule> {
    calc_trans_rules()
        .iter()
        .find(|rule| rule.rel_a == rel_a && rule.rel_b == rel_b)
}

/// Build the composite proof term for a multi-step calc chain.
///
/// REQUIRES: `steps` is non-empty and `step_proofs.len() == steps.len()`.
/// ENSURES: On `Ok(proof)`, `proof` is the iterated transitivity composition
/// of the step proofs from `start` to the final RHS.
/// ENSURES: Returns `Err` when an adjacent relation pair is unsupported or its
/// lemma is missing from the environment.
pub(crate) fn build_trans_chain(
    state: &mut ProofState,
    steps: &[CalcStep],
    step_proofs: &[Expr],
    start: &Expr,
    ty: &Expr,
    levels: &[Level],
) -> Result<Expr, TacticError> {
    if steps.is_empty() {
        return Err(TacticError::MissingArgument {
            tactic: "build_trans_chain".into(),
            expected: "at least one calc step".into(),
        });
    }
    if step_proofs.len() != steps.len() {
        return Err(TacticError::InvalidTarget {
            tactic: "build_trans_chain".into(),
            detail: format!(
                "step proof count {} does not match calc step count {}",
                step_proofs.len(),
                steps.len()
            ),
        });
    }
    if steps.len() == 1 {
        return Ok(state.metas.instantiate(&step_proofs[0]));
    }

    let ty = state.metas.instantiate(ty);
    let start = state.metas.instantiate(start);
    let mut acc = state.metas.instantiate(&step_proofs[0]);
    let mut current_rel = steps[0].rel;
    let mut current_rhs = state.metas.instantiate(&steps[0].rhs);

    for index in 1..steps.len() {
        let next_rel = steps[index].rel;
        let next_rhs = state.metas.instantiate(&steps[index].rhs);
        let next_proof = state.metas.instantiate(&step_proofs[index]);
        let rule =
            lookup_trans_rule(current_rel, next_rel).ok_or_else(|| TacticError::InvalidTarget {
                tactic: "calc_block".into(),
                detail: format!(
                    "unsupported calc transitivity step: {:?} followed by {:?}",
                    current_rel, next_rel
                ),
            })?;

        acc = apply_trans_rule(
            state,
            rule,
            &ty,
            levels,
            &start,
            &current_rhs,
            &next_rhs,
            &acc,
            &next_proof,
        )?;
        current_rel = rule.result_rel;
        current_rhs = next_rhs;
    }

    Ok(acc)
}
