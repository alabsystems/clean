// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural proof translation from resolved Metamath frames into clean AST.

use super::ast::{
    CompressedProof, Formula, Proof, ResolvedAssertion, ResolvedDatabase, ResolvedStatement,
};
use super::encode::{decl_name, encode_assertion, encode_proof};
use super::{MetamathError, MetamathResult};
use clean_kernel::Declaration;
use hashbrown::{HashMap, HashSet};

/// Translate a parsed Metamath database into clean kernel declarations.
pub fn translate_database(db: &super::Database) -> MetamathResult<Vec<Declaration>> {
    let resolved = super::resolve_database(db)?;
    resolved
        .statements
        .iter()
        .map(|statement| translate_statement(statement, &resolved))
        .collect()
}

#[derive(Clone)]
struct StackEntry {
    formula: Formula,
    proof: ProofNode,
}

#[derive(Clone)]
pub(super) enum ProofNode {
    Hyp {
        label: String,
        formula: Formula,
    },
    Apply {
        label: String,
        args: Vec<ProofNode>,
        substitutions: Vec<Substitution>,
        result: Formula,
    },
}

#[derive(Clone)]
pub(super) struct Substitution {
    pub(super) variable: String,
    pub(super) typecode: String,
    pub(super) formula: Formula,
}

enum ProofCode {
    Label(String),
    Save,
    SavedRef(usize),
}

fn translate_statement(
    statement: &ResolvedStatement,
    db: &ResolvedDatabase,
) -> MetamathResult<Declaration> {
    match statement {
        ResolvedStatement::Floating(hyp) => Ok(Declaration::Axiom {
            name: decl_name(&hyp.label),
            level_params: vec![],
            type_: encode_assertion(
                "floating",
                &hyp.label,
                &Formula {
                    typecode: hyp.typecode.clone(),
                    tokens: vec![hyp.variable.clone()],
                },
                &[],
                &[],
                &[],
            ),
        }),
        ResolvedStatement::Essential(hyp) => Ok(Declaration::Axiom {
            name: decl_name(&hyp.label),
            level_params: vec![],
            type_: encode_assertion("essential", &hyp.label, &hyp.formula, &[], &[], &[]),
        }),
        ResolvedStatement::Assertion(assertion) => {
            let mandatory_labels: Vec<String> = assertion
                .mandatory_floats
                .iter()
                .map(|hyp| hyp.label.clone())
                .collect();
            let essential_labels: Vec<String> = assertion
                .essential_hyps
                .iter()
                .map(|hyp| hyp.label.clone())
                .collect();
            let type_ = encode_assertion(
                assertion.kind,
                &assertion.label,
                &assertion.formula,
                &mandatory_labels,
                &essential_labels,
                &assertion.disjoints,
            );
            if assertion.kind == "provable" {
                let proof = translate_proof(assertion, db)?;
                Ok(Declaration::Opaque {
                    name: decl_name(&assertion.label),
                    level_params: vec![],
                    type_,
                    value: encode_proof(&proof),
                })
            } else {
                Ok(Declaration::Axiom {
                    name: decl_name(&assertion.label),
                    level_params: vec![],
                    type_,
                })
            }
        }
    }
}

fn translate_proof(
    assertion: &ResolvedAssertion,
    db: &ResolvedDatabase,
) -> MetamathResult<ProofNode> {
    let proof = assertion.proof.as_ref().ok_or_else(|| {
        MetamathError::InvalidStatement(format!("missing proof for {}", assertion.label))
    })?;
    let codes = proof_codes(assertion, proof)?;
    let theorem_disjoints: HashSet<(String, String)> =
        assertion.disjoints.iter().cloned().collect();
    let theorem_vars: HashSet<String> = assertion
        .mandatory_floats
        .iter()
        .map(|hyp| hyp.variable.clone())
        .collect();
    let mut stack = Vec::new();
    let mut saved = Vec::new();
    let mut last_result: Option<StackEntry> = None;
    for code in codes {
        let entry = match code {
            ProofCode::Label(label) => apply_label(
                assertion,
                &label,
                db,
                &theorem_vars,
                &theorem_disjoints,
                &mut stack,
            )?,
            ProofCode::Save => {
                let Some(prev) = last_result.clone() else {
                    return Err(MetamathError::InvalidCompressedProof {
                        theorem: assertion.label.clone(),
                        message: "Z used before any proof step".to_string(),
                    });
                };
                saved.push(prev);
                continue;
            }
            ProofCode::SavedRef(index) => {
                let entry = saved
                    .get(index)
                    .cloned()
                    .ok_or(MetamathError::InvalidSavedStep {
                        theorem: assertion.label.clone(),
                        index,
                    })?;
                stack.push(entry.clone());
                entry
            }
        };
        last_result = Some(entry);
    }
    if stack.len() != 1 {
        return Err(MetamathError::FinalResultMismatch {
            theorem: assertion.label.clone(),
        });
    }
    let result = stack.pop().expect("stack length checked");
    if result.formula != assertion.formula {
        return Err(MetamathError::FinalResultMismatch {
            theorem: assertion.label.clone(),
        });
    }
    Ok(result.proof)
}

fn apply_label(
    theorem: &ResolvedAssertion,
    label: &str,
    db: &ResolvedDatabase,
    theorem_vars: &HashSet<String>,
    theorem_disjoints: &HashSet<(String, String)>,
    stack: &mut Vec<StackEntry>,
) -> MetamathResult<StackEntry> {
    let statement = db.get(label).ok_or(MetamathError::UnknownLabel {
        theorem: theorem.label.clone(),
        label: label.to_string(),
    })?;
    let entry = match statement {
        ResolvedStatement::Floating(hyp) => StackEntry {
            formula: Formula {
                typecode: hyp.typecode.clone(),
                tokens: vec![hyp.variable.clone()],
            },
            proof: ProofNode::Hyp {
                label: hyp.label.clone(),
                formula: Formula {
                    typecode: hyp.typecode.clone(),
                    tokens: vec![hyp.variable.clone()],
                },
            },
        },
        ResolvedStatement::Essential(hyp) => StackEntry {
            formula: hyp.formula.clone(),
            proof: ProofNode::Hyp {
                label: hyp.label.clone(),
                formula: hyp.formula.clone(),
            },
        },
        ResolvedStatement::Assertion(assertion) => {
            apply_assertion(theorem, assertion, theorem_vars, theorem_disjoints, stack)?
        }
    };
    stack.push(entry.clone());
    Ok(entry)
}

fn apply_assertion(
    theorem: &ResolvedAssertion,
    assertion: &ResolvedAssertion,
    theorem_vars: &HashSet<String>,
    theorem_disjoints: &HashSet<(String, String)>,
    stack: &mut Vec<StackEntry>,
) -> MetamathResult<StackEntry> {
    let hyp_count = assertion.mandatory_floats.len() + assertion.essential_hyps.len();
    if stack.len() < hyp_count {
        return Err(MetamathError::StackUnderflow {
            theorem: theorem.label.clone(),
            label: assertion.label.clone(),
        });
    }
    let args: Vec<StackEntry> = stack.drain(stack.len() - hyp_count..).collect();
    let mut subst = HashMap::new();
    let mut substitutions = Vec::new();
    for (arg, hyp) in args.iter().zip(assertion.mandatory_floats.iter()) {
        if arg.formula.typecode != hyp.typecode {
            return Err(MetamathError::TypeMismatch {
                theorem: theorem.label.clone(),
                label: assertion.label.clone(),
                expected: hyp.typecode.clone(),
                actual: arg.formula.typecode.clone(),
            });
        }
        let binding = Substitution {
            variable: hyp.variable.clone(),
            typecode: hyp.typecode.clone(),
            formula: arg.formula.clone(),
        };
        subst.insert(hyp.variable.clone(), arg.formula.clone());
        substitutions.push(binding);
    }
    let essential_offset = assertion.mandatory_floats.len();
    for (arg, hyp) in args[essential_offset..]
        .iter()
        .zip(assertion.essential_hyps.iter())
    {
        let expected = instantiate_formula(&hyp.formula, &subst);
        if arg.formula != expected {
            return Err(MetamathError::EssentialMismatch {
                theorem: theorem.label.clone(),
                label: assertion.label.clone(),
            });
        }
    }
    enforce_disjoints(
        theorem,
        assertion,
        theorem_vars,
        theorem_disjoints,
        &substitutions,
    )?;
    let result = instantiate_formula(&assertion.formula, &subst);
    Ok(StackEntry {
        formula: result.clone(),
        proof: ProofNode::Apply {
            label: assertion.label.clone(),
            args: args.into_iter().map(|entry| entry.proof).collect(),
            substitutions,
            result,
        },
    })
}

fn enforce_disjoints(
    theorem: &ResolvedAssertion,
    assertion: &ResolvedAssertion,
    theorem_vars: &HashSet<String>,
    theorem_disjoints: &HashSet<(String, String)>,
    substitutions: &[Substitution],
) -> MetamathResult<()> {
    let mut subst_map = HashMap::new();
    for binding in substitutions {
        subst_map.insert(binding.variable.clone(), binding.formula.clone());
    }
    for (left, right) in &assertion.disjoints {
        let Some(left_formula) = subst_map.get(left) else {
            continue;
        };
        let Some(right_formula) = subst_map.get(right) else {
            continue;
        };
        let left_vars = vars_in_formula(left_formula, theorem_vars);
        let right_vars = vars_in_formula(right_formula, theorem_vars);
        for left_var in &left_vars {
            for right_var in &right_vars {
                if left_var == right_var
                    || !theorem_disjoints.contains(&ordered_pair(left_var, right_var))
                {
                    return Err(MetamathError::DisjointViolation {
                        theorem: theorem.label.clone(),
                        label: assertion.label.clone(),
                        left: left_var.clone(),
                        right: right_var.clone(),
                    });
                }
            }
        }
    }
    Ok(())
}

fn vars_in_formula(formula: &Formula, theorem_vars: &HashSet<String>) -> HashSet<String> {
    formula
        .tokens
        .iter()
        .filter(|token| theorem_vars.contains(*token))
        .cloned()
        .collect()
}

fn instantiate_formula(formula: &Formula, subst: &HashMap<String, Formula>) -> Formula {
    let mut tokens = Vec::new();
    for token in &formula.tokens {
        if let Some(replacement) = subst.get(token) {
            tokens.extend(replacement.tokens.iter().cloned());
        } else {
            tokens.push(token.clone());
        }
    }
    Formula {
        typecode: formula.typecode.clone(),
        tokens,
    }
}

fn proof_codes(assertion: &ResolvedAssertion, proof: &Proof) -> MetamathResult<Vec<ProofCode>> {
    match proof {
        Proof::Uncompressed(labels) => Ok(labels.iter().cloned().map(ProofCode::Label).collect()),
        Proof::Compressed(compressed) => decode_compressed(assertion, compressed),
    }
}

fn decode_compressed(
    assertion: &ResolvedAssertion,
    proof: &CompressedProof,
) -> MetamathResult<Vec<ProofCode>> {
    let mut labels: Vec<String> = assertion
        .mandatory_floats
        .iter()
        .map(|hyp| hyp.label.clone())
        .collect();
    labels.extend(assertion.essential_hyps.iter().map(|hyp| hyp.label.clone()));
    labels.extend(proof.labels.iter().cloned());
    let label_count = labels.len();
    let mut codes = Vec::new();
    let mut value = 0usize;
    for ch in proof.code.chars().filter(|c| !c.is_whitespace()) {
        match ch {
            'A'..='T' => {
                value = value
                    .checked_mul(20)
                    .and_then(|v| v.checked_add(ch as usize - 'A' as usize + 1))
                    .ok_or_else(|| MetamathError::InvalidCompressedProof {
                        theorem: assertion.label.clone(),
                        message: "compressed proof numeric code overflow".to_string(),
                    })?;
                if value == 0 {
                    return Err(MetamathError::InvalidCompressedProof {
                        theorem: assertion.label.clone(),
                        message: "zero label code".to_string(),
                    });
                }
                if value <= label_count {
                    codes.push(ProofCode::Label(labels[value - 1].clone()));
                } else {
                    codes.push(ProofCode::SavedRef(value - label_count - 1));
                }
                value = 0;
            }
            'U'..='Y' => {
                value = value
                    .checked_mul(5)
                    .and_then(|v| v.checked_add(ch as usize - 'U' as usize + 1))
                    .ok_or_else(|| MetamathError::InvalidCompressedProof {
                        theorem: assertion.label.clone(),
                        message: "compressed proof numeric code overflow".to_string(),
                    })?;
            }
            'Z' => {
                if value != 0 {
                    return Err(MetamathError::InvalidCompressedProof {
                        theorem: assertion.label.clone(),
                        message: "unfinished numeric code before Z".to_string(),
                    });
                }
                codes.push(ProofCode::Save);
            }
            _ => {
                return Err(MetamathError::InvalidCompressedProof {
                    theorem: assertion.label.clone(),
                    message: format!("unexpected compressed proof character {ch}"),
                })
            }
        }
    }
    if value != 0 {
        return Err(MetamathError::InvalidCompressedProof {
            theorem: assertion.label.clone(),
            message: "unterminated compressed code".to_string(),
        });
    }
    Ok(codes)
}

fn ordered_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}
