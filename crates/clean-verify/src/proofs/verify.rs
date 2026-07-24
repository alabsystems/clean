// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ProofTerm verification methods and level-parameter utilities.

use super::{ProofError, ProofTerm};
use crate::spec::{AxiomCategory, ProofStatus, Specification};
use clean_elab::ElabCtx;
use clean_kernel::{Expr, ExprKind, Level, Name, TypeChecker};
use clean_parser::parse_expr;
use std::collections::HashSet;
use std::panic::Location;

fn canonical_property_type(spec: &Specification, property: &str) -> Option<Expr> {
    let env = spec.env();
    let name = Name::from_string(property);
    env.get_const(&name)
        .map(|decl| decl.type_.clone())
        .or_else(|| env.get_inductive(&name).map(|decl| decl.type_.clone()))
        .or_else(|| env.get_constructor(&name).map(|decl| decl.type_.clone()))
        .or_else(|| env.get_recursor(&name).map(|decl| decl.type_.clone()))
}

fn normalize_level_param_names(expr: &Expr) -> Expr {
    let mut params = Vec::new();
    collect_level_params_expr(expr, &mut params);
    if params.is_empty() {
        return expr.clone();
    }
    let subst: Vec<_> = params
        .into_iter()
        .enumerate()
        .map(|(idx, name)| (name, Level::param(Name::from_string(&format!("u_{idx}")))))
        .collect();
    expr.instantiate_level_params(&subst)
}

fn collect_level_params_expr(expr: &Expr, out: &mut Vec<Name>) {
    let mut stack = vec![expr];
    while let Some(curr) = stack.pop() {
        match curr.kind() {
            ExprKind::Sort(level) => collect_level_params_level(level, out),
            ExprKind::Const(_, levels) => {
                for level in levels {
                    collect_level_params_level(level, out);
                }
            }
            ExprKind::App(func, arg) => {
                stack.push(arg);
                stack.push(func);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(body);
                stack.push(ty);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(body);
                stack.push(val);
                stack.push(ty);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }
}

fn proof_type_matches(tc: &TypeChecker<'_>, inferred: &Expr, expected: &Expr) -> bool {
    if tc.is_def_eq(inferred, expected) {
        return true;
    }
    let normalized_inferred = normalize_level_param_names(inferred);
    let normalized_expected = normalize_level_param_names(expected);
    tc.is_def_eq(&normalized_inferred, &normalized_expected)
}

fn collect_level_params_level(level: &Level, out: &mut Vec<Name>) {
    let mut stack = vec![level];
    while let Some(curr) = stack.pop() {
        match curr {
            Level::Param(name) => {
                if !out.contains(name) {
                    out.push(name.clone());
                }
            }
            Level::Succ(inner) => stack.push(inner),
            Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
                stack.push(rhs);
                stack.push(lhs);
            }
            Level::Zero => {}
        }
    }
}

impl ProofTerm {
    /// Create a new proof term
    #[track_caller]
    #[must_use]
    pub fn new(property: &str, proof_src: &str, explanation: &str) -> Self {
        let caller = Location::caller();
        ProofTerm {
            property: property.to_string(),
            proof_src: proof_src.to_string(),
            source_file: caller.file().to_string(),
            source_line: caller.line(),
            _elaborated: None,
            explanation: explanation.to_string(),
        }
    }

    /// Verify the proof against the specification
    ///
    /// # Errors
    /// Returns `ProofError` if verification fails.
    pub fn verify(&self, spec: &Specification) -> Result<(), ProofError> {
        let _ = self.verify_and_elaborate(spec)?;
        Ok(())
    }

    /// Verify proof and compute its dependency classification
    ///
    /// Returns (proof_status, axiom_dependencies) where:
    /// - proof_status: DerivedProved if no helper axiom deps, DerivedPending otherwise
    /// - axiom_dependencies: names of HelperAxiom constants this proof depends on
    ///
    /// Part of #326: Proof dependency audit
    ///
    /// # Errors
    /// Returns `ProofError` if verification fails.
    pub fn verify_with_deps(
        &self,
        spec: &Specification,
    ) -> Result<(ProofStatus, HashSet<String>), ProofError> {
        let proof_expr = self.verify_and_elaborate(spec)?;

        // Extract all constants from the proof
        let proof_consts = proof_expr.collect_constants();

        // Classify dependencies - find which are HelperAxioms
        let mut axiom_deps = HashSet::new();
        for const_name in proof_consts {
            let name_str = const_name.to_string();
            if let Some(dep_def) = spec.definitions().get(&name_str) {
                match dep_def.category {
                    AxiomCategory::HelperAxiom => {
                        axiom_deps.insert(name_str);
                    }
                    AxiomCategory::DerivedLemma
                        if dep_def.proof_status != ProofStatus::DerivedProved =>
                    {
                        // Transitive: depends on unproved lemma's axiom deps
                        axiom_deps.extend(dep_def.axiom_deps.iter().cloned());
                    }
                    _ => {}
                }
            }
        }

        // Determine final status
        let status = if axiom_deps.is_empty() {
            ProofStatus::DerivedProved
        } else {
            ProofStatus::DerivedPending
        };

        Ok((status, axiom_deps))
    }

    /// Internal: verify proof and return elaborated expression
    fn verify_and_elaborate(&self, spec: &Specification) -> Result<Expr, ProofError> {
        // Get the property's type from the specification
        let def = spec
            .definitions()
            .get(&self.property)
            .ok_or_else(|| ProofError::UnknownProperty(self.property.clone()))?;

        let type_expr = canonical_property_type(spec, &self.property)
            .or_else(|| def.elaborated_type.clone())
            .ok_or_else(|| ProofError::ElabError("property type".to_string()))?;

        // Parse and elaborate the proof term
        let proof_surface = parse_expr(&self.proof_src)
            .map_err(|e| ProofError::ParseError(format!("proof: {e}")))?;
        let mut ctx = ElabCtx::new(spec.env());
        let proof_expr = ctx
            .elaborate(&proof_surface)
            .map_err(|e| ProofError::ElabError(format!("proof: {e}")))?;

        // Type check
        let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
        let inferred = tc
            .infer_type(&proof_expr)
            .map_err(|e| ProofError::TypeMismatch {
                expected: format!("{type_expr:?}"),
                actual: format!("type error: {e:?}"),
            })?;

        if !proof_type_matches(&tc, &inferred, &type_expr) {
            return Err(ProofError::TypeMismatch {
                expected: format!("{type_expr:?}"),
                actual: format!("{inferred:?}"),
            });
        }

        Ok(proof_expr)
    }
}

// Re-export proof_type_matches for tests
#[cfg(test)]
pub(super) fn test_proof_type_matches(
    tc: &TypeChecker<'_>,
    inferred: &Expr,
    expected: &Expr,
) -> bool {
    proof_type_matches(tc, inferred, expected)
}
