// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier flattening, BVar substitution, and E-matching instantiation.
//!
//! Handles the structural manipulation of quantified formulas: flattening
//! nested ∀/∃ binders, substituting bound variables with witness terms,
//! and converting E-matching substitutions into concrete instantiations.

use super::expr_classifier::LogicalForm;
use super::{BridgeResult, SmtBridge};
use crate::egraph::EClassId;
use crate::smt::TermId;
use clean_kernel::{Expr, ExprKind};
use std::collections::HashMap;

use super::quantifier::{QuantifierBinder, QuantifierKind, QuantifierPrefix};

impl<'env> SmtBridge<'env> {
    /// Map flattened binder order (outermost-first) to the body's de Bruijn
    /// indices (innermost-first).
    ///
    /// `flatten_forall` / `flatten_exists` return binder types in declaration
    /// order, but the flattened body still uses Lean's standard indexing where
    /// the innermost binder is `BVar(0)` and the outermost is `BVar(n - 1)`.
    pub(super) fn flattened_bvar_indices(bound_count: u32) -> Vec<u32> {
        (0..bound_count).rev().collect()
    }

    /// Flatten nested forall binders into a list of types and the innermost body.
    pub(super) fn flatten_forall(&self, first_ty: &Expr, body: &Expr) -> (Vec<Expr>, Expr) {
        let mut types = vec![first_ty.clone()];
        let mut current = body.clone();

        // Keep peeling Pis that still bind variables (dependent Pis)
        // Strip MData so metadata-wrapped Pi nodes are recognized (#2261)
        while let ExprKind::Pi(_, ty, codomain) = current.strip_mdata().kind() {
            if !codomain.has_loose_bvars() {
                break;
            }
            types.push((**ty).clone());
            current = (**codomain).clone();
        }

        (types, current)
    }

    /// Flatten nested exists binders into a list of types and the innermost body.
    ///
    /// Handles patterns like: ∃ x : A, ∃ y : B, P(x, y)
    /// Returns: ([A, B], P(x, y)) where BVar indices are adjusted for the combined context.
    ///
    /// Since Exists in Lean is encoded as `Exists T (fun x => body)`, nested existentials
    /// appear as `Exists T1 (fun x => Exists T2 (fun y => P(x, y)))`.
    pub(super) fn flatten_exists(&self, first_ty: &Expr, body: &Expr) -> (Vec<Expr>, Expr) {
        let mut types = vec![first_ty.clone()];
        let mut current = body.clone();

        // Keep looking for nested Exists patterns in the body
        // Exists is classified by looking at App(App(Const("Exists"), type), Lam(_, _, body))
        loop {
            // Strip MData so metadata-wrapped Exists nodes are recognized (#2261)
            let stripped = current.strip_mdata().clone();
            // Check if current is an Exists application
            let next = if let ExprKind::App(func, arg) = stripped.kind() {
                let inner_head = func.get_app_fn().strip_mdata();
                if let ExprKind::Const(name, _) = inner_head.kind() {
                    if name.to_string() == "Exists" {
                        let func_args = func.get_app_args();
                        if !func_args.is_empty() {
                            // Get the type from Exists application
                            let ty = func_args[0].clone();
                            // The arg should be a lambda: fun x : T => P(x)
                            if let ExprKind::Lam(_, _, inner_body) = arg.kind() {
                                // Check if the inner body actually uses the bound variable
                                if inner_body.has_loose_bvars() {
                                    types.push(ty);
                                    Some(Expr::clone(inner_body))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };

            if let Some(next) = next {
                current = next;
                continue;
            }
            // Not a nested Exists, stop flattening
            break;
        }

        (types, current)
    }

    /// Flatten a mixed quantifier prefix into a QuantifierPrefix structure.
    ///
    /// This handles arbitrary alternations of ∀ and ∃ quantifiers:
    /// - `∀x. ∃y. P(x,y)` -> binders: [(∀, A, 1), (∃, B, 0)], body: P(x,y)
    /// - `∃x. ∀y. ∃z. P(x,y,z)` -> binders: [(∃, A, 2), (∀, B, 1), (∃, C, 0)]
    ///
    /// The de Bruijn indices are assigned in standard order: outermost binder
    /// gets the highest index (n-1), innermost gets 0.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::InferSortFailed` if the body expression requires
    /// universe level inference that fails (propagated from `logicalform_to_expr`).
    pub(super) fn flatten_quantifier_prefix(
        &self,
        prop: &LogicalForm,
    ) -> BridgeResult<QuantifierPrefix> {
        let mut binders: Vec<(QuantifierKind, Expr)> = Vec::new();
        let mut current: LogicalForm = prop.clone();

        loop {
            match current {
                LogicalForm::Forall { binder_type, body } => {
                    binders.push((QuantifierKind::Forall, binder_type));
                    current = self.classify_prop(&body);
                }
                LogicalForm::Exists { binder_type, body } => {
                    binders.push((QuantifierKind::Exists, binder_type));
                    current = self.classify_prop(&body);
                }
                _ => break,
            }
        }

        // Convert the body back to an Expr
        let body = self.logicalform_to_expr(&current)?;

        // Assign de Bruijn indices (outermost = len-1, innermost = 0)
        let n = binders.len();
        let quantifier_binders: Vec<QuantifierBinder> = binders
            .into_iter()
            .enumerate()
            .map(|(i, (kind, ty))| QuantifierBinder {
                kind,
                ty,
                index: u32::try_from(n - 1 - i)
                    .expect("invariant: quantifier binder index fits in u32"),
            })
            .collect();

        Ok(QuantifierPrefix {
            binders: quantifier_binders,
            body,
        })
    }

    /// Instantiate a body using witness terms for each bound variable.
    pub(super) fn instantiate_body_with_terms(
        &self,
        body: &Expr,
        bound_vars: &[u32],
        witness_terms: &[TermId],
    ) -> Option<Expr> {
        if bound_vars.len() != witness_terms.len() {
            return None;
        }

        let mut replacements = Vec::new();
        for (idx, term) in bound_vars.iter().zip(witness_terms.iter()) {
            let expr = self.term_to_expr.get(term).cloned()?;
            replacements.push((*idx, expr));
        }

        Some(self.instantiate_bvars(body, &replacements))
    }

    /// Apply bound-variable substitutions in descending index order to avoid shifting.
    pub(super) fn instantiate_bvars(&self, body: &Expr, replacements: &[(u32, Expr)]) -> Expr {
        let mut ordered = replacements.to_vec();
        ordered.sort_by_key(|b| std::cmp::Reverse(b.0));

        let mut result = body.clone();
        for (idx, expr) in ordered {
            result = self.substitute_bvar(&result, idx, &expr);
        }
        result
    }

    /// Substitute BVar(idx) with the given expression.
    ///
    /// Delegates to the kernel's `Expr::instantiate_at` which uses
    /// `ExprFolderOpt` for sharing-preserving traversal with O(1) metadata
    /// guards. This replaces ~50 LOC of manual match arms that missed new
    /// expression variants (Cubical, ZFC extensions). (#2141)
    pub(super) fn substitute_bvar(&self, expr: &Expr, idx: u32, replacement: &Expr) -> Expr {
        debug_assert!(
            !replacement.has_loose_bvars(),
            "substitute_bvar: replacement has loose BVars (idx={idx})"
        );
        expr.instantiate_at(replacement, idx)
    }

    /// Build a reverse index from canonical E-class IDs to expressions.
    ///
    /// The equality theory maps TermId → EClassId, and `term_to_expr` maps
    /// TermId → Expr. This method pre-joins them into canonical EClassId → Expr
    /// so that lookups during E-matching instantiation are O(1) instead of
    /// scanning the entire term-to-eclass map per bound variable.
    pub(super) fn build_eclass_to_expr_index(&self) -> HashMap<EClassId, Expr> {
        let mut index: HashMap<EClassId, Expr> = HashMap::new();
        let Some(eq) = self.equality_theory() else {
            return index;
        };
        let egraph = eq.egraph();
        for (&term_id, &eclass_id) in eq.term_to_eclass_map() {
            let canonical = egraph.find_const(eclass_id);
            if let Some(expr) = self.term_to_expr.get(&term_id) {
                index.entry(canonical).or_insert_with(|| expr.clone());
            }
        }
        index
    }

    /// Instantiate a forall body using an E-matching substitution.
    ///
    /// The substitution maps pattern variable names ("?x0", "?x1", etc.)
    /// to E-class IDs. The `eclass_index` is a pre-built reverse index from
    /// canonical EClassId to Expr, created by `build_eclass_to_expr_index`.
    /// Building it once per E-matching round avoids O(terms) scans per bound
    /// variable.
    pub(super) fn instantiate_from_substitution(
        &self,
        body: &Expr,
        subst: &crate::egraph::Substitution,
        bound_vars: &[u32],
        eclass_index: &HashMap<EClassId, Expr>,
    ) -> Option<Expr> {
        let egraph = self.equality_theory().map(|eq| eq.egraph());

        let mut replacements: Vec<(u32, Expr)> = Vec::new();

        for &bvar_idx in bound_vars {
            let var_name = format!("?x{bvar_idx}");
            if let Some(eclass_id) = subst.get(&var_name) {
                let canonical = egraph
                    .map(|eg| eg.find_const(eclass_id))
                    .unwrap_or(eclass_id);
                if let Some(expr) = eclass_index.get(&canonical) {
                    replacements.push((bvar_idx, expr.clone()));
                }
            }
        }

        // Check we have all variables
        if replacements.len() != bound_vars.len() {
            return None;
        }

        // Substitute all bound variables in the body (descending order inside)
        Some(self.instantiate_bvars(body, &replacements))
    }
}
