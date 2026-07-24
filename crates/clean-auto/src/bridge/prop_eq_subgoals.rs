// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-reflexive equality sub-goal proof builders (#2442 Phase 3B).
//!
//! Extracted from `prop_reconstruction.rs` for file size compliance.
//! Provides Eq.symm and Eq.trans search for equality sub-goals that appear
//! inside compound propositional goals (e.g., `And(Eq(Nat, b, a), True)`
//! where `h : Eq(Nat, a, b)` is available).

use crate::proof::ProofStep;
use clean_kernel::{Expr, FVarId, Level};
use std::collections::HashMap;

use super::chain_search::bfs_chain_search;
use super::eq_proof_builders::{mk_eq_symm, mk_eq_trans};
use super::expr_classifier::LogicalForm;
use super::translate::ExprKey;
use super::{BridgeError, BridgeResult, SmtBridge};

#[derive(Clone)]
struct EqHypothesisEdge {
    fvar_id: FVarId,
    lhs_key: ExprKey,
    rhs_key: ExprKey,
    lhs_expr: Expr,
    rhs_expr: Expr,
}

impl<'env> SmtBridge<'env> {
    fn build_eq_trans_path_proof(
        &self,
        u: &Level,
        ty: &Expr,
        start: &Expr,
        path: &[(usize, bool)],
        eq_hyps: &[EqHypothesisEdge],
    ) -> BridgeResult<Expr> {
        let Some(&(first_idx, first_needs_symm)) = path.first() else {
            return Err(BridgeError::UnsupportedExpr {
                context: "Eq.trans: empty path".into(),
            });
        };
        let first_edge = &eq_hyps[first_idx];
        let mut current_proof = if first_needs_symm {
            mk_eq_symm(
                u,
                ty,
                &first_edge.lhs_expr,
                &first_edge.rhs_expr,
                &Expr::fvar(first_edge.fvar_id),
            )
        } else {
            Expr::fvar(first_edge.fvar_id)
        };
        let mut current_target = if first_needs_symm {
            first_edge.lhs_expr.clone()
        } else {
            first_edge.rhs_expr.clone()
        };

        for &(edge_idx, needs_symm) in &path[1..] {
            let edge = &eq_hyps[edge_idx];
            let next_proof = if needs_symm {
                mk_eq_symm(
                    u,
                    ty,
                    &edge.lhs_expr,
                    &edge.rhs_expr,
                    &Expr::fvar(edge.fvar_id),
                )
            } else {
                Expr::fvar(edge.fvar_id)
            };
            let next_target = if needs_symm {
                edge.lhs_expr.clone()
            } else {
                edge.rhs_expr.clone()
            };
            current_proof = mk_eq_trans(
                u,
                ty,
                start,
                &current_target,
                &next_target,
                &current_proof,
                &next_proof,
            );
            current_target = next_target;
        }

        Ok(current_proof)
    }

    /// Try `Eq.symm h` for goal `Eq(ty, lhs, rhs)` from hypothesis `h : Eq(ty, rhs, lhs)`.
    pub(super) fn try_eq_symm_subgoal(
        &self,
        ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let Some(ty_key) = ExprKey::from_expr(ty) else {
            return Err(BridgeError::UnsupportedExpr {
                context: "Eq.symm: ExprKey unavailable".into(),
            });
        };
        let Some(lhs_key) = ExprKey::from_expr(lhs) else {
            return Err(BridgeError::UnsupportedExpr {
                context: "Eq.symm: ExprKey unavailable".into(),
            });
        };
        let Some(rhs_key) = ExprKey::from_expr(rhs) else {
            return Err(BridgeError::UnsupportedExpr {
                context: "Eq.symm: ExprKey unavailable".into(),
            });
        };
        let u = self.sort_level_of_type(ty)?;
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            let hyp_class = self.classify_prop(hyp_type);
            if let LogicalForm::Eq {
                ty: ref h_ty,
                lhs: ref h_lhs,
                rhs: ref h_rhs,
            } = hyp_class
            {
                let Some(h_ty_key) = ExprKey::from_expr(h_ty) else {
                    continue;
                };
                let Some(h_rhs_key) = ExprKey::from_expr(h_rhs) else {
                    continue;
                };
                let Some(h_lhs_key) = ExprKey::from_expr(h_lhs) else {
                    continue;
                };
                if ty_key == h_ty_key && lhs_key == h_rhs_key && rhs_key == h_lhs_key {
                    let proof = mk_eq_symm(&u, ty, rhs, lhs, &Expr::fvar(fvar_id));
                    return Ok((ProofStep::Propositional("Eq.symm".into()), proof));
                }
            }
        }
        Err(BridgeError::UnsupportedExpr {
            context: "Eq.symm: no reversed equality hypothesis found".into(),
        })
    }

    /// Try `Eq.trans h1 h2` for goal `Eq(ty, lhs, rhs)` from hypotheses
    /// `h1 : Eq(ty, lhs, mid)` and `h2 : Eq(ty, mid, rhs)`.
    ///
    /// Handles four orientations via implicit Eq.symm on each hypothesis:
    /// - direct/direct: h1 : lhs=mid, h2 : mid=rhs
    /// - symm/direct:   h1 : mid=lhs, h2 : mid=rhs
    /// - direct/symm:   h1 : lhs=mid, h2 : rhs=mid
    /// - symm/symm:     h1 : mid=lhs, h2 : rhs=mid
    ///
    /// For longer chains, performs a shortest-path search over equality
    /// hypotheses and folds the resulting path into nested `Eq.trans` terms.
    pub(super) fn try_eq_trans_subgoal(
        &self,
        ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let Some(ty_key) = ExprKey::from_expr(ty) else {
            return Err(BridgeError::UnsupportedExpr {
                context: "Eq.trans: ExprKey unavailable".into(),
            });
        };
        let Some(goal_lhs) = ExprKey::from_expr(lhs) else {
            return Err(BridgeError::UnsupportedExpr {
                context: "Eq.trans: ExprKey unavailable".into(),
            });
        };
        let Some(goal_rhs) = ExprKey::from_expr(rhs) else {
            return Err(BridgeError::UnsupportedExpr {
                context: "Eq.trans: ExprKey unavailable".into(),
            });
        };
        let u = self.sort_level_of_type(ty)?;

        // Collect Eq hypotheses with matching type
        let eq_hyps: Vec<_> = self
            .iter_guided_hypotheses()
            .filter_map(|(fvar_id, hyp_type)| {
                let hyp_class = self.classify_prop(hyp_type);
                if let LogicalForm::Eq {
                    ty: h_ty,
                    lhs: h_lhs,
                    rhs: h_rhs,
                } = hyp_class
                {
                    if ty_key == ExprKey::from_expr(&h_ty)? {
                        return Some(EqHypothesisEdge {
                            fvar_id,
                            lhs_key: ExprKey::from_expr(&h_lhs)?,
                            rhs_key: ExprKey::from_expr(&h_rhs)?,
                            lhs_expr: h_lhs,
                            rhs_expr: h_rhs,
                        });
                    }
                }
                None
            })
            .collect();

        let mut adjacency: HashMap<ExprKey, Vec<(ExprKey, (usize, bool))>> = HashMap::new();
        for (idx, edge) in eq_hyps.iter().enumerate() {
            adjacency
                .entry(edge.lhs_key.clone())
                .or_default()
                .push((edge.rhs_key.clone(), (idx, false)));
            adjacency
                .entry(edge.rhs_key.clone())
                .or_default()
                .push((edge.lhs_key.clone(), (idx, true)));
        }

        if let Some(proof) =
            bfs_chain_search(goal_lhs.clone(), goal_rhs.clone(), &adjacency, |path| {
                self.build_eq_trans_path_proof(&u, ty, lhs, path, &eq_hyps)
                    .ok()
            })
        {
            return Ok((ProofStep::Propositional("Eq.trans".into()), proof));
        }

        Err(BridgeError::UnsupportedExpr {
            context: "Eq.trans: no transitivity chain found".into(),
        })
    }
}
