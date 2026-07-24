// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality proof reconstruction for the SMT-Kernel Bridge.
//!
//! Builds Lean kernel proof terms from SMT solver equality results.
//! Multiple strategies in priority order: reflexivity, E-graph proof trace,
//! direct hypothesis lookup, trail-guided hypothesis reconstruction,
//! BFS transitivity, and term-based congruence.
//!
//! Low-level proof term constructors are in `proof_terms.rs`. This module
//! contains the strategy-level proof construction logic.

use crate::proof::{ProofBuilder, ProofStep};
use crate::smt::TermId;
use clean_kernel::{Expr, ExprKind, FVarId};

use super::chain_search::bfs_chain_search;
use super::{BridgeError, BridgeResult, SmtBridge};

/// Maximum recursion depth for congruence proof reconstruction.
/// Prevents stack overflow on deeply nested function applications
/// (e.g., f(f(f(f(...))))). Matches ProofForest's MAX_EXPLAIN_RECURSION.
const MAX_PROOF_RECONSTRUCTION_DEPTH: u32 = 100;

impl<'env> SmtBridge<'env> {
    /// Try to build a proof from the equality theory's proof trace.
    ///
    /// This leverages the E-graph union reasons (including hypotheses) recorded
    /// by the EUF solver. Falls back to reflexivity when both terms are already
    /// in the same equivalence class.
    pub(crate) fn proof_from_equality_theory(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<(ProofStep, Expr)> {
        let eq = self.equality_theory()?;
        let ec1 = eq.get_eclass(t1)?;
        let ec2 = eq.get_eclass(t2)?;

        let step = eq.proof_trace().build_proof(ec1, ec2)?;

        let builder = ProofBuilder::with_hypotheses(
            &self.term_to_expr,
            &self.term_to_type,
            self.env,
            &self.eq_hypothesis_canonical,
        );
        let proof_term = builder.build(&step).ok()?;
        Some((step, proof_term))
    }

    /// Build a proof term for an equality goal.
    ///
    /// # Arguments
    /// * `t1`, `t2` - SMT term IDs for the equality's LHS and RHS
    /// * `lhs_expr`, `rhs_expr` - Lean kernel expressions for LHS and RHS
    /// * `eq_ty` - The type argument α from `@Eq.{u} α lhs rhs`
    ///
    /// # Proof Construction Strategy
    ///
    /// We use multiple strategies in priority order:
    ///
    /// 1. **Reflexivity**: If t1 == t2, return Eq.refl
    ///
    /// 2. **E-graph proof trace** (primary path): Uses the equality theory's
    ///    ProofTrace which records union reasons with hypothesis tracking.
    ///    Handles transitivity, congruence, and mixed proofs naturally.
    ///
    /// 3. **Direct hypothesis lookup**: For simple cases where a single
    ///    hypothesis proves the goal (with optional symmetry).
    ///
    /// 4. **Guided propositional hypotheses**: Scan the tracked hypotheses
    ///    (preferring trail-guided ones first) for direct or conjunctive
    ///    equality evidence such as `h : a = b ∧ b = c`.
    ///
    /// 5. **BFS transitivity**: Fallback for when the proof trace doesn't
    ///    have the path (shouldn't happen normally, but useful for testing).
    ///
    /// 6. **Term-based congruence**: Fallback for congruence when E-graph
    ///    doesn't have the proof recorded.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError` when all 6 strategies are exhausted, or when
    /// a strategy that should succeed (e.g., reflexivity) fails during
    /// proof term construction.
    pub(crate) fn build_equality_proof(
        &self,
        t1: TermId,
        t2: TermId,
        lhs_expr: &Expr,
        rhs_expr: &Expr,
        eq_ty: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        // Strategy 1: Reflexivity
        if t1 == t2 {
            let proof_step = ProofStep::refl(t1);
            let proof_term = self.mk_eq_refl(eq_ty, lhs_expr)?;
            return Ok((proof_step, proof_term));
        }

        // Strategy 2: E-graph proof trace (primary path)
        // This is the preferred approach as it handles all proof types uniformly
        if let Some((step, proof)) = self.proof_from_equality_theory(t1, t2) {
            return Ok((step, proof));
        }

        // Strategy 3: Direct hypothesis lookup
        // Used when the E-graph trace doesn't have the proof but we have a hypothesis
        if let Some(&fvar) = self.eq_hypothesis_canonical.get(&(t1, t2)) {
            let proof_step = ProofStep::hypothesis(fvar);
            let proof_term = Expr::fvar(fvar);
            return Ok((proof_step, proof_term));
        }

        // Check hypothesis in reverse direction (needs symmetry)
        // Hypothesis is stored as (t2, t1) → fvar, i.e., h : rhs_expr = lhs_expr
        // We need @Eq.symm.{u} α rhs_expr lhs_expr h to get lhs_expr = rhs_expr
        if let Some(&fvar) = self.eq_hypothesis_canonical.get(&(t2, t1)) {
            let proof_step = ProofStep::symm(ProofStep::hypothesis(fvar));
            let proof_term = self.mk_eq_symm(eq_ty, rhs_expr, lhs_expr, &Expr::fvar(fvar))?;
            return Ok((proof_step, proof_term));
        }

        // Strategy 4: Guided propositional hypotheses (including And projections)
        if let Some((proof_step, proof_term)) =
            self.try_guided_hypothesis_equality_proof(t1, t2, lhs_expr, rhs_expr, eq_ty)?
        {
            return Ok((proof_step, proof_term));
        }

        // Strategy 5: BFS transitivity (fallback)
        if let Some((proof_step, proof_term)) =
            self.try_transitive_proof(t1, t2, lhs_expr, rhs_expr, eq_ty)
        {
            return Ok((proof_step, proof_term));
        }

        // Strategy 6: Term-based congruence (fallback, depth-bounded)
        if let Some((proof_step, proof_term)) =
            self.try_congruence_proof(t1, t2, lhs_expr, rhs_expr, depth)
        {
            return Ok((proof_step, proof_term));
        }

        Err(BridgeError::ProofTraceFailed(format!(
            "all 6 proof strategies exhausted for {t1} = {t2}"
        )))
    }

    /// Try to build a transitive proof using BFS to find a path from t1 to t2.
    ///
    /// Supports arbitrary-length chains: a=b, b=c, c=d, ... → a=z
    fn try_transitive_proof(
        &self,
        t1: TermId,
        t2: TermId,
        _lhs_expr: &Expr,
        _rhs_expr: &Expr,
        eq_ty: &Expr,
    ) -> Option<(ProofStep, Expr)> {
        // BFS to find shortest path from t1 to t2 through equality hypotheses
        // Each edge represents a hypothesis (with possible symmetry)

        // Build adjacency list from hypotheses
        // neighbor_term -> (hypothesis_fvar, needs_symm_to_reach_neighbor)
        type PathEdge = (FVarId, bool, TermId, TermId);
        let mut adjacency: std::collections::HashMap<TermId, Vec<(TermId, PathEdge)>> =
            std::collections::HashMap::new();
        for (&(a, b), &fvar) in &self.eq_hypothesis_canonical {
            // a = b: from a, reach b without symm; from b, reach a with symm
            adjacency
                .entry(a)
                .or_default()
                .push((b, (fvar, false, a, b)));
            adjacency
                .entry(b)
                .or_default()
                .push((a, (fvar, true, a, b)));
        }

        bfs_chain_search(t1, t2, &adjacency, |path| {
            self.build_path_proof(t1, path, eq_ty)
        })
    }

    /// Build proof step + term for a single hypothesis edge.
    fn edge_proof(
        &self,
        fvar: FVarId,
        needs_symm: bool,
        from: TermId,
        to: TermId,
        eq_ty: &Expr,
    ) -> Option<(ProofStep, Expr)> {
        if needs_symm {
            let a = self.term_to_expr.get(&from).cloned()?;
            let b = self.term_to_expr.get(&to).cloned()?;
            Some((
                ProofStep::symm(ProofStep::hypothesis(fvar)),
                self.mk_eq_symm(eq_ty, &a, &b, &Expr::fvar(fvar)).ok()?,
            ))
        } else {
            Some((ProofStep::hypothesis(fvar), Expr::fvar(fvar)))
        }
    }

    /// Build a proof term from a BFS path of hypothesis edges.
    fn build_path_proof(
        &self,
        start: TermId,
        path: &[(FVarId, bool, TermId, TermId)],
        eq_ty: &Expr,
    ) -> Option<(ProofStep, Expr)> {
        if path.is_empty() {
            return None;
        }

        let (fvar, needs_symm, canon_from, canon_to) = path[0];
        let (mut current_step, mut current_term) =
            self.edge_proof(fvar, needs_symm, canon_from, canon_to, eq_ty)?;

        let chain_start_expr = self.term_to_expr.get(&start).cloned()?;
        let mut chain_current = if needs_symm { canon_from } else { canon_to };

        for &(fvar, needs_symm, canon_from, canon_to) in &path[1..] {
            let (next_step, next_term) =
                self.edge_proof(fvar, needs_symm, canon_from, canon_to, eq_ty)?;
            let b_expr = self.term_to_expr.get(&chain_current).cloned()?;
            let next_dest = if needs_symm { canon_from } else { canon_to };
            let c_expr = self.term_to_expr.get(&next_dest).cloned()?;

            current_step = ProofStep::trans(current_step, next_step);
            current_term = self
                .mk_eq_trans(
                    eq_ty,
                    &chain_start_expr,
                    &b_expr,
                    &c_expr,
                    &current_term,
                    &next_term,
                )
                .ok()?;
            chain_current = next_dest;
        }

        Some((current_step, current_term))
    }

    /// Try to build a congruence proof: a=b → f(a)=f(b)
    ///
    /// For multi-argument functions f(a₁, a₂, ...) = f(b₁, b₂, ...):
    /// - First find proofs that each aᵢ = bᵢ
    /// - Chain them using: congr (congrArg f h₁) h₂ etc.
    fn try_congruence_proof(
        &self,
        t1: TermId,
        t2: TermId,
        lhs_expr: &Expr,
        rhs_expr: &Expr,
        depth: u32,
    ) -> Option<(ProofStep, Expr)> {
        // Guard against unbounded recursion on deeply nested terms
        if depth >= MAX_PROOF_RECONSTRUCTION_DEPTH {
            return None;
        }

        // Get the SMT terms for t1 and t2
        let smt_t1 = self.smt.get_term(t1)?;
        let smt_t2 = self.smt.get_term(t2)?;

        // Both must be applications with the same function symbol
        let (func_name, args1) = match smt_t1 {
            crate::smt::SmtTerm::App(name, args) => (name.name().to_string(), args.clone()),
            _ => return None,
        };

        let args2 = match smt_t2 {
            crate::smt::SmtTerm::App(name, args) if name.name() == func_name => args.clone(),
            _ => return None,
        };

        // Must have same number of arguments
        if args1.len() != args2.len() {
            return None;
        }

        if args1.is_empty() {
            return None; // No arguments to compare
        }

        // Collect proofs for each argument pair
        let mut arg_steps: Vec<ProofStep> = Vec::new();
        let mut arg_proofs: Vec<Expr> = Vec::new();

        for (arg1, arg2) in args1.iter().zip(args2.iter()) {
            let arg1_expr = self.term_to_expr.get(arg1)?;
            let arg2_expr = self.term_to_expr.get(arg2)?;

            // Use the type from term_to_type for this argument's equality type
            let arg_ty = self.get_type_for_term(*arg1).ok()?;

            // Recursively try to build proof for this argument equality
            let (arg_step, arg_proof) = self
                .build_equality_proof(*arg1, *arg2, arg1_expr, arg2_expr, &arg_ty, depth + 1)
                .ok()?;
            arg_steps.push(arg_step);
            arg_proofs.push(arg_proof);
        }

        // Build the proof term — extract func expression with universe levels preserved
        let func_expr = match lhs_expr.get_app_fn().kind() {
            ExprKind::Const(name, levels) => Expr::const_(name.clone(), levels.clone()),
            ExprKind::FVar(fvar) => Expr::fvar(*fvar),
            _ => return None,
        };

        // Build the composite proof step with the full function expression
        let proof_step = ProofStep::congr(func_expr.clone(), arg_steps);

        let proof_term = if arg_proofs.len() == 1 {
            let arg_ty = self.get_type_for_term(args1[0]).ok()?;
            let (u, v) = self.congr_universe_levels(&func_expr, &arg_ty).ok()?;
            let a1 = self.term_to_expr.get(&args1[0])?.clone();
            let a2 = self.term_to_expr.get(&args2[0])?.clone();
            let beta = self.infer_codomain(&func_expr).ok()?;
            self.mk_congr_arg(u, v, &arg_ty, &beta, &a1, &a2, &func_expr, &arg_proofs[0])
        } else {
            // Multiple arguments: chain congrArg + congr
            let arg_ty = self.get_type_for_term(args1[0]).ok()?;
            let (u, v) = self.congr_universe_levels(&func_expr, &arg_ty).ok()?;
            let a1_0 = self.term_to_expr.get(&args1[0])?.clone();
            let a2_0 = self.term_to_expr.get(&args2[0])?.clone();
            let beta = self.infer_codomain(&func_expr).ok()?;
            let mut current_proof = self.mk_congr_arg(
                u,
                v,
                &arg_ty,
                &beta,
                &a1_0,
                &a2_0,
                &func_expr,
                &arg_proofs[0],
            );

            let mut partial_func_lhs = Expr::app(func_expr.clone(), a1_0);
            let mut partial_func_rhs = Expr::app(func_expr.clone(), a2_0);

            for (i, proof) in arg_proofs[1..].iter().enumerate() {
                let idx = i + 1;
                let arg_ty_i = self.get_type_for_term(args1[idx]).ok()?;
                let (u_i, v_i) = self
                    .congr_universe_levels(&partial_func_lhs, &arg_ty_i)
                    .ok()?;
                let a1_i = self.term_to_expr.get(&args1[idx])?.clone();
                let a2_i = self.term_to_expr.get(&args2[idx])?.clone();
                let beta_i = self.infer_codomain(&partial_func_lhs).ok()?;
                current_proof = self.mk_congr(
                    u_i,
                    v_i,
                    &arg_ty_i,
                    &beta_i,
                    &partial_func_lhs,
                    &partial_func_rhs,
                    &a1_i,
                    &a2_i,
                    &current_proof,
                    proof,
                );

                partial_func_lhs = Expr::app(partial_func_lhs, a1_i);
                partial_func_rhs = Expr::app(partial_func_rhs, a2_i);
            }

            current_proof
        };

        let _ = rhs_expr; // suppress warning
        Some((proof_step, proof_term))
    }
}
