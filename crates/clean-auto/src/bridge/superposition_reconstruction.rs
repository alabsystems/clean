// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Superposition proof reconstruction for the SMT-Kernel Bridge.
//!
//! Translates superposition proof traces (clause derivation DAGs) back to
//! Lean kernel proof terms (`Expr`). Walks the DAG bottom-up, converting
//! each inference step to kernel proof terms (Eq.refl, Eq.subst, absurd).
//!
//! | Superposition Rule    | Kernel Proof                              |
//! |-----------------------|-------------------------------------------|
//! | Input                 | Hypothesis reference (FVar)               |
//! | EqualityResolution    | Or.rec + absurd (Eq.refl t) (h : t ≠ t)  |
//! | Superposition         | Eq.subst with motive + congr chain        |
//! | EqualityFactoring     | Or.rec + Classical.em case split          |
//! | Demodulation          | Eq.subst with motive                      |
//!
//! Split into submodules:
//! - `disjunction_helpers`: Or.inl, Or.inr, Or.rec, Classical.em
//! - `equality_factoring`: Or.rec-based equality factoring reconstruction
//! - `equality_resolution`: Or.rec-based equality resolution for multi-literal clauses
//! - `goal_wrappers`: Or/Implies/Iff goal wrappers (byContradiction, Iff.intro)
//! - `proof_helpers`: Free functions, Eq helpers, and proposition builders
//! - `types`: Error types, `SymbolMap`

mod disjunction_helpers;
mod eq_true_bridge;
mod equality_factoring;
mod equality_resolution;
mod goal_wrappers;
mod proof_helpers;
mod superposition_step;
mod types;

use proof_helpers::{extract_iff_components, extract_implies_components, mk_negation};
pub use types::*;

use std::collections::HashMap;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, TypeChecker};

use crate::superposition::{Clause, Inference, ProofTrace};

/// Reconstructs kernel proof terms from superposition proof traces.
///
/// Given a `ProofTrace` from the superposition prover and a `SymbolMap`
/// connecting superposition symbols to kernel expressions, produces a
/// kernel `Expr` proof term that the type checker can verify.
pub struct SuperpositionReconstructor<'a> {
    /// Symbol/variable → kernel Expr mapping
    symbol_map: &'a SymbolMap,
    /// Clause lookup by ID (from the proof trace)
    clause_map: HashMap<u64, &'a Clause>,
    /// Cache of already-reconstructed clause proofs
    proof_cache: HashMap<u64, Expr>,
    /// Optional kernel environment for accurate sort level inference
    env: Option<&'a Environment>,
}

impl<'a> SuperpositionReconstructor<'a> {
    /// Create a new reconstructor from a proof trace and symbol map.
    pub fn new(trace: &'a ProofTrace, symbol_map: &'a SymbolMap) -> Self {
        let mut clause_map = HashMap::new();
        for clause in &trace.clauses {
            clause_map.insert(clause.id, clause);
        }
        clause_map.insert(trace.empty_clause.id, &trace.empty_clause);

        SuperpositionReconstructor {
            symbol_map,
            clause_map,
            proof_cache: HashMap::new(),
            env: None,
        }
    }

    /// Create a new reconstructor with access to the kernel environment.
    ///
    /// The environment enables accurate universe level inference via
    /// `TypeChecker::infer_sort` instead of the Level 1 heuristic.
    pub fn with_env(
        trace: &'a ProofTrace,
        symbol_map: &'a SymbolMap,
        env: &'a Environment,
    ) -> Self {
        let mut r = Self::new(trace, symbol_map);
        r.env = Some(env);
        r
    }

    /// Compute the sort level of a type expression.
    ///
    /// Uses `TypeChecker::infer_sort` when the environment is available.
    ///
    /// # Errors
    ///
    /// Returns `ReconstructionError::SortInferenceFailed` if no environment
    /// is available or if `TypeChecker::infer_sort` fails.
    pub(crate) fn sort_level_of_type(&self, ty: &Expr) -> ReconstructionResult<Level> {
        let env = self.env.ok_or_else(|| {
            ReconstructionError::SortInferenceFailed("no environment available".into())
        })?;
        let tc = TypeChecker::new(env);
        tc.infer_sort(ty)
            .map_err(|e| ReconstructionError::SortInferenceFailed(format!("{e:?}")))
    }

    /// Reconstruct a kernel proof term from the proof trace.
    ///
    /// The superposition prover derives a refutation (empty clause = False).
    /// This method builds a proof of `False` from the hypotheses, which can
    /// then be used via `False.elim` to prove the original goal.
    pub fn reconstruct(&mut self) -> ReconstructionResult<(Expr, String)> {
        let empty_id = self
            .clause_map
            .keys()
            .find(|id| {
                self.clause_map
                    .get(id)
                    .is_some_and(|c| c.literals.is_empty())
            })
            .copied()
            .ok_or_else(|| {
                ReconstructionError::MalformedTrace("no empty clause in proof trace".into())
            })?;

        let proof = self.reconstruct_clause(empty_id)?;
        let num_clauses = self.clause_map.len();
        let description = format!("Superposition refutation proof ({num_clauses} clauses)");
        Ok((proof, description))
    }

    /// Reconstruct a proof of the original goal using `Classical.byContradiction`.
    ///
    /// When the superposition prover was invoked via `clausify_goal`, the proof
    /// trace is a refutation of `¬P` (proving `False` from `¬P` as a hypothesis).
    /// This method wraps the `False` proof with `Classical.byContradiction` to
    /// produce a proof of `P`:
    ///
    /// ```text
    /// Classical.byContradiction (fun (h : ¬P) => <proof of False using h>)
    /// ```
    ///
    /// For single-clause goals (equations, conjunctions, atoms), the proof
    /// directly abstracts over the ¬P hypothesis.
    ///
    /// For multi-clause Or-goals (P ∨ Q, P ∨ Q ∨ R, etc.), decomposes
    /// `h : ¬(P ∨ Q)` into per-clause hypotheses.
    ///
    /// For Implies goals (P → Q), produces `fun (p : P) => byContradiction @Q ...`.
    ///
    /// For Iff goals (P ↔ Q), produces `Iff.intro mp mpr` where each
    /// direction uses `byContradiction` with the same refutation proof.
    pub fn reconstruct_goal(&mut self) -> ReconstructionResult<(Expr, String)> {
        let (goal, num_goal_clauses, fvar_base) =
            self.symbol_map.goal_info.clone().ok_or_else(|| {
                ReconstructionError::MalformedTrace(
                    "no goal info: use reconstruct() for hypothesis-only proofs".into(),
                )
            })?;

        let (false_proof, _) = self.reconstruct()?;

        // Detect goal structure for appropriate wrapping strategy.
        // Check Iff first (4 clauses), then Implies (2 clauses), then Or/single.
        if num_goal_clauses == 4 {
            if let Some((p, q)) = extract_iff_components(&goal) {
                return self.build_iff_proof(false_proof, &goal, &p, &q, fvar_base);
            }
        }

        if num_goal_clauses == 2 {
            if let Some((p, q)) = extract_implies_components(&goal) {
                return self.build_implies_proof(false_proof, &goal, &p, &q, fvar_base);
            }
        }

        let body = if num_goal_clauses == 1 {
            self.build_single_clause_body(false_proof, &goal, fvar_base)?
        } else {
            // Multi-clause goal: try Or-decomposition
            self.build_multi_clause_body(false_proof, &goal, num_goal_clauses, fvar_base)?
        };

        // ¬goal = goal → False
        let neg_goal = mk_negation(&goal);

        // fun (h : ¬goal) => body
        let proof_fun = Expr::lam(BinderInfo::Default, neg_goal, body);

        // @Classical.byContradiction goal proof_fun : goal
        let result = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Classical.byContradiction"), vec![]),
                goal,
            ),
            proof_fun,
        );

        let num_clauses = self.clause_map.len();
        let description =
            format!("Superposition goal proof ({num_clauses} clauses, byContradiction)");
        Ok((result, description))
    }

    /// Reconstruct the proof for a single clause in the derivation.
    ///
    /// Protected by `stacker::maybe_grow` since proof DAG depth is unbounded —
    /// long derivation chains (hundreds of inference steps) can overflow the
    /// default thread stack without heap-extension.
    fn reconstruct_clause(&mut self, clause_id: u64) -> ReconstructionResult<Expr> {
        stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
            if let Some(cached) = self.proof_cache.get(&clause_id) {
                return Ok(cached.clone());
            }

            let clause = self
                .clause_map
                .get(&clause_id)
                .ok_or(ReconstructionError::MissingClause(clause_id))?;
            let inference = clause.inference.clone();

            let proof = match inference {
                Inference::Input => self.reconstruct_input(clause_id)?,
                Inference::EqualityResolution(parent) => {
                    self.reconstruct_equality_resolution(clause_id, parent)?
                }
                Inference::Superposition(c1, c2, ref _pos) => {
                    self.reconstruct_superposition(clause_id, c1, c2)?
                }
                Inference::EqualityFactoring(parent) => {
                    self.reconstruct_equality_factoring(clause_id, parent)?
                }
                Inference::Demodulation(clause_id_orig, unit_id) => {
                    self.reconstruct_demodulation(clause_id, clause_id_orig, unit_id)?
                }
                Inference::Subsumption(_) => {
                    return Err(ReconstructionError::UnsupportedInference(
                        "Subsumption (should not appear in proof trace)".to_string(),
                    ))
                }
            };

            self.proof_cache.insert(clause_id, proof.clone());
            Ok(proof)
        })
    }

    /// Reconstruct proof for an input clause (hypothesis reference).
    fn reconstruct_input(&self, clause_id: u64) -> ReconstructionResult<Expr> {
        let fvar = self
            .symbol_map
            .input_to_fvar
            .get(&clause_id)
            .ok_or(ReconstructionError::MissingInputHypothesis(clause_id))?;

        if self
            .symbol_map
            .goal_info
            .as_ref()
            .is_some_and(|(_, num_goal_clauses, _)| clause_id < *num_goal_clauses as u64)
        {
            return Ok(Expr::fvar(*fvar));
        }

        // For hypothesis clauses, try the eq_true bridge to handle non-equational
        // props encoded as P = True by the clausifier. Fall back to the raw FVar
        // proof if bridging fails (equational hypotheses don't need bridging).
        let Some(raw_prop) = self.symbol_map.input_to_type.get(&clause_id) else {
            return Ok(Expr::fvar(*fvar));
        };
        self.bridge_raw_prop_proof_to_clause_id(
            raw_prop,
            &Expr::fvar(*fvar),
            clause_id,
            "input clause reconstruction",
        )
        .or_else(|_| Ok(Expr::fvar(*fvar)))
    }

    /// Reconstruct proof for demodulation (rewriting by unit equation).
    ///
    /// Uses Eq.subst with motive to rewrite subterms using a unit equation.
    /// The equation l=r from the unit clause may be applied in either direction
    /// by the prover's term ordering. Detect the actual direction by checking
    /// if the motive body abstracts over BVar(0).
    fn reconstruct_demodulation(
        &mut self,
        _clause_id: u64,
        orig_id: u64,
        unit_id: u64,
    ) -> ReconstructionResult<Expr> {
        let unit = self
            .clause_map
            .get(&unit_id)
            .ok_or(ReconstructionError::MissingClause(unit_id))?;
        let eq_lit = unit
            .literals
            .first()
            .ok_or_else(|| {
                ReconstructionError::MalformedTrace("demodulation unit clause is empty".into())
            })?
            .clone();

        let orig = self
            .clause_map
            .get(&orig_id)
            .ok_or(ReconstructionError::MissingClause(orig_id))?;
        let orig_prop = self.clause_to_prop(orig)?;

        let lhs_expr = self.symbol_map.term_to_expr(&eq_lit.lhs)?;
        let rhs_expr = self.symbol_map.term_to_expr(&eq_lit.rhs)?;
        let eq_type = self.symbol_map.term_type(&eq_lit.lhs)?;

        // Try l→r direction first; if motive doesn't abstract, use r→l with Eq.symm.
        let motive_lr = self.build_motive(&orig_prop, &lhs_expr, &eq_type);
        let lr_abstracts = match motive_lr.kind() {
            ExprKind::Lam(_, _, body) => body.has_loose_bvars(),
            _ => false,
        };

        let orig_proof = self.reconstruct_clause(orig_id)?;
        let unit_proof = self.reconstruct_clause(unit_id)?;

        if lr_abstracts {
            self.mk_eq_subst(
                &eq_type,
                &motive_lr,
                &lhs_expr,
                &rhs_expr,
                &unit_proof,
                &orig_proof,
            )
        } else {
            let motive_rl = self.build_motive(&orig_prop, &rhs_expr, &eq_type);
            let unit_proof_sym = self.mk_eq_symm(&eq_type, &lhs_expr, &rhs_expr, &unit_proof)?;
            self.mk_eq_subst(
                &eq_type,
                &motive_rl,
                &rhs_expr,
                &lhs_expr,
                &unit_proof_sym,
                &orig_proof,
            )
        }
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_e2e;
#[cfg(test)]
mod tests_factoring;
#[cfg(test)]
mod tests_proof_helpers;
