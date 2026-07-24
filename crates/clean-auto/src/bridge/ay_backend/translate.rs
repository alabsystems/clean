// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AyBackend public translation and registration API.
//!
//! Thin delegation layer — all expression lowering logic lives in the
//! `translator/` module behind the `TermTranslator` trait. This module preserves
//! the existing public surface so callers and tests do not need migration.

use super::{infer_sort_from_lean_type, AyBackend, AyError, AyResult, AySolveEnvelope, AyTerm};
use ay::Sort;
use ay_translate::{TermTranslator, TranslationSession};
use clean_kernel::{Expr, FVarId};

impl AyBackend {
    // =========================================================================
    // Expression translation (delegates to LeanExprTranslator)
    // =========================================================================

    /// Translate a kernel expression to a ay term.
    ///
    /// Delegates to `LeanExprTranslator::translate` which implements the
    /// `ay_translate::TermTranslator` trait against a generic host.
    pub fn translate_expr(&mut self, expr: &Expr) -> AyResult<AyTerm> {
        let mut session = TranslationSession::new(&mut self.solver, &mut self.state);
        self.translator
            .translate(&mut session, expr)
            .map(AyTerm::from_inner)
    }

    // =========================================================================
    // High-level interface for tactics
    // =========================================================================

    /// Try to prove that a proposition is true using SMT
    ///
    /// Asserts the negation of the proposition and checks for UNSAT.
    ///
    /// # Trust Assumption (TTB.External)
    ///
    /// This method trusts ay's UNSAT result for theory queries without
    /// independent verification. See #571 and `designs/2026-01-31-trusted-theory-base.md`
    /// Tier 5 for the full trust gap analysis.
    ///
    /// For verified proofs, use `AyProofBackend::check_sat()` with `produce_proofs: true`
    /// which extracts Alethe proofs that can be independently verified.
    pub fn prove_with_report(&mut self, prop: &Expr) -> AyResult<AySolveEnvelope> {
        let term = self.translate_expr(prop)?;
        let negated = self.not(term);
        self.assert_term(negated);

        Ok(self.check_sat())
    }

    /// Try to prove that a proposition is true using SMT
    ///
    /// Compatibility wrapper over `prove_with_report()` that preserves the
    /// historical `bool`/`Unknown` contract for existing callers.
    pub fn prove(&mut self, prop: &Expr) -> AyResult<bool> {
        let report = self.prove_with_report(prop)?;
        if report.is_unsat() {
            Ok(true)
        } else if report.is_sat() {
            Ok(false)
        } else {
            Err(AyError::Unknown)
        }
    }

    // =========================================================================
    // FVar registration (delegates to LeanExprTranslator)
    // =========================================================================

    /// Register a typed free variable (using TranslationSession).
    ///
    /// Must be called before `translate_expr` for expressions containing
    /// this FVar. Unregistered FVars are rejected to prevent #2129.
    pub(crate) fn register_fvar(&mut self, fvar_id: FVarId, sort: Sort) -> AyTerm {
        let mut session = TranslationSession::new(&mut self.solver, &mut self.state);
        AyTerm::from_inner(self.translator.register_fvar(&mut session, fvar_id, sort))
    }

    /// Register a free variable with sort inferred from its Lean type.
    ///
    /// Maps `Nat`/`Int` -> `Sort::Int`, `Bool` -> `Sort::Bool`,
    /// `Real` -> `Sort::Real`, `String` -> `Sort::String`,
    /// `Prop` (Sort 0) -> `Sort::Bool`, unknown -> `Sort::Uninterpreted` (#2260).
    /// Rejects `UInt*`, `USize`, and `Float` as unsound domain mappings (#2849, #2852).
    pub fn register_fvar_from_lean_type(
        &mut self,
        fvar_id: FVarId,
        lean_type: &Expr,
    ) -> AyResult<AyTerm> {
        let sort = infer_sort_from_lean_type(lean_type)?;
        Ok(self.register_fvar(fvar_id, sort))
    }

    /// Register a typed free variable for integers
    pub fn register_fvar_int(&mut self, fvar_id: FVarId) -> AyTerm {
        self.register_fvar(fvar_id, Sort::Int)
    }

    /// Register a typed free variable for booleans
    pub fn register_fvar_bool(&mut self, fvar_id: FVarId) -> AyTerm {
        self.register_fvar(fvar_id, Sort::Bool)
    }

    /// Register a typed free variable for reals
    pub fn register_fvar_real(&mut self, fvar_id: FVarId) -> AyTerm {
        self.register_fvar(fvar_id, Sort::Real)
    }

    /// Register a typed free variable for bitvectors
    pub fn register_fvar_bv(&mut self, fvar_id: FVarId, width: u32) -> AyTerm {
        self.register_fvar(fvar_id, Sort::bitvec(width))
    }
}
