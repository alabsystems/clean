// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::SmtBridge;
use super::ExprKey;
use crate::smt::TermId;
use clean_kernel::{Expr, FVarId};

impl<'env> SmtBridge<'env> {
    /// Create a witness/Skolem constant registered in all bridge maps.
    ///
    /// Unlike `smt.const_term()` alone, this also creates a fresh FVar Expr
    /// and registers it in term_to_expr, expr_to_term, and term_to_type.
    /// This ensures `instantiate_body_with_terms` can look up the witness.
    pub(crate) fn create_witness_term(&mut self, name: &str, witness_type: &Expr) -> TermId {
        let term_id = self.smt.const_term(name.to_string());
        self.register_witness_for_term(term_id, witness_type);
        term_id
    }

    /// Register an existing TermId as a witness in bridge maps.
    ///
    /// Creates a fresh FVar as the Expr-level representative and registers
    /// it in term_to_expr, expr_to_term, and term_to_type. Used for both
    /// simple witness constants and applied Skolem function terms.
    pub(crate) fn register_witness_for_term(&mut self, term_id: TermId, witness_type: &Expr) {
        // Derive FVarId from TermId with high bits set to avoid collision with
        // kernel FVarIds. TermIds are unique within a bridge session, so this
        // mapping is injective.
        let fvar_id = FVarId::new(0xFFFF_0000_0000_0000_u64 | term_id.raw() as u64);
        let expr = Expr::fvar(fvar_id);
        self.term_to_expr.insert(term_id, expr.clone());
        if let Some(key) = ExprKey::from_expr(&expr) {
            self.expr_to_term.insert(key, term_id);
        }
        self.term_to_type.insert(term_id, witness_type.clone());
    }
}
