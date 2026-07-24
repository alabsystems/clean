// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::bridge::QuantifierOrigin;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, LocalContext, Name, TypeChecker};

/// Synthetic FVarId base for `auto_prove_with_premises` hypothesis binders.
///
/// Keeps the engine-generated proof context away from the low sequential IDs
/// typically used by caller-created local contexts.
const AUTO_PREMISE_FVAR_BASE: u64 = u64::MAX / 4;

pub(crate) type HypothesisWithProofFVar = (Expr, FVarId, Option<QuantifierOrigin>);

pub(crate) fn build_hypothesis_proof_context(
    hypotheses: &[(Expr, Option<QuantifierOrigin>)],
    local_ctx: Option<&LocalContext>,
) -> (Vec<HypothesisWithProofFVar>, Option<LocalContext>) {
    if hypotheses.is_empty() && local_ctx.is_none() {
        return (Vec::new(), None);
    }

    let mut proof_context = local_ctx.cloned().unwrap_or_default();
    let existing_decls: Vec<_> = proof_context.iter().cloned().collect();
    let source_len = hypotheses.len().max(existing_decls.len());
    let max_existing_id = existing_decls
        .iter()
        .map(|decl| decl.id.as_u64())
        .max()
        .unwrap_or(0);
    let mut next_fvar = (max_existing_id + 1).max(AUTO_PREMISE_FVAR_BASE);
    let mut hypotheses_with_fvars = Vec::with_capacity(source_len);

    for idx in 0..source_len {
        let (hyp, origin) = match hypotheses.get(idx) {
            Some((hyp, origin)) => (hyp.clone(), origin.clone()),
            None => {
                let decl = &existing_decls[idx];
                (decl.type_.clone(), None)
            }
        };

        let fvar = if let Some(decl) = existing_decls.get(idx) {
            decl.id
        } else {
            let fvar = FVarId::new(next_fvar);
            next_fvar += 1;
            proof_context.push_with_id(
                fvar,
                Name::from_string(&format!("auto_h{idx}")),
                hyp.clone(),
                BinderInfo::Default,
            );
            fvar
        };

        hypotheses_with_fvars.push((hyp, fvar, origin));
    }

    (
        hypotheses_with_fvars,
        if proof_context.is_empty() {
            None
        } else {
            Some(proof_context)
        },
    )
}

/// Result of automatic proof search.
///
/// Use [`ProofResult::new`] to construct. Field accessors are provided for
/// reading; direct field access is deprecated in favour of the accessor methods
/// to allow future field additions without source breakage (#2608).
#[derive(Debug)]
#[non_exhaustive]
pub struct ProofResult {
    /// The proof term
    pub proof_term: Expr,
    /// Human-readable proof steps
    pub proof_text: String,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Local context required to type-check premise-dependent proof terms.
    ///
    /// `None` means the proof term is closed. `Some(ctx)` exposes the synthetic
    /// hypothesis binders created by `auto_prove_with_premises`.
    pub proof_context: Option<LocalContext>,
}

impl ProofResult {
    /// Construct a new proof result.
    pub fn new(
        proof_term: Expr,
        proof_text: impl Into<String>,
        time_ms: u64,
        proof_context: Option<LocalContext>,
    ) -> Self {
        Self {
            proof_term,
            proof_text: proof_text.into(),
            time_ms,
            proof_context,
        }
    }

    /// The proof term.
    pub fn proof_term(&self) -> &Expr {
        &self.proof_term
    }

    /// Human-readable proof steps.
    pub fn proof_text(&self) -> &str {
        &self.proof_text
    }

    /// Time taken in milliseconds.
    pub fn time_ms(&self) -> u64 {
        self.time_ms
    }

    /// Local context required to type-check premise-dependent proof terms.
    pub fn proof_context(&self) -> Option<&LocalContext> {
        self.proof_context.as_ref()
    }

    /// Return a copy with `time_ms` replaced.
    pub fn with_time_ms(mut self, time_ms: u64) -> Self {
        self.time_ms = time_ms;
        self
    }

    /// Infer the proof term's type using the stored proof context when needed.
    pub fn infer_type(&self, env: &Environment) -> Result<Expr, clean_kernel::TypeError> {
        match &self.proof_context {
            Some(ctx) => TypeChecker::with_context(env, ctx.clone()).infer_type(&self.proof_term),
            None => TypeChecker::new(env).infer_type(&self.proof_term),
        }
    }
}
