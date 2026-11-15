// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The micro band's totality contrast, in kernel-checked constants.**
//!
//! `micro_soundness.rs` exposes `micro_has_type` as a TOTAL (degenerate)
//! predicate: `micro_has_type_total : forall e U, micro_has_type e U` is a
//! genuine zero-domain-axiom theorem, so EVERY expression has EVERY type and
//! the whole historical `micro_*` band means nothing.
//!
//! `micro_verifies_r0.rs` builds the honest successor — `MicroVerifies`, the
//! FRESH-NAME context-indexed relation modelling
//! `crates/clean-kernel/src/micro/checker.rs::verify_impl` arm-for-arm — and
//! registers `mv_bvar_nil_reject`, whose own description calls it *"the
//! discriminating half that the degenerate `micro_has_type` cannot state"*.
//!
//! **What was missing is the other half: the headline.** A rejection at ONE
//! index is a fact about that index. The claim that separates a faithful family
//! from a degenerate one is that the family is NOT TOTAL, and that claim was
//! nowhere in the tree — `micro_verifies_r0.rs` contains no `-> Empty`
//! statement quantified over the whole relation. This module states it, and
//! pairs it with its opposite.
//!
//! * **`mv_not_total`** — `(forall G c e U, MicroVerifies G c e U) -> Empty`.
//!   One line off `mv_bvar_nil_reject`, and the exact negation of the shape
//!   `micro_has_type_total` has.
//! * **`mv_totality_contrast`** — an `AndType` carrying both: the old band is
//!   provably TOTAL, the new family provably NOT.
//!
//! ## Why a pair rather than a deletion
//!
//! Retiring the vacuous band is a separate act with its own review, and the
//! contrast is more useful than a deletion would be: it keeps both facts
//! kernel-checked and side by side, so a reader does not have to take the
//! degeneracy on trust or dig it out of a header comment. `micro_has_type` and
//! its producers are untouched here, and the Brick-6 fresh-names constraint
//! (`micro_soundness.rs:33-38`) is honoured — no producer is re-pointed at
//! `MicroVerifies`, which over a non-total family would derive `Empty`.
//!
//! ## What this does NOT claim
//!
//! Nothing about the Rust checker. `MicroVerifies` carries THREE arms — Sort
//! (`checker.rs:319-327`), BVar (`checker.rs:363-381`) and Pi
//! (`checker.rs:464-510`) — and absence of a
//! derivation at any other shape means "outside the modeled fragment", NOT
//! "the checker rejects". Non-totality here says the relation refuses
//! *something*, which is the minimum a faithful family must do and the maximum
//! this pair establishes. The whole-checker relating proof remains unstarted.
//!
//! ## Census
//!
//! ZERO new axioms, ZERO new inductives: 2 value-bearing theorems through
//! `add_definition` with kernel `add_decl` checking.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The totality shape of the faithful relation, spelled once.
pub(super) const TY_MV_TOTAL: &str = "forall (G : ListType MicroExpr) (c : MicroCert) (e : MicroExpr) (U : MicroExpr), MicroVerifies G c e U";

/// The totality shape of the degenerate historical band, spelled once.
pub(super) const TY_MHT_TOTAL: &str = "forall (e : MicroExpr) (U : MicroExpr), micro_has_type e U";

/// A concrete micro expression for the two witness slots.
const S0: &str = "(MicroExpr.sort MicroLevel.zero)";

pub(super) fn ty_mv_not_total() -> String {
    format!("({TY_MV_TOTAL}) -> Empty")
}

pub(super) fn val_mv_not_total() -> String {
    format!("fun (htot : {TY_MV_TOTAL}) => mv_bvar_nil_reject {S0} {S0} (htot (ListType.nil MicroExpr) (MicroCert.bvar Nat.zero {S0}) (MicroExpr.bvar Nat.zero) {S0})")
}

pub(super) fn ty_mv_totality_contrast() -> String {
    format!("AndType ({TY_MHT_TOTAL}) (({TY_MV_TOTAL}) -> Empty)")
}

pub(super) fn val_mv_totality_contrast() -> String {
    format!("AndType.intro ({TY_MHT_TOTAL}) (({TY_MV_TOTAL}) -> Empty) micro_has_type_total mv_not_total")
}

fn thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Register the micro band's totality contrast.
    pub(super) fn add_micro_totality_contrast(&mut self) -> Result<(), SpecError> {
        thm(
            self,
            "mv_not_total",
            ty_mv_not_total(),
            val_mv_not_total(),
            &["mv_bvar_nil_reject", "MicroVerifies"],
            "THE HEADLINE the faithful micro family was missing: MicroVerifies is NOT TOTAL. \
             mv_bvar_nil_reject is a rejection at ONE index, which is a fact about that index; \
             this is the claim that separates a faithful family from a degenerate one, and it is \
             the exact negation of the shape micro_has_type_total has. One line off the rejection \
             witness.",
        )?;
        thm(
            self,
            "mv_totality_contrast",
            ty_mv_totality_contrast(),
            val_mv_totality_contrast(),
            &["micro_has_type_total", "mv_not_total", "AndType.intro"],
            "THE CONTRAST, IN ONE CONSTANT: the historical micro_* band is provably TOTAL (every \
             expression has every type) and the faithful successor is provably NOT. Kept as a pair \
             rather than retiring the old band, because both facts are worth having kernel-checked \
             side by side -- a deletion would leave the reader to take the degeneracy on trust. No \
             producer is re-pointed at MicroVerifies, honouring the Brick-6 fresh-names constraint: \
             a retained producer over a non-total family would derive Empty.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
#[path = "micro_totality_contrast_tests.rs"]
mod tests;
