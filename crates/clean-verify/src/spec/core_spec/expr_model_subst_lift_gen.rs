// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Registration entrypoint for cutoff-generalized substitution/lift proofs.
//!
//! The proof terms are split across smaller sibling modules to keep each file
//! below the repo's size cap while preserving the dependency order.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_subst_lift_gen(&mut self) -> Result<(), SpecError> {
        self.add_expr_model_subst_lift_cross_bvar()?;
        self.add_expr_model_subst_lift_cross_compose()?;
        self.add_expr_model_subst_lift_exchange()?;
        Ok(())
    }
}
