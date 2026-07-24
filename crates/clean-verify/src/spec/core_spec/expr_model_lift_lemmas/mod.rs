// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! lift_at structural lemmas and derived proofs (split from expr_model.rs)

mod amount_zero;
mod bvar_cases;
mod structural;

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_lemmas(&mut self) -> Result<(), SpecError> {
        self.add_expr_model_lift_structural_lemmas()?;
        self.add_expr_model_lift_bvar_lemmas()?;
        self.add_expr_model_lift_zero_lemmas()?;
        Ok(())
    }
}
