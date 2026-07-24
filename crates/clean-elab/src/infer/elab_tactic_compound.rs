// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic sequence evaluation.
//!
//! Compound tactic dispatch migrated to registry-based handlers in
//! `builtins_compound.rs` (Wave 5) and `builtins_phase3d_elab.rs` (Wave 6).
//! This file retains only `eval_tactic_seq`, which is used by `elab_by_tactic`
//! and the `TacticEval` implementation on `ElabCtx`.

use super::ElabCtx;
use crate::tactic::ProofState;
use crate::ElabError;
use clean_parser::SurfaceTactic;

impl<'a> ElabCtx<'a> {
    /// Run a sequence of tactics.
    pub(super) fn eval_tactic_seq(
        &mut self,
        ps: &mut ProofState,
        tacs: &[SurfaceTactic],
    ) -> Result<(), ElabError> {
        for t in tacs {
            self.eval_tactic(ps, t)?;
        }
        Ok(())
    }
}
