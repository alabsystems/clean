// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The type-less ascription `(e :)`.
//!
//! Lean's grammar is `typeAscription := "(" term " :" optional term ")"`
//! (`Lean/Parser/Term.lean:182-183`), and the `(e :)` form elaborates `e`
//! with NO expected type under `withSynthesize (postpone := .no)`, then runs
//! `ensureHasType` against the surrounding expected type
//! (`Lean/Elab/BuiltinNotation.lean:433-435`). Mathlib writes it to keep the
//! expected type from steering `e` (`hf.left b <| (congr_fun h b :)`,
//! `Function.Injective2.left'`/`right'` in `Logic/Function/Basic.lean`).
//! The parser hands it over as `App(Ident(TYPE_ASCRIPTION_WITHOUT_TYPE), [e])`.
//!
//! It is deliberately NOT `(e : _)`: `elab_ascription` unifies a hole type
//! with the expected type first and then elaborates `e` against it, which is
//! the opposite of what the form is for.

use super::ElabCtx;
use crate::error::ElabError;
use clean_kernel::Expr;
use clean_parser::SurfaceArg;

impl ElabCtx<'_> {
    /// Elaborate `(e :)`: `e` with no expected type; the caller's own
    /// expected-type check (`elaborate_with_expected_type`, argument
    /// unification) then plays `ensureHasType`.
    pub(super) fn elab_ascription_without_type(
        &mut self,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        let [arg] = args else {
            return Err(ElabError::InternalInvariant(format!(
                "`(e :)` carries exactly one term, got {}",
                args.len()
            )));
        };
        if arg.name.is_some() {
            return Err(ElabError::InternalInvariant(
                "`(e :)` carries a positional term, not a named argument".to_string(),
            ));
        }
        let value = self.elaborate_with_expected_type(&arg.expr, None)?;
        Ok(self.metas.instantiate(&value))
    }
}
