// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaboration of explicit universe instance expressions (`.{u v}` syntax).
//!
//! When a constant reference includes universe instances like `@List.{u}`,
//! the elaborator uses these explicit universe levels instead of generating
//! fresh universe metavariables.

use super::*;

impl<'a> ElabCtx<'a> {
    /// Elaborate a universe instance expression: `Foo.{u v}`.
    ///
    /// Elaborates the inner expression and the explicit level arguments,
    /// then replaces the constant's fresh universe parameters with the
    /// explicitly provided levels.
    pub(super) fn elab_universe_inst(
        &mut self,
        expr: &SurfaceExpr,
        levels: &[LevelExpr],
    ) -> Result<Expr, ElabError> {
        // Elaborate the level expressions first.
        let elab_levels: Vec<Level> = levels
            .iter()
            .map(|l| self.elab_level(l))
            .collect::<Result<Vec<_>, _>>()?;

        // Elaborate the inner expression (typically an identifier like `List`).
        let inner = self.elaborate(expr)?;

        // The inner expression must be a constant for universe instantiation.
        match inner.kind() {
            ExprKind::Const(name, existing_levels) => {
                // More explicit levels than the constant has parameters is an
                // error, as in Lean ("too many explicit universe levels").
                if elab_levels.len() > existing_levels.len() {
                    return Err(ElabError::UniverseLevelMismatch {
                        name: format!("{name}"),
                        expected: existing_levels.len(),
                        actual: elab_levels.len(),
                    });
                }
                // A PARTIAL list fills the leading parameters and leaves the
                // rest to inference, as Lean's `mkConst` pads with fresh level
                // metavariables (pinned Lean v4.30.0-rc2: `ULift.{1} Nat :
                // Type 1`, and `def t : Type := ULift.{1} Nat` is a type
                // mismatch, so the given level is enforced). The levels the
                // bare reference was just elaborated with are exactly those
                // fresh levels, so the tail is taken from them: `Foo.{u}` means
                // `Foo` with its first level fixed. Breadth class (65) in
                // docs/FRONTEND_CLASS_LEDGER.md.
                let mut levels = elab_levels;
                levels.extend(existing_levels[levels.len()..].iter().cloned());
                Ok(Expr::const_(name.clone(), levels))
            }
            _ => Err(ElabError::UniverseInstNotConst),
        }
    }
}
