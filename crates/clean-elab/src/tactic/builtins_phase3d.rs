// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D tactic registrations: keyword-parsed tactics migrated from
//! dedicated `SurfaceTactic` variants to registry dispatch via
//! keyword-to-Named routing in the parser (#2440).
//!
//! Split from `builtins.rs` for file-size compliance.

use std::sync::Arc;

use super::builtins::nullary;
use super::registry::{TacticArgPattern, TacticEntry, TacticRegistry};

/// Register keyword-parsed tactics migrated in Phase 3D.6.
///
/// These tactics were previously parsed as dedicated `SurfaceTactic` variants
/// (e.g., `Rfl(Span)`) via `TokenKind` keyword matching. Now the parser emits
/// `SurfaceTactic::Named` for the keyword token, and the handler is looked up
/// in the registry.
/// ENSURES: `registry` contains simple handlers for `rfl`, `reduce_eq`, `sorry`, and `show`.
/// ENSURES: Existing simple entries with those names are replaced.
pub(super) fn register_phase3d_keyword(registry: &mut TacticRegistry) {
    // rfl — prove by reflexivity
    // Parser: TokenKind::Rfl → Named { name: "rfl", args: [] }
    registry.register(nullary("rfl", super::rfl));

    // reduce_eq — prove equality by reducing both sides via WHNF
    // Produces explicit proof terms witnessing each reduction step.
    // Part of #685.
    registry.register(nullary("reduce_eq", super::reduce_eq));

    // sorry — admit the current goal
    // Parser: TokenKind::Sorry → Named { name: "sorry", args: [] }
    // Special semantics (SORRY_COUNTER, DENY_SORRY) are handled inside
    // term_close::sorry via create_sorry_term — no tactic-level concern.
    registry.register(nullary("sorry", super::sorry));

    // show — change the goal type (must be definitionally equal)
    // Parser: TokenKind::Show → Named { name: "show", args: [ty] }
    // Alias for `change`; handler is term_close::show.
    registry.register(TacticEntry {
        name: "show".to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(|ps, args| {
            let ty = args
                .first()
                .ok_or_else(|| super::TacticError::MissingArgument {
                    tactic: "show".into(),
                    expected: "a type expression".into(),
                })?;
            super::term_close::show(ps, ty.clone())
        }),
    });
}
// Location-aware tactics (push_neg, dsimp, unfold) are in builtins_phase3d_loc.rs.
