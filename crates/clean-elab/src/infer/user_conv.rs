// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conv-position user macros: the substitute-and-delegate bridge for
//! `macro "kw" … : conv => `(conv| …)` declarations and conv-headed
//! `macro_rules` arms.
//!
//! Mirrors [`super::user_tactic`] (the `(tactic| …)` bridge) with two
//! conv-specific obligations:
//!
//! 1. **Conv-body-only dispatch.** Clean's tactic registry is category-flat:
//!    the conv keyword is parsed and dispatched through the same
//!    `SurfaceTactic::Named` route as ordinary tactics, so the handler itself
//!    must refuse to run unless the proof state is a conv-body sub-state
//!    (`ProofState::in_conv_body`, stamped by `eval_conv_goal` /
//!    `eval_conv_hyps` / `eval_conv`). Running conv navigation against a real
//!    goal would overwrite the target with a (possibly non-Prop) focus with
//!    no reconstruction boundary — the kernel would still reject the final
//!    proof, but the guard fails closed at dispatch instead.
//! 2. **Delegation through `run_conv_body`.** The expanded script runs through
//!    the SAME sequencer the inline `conv => …` body uses (including its
//!    conv-mode `congr` interception), so an expanded conv macro and its
//!    inline spelling are the same program.
//!
//! # Expansion
//!
//! The script is the macro's TEMPLATE: a use instantiates it with the call's
//! arguments (`clean_parser::instantiate_tactic_template`), as Lean expands
//! the quotation — an argument stands wherever the script writes its
//! variable, the script's binders are renamed apart, and its free names
//! resolve where the macro was declared (the registration marks them).
//!
//! # Substitution reach (fail closed)
//!
//! The registration path still consults [`substitution_reaches`] for every
//! script tactic of an argument-taking macro and rejects the declaration
//! loudly when a variable could stand where the bridge cannot show it is
//! meant to (a hypothesis location, an `enter` binder step, a tactic shape it
//! does not list). Nullary macros have nothing to substitute, so ANY
//! parseable conv script is instantiated.
//!
//! # Soundness
//!
//! Delegation only: the handler adds no way to change a target or close a
//! goal. Every effect of the expanded script flows through the existing conv
//! machinery, whose boundary (`eval_conv_goal` / `eval_conv_hyps`) rebuilds
//! the whole-target equality and kernel-checks it via `replace_target_eq` /
//! `replace_local_decl_with_cast` — exactly as for an inline conv script.

use std::sync::Arc;

use super::user_tactic::call_site_args;
use crate::tactic::{CompoundTacticEntry, CompoundTacticHandler, TacticError};
use clean_parser::{ConvEnterArg, SurfaceTactic, SurfaceTacticLocation};

/// Whether argument substitution provably reaches every bound-name occurrence
/// a conv-script tactic could carry. Used at REGISTRATION time for
/// argument-taking conv macros; see the module docs for why anything outside
/// this set must be rejected rather than delegated.
///
/// - `Named` / `Term`: payloads are expression lists `substitute_in_tactic`
///   rewrites — reachable.
/// - `Rw`: rule terms are rewritten; the `at h` location carries hypothesis
///   names as plain strings substitution cannot touch, so a bound name there
///   is a hidden occurrence — not reachable.
/// - `ConvArg`: payload is an index (`i64`) — nothing to reach.
/// - `ConvEnter`: index steps carry no names; a `Name` step equal to a bound
///   name is a hidden occurrence — not reachable.
/// - Everything else (`Simp`, nested `Conv`, `Cases`, …): payload coverage is
///   unverified — not reachable (fail closed).
pub(super) fn substitution_reaches(
    tac: &SurfaceTactic,
    bound: &[clean_parser::SurfaceName],
) -> bool {
    match tac {
        SurfaceTactic::Named { .. } | SurfaceTactic::Term(..) => true,
        SurfaceTactic::Rw(_, _, location) | SurfaceTactic::Rewrite(_, _, location) => {
            !location_mentions(location, bound)
        }
        SurfaceTactic::ConvArg(..) => true,
        SurfaceTactic::ConvEnter(_, args) => args.iter().all(|arg| match arg {
            ConvEnterArg::Index(_) => true,
            ConvEnterArg::Name(n) => !bound.iter().any(|b| b == n),
        }),
        _ => false,
    }
}

/// Short human-readable shape name for registration-rejection diagnostics.
pub(super) fn conv_tactic_shape(tac: &SurfaceTactic) -> &'static str {
    match tac {
        SurfaceTactic::Rw(..) => "`rw … at h` (bound name in the location)",
        SurfaceTactic::Rewrite(..) => "`rewrite … at h` (bound name in the location)",
        SurfaceTactic::Rwa(..) => "`rwa`",
        SurfaceTactic::ConvEnter(..) => "`enter [binder-name]` (bound name as a binder step)",
        SurfaceTactic::Simp { all: true, .. } => "`simp_all`",
        SurfaceTactic::Simp { all: false, .. } => "`simp`",
        SurfaceTactic::SimpRw(..) => "`simp_rw`",
        SurfaceTactic::Conv(..) => "nested `conv`",
        _ => "a non-substitutable tactic shape",
    }
}

/// True iff a tactic location names any of the bound pattern variables — a
/// hidden occurrence substitution cannot rewrite (locations carry hypothesis
/// names as plain strings).
fn location_mentions(
    location: &SurfaceTacticLocation,
    bound: &[clean_parser::SurfaceName],
) -> bool {
    match location {
        SurfaceTacticLocation::Goal | SurfaceTacticLocation::Wildcard => false,
        SurfaceTacticLocation::Hyps(names) | SurfaceTacticLocation::HypsAndGoal(names) => {
            names.iter().any(|n| bound.iter().any(|b| b == n))
        }
    }
}

/// Build the compound handler for a conv-position user macro.
///
/// `name` is the macro keyword (dispatch + diagnostics). `bound_names` are the
/// pattern variable names in declaration order (empty for a nullary macro).
/// `script` is the parsed conv tactic sequence from the `(conv| …)` expansion.
///
/// The handler: (1) refuses outside a conv body (fail closed — see module
/// docs), (2) binds the call-site arguments 1:1 to the pattern variables,
/// (3) substitutes them into the script, and (4) delegates the substituted
/// script to [`run_conv_body`](crate::tactic::builtins_phase3d_conv::run_conv_body)
/// — the SAME sequencer the inline `conv => …` body uses. Soundness:
/// delegation only; no new way to change a focus or close a goal.
pub(super) fn build_user_conv_handler(
    name: String,
    bound_names: Vec<clean_parser::SurfaceName>,
    script: Vec<SurfaceTactic>,
    hygienic: bool,
) -> CompoundTacticEntry {
    let entry_name = name.clone();
    let handler: CompoundTacticHandler = Arc::new(move |eval, ps, tac| {
        if !ps.in_conv_body {
            return Err(TacticError::InvalidTarget {
                tactic: name.clone(),
                detail: format!(
                    "`{name}` is a conv macro; it can only be used inside a `conv` block \
                     (fail closed: its navigation script has no meaning against a real goal)"
                ),
            });
        }
        let args = call_site_args(tac).ok_or_else(|| TacticError::ElaborationFailed {
            detail: format!("conv macro `{name}` invoked with unexpected syntax"),
        })?;
        if args.len() != bound_names.len() {
            return Err(TacticError::MissingArgument {
                tactic: name.clone(),
                expected: format!(
                    "{} argument(s) ({}), received {}",
                    bound_names.len(),
                    bound_names
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", "),
                    args.len()
                ),
            });
        }
        // The script is the macro's template: the arguments stand wherever it
        // writes their variables, and its binders are renamed apart
        // (`clean_parser::instantiate_tactic_template`).
        let expanded =
            clean_parser::instantiate_tactic_template(&script, &bound_names, args, hygienic)
                .map_err(|refusal| TacticError::ElaborationFailed {
                    detail: format!("conv macro `{name}`: {}", refusal.reason()),
                })?;
        crate::tactic::builtins_phase3d_conv::run_conv_body(eval, ps, &expanded)
    });
    CompoundTacticEntry {
        name: entry_name,
        handler,
    }
}

/// Build the simple-entry handler registered alongside a conv macro's
/// compound handler.
///
/// The simple entry exists so the parser learns the keyword and its argument
/// pattern (`tactic_patterns()`); dispatch always prefers the compound entry,
/// so this handler firing means the compound registration is missing — an
/// honest registration-bug error, never a fabricated success.
pub(super) fn conv_macro_simple_handler(name: String) -> crate::tactic::TacticHandler {
    Arc::new(move |_ps, _args| {
        Err(TacticError::ElaborationFailed {
            detail: format!(
                "conv macro `{name}` was dispatched through the simple tactic path; its \
                 compound handler owns dispatch — this indicates a registration bug"
            ),
        })
    })
}
