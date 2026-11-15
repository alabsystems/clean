// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed accounting for `clean olean replay`: every constant a replayed
//! module's `.olean` names must be replayed, left out as `unsafe`/`partial`, or
//! refused.
//!
//! The replay learns what a module declares from the loader's summaries
//! (`LoadSummary::added_names`, `skipped_constants`, `shadowed_declarations`).
//! A declaration the loader dropped without saying so in any of them would be
//! checked by `leanchecker` and by nothing here, so the verb would admit a
//! module one of whose declarations it never saw. This cross-checks the
//! summaries against the constants every part of the module's `.olean` stores
//! (base, `.olean.server`, `.olean.private`; read with the loader's own
//! parsers, without converting an expression), and refuses every name nothing
//! accounts for. The header's `extraConstNames` is not consulted: it names the
//! compiler's IR declarations, which are no kernel constants and which
//! `leanchecker` never sees (measured: `ReplayHonestInd` lists
//! `HV.ctorIdx._boxed` and `honest_ht_leaf._closed_0` there).
//!
//! The one exception is the canonical quotient (`Quot`, `Quot.mk`, `Quot.lift`,
//! `Quot.ind`): Lean's replay turns a stored `quotInfo` into the kernel's own
//! `quotDecl` (`Lean/Replay.lean`), and the replay environment already holds
//! exactly that declaration (`Environment::for_lean_replay`), so the loader
//! keeps the resident one and records nothing.

use std::path::PathBuf;

use crate::find_module_olean;
use crate::import::stored_constant_names;

/// The declarations of Lean's `quotDecl`, which the replay environment seeds.
pub(super) const QUOT_PRIMITIVES: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

/// The display names the `.olean` parts of `module` store that `covered`
/// does not account for, sorted.
///
/// # Errors
/// The module's `.olean` cannot be found or its name table cannot be read:
/// nothing can then be accounted for, and the caller refuses the module.
pub(super) fn unaccounted_declarations(
    module: &str,
    search_path: &[PathBuf],
    covered: &dyn Fn(&str) -> bool,
) -> Result<Vec<String>, String> {
    let path = find_module_olean(module, search_path)
        .ok_or_else(|| format!("no .olean for `{module}` on the search path"))?;
    let names = stored_constant_names(&path)
        .map_err(|e| format!("{}: stored constants unreadable: {e}", path.display()))?;
    Ok(names
        .into_iter()
        .filter(|name| !covered(name) && !QUOT_PRIMITIVES.contains(&name.as_str()))
        .collect())
}
