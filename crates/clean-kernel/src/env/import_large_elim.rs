// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Large-elimination inference for an `.olean` module's inductives, run IN
//! PLACE after the part's family and own definitions are registered, and
//! refreshed for owned structural families when its private part completes.
//!
//! [`crate::inductive::allows_large_elim`] infers constructor field sorts with
//! a `TypeChecker`, so the module's own inductives and constructors must be
//! resident while it runs. The importer used to get that by cloning the WHOLE
//! environment once per module, staging the family in the clone, deciding,
//! and dropping the clone — measured 2026-09-23 at 71-74% of steady-state
//! import samples (`reports/lean4-replacement-audit-2026-09-24/performance.json`,
//! gap 1), and the reason import cost grew faster than the closure.
//!
//! The old clone staged the inductives and constructors. The importer now
//! decides on the real environment after its own definitions are also resident:
//! constructor field types may refer to those definitions. Every decision is
//! still taken BEFORE any flag is written. Lean's own kernel decides this inside
//! `add_inductive` with the block already added to its (persistent, hence
//! cheap) environment: `inductive.cpp`, `elim_only_at_universe_zero`.
//!
//! [`allows_large_elim`] reads the family's result level up to whnf by the
//! same helper native admission and recursor regeneration use
//! (`Environment::type_former_result_level`, `env/inductive_result_sort.rs`),
//! so a `δ`-hidden Prop follows the actual elimination criterion. If a
//! codomain or field type needs a declaration available only in a later part,
//! its flag is then `false`, the restrictive answer. A complete module artifact
//! can stage an early recursor until that context exists; its authoritative
//! recursor still undergoes strict regeneration and comparison. The importer
//! refreshes only that artifact's structural families with this same criterion
//! after private declarations arrive. No stored elimination flag decides it.

use super::{DeclarationVerification, Environment};
use crate::inductive::{allows_large_elim, Constructor};
use crate::name::Name;

impl Environment {
    /// Recompute `is_large_elim` for inductives the `.olean` importer has just
    /// registered through the structural tier, each against the constructor
    /// list the importer converted for it.
    ///
    /// Only an inductive stamped [`DeclarationVerification::StructuralOnly`]
    /// is touched: a kernel-checked inductive's flag was decided by the
    /// kernel's own `add_inductive` and is never revisited here. A name that
    /// is not a resident inductive is ignored. Returns how many flags changed.
    ///
    /// SOUNDNESS: the value written is the kernel's own
    /// [`allows_large_elim`] verdict, never a caller-supplied boolean. The
    /// caller supplies only the constructor list — the same input it passed to
    /// the per-module staging clone this replaces, and strictly less authority
    /// than the structural tier already grants it (which inserts whatever
    /// `is_large_elim` the record carries). The generation counter is bumped
    /// when a flag changes, so no type-checker cache keyed on it survives.
    pub fn recompute_imported_large_elim(
        &mut self,
        targets: impl IntoIterator<Item = (Name, Vec<Constructor>)>,
    ) -> usize {
        let decided: Vec<(Name, bool)> = targets
            .into_iter()
            .filter_map(|(name, ctors)| {
                let ind = self.inductives.get(&name)?;
                if self.declaration_verification.get(&name)
                    != Some(&DeclarationVerification::StructuralOnly)
                {
                    return None;
                }
                let large = allows_large_elim(
                    self,
                    &ind.type_,
                    &ctors,
                    ind.num_params,
                    ind.all_names.len(),
                );
                Some((name, large))
            })
            .collect();
        let mut changed = 0usize;
        for (name, large) in decided {
            if let Some(ind) = self.inductives.get_mut(&name) {
                if ind.is_large_elim != large {
                    ind.is_large_elim = large;
                    changed += 1;
                }
            }
        }
        if changed > 0 {
            self.generation += 1;
        }
        changed
    }
}

#[cfg(test)]
#[path = "import_large_elim_tests.rs"]
mod tests;
