// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which elaboration run added a source declaration: Clean's answer to
//! Lean's `env.getModuleIdxFor? decl`, which `ParametricAttribute.add`
//! (`Lean/Attributes.lean@v4.30.0-rc2`) asks before it lets the
//! `attribute [..]` command bind `implemented_by` or `extern` to `decl`:
//! "Cannot add attribute `[attr]` to declaration `decl` because it is in an
//! imported module".
//!
//! A run is an [`ElabUnit`]: each `FileContext` mints its own (a file, a
//! header-first batch, whose per-declaration lexical snapshots keep it), and
//! every caller that elaborates without one, Trust's bridge
//! (`elaborate_decl_and_register_with_warning`) and the temporary context a
//! `namespace` or `section` block builds for it included, shares
//! [`ElabUnit::UNSCOPED`]. Registration records each declaration's own names
//! with its run (`crate::register::leaf_own_names`), in the environment, so
//! the answer does not depend on which driver asks. A constant no run
//! recorded (the prelude, an `.olean` import) is imported to every run, and
//! so is one another run recorded (an earlier source module of `clean
//! check`, elaborated with its own `FileContext`).
//!
//! What that does NOT see, stated: a clone of a `FileContext` stays in its
//! run, so a driver that elaborates a prelude once and hands every consumer
//! a copy must make the copy with `FileContext::fork_run` (Trust's temporal
//! lanes clone theirs today, so a check there may bind a prelude
//! declaration); and every caller without a `FileContext` shares one run, so
//! two such sessions over one environment see each other's declarations as
//! their own. Both accept a binding Lean refuses as imported; neither lets
//! compiled code skip the order record (`clean_compiler::implemented_by_order`).
//!
//! Session state, like `Clean.elab.mutualLift`: nothing is exported to
//! `.olean`, and an empty export keeps it out of the environment digest.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, ExtensionIdx, PersistentExtEntry,
    PersistentExtState,
};
use clean_kernel::{Environment, Name};

use crate::FileContext;

/// One elaboration run (module doc).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ElabUnit(u64);

impl ElabUnit {
    /// The run every caller without a `FileContext` belongs to.
    pub(crate) const UNSCOPED: Self = Self(0);

    /// A run no other has: what a new `FileContext` holds.
    pub(crate) fn fresh() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        Self(NEXT.fetch_add(1, Ordering::Relaxed))
    }

    /// The run of `file_ctx`, or [`Self::UNSCOPED`] without one.
    pub(crate) fn of(file_ctx: Option<&FileContext>) -> Self {
        file_ctx.map_or(Self::UNSCOPED, FileContext::elab_unit)
    }
}

impl Default for ElabUnit {
    fn default() -> Self {
        Self::fresh()
    }
}

/// Where an attribute was written. Only the `attribute [..]` command can
/// name a declaration of another run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AttributeSite {
    /// `@[attr] def d …`: `d` is being declared here.
    Declaration,
    /// `attribute [attr] d`.
    AttributeCommand,
}

/// One recorded declaration.
#[derive(Debug, Clone)]
pub(crate) struct DeclaredInEntry {
    name: Name,
    unit: ElabUnit,
    simple_equation_source: bool,
}

impl PersistentExtEntry for DeclaredInEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.name.clone(),
            data: clean_kernel::env::EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

/// Declaration → the run that added it. Shared on clone: an environment is
/// cloned far more often than a declaration is added.
#[derive(Debug, Clone, Default)]
pub(crate) struct DeclaredInState {
    units: Arc<HashMap<Name, (ElabUnit, bool)>>,
}

impl PersistentExtState for DeclaredInState {
    type Entry = DeclaredInEntry;

    fn add_entry(&mut self, entry: &DeclaredInEntry) {
        Arc::make_mut(&mut self.units).insert(
            entry.name.clone(),
            (entry.unit, entry.simple_equation_source),
        );
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static DECLARED_IN_IDX: OnceLock<ExtensionIdx> = OnceLock::new();

fn declared_in_idx() -> ExtensionIdx {
    *DECLARED_IN_IDX.get_or_init(|| {
        register_persistent_ext::<DeclaredInState>(Name::from_string("Clean.elab.declaredIn"))
    })
}

/// Record that `unit` added `names` (after they registered).
pub(crate) fn record_declared(
    env: &mut Environment,
    unit: ElabUnit,
    names: impl IntoIterator<Item = Name>,
) {
    record_declared_with_equation_sources(env, unit, names, &[]);
}

pub(crate) fn record_declared_with_equation_sources(
    env: &mut Environment,
    unit: ElabUnit,
    names: impl IntoIterator<Item = Name>,
    simple_equation_sources: &[Name],
) {
    for name in names {
        let simple_equation_source = simple_equation_sources.contains(&name);
        env.add_ext_entry::<DeclaredInState>(
            declared_in_idx(),
            &DeclaredInEntry {
                name,
                unit,
                simple_equation_source,
            },
        );
    }
}

/// Whether `unit` added `decl`: `false` for a constant of an imported module
/// (module doc), the question `attribute [..] decl` asks first.
pub(crate) fn declared_by(env: &Environment, unit: ElabUnit, decl: &Name) -> bool {
    env.get_ext_state::<DeclaredInState>(declared_in_idx())
        .and_then(|state| state.units.get(decl))
        .is_some_and(|(owner, _)| *owner == unit)
}

/// Whether this declaration used the ordinary source definition path on
/// which a single defining equation can be realized.
pub(crate) fn simple_equation_source(env: &Environment, decl: &Name) -> bool {
    env.get_ext_state::<DeclaredInState>(declared_in_idx())
        .and_then(|state| state.units.get(decl))
        .is_some_and(|(_, simple)| *simple)
}

/// Whether any source run added `decl` (this file, or an earlier source
/// module of the same check): `false` for the prelude and an `.olean` import.
pub(crate) fn declared_in_source(env: &Environment, decl: &Name) -> bool {
    env.get_ext_state::<DeclaredInState>(declared_in_idx())
        .is_some_and(|state| state.units.contains_key(decl))
}

#[cfg(test)]
#[path = "declared_here_tests.rs"]
mod tests;
