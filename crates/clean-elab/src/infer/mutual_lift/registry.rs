// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lifted-member registry (design §5.3 step 8): for every member a
//! recursive `mutual` block was lifted into, which recursor and slot its value
//! eliminates and how its parameters map onto that recursor's arguments.
//! Equation synthesis (`tactic/simp/rec_equations.rs`, brick B3) reads it to
//! fold a recursor application in an unfolded member back to the member.
//!
//! The entries are recorded only AFTER the members register (through
//! `CtxAttributes::apply`), so a refused block leaves no entry. Session state,
//! like `Clean.olean.scopedInstances`: nothing is exported to `.olean` yet.

use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, ExtensionIdx, PersistentExtEntry,
    PersistentExtState,
};
use clean_kernel::{Expr, Name};
use std::collections::HashMap;
use std::sync::OnceLock;

/// One lifted member.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct MutualLiftEntry {
    /// The member constant.
    pub member: Name,
    /// Every member of its strongly connected component, in source order.
    pub block: Vec<Name>,
    /// The recursor its value applies (`T.rec`, `T.rec_N`).
    pub recursor: Name,
    /// The motive slot it owns.
    pub slot: usize,
    /// Its index among the slot's owners: its value projects component
    /// `owner_index` of `owner_count` out of the recursor application (a
    /// right-nested `PProd`, or `And` for theorems; no projection for one).
    pub owner_index: usize,
    /// The number of members owning its slot.
    pub owner_count: usize,
    /// Number of leading parameters every call passes unchanged.
    pub fixed_arity: usize,
    /// Parameter index of the major premise.
    pub major_param: usize,
    /// Parameter indices passed after the major, in order.
    pub rest_params: Vec<usize>,
    /// The pre-definition with siblings as constants (the recursive form, for
    /// the compiler and diagnostics; never kernel-checked).
    pub predef: Expr,
    /// Per-constructor equations `∀ xs, member … (c fields) … = rhs` as
    /// closed statements (`mutual_lift/eqns.rs`), read by `simp [member]`.
    /// Empty for a theorem, or when synthesis declined for some constructor.
    /// Never trusted: each rewrite is re-checked by the kernel.
    pub equations: Vec<Expr>,
}

impl PersistentExtEntry for MutualLiftEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.member.clone(),
            data: clean_kernel::env::EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

/// The registry state: member name → entry.
#[derive(Debug, Clone, Default)]
pub(crate) struct MutualLiftState {
    entries: HashMap<Name, MutualLiftEntry>,
}

impl MutualLiftState {
    /// The entry of a lifted member.
    #[must_use]
    pub(crate) fn get(&self, member: &Name) -> Option<&MutualLiftEntry> {
        self.entries.get(member)
    }
}

impl PersistentExtState for MutualLiftState {
    type Entry = MutualLiftEntry;

    fn add_entry(&mut self, entry: &MutualLiftEntry) {
        self.entries.insert(entry.member.clone(), entry.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static MUTUAL_LIFT_IDX: OnceLock<ExtensionIdx> = OnceLock::new();

/// The extension index of [`MutualLiftState`].
pub(crate) fn mutual_lift_idx() -> ExtensionIdx {
    *MUTUAL_LIFT_IDX.get_or_init(|| {
        register_persistent_ext::<MutualLiftState>(Name::from_string("Clean.elab.mutualLift"))
    })
}
