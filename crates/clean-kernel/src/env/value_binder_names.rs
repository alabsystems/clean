// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder NAMES of the `∀` telescope a DEFINITION's value unfolds to.
//!
//! Lean binds a named argument by the binder names of the function's type
//! AFTER `whnf` (`ElabAppArgs`, `Lean/Elab/App.lean:803-815` with
//! `normalizeFunType`): for a local `h : Function.Injective f`, whose type
//! unfolds to `∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`, `h (a₁ := x) (a₂ := y) e`
//! names binders that exist only in `Function.Injective`'s VALUE. Clean's
//! kernel `Expr` keeps no binder names, so the environment records, per
//! definition, how many leading `fun` binders its value has and the names of
//! the `∀` binders directly under them. The `.olean` importer fills it off
//! the raw value; the elaborator fills it for the definitions it elaborates
//! and reads it when it binds a named argument.
//!
//! # Where it lives, and why
//!
//! It is a per-name table, held in the typed extension state
//! [`VALUE_BINDER_NAMES_EXTENSION`], which the KERNEL owns so that the local
//! fact delta can carry it by type (`fact_delta`, its one carried extension
//! state), the elaboration record can digest it per name (`content_digest`)
//! and an effect can compare it (`effect`): a replayed elaboration leaves the
//! table a real one leaves. Every other extension state that exports nothing
//! is refused by a delta or listed as elaboration-private.
//!
//! It is not a field of [`Environment`]: a field moves the struct's layout,
//! which Clean's Crystal chains pin item by item
//! (`scripts/crystal_freshness_scope.py`, `strict_monads`), and clearing that
//! pin takes a live re-derivation with the chain's recorded compiler. The
//! state exports nothing and serializes as nothing (extension states
//! serialize as unit), exactly as when `clean-olean` owned it: an environment
//! restored from an artifact has no table.

use std::sync::OnceLock;

use hashbrown::HashMap;
use serde::{Deserialize, Serialize};

use super::persistent_ext::{register_persistent_ext, PersistentExtEntry, PersistentExtState};
use super::{EnvExtensionEntry, EnvExtensionEntryData, Environment, ExtensionIdx};
use crate::name::Name;

/// The registered name of the table's typed extension state.
pub const VALUE_BINDER_NAMES_EXTENSION: &str = "Clean.kernel.valueBinderNames";

/// The shape of one definition's value: `fun x₁ … xₖ => ∀ y₁ … yₙ, body`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValueForallBinderNames {
    /// `k`: the number of leading `fun` binders of the value.
    pub lambdas: usize,
    /// `y₁ … yₙ`, outermost first (`n ≥ 1`). An arrow's binder keeps the
    /// inaccessible name Lean gave it, which no source text can spell.
    pub names: Vec<Name>,
}

/// Definition → the `∀` binder names under its value's leading lambdas.
#[derive(Clone, Debug, Default)]
pub(crate) struct ValueBinderNameState {
    values: HashMap<Name, ValueForallBinderNames>,
}

/// The state is written directly and persists no entries.
#[derive(Clone, Debug)]
pub(crate) struct ValueBinderNameEntry;

impl PersistentExtEntry for ValueBinderNameEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: Name::anon(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

impl PersistentExtState for ValueBinderNameState {
    type Entry = ValueBinderNameEntry;

    fn add_entry(&mut self, _entry: &Self::Entry) {}

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

fn value_binder_name_idx() -> ExtensionIdx {
    static IDX: OnceLock<ExtensionIdx> = OnceLock::new();
    *IDX.get_or_init(|| {
        register_persistent_ext::<ValueBinderNameState>(Name::from_string(
            VALUE_BINDER_NAMES_EXTENSION,
        ))
    })
}

fn empty_table() -> &'static HashMap<Name, ValueForallBinderNames> {
    static EMPTY: OnceLock<HashMap<Name, ValueForallBinderNames>> = OnceLock::new();
    EMPTY.get_or_init(HashMap::new)
}

impl Environment {
    /// The recorded `∀` binder names of `constant`'s value, if any.
    #[must_use]
    pub fn get_value_forall_binder_names(
        &self,
        constant: &Name,
    ) -> Option<&ValueForallBinderNames> {
        self.value_binder_table().get(constant)
    }

    /// Record the shape of `constant`'s value. A value with no `∀` binder
    /// under its lambdas records nothing.
    pub fn record_value_forall_binder_names(
        &mut self,
        constant: Name,
        lambdas: usize,
        names: Vec<Name>,
    ) {
        if names.is_empty() {
            return;
        }
        self.value_binder_table_mut()
            .insert(constant, ValueForallBinderNames { lambdas, names });
    }

    /// The whole table (empty when nothing was recorded).
    pub(crate) fn value_binder_table(&self) -> &HashMap<Name, ValueForallBinderNames> {
        match self.get_ext_state::<ValueBinderNameState>(value_binder_name_idx()) {
            Some(state) => &state.values,
            None => empty_table(),
        }
    }

    /// The table, for a write; counts as a write of its extension state.
    pub(crate) fn value_binder_table_mut(&mut self) -> &mut HashMap<Name, ValueForallBinderNames> {
        &mut self
            .get_ext_state_mut::<ValueBinderNameState>(value_binder_name_idx())
            .values
    }
}
