// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary declaration fields read from Lean before import adjusts transparency.
//! They belong to the source declaration and are used only for writing exports.

use super::artifact_ledger::NoLedgerEntry;
use crate::module::ReducibilityHintsData;
use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, Environment, ExtensionIdx, PersistentExtState,
};
use clean_kernel::name::Name;
use hashbrown::HashMap;
use std::sync::{Arc, OnceLock};

#[derive(Clone, Default)]
pub(crate) struct ExportFields {
    pub(crate) hints: Option<ReducibilityHintsData>,
    pub(crate) all: Option<Vec<Name>>,
}

#[derive(Clone, Default)]
struct ImportedFields(Arc<HashMap<Name, ExportFields>>);

impl PersistentExtState for ImportedFields {
    type Entry = NoLedgerEntry;

    fn add_entry(&mut self, _entry: &Self::Entry) {}

    fn forget_declaration(&mut self, name: &Name) -> bool {
        self.0.contains_key(name) && Arc::make_mut(&mut self.0).remove(name).is_some()
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

fn index() -> ExtensionIdx {
    static IDX: OnceLock<ExtensionIdx> = OnceLock::new();
    *IDX.get_or_init(|| {
        register_persistent_ext::<ImportedFields>(Name::from_string("Clean.olean.sourceFields"))
    })
}

impl ExportFields {
    pub(crate) fn remember(mut self, env: &mut Environment, name: &Name) {
        // Singleton annotations reconstruct exactly from the declaration name.
        if self.all.as_deref() == Some(std::slice::from_ref(name)) {
            self.all = None;
        }
        if self.all.is_none() && self.hints.is_none() {
            return;
        }
        let state = env.get_ext_state_mut::<ImportedFields>(index());
        Arc::make_mut(&mut state.0).insert(name.clone(), self);
    }

    pub(crate) fn for_constant<'a>(env: &'a Environment, name: &Name) -> Option<&'a Self> {
        env.get_ext_state::<ImportedFields>(index())?.0.get(name)
    }
}
