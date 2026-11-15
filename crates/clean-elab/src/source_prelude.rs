// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Session-only evidence that a frontend deliberately chose a bare environment.
use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, ExtensionIdx, PersistentExtEntry,
    PersistentExtState,
};
use clean_kernel::{Environment, Name};
use std::sync::OnceLock;

#[derive(Clone)]
struct Marker;
impl PersistentExtEntry for Marker {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: Name::anon(),
            data: clean_kernel::env::EnvExtensionEntryData::Scalar(0),
        }
    }
    fn from_env_entry(_: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}
#[derive(Clone, Default)]
struct State {
    bare: bool,
}
impl PersistentExtState for State {
    type Entry = Marker;
    fn add_entry(&mut self, _: &Marker) {}
    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}
fn index() -> ExtensionIdx {
    static INDEX: OnceLock<ExtensionIdx> = OnceLock::new();
    *INDEX.get_or_init(|| {
        register_persistent_ext::<State>(Name::from_string("Clean.elab.bareSourceModule"))
    })
}
pub(crate) fn mark_bare_module(env: &mut Environment) {
    env.get_ext_state_mut::<State>(index()).bare = true;
}
pub(crate) fn is_bare_module(env: &Environment) -> bool {
    env.get_ext_state::<State>(index())
        .is_some_and(|state| state.bare)
}
