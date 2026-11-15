// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local format requirement for environments seeded by Clean's bootstrap.
//!
//! Classification selects a bootstrap from earlier reads. The actual importer
//! must enforce the same format on the objects it consumes, including cache
//! hits and every companion. This requirement authenticates neither an author
//! nor a producer: ordinary payload/declaration/world checks still apply.

use super::artifact_ledger::NoLedgerEntry;
use super::load_parse::LoadModule;
use super::ImportError;
use crate::module::ParsedModule;
use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, Environment, ExtensionIdx, PersistentExtState,
};
use clean_kernel::name::Name;

#[derive(Clone, Debug, Default)]
struct CleanPayloadRequirement {
    required: bool,
}

impl PersistentExtState for CleanPayloadRequirement {
    type Entry = NoLedgerEntry;

    fn add_entry(&mut self, _entry: &Self::Entry) {}

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

// Only the extension type has a global index. Its requirement is local to each
// Environment, survives clones, and cannot be imported or exported by artifacts.
static REQUIREMENT_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

fn requirement_idx() -> ExtensionIdx {
    *REQUIREMENT_IDX.get_or_init(|| {
        register_persistent_ext::<CleanPayloadRequirement>(Name::from_string(
            "Clean.olean.cleanPayloadRequirement",
        ))
    })
}

/// Require every subsequent artifact part loaded into this environment to
/// carry a validated Clean payload. Clones retain the requirement; it cannot
/// be disabled or changed by imported extension entries. This local loading
/// policy is not exported into `.olean` files and is no authenticity claim.
pub fn require_clean_payload_imports(env: &mut Environment) {
    env.get_ext_state_mut::<CleanPayloadRequirement>(requirement_idx())
        .required = true;
}

/// Whether this environment requires validated Clean payloads on subsequent
/// artifact imports. Used by the frontend to prevent failed artifact loads
/// from being replaced by a provider or permissive-import stand-in.
#[must_use]
pub fn clean_payload_imports_required(env: &Environment) -> bool {
    env.get_ext_state::<CleanPayloadRequirement>(requirement_idx())
        .is_some_and(|state| state.required)
}

fn check(env: &Environment, has_payload: bool, module: Option<&str>) -> Result<(), ImportError> {
    if clean_payload_imports_required(env) && !has_payload {
        return Err(ImportError::CleanPayloadRequired {
            module: module.unwrap_or("<unnamed module>").to_owned(),
        });
    }
    Ok(())
}

pub(super) fn check_load_module(
    env: &Environment,
    module: &LoadModule,
    label: Option<&str>,
) -> Result<(), ImportError> {
    check(env, module.clean_payload.is_some(), label)
}

pub(super) fn check_parsed_module(
    env: &Environment,
    module: &ParsedModule,
    label: Option<&str>,
) -> Result<(), ImportError> {
    check(env, module.clean_payload.is_some(), label)
}

pub(super) fn check_artifact_parts(
    env: &Environment,
    module: &str,
    base: &LoadModule,
    server: Option<&LoadModule>,
    private: Option<&LoadModule>,
) -> Result<(), ImportError> {
    if !clean_payload_imports_required(env) {
        return Ok(());
    }
    check_load_module(env, base, Some(module))?;
    for (suffix, part) in [("._server", server), ("._private", private)] {
        if let Some(part) = part {
            check_load_module(env, part, Some(&format!("{module}{suffix}")))?;
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "clean_payload_requirement_tests.rs"]
mod tests;
