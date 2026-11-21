// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture the private records that implement the stable ToString Nat dictionary.
use super::native_owners::CapturedPrivateNativeModule;
use clean_kernel::Name;
use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

#[derive(Deserialize)]
#[serde(untagged)]
enum Component {
    Text(String),
    Index(u64),
}

#[derive(Deserialize)]
struct Row {
    name: Vec<Component>,
    owner: String,
}

#[derive(Deserialize)]
struct Original {
    owners: HashMap<String, String>,
    declarations: Vec<Row>,
}

struct Manifest {
    modules: HashMap<Name, String>,
    rows: HashMap<Name, Name>,
}

fn manifest() -> Option<&'static Manifest> {
    static MANIFEST: OnceLock<Option<Manifest>> = OnceLock::new();
    MANIFEST
        .get_or_init(|| {
            let original: Original =
                serde_json::from_str(include_str!("native_nat_dictionary_436.json")).ok()?;
            let modules = original
                .owners
                .into_iter()
                .map(|(module, digest)| (Name::interned(&module), digest))
                .collect();
            let rows =
                original
                    .declarations
                    .into_iter()
                    .map(|row| {
                        let name = row.name.into_iter().fold(Name::anon(), |name, component| {
                            match component {
                                Component::Text(s) => name.str(s),
                                Component::Index(n) => name.num(n),
                            }
                        });
                        (name, Name::interned(&row.owner))
                    })
                    .collect();
            Some(Manifest { modules, rows })
        })
        .as_ref()
}

/// Tracks the original SDK graph while the frontend loads the selected imports.
#[derive(Default)]
pub struct StableNatDictionaryCheck {
    seen: HashSet<Name>,
    conflict: bool,
}

impl StableNatDictionaryCheck {
    /// Visit the same immutable module parts from which the program is imported.
    pub fn observe(&mut self, module: &CapturedPrivateNativeModule<'_, '_>) {
        if self.conflict {
            return;
        }
        let Some(manifest) = manifest() else {
            self.conflict = true;
            return;
        };
        if let Some(expected) = manifest.modules.get(module.name) {
            let digest: String = module
                .digest()
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect();
            self.conflict = digest != *expected || !self.seen.insert(module.name.clone());
        } else {
            self.conflict = module
                .owners()
                .is_none_or(|names| names.iter().any(|name| manifest.rows.contains_key(name)));
        }
    }

    /// Seal the graph once every selected backend record has an original owner.
    pub fn finish(self) -> Option<StableNatDictionary> {
        (!self.conflict && self.seen.len() == manifest()?.modules.len())
            .then_some(StableNatDictionary(()))
    }
}

/// The captured private dictionary's two closure records and its 32 Nat.reprFast records.
pub struct StableNatDictionary(());

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CapturedModuleBytes;
    use clean_kernel::LeanWorld;

    #[test]
    #[ignore = "requires CLEAN_LEAN436_LIB from the official v4.36.0 SDK"]
    fn captured_nat_dictionary_rejects_changed_implementation_bytes() {
        let lib = std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = clean_kernel::Environment::for_lean_replay();
        crate::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        let dictionary_module = Name::interned("Init.Data.ToString.Basic");
        let mut original = StableNatDictionaryCheck::default();
        let mut altered = StableNatDictionaryCheck::default();
        let mut duplicate = StableNatDictionaryCheck::default();
        crate::load_modules_with_deps_checked(
            &mut env,
            &["Init.Data.ToString.Basic".into()],
            &[lib],
            &mut |_, _, _| Ok(()),
            &mut |name, _, parts| {
                let module = CapturedPrivateNativeModule::new(name, parts);
                original.observe(&module);
                duplicate.observe(&module);
                if *name == dictionary_module {
                    duplicate.observe(&module);
                    let mut ir = parts.ir.unwrap().to_vec();
                    *ir.last_mut().unwrap() ^= 1;
                    let changed = CapturedModuleBytes {
                        ir: Some(&ir),
                        ..parts
                    };
                    altered.observe(&CapturedPrivateNativeModule::new(name, changed));
                } else {
                    altered.observe(&module);
                }
                Ok(())
            },
        )
        .unwrap();
        assert!(original.finish().is_some());
        assert!(altered.finish().is_none());
        assert!(duplicate.finish().is_none());
        assert!(StableNatDictionaryCheck::default().finish().is_none());
    }
}
