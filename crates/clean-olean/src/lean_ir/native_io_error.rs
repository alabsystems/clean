// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture the exact stable SDK import and runtime names used by the private
//! IO error formatter. A source file can import other modules if none of
//! their kernel or generated IR names competes with a selected runtime row.

use super::native_owners::CapturedPrivateNativeModule;
use crate::{CapturedModuleBytes, OleanError, OleanResult};
use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{Environment, Name};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write;
use std::sync::OnceLock;

#[derive(Deserialize)]
struct Oracle {
    modules: Vec<String>,
    digest: String,
    owners: BTreeMap<String, String>,
    externs: BTreeMap<String, String>,
}

struct Manifest {
    oracle: Oracle,
    modules: HashMap<Name, usize>,
    owners: HashMap<Name, Name>,
}

fn oracle_name(text: &str) -> Name {
    // These are the release oracle's string or numeric Name components. The
    // source generator checks them against the SDK's original structured name.
    text.split('.').fold(Name::anon(), |name, component| {
        if let Ok(n) = component.parse::<u64>() {
            name.num(n)
        } else {
            name.str(component)
        }
    })
}

fn manifest() -> Option<&'static Manifest> {
    static MANIFEST: OnceLock<Option<Manifest>> = OnceLock::new();
    MANIFEST
        .get_or_init(|| {
            let oracle: Oracle =
                serde_json::from_str(include_str!("native_io_error_436.json")).ok()?;
            let modules = oracle
                .modules
                .iter()
                .enumerate()
                .map(|(i, n)| (oracle_name(n), i))
                .collect();
            let owners = oracle
                .owners
                .iter()
                .map(|(name, owner)| (oracle_name(name), oracle_name(owner)))
                .collect();
            Some(Manifest {
                oracle,
                modules,
                owners,
            })
        })
        .as_ref()
}

fn error(message: impl Into<String>) -> OleanError {
    OleanError::Region(message.into())
}

/// A single candidate's original captured graph. Keep hashes after the load,
/// and examine unrelated modules only for competing declarations.
#[derive(Default)]
pub struct StableIoErrorImportCheck {
    modules: BTreeMap<usize, [u8; 32]>,
    refused: bool,
}

impl StableIoErrorImportCheck {
    /// Observe a selected source import before the shared loader consumes it.
    pub fn observe(&mut self, module: &Name, capture: CapturedModuleBytes<'_>) {
        self.observe_module(&CapturedPrivateNativeModule::new(module, capture))
    }

    /// Reuse the ownership and digest of other consumers of this private import.
    pub fn observe_module(&mut self, capture: &CapturedPrivateNativeModule<'_, '_>) {
        let module = capture.name;
        if self.refused {
            return;
        }
        let Some(manifest) = manifest() else {
            self.refused = true;
            return;
        };
        if let Some(index) = manifest.modules.get(module) {
            self.refused = self.modules.insert(*index, capture.digest()).is_some();
        } else {
            self.refused = capture
                .owners()
                .is_none_or(|names| names.iter().any(|name| manifest.owners.contains_key(name)));
        }
    }

    /// Finish after capture, import checks, cycle checks and registration.
    /// Missing, changed or competing inputs cannot authorize the formatter.
    pub fn finish(self) -> Option<StableIoErrorImports> {
        let manifest = manifest()?;
        if self.refused || self.modules.len() != manifest.oracle.modules.len() {
            return None;
        }
        let mut hash = Sha256::new();
        hash.update(b"Clean stable native IO error import graph\0");
        for (index, original) in manifest.oracle.modules.iter().enumerate() {
            hash.update((original.len() as u64).to_le_bytes());
            hash.update(original.as_bytes());
            hash.update(self.modules.get(&index)?);
        }
        let mut digest = String::with_capacity(64);
        for byte in hash.finalize() {
            write!(&mut digest, "{byte:02x}").ok()?;
        }
        (digest == manifest.oracle.digest).then_some(StableIoErrorImports(()))
    }
}

/// Complete bytes and unambiguous selected native owners for the original
/// Init.System.IO code import in a non-module-system stable source file.
#[derive(Debug)]
pub struct StableIoErrorImports(());

impl StableIoErrorImports {
    /// Recheck every original runtime leaf's compiler descriptor in the
    /// actual post-elaboration environment, including UInt32.toUSize.
    ///
    /// # Errors
    /// Refuses missing or conflicting owners, substitutions or descriptors.
    pub fn check_externs(&self, env: &Environment) -> OleanResult<()> {
        let manifest = manifest().ok_or_else(|| error("invalid stable IO error manifest"))?;
        for (text, symbol) in &manifest.oracle.externs {
            let name = oracle_name(text);
            let owner = manifest
                .owners
                .get(&name)
                .ok_or_else(|| error("missing stable IO error owner"))?;
            let binding = env
                .extern_metadata(&name)
                .map_err(|e| error(e.to_string()))?;
            if crate::import::lean_declaration_artifact(env, &name).as_deref()
                != Some(owner.to_string().as_str())
                || env.has_implemented_by(&name)
                || !matches!(binding, Some(CompilerExternMetadata::Complete(ref b)) if b.arity == CompilerExternArity::Unspecified &&
                    matches!(b.entries.as_slice(),[CompilerExternEntry::Standard{backend,symbol:found}] if *backend==Name::interned("all") && found==symbol))
            {
                return Err(error(format!(
                    "different compiled stable error operation {name}"
                )));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::LeanWorld;

    #[test]
    #[ignore = "requires the original CLEAN_LEAN436_LIB"]
    fn stable_io_error_authority_requires_the_original_code_graph_and_unique_owners() {
        let lib = std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::new();
        crate::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        let mut genuine = StableIoErrorImportCheck::default();
        let mut missing = StableIoErrorImportCheck::default();
        let mut changed = StableIoErrorImportCheck::default();
        let mut duplicate = StableIoErrorImportCheck::default();
        let mut spoofed = StableIoErrorImportCheck::default();
        let original = Name::interned("Init.Data.Repr");
        let extra = Name::interned("Init.Data.Array.BinSearch");
        assert!(!manifest().unwrap().modules.contains_key(&extra));
        let mut saw_extra = false;
        crate::load_modules_with_deps_checked(
            &mut env,
            &["Init.System.IO".into(), "Init.Data.Array.BinSearch".into()],
            &[lib],
            &mut |_, _, _| Ok(()),
            &mut |module, _, capture| {
                genuine.observe(module, capture);
                if *module == extra {
                    saw_extra = true;
                    assert!(CapturedPrivateNativeModule::new(module, capture)
                        .owners()
                        .unwrap()
                        .contains(&Name::interned("Array.binSearch")));
                }
                duplicate.observe(module, capture);
                spoofed.observe(module, capture);
                if *module == original {
                    let mut modified = capture.ir.unwrap().to_vec();
                    let last = modified.last_mut().unwrap();
                    *last ^= 1;
                    changed.observe(
                        module,
                        CapturedModuleBytes {
                            ir: Some(&modified),
                            ..capture
                        },
                    );
                    assert!(CapturedPrivateNativeModule::new(
                        module,
                        CapturedModuleBytes {
                            ir_signature: None,
                            ..capture
                        }
                    )
                    .owners()
                    .is_none());
                    assert!(CapturedPrivateNativeModule::new(
                        module,
                        CapturedModuleBytes {
                            ir: None,
                            ..capture
                        }
                    )
                    .owners()
                    .is_none());
                    duplicate.observe(&Name::interned("OtherModule"), capture);
                    spoofed.observe(&Name::anon().str("Init.Data.Repr"), capture);
                } else {
                    missing.observe(module, capture);
                    changed.observe(module, capture);
                }
                Ok(())
            },
        )
        .unwrap();
        assert!(saw_extra);
        let authority = genuine.finish().expect("original 4.36 imports");
        authority.check_externs(&env).unwrap();
        assert!(missing.finish().is_none());
        assert!(changed.finish().is_none());
        assert!(duplicate.finish().is_none());
        assert!(spoofed.finish().is_none());
        let target = Name::interned("UInt32.toUSize");
        env.register_extern(target, "different_uint32_to_usize".into());
        assert!(authority.check_externs(&env).is_err());
    }
}

#[cfg(test)]
mod sdk_tests {
    use super::*;
    use serde_json::Value;
    use std::path::PathBuf;

    #[test]
    #[ignore = "requires the original CLEAN_LEAN436_BIN"]
    fn stable_sdk_selects_the_manifest_owners_phases_and_externs() {
        let binary = PathBuf::from(std::env::var_os("CLEAN_LEAN436_BIN").unwrap());
        let bin_dir = binary.parent().unwrap();
        let path = std::env::join_paths(std::iter::once(bin_dir.to_owned()).chain(
            std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()),
        ))
        .unwrap();
        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/lean/StableIOErrorRuntime436.lean");
        let output = std::process::Command::new(&binary)
            .env("PATH", path)
            .env("LEAN_SYSROOT", bin_dir.parent().unwrap())
            .arg("--run")
            .arg(fixture)
            .output()
            .unwrap();
        assert!(output.status.success(), "{:?}", output);
        let lines = String::from_utf8(output.stdout).unwrap();
        let mut lines = lines
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap());
        let graph = lines.next().unwrap();
        let mut modules = Vec::new();
        for module in graph["graph"].as_array().unwrap() {
            assert_eq!(module["phase"], "Lean.IRPhases.all");
            modules.push(module["name"].as_str().unwrap().to_owned());
        }
        modules.sort();
        let manifest = manifest().unwrap();
        assert_eq!(modules, manifest.oracle.modules);
        let mut owners = HashMap::new();
        let mut externs = BTreeMap::new();
        for cone in lines {
            for row in cone["result"]["rows"].as_array().unwrap() {
                assert_eq!(row["phase"], "Lean.IRPhases.all");
                assert_eq!(row["source"], "IR");
                let record = &row["record"];
                let text = record["name"].as_str().unwrap();
                let typed =
                    record["typedName"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .fold(Name::anon(), |n, p| {
                            if let Some(s) = p.as_str() {
                                n.str(s)
                            } else {
                                n.num(p.as_u64().unwrap())
                            }
                        });
                assert_eq!(typed, oracle_name(text));
                let owner = oracle_name(row["owner"].as_str().unwrap());
                if let Some(prior) = owners.insert(typed, owner.clone()) {
                    assert_eq!(prior, owner);
                }
                if !record["extern"].is_null() {
                    let symbol = record["nameForC"].as_str().unwrap();
                    assert_eq!(
                        record["extern"],
                        serde_json::json!([["standard", "all", symbol]])
                    );
                    externs.insert(text.to_owned(), symbol.to_owned());
                }
            }
        }
        assert_eq!(owners, manifest.owners);
        assert_eq!(externs, manifest.oracle.externs);
    }
}
