// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Measure the tracked Python inputs and the two gate-registry columns.

use std::{collections::BTreeMap, fs, path::Path};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{git, InputIdentity};

mod membership;
mod record;

pub use membership::{check, check_publication, render};
pub use record::{read_record, record, RecordReading};

pub const FIGURE: &str = "tooling.python_minters";
pub const RECORD_PATH: &str = "data/python_minters_evidence.json";
pub const PRODUCER_SOURCE: &str = "crates/clean-evidence/src/python_minters/record.rs";
pub const REGISTRY: &str = "data/gate_registry.json";
pub const TRACKED_INPUT: &str = "git-index:scripts/**/*.py";

const INPUT_SCOPE: &str =
    "tracked Python paths in the Git index and the working-tree gate registry";

#[derive(Debug, thiserror::Error)]
pub enum InventoryError {
    #[error("{0}")]
    Invalid(String),
    #[error("{0}")]
    Unavailable(String),
}

#[derive(Deserialize)]
struct Registry {
    schema: String,
    rows: Vec<RegistryRow>,
}

#[derive(Deserialize)]
struct RegistryRow {
    id: Option<serde_json::Value>,
    path: String,
    implemented_by: Option<String>,
}

#[derive(Serialize)]
pub struct Inventory {
    figure: &'static str,
    gate_registry_sha256: String,
    #[serde(flatten)]
    counts: Counts,
    tracked_scripts_sha256: String,
}

impl Inventory {
    fn input_identity(&self) -> InputIdentity {
        InputIdentity::from_files(
            INPUT_SCOPE,
            BTreeMap::from([
                (
                    TRACKED_INPUT.to_owned(),
                    self.tracked_scripts_sha256.clone(),
                ),
                (REGISTRY.to_owned(), self.gate_registry_sha256.clone()),
            ]),
        )
    }
}

#[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Counts {
    pub registry_implemented_by: usize,
    pub registry_path: usize,
    pub registry_rows: usize,
    pub tracked_scripts: usize,
}

#[derive(PartialEq)]
struct Inputs {
    names: Vec<u8>,
    registry: Vec<u8>,
}

impl Inputs {
    fn read(root: &Path) -> Result<Self, InventoryError> {
        let names = git::read(root, &["ls-files", "--deduplicate", "-z", "--", "scripts"])
            .map_err(InventoryError::Unavailable)?;
        let path = root.join(REGISTRY);
        let registry = fs::read(&path)
            .map_err(|err| InventoryError::Unavailable(format!("{}: {err}", path.display())))?;
        Ok(Self { names, registry })
    }

    fn tracked_python(&self) -> Result<Vec<&[u8]>, InventoryError> {
        if !self.names.is_empty() && !self.names.ends_with(b"\0") {
            return Err(InventoryError::Invalid(
                "unterminated Git index path list".to_owned(),
            ));
        }
        let mut python: Vec<&[u8]> = self
            .names
            .split(|byte| *byte == 0)
            .filter(|path| path.starts_with(b"scripts/") && path.ends_with(b".py"))
            .collect();
        python.sort_unstable();
        Ok(python)
    }

    fn registry(&self) -> Result<Registry, InventoryError> {
        let invalid_json = |err| InventoryError::Invalid(format!("{REGISTRY}: {err}"));
        let shape: serde_json::Value =
            serde_json::from_slice(&self.registry).map_err(invalid_json)?;
        if !shape.is_object()
            || shape["rows"]
                .as_array()
                .is_some_and(|rows| rows.iter().any(|row| !row.is_object()))
        {
            return Err(InventoryError::Invalid(format!(
                "{REGISTRY}: expected a registry object and row objects"
            )));
        }
        let registry: Registry = serde_json::from_slice(&self.registry).map_err(invalid_json)?;
        if registry.schema != "clean.gate-registry/v1" {
            return Err(InventoryError::Invalid(format!(
                "{REGISTRY}: unsupported schema {:?}",
                registry.schema
            )));
        }
        Ok(registry)
    }

    fn measure(&self) -> Result<Inventory, InventoryError> {
        let python = self.tracked_python()?;
        let registry = self.registry()?;
        let mut hash = Sha256::new();
        for path in &python {
            hash.update(path);
            hash.update([0]);
        }
        Ok(Inventory {
            figure: FIGURE,
            gate_registry_sha256: hex(&Sha256::digest(&self.registry)),
            counts: Counts {
                registry_implemented_by: registry
                    .rows
                    .iter()
                    .filter(|row| {
                        row.implemented_by
                            .as_ref()
                            .is_some_and(|path| path.ends_with(".py"))
                    })
                    .count(),
                registry_path: registry
                    .rows
                    .iter()
                    .filter(|row| row.path.ends_with(".py"))
                    .count(),
                registry_rows: registry.rows.len(),
                tracked_scripts: python.len(),
            },
            tracked_scripts_sha256: hex(&hash.finalize()),
        })
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub fn inventory(root: &Path) -> Result<Inventory, InventoryError> {
    from_stable_inputs(root, Inputs::measure)
}

fn from_stable_inputs<T>(
    root: &Path,
    apply: impl FnOnce(&Inputs) -> Result<T, InventoryError>,
) -> Result<T, InventoryError> {
    require_root(root)?;
    let source = Inputs::read(root)?;
    let inventory = apply(&source)?;
    if source != Inputs::read(root)? {
        return Err(InventoryError::Invalid(
            "inventory inputs changed during measurement".to_owned(),
        ));
    }
    Ok(inventory)
}

fn require_root(root: &Path) -> Result<(), InventoryError> {
    if git::read(
        root,
        &["rev-parse", "--is-inside-work-tree", "--show-prefix"],
    )
    .map_err(InventoryError::Unavailable)?
        != b"true\n\n"
    {
        return Err(InventoryError::Unavailable(format!(
            "{} is not the root of a Git worktree",
            root.display()
        )));
    }
    Ok(())
}
