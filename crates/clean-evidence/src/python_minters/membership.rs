// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact membership of the tracked Python paths and two registry columns.

use std::{collections::BTreeSet, fs, path::Path};

use serde::{Deserialize, Serialize};

use super::{from_stable_inputs, hex, Inputs, InventoryError};

mod publication;

pub use publication::check_publication;

const BASELINE: &str = "data/python_minters_baseline.json";
const SCHEMA: &str = "clean.python_minters_baseline/v1";

#[derive(Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
struct RegistryMember {
    id: String,
    path: String,
}

#[derive(Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Membership {
    registry_implemented_by: BTreeSet<RegistryMember>,
    registry_path: BTreeSet<RegistryMember>,
    schema: String,
    tracked_scripts_hex: BTreeSet<String>,
}

impl Membership {
    fn collect(inputs: &Inputs) -> Result<Self, InventoryError> {
        let mut members = Self {
            registry_implemented_by: BTreeSet::new(),
            registry_path: BTreeSet::new(),
            schema: SCHEMA.to_owned(),
            tracked_scripts_hex: inputs.tracked_python()?.into_iter().map(hex).collect(),
        };
        let mut ids = BTreeSet::new();
        for row in inputs.registry()?.rows {
            let Some(serde_json::Value::String(id)) = row.id else {
                return Err(InventoryError::Invalid(
                    "gate registry row requires a string id".to_owned(),
                ));
            };
            if id.is_empty() || !ids.insert(id.clone()) {
                return Err(InventoryError::Invalid(format!(
                    "empty or duplicate gate registry row id {id:?}"
                )));
            }
            if let Some(path) = row.implemented_by.filter(|path| path.ends_with(".py")) {
                members.registry_implemented_by.insert(RegistryMember {
                    id: id.clone(),
                    path,
                });
            }
            if row.path.ends_with(".py") {
                members
                    .registry_path
                    .insert(RegistryMember { id, path: row.path });
            }
        }
        Ok(members)
    }

    fn canonical_json(&self) -> Result<String, InventoryError> {
        let mut json = serde_json::to_string_pretty(self)
            .map_err(|err| InventoryError::Invalid(format!("cannot render membership: {err}")))?;
        json.push('\n');
        Ok(json)
    }

    fn from_baseline(bytes: &[u8]) -> Result<Self, InventoryError> {
        let baseline: Self = serde_json::from_slice(bytes)
            .map_err(|err| InventoryError::Invalid(format!("{BASELINE}: {err}")))?;
        if baseline.schema != SCHEMA {
            return Err(InventoryError::Invalid(format!(
                "{BASELINE}: unsupported schema {:?}",
                baseline.schema
            )));
        }
        if baseline.canonical_json()?.as_bytes() != bytes {
            return Err(InventoryError::Invalid(format!(
                "{BASELINE}: expected canonical JSON and ordered unique members"
            )));
        }
        for path in &baseline.tracked_scripts_hex {
            let decoded = decode_path(path);
            if !decoded.is_some_and(|path| {
                !path.contains(&0) && path.starts_with(b"scripts/") && path.ends_with(b".py")
            }) {
                return Err(InventoryError::Invalid(format!(
                    "{BASELINE}: invalid tracked Python path hex {path:?}"
                )));
            }
        }
        for column in [&baseline.registry_path, &baseline.registry_implemented_by] {
            let mut ids = BTreeSet::new();
            for member in column {
                if member.id.is_empty() || !ids.insert(&member.id) || !member.path.ends_with(".py")
                {
                    return Err(InventoryError::Invalid(format!(
                        "{BASELINE}: invalid or duplicate Python registry row {:?}",
                        member.id
                    )));
                }
            }
        }
        Ok(baseline)
    }

    fn check(&self, baseline: &Self) -> Result<(), InventoryError> {
        if let Some(path) = self
            .tracked_scripts_hex
            .difference(&baseline.tracked_scripts_hex)
            .next()
        {
            let decoded = decode_path(path).unwrap_or_default();
            return Err(InventoryError::Invalid(format!(
                "new tracked Python path {:?} (hex {path})",
                String::from_utf8_lossy(&decoded)
            )));
        }
        for (field, current, allowed) in [
            ("path", &self.registry_path, &baseline.registry_path),
            (
                "implemented_by",
                &self.registry_implemented_by,
                &baseline.registry_implemented_by,
            ),
        ] {
            if let Some(member) = current.difference(allowed).next() {
                return Err(InventoryError::Invalid(format!(
                    "new Python registry {field} for row {:?}: {:?}",
                    member.id, member.path
                )));
            }
        }
        Ok(())
    }
}

fn decode_path(encoded: &str) -> Option<Vec<u8>> {
    let (pairs, remainder) = encoded.as_bytes().as_chunks::<2>();
    if !remainder.is_empty()
        || !encoded
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    pairs
        .iter()
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).ok()?, 16).ok())
        .collect()
}

pub fn render(root: &Path) -> Result<String, InventoryError> {
    from_stable_inputs(root, |inputs| Membership::collect(inputs)?.canonical_json())
}

pub fn check(root: &Path) -> Result<(), InventoryError> {
    let path = root.join(BASELINE);
    let read = || {
        fs::read(&path)
            .map_err(|err| InventoryError::Unavailable(format!("{}: {err}", path.display())))
    };
    let bytes = read()?;
    let baseline = Membership::from_baseline(&bytes)?;
    let live = from_stable_inputs(root, Membership::collect)?;
    if bytes != read()? {
        return Err(InventoryError::Invalid(
            "Python membership baseline changed during check".to_owned(),
        ));
    }
    live.check(&baseline)
}
