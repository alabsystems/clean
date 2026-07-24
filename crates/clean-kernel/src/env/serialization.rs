// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment serialization (JSON, bincode, file I/O).
//!
//! Extracted from env/mod.rs for maintainability (see #307).
//! Contains `JsonEnvironment`, `StructureFieldInfo`, and serialization
//! methods on `Environment`.

use crate::inductive::{ConstructorVal, InductiveVal, RecursorVal};
use crate::name::Name;
use crate::quot::QuotVal;
use serde::{Deserialize, Serialize};

use super::origin::ConstantOrigin;
use super::types::ConstantInfo;
use super::Environment;

/// JSON-friendly intermediate representation of Environment
/// Uses Vec instead of HashMap for JSON compatibility
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct JsonEnvironment {
    /// All constant declarations (definitions, axioms, theorems, opaques)
    pub constants: Vec<ConstantInfo>,
    /// Per-constant origin metadata, keyed by name.
    #[serde(default)]
    pub constant_origins: Vec<ConstantOriginInfo>,
    /// Inductive type definitions
    pub inductives: Vec<InductiveVal>,
    /// Constructor declarations for inductive types
    pub constructors: Vec<ConstructorVal>,
    /// Recursor declarations for inductive types
    pub recursors: Vec<RecursorVal>,
    /// Quotient type declarations
    #[serde(default)]
    pub quotients: Vec<QuotVal>,
    /// Structure field information
    #[serde(default)]
    pub structure_fields: Vec<StructureFieldInfo>,
}

/// Information about structure fields for a given structure type
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StructureFieldInfo {
    /// Name of the structure type
    pub struct_name: Name,
    /// Names of the fields in order
    pub field_names: Vec<Name>,
}

/// JSON-friendly origin metadata entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConstantOriginInfo {
    /// Name of the constant.
    pub name: Name,
    /// Origin and trust metadata for the constant.
    pub origin: ConstantOrigin,
}

impl JsonEnvironment {
    /// Create from an Environment
    pub(super) fn from_env(env: &Environment) -> Self {
        Self {
            constants: env.constants.values().cloned().collect(),
            constant_origins: env
                .constant_origins
                .iter()
                .map(|(name, origin)| ConstantOriginInfo {
                    name: name.clone(),
                    origin: origin.clone(),
                })
                .collect(),
            inductives: env.inductives.values().cloned().collect(),
            constructors: env.constructors.values().cloned().collect(),
            recursors: env.recursors.values().cloned().collect(),
            quotients: env.quotients.values().cloned().collect(),
            structure_fields: env
                .structure_fields
                .iter()
                .map(|(struct_name, fields)| StructureFieldInfo {
                    struct_name: struct_name.clone(),
                    field_names: fields.clone(),
                })
                .collect(),
        }
    }

    /// Convert into an Environment.
    ///
    /// Non-serialized fields (init flags, registries, attributes) use their
    /// `Default` values — all bools are `false`, all maps/sets are empty.
    pub(super) fn into_env(self) -> Environment {
        let quot_init = !self.quotients.is_empty();
        Environment {
            constants: self
                .constants
                .into_iter()
                .map(|c| (c.name.clone(), c))
                .collect(),
            constant_origins: self
                .constant_origins
                .into_iter()
                .map(|entry| (entry.name, entry.origin))
                .collect(),
            inductives: self
                .inductives
                .into_iter()
                .map(|i| (i.name.clone(), i))
                .collect(),
            constructors: self
                .constructors
                .into_iter()
                .map(|c| (c.name.clone(), c))
                .collect(),
            recursors: self
                .recursors
                .into_iter()
                .map(|r| (r.name.clone(), r))
                .collect(),
            quotients: self
                .quotients
                .into_iter()
                .map(|q| (q.name.clone(), q))
                .collect(),
            quot_init,
            structure_fields: self
                .structure_fields
                .into_iter()
                .map(|info| (info.struct_name.clone(), info.field_names))
                .collect(),
            ..Default::default()
        }
    }
}

impl Environment {
    /// Serialize the environment to JSON using an intermediate representation
    /// that converts HashMap<Name, _> to Vec<_> for JSON compatibility
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        let json_env = JsonEnvironment::from_env(self);
        serde_json::to_string(&json_env)
    }

    /// Serialize the environment to pretty JSON
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn to_json_pretty(&self) -> Result<String, serde_json::Error> {
        let json_env = JsonEnvironment::from_env(self);
        serde_json::to_string_pretty(&json_env)
    }

    /// Deserialize an environment from JSON
    /// REQUIRES: `json` is valid JSON representing a JsonEnvironment (or returns Err)
    /// ENSURES: On Ok, returns Environment equivalent to the JSON representation
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        let json_env: JsonEnvironment = serde_json::from_str(json)?;
        Ok(json_env.into_env())
    }

    /// Serialize the environment to binary format (bincode)
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn to_bincode(&self) -> Result<Vec<u8>, bincode::error::EncodeError> {
        bincode::serde::encode_to_vec(self, bincode::config::standard())
    }

    /// Deserialize an environment from binary format (bincode)
    /// REQUIRES: `data` is valid bincode-encoded Environment (or returns Err)
    /// ENSURES: On Ok, returns Environment equivalent to the one that was serialized
    pub fn from_bincode(data: &[u8]) -> Result<Self, bincode::error::DecodeError> {
        bincode::serde::decode_from_slice(data, bincode::config::standard()).map(|(__v, _)| __v)
    }

    /// Save environment to a file (binary format)
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn save_to_file(&self, path: &std::path::Path) -> std::io::Result<()> {
        let data = self
            .to_bincode()
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        std::fs::write(path, data)
    }

    /// Load environment from a file (binary format)
    /// REQUIRES: `path` points to a readable file with valid bincode Environment (or returns Err)
    /// ENSURES: On Ok, returns Environment loaded from the file
    pub fn load_from_file(path: &std::path::Path) -> std::io::Result<Self> {
        let data = std::fs::read(path)?;
        Self::from_bincode(&data)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }
}
