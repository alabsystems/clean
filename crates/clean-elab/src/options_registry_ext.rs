// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#![cfg_attr(not(test), allow(dead_code))]
use super::options_registry::{FileOptions, OptionDecl, OptionError, OptionValue, OptionsRegistry};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    fmt::Write as _,
    fs,
    path::Path,
    time::{SystemTime, UNIX_EPOCH},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[non_exhaustive]
pub(crate) enum OptionCategory {
    Pp,
    Tactic,
    Elaboration,
    Kernel,
    Linter,
    Trace,
    #[default]
    Custom,
}

impl OptionCategory {
    #[must_use]
    pub(crate) const fn title(self) -> &'static str {
        match self {
            Self::Pp => "Pretty Printer",
            Self::Tactic => "Tactic",
            Self::Elaboration => "Elaboration",
            Self::Kernel => "Kernel",
            Self::Linter => "Linter",
            Self::Trace => "Trace",
            Self::Custom => "Custom",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub(crate) enum OptionConstraint {
    #[default]
    None,
    NatRange(u64, u64),
    StringOneOf(Vec<String>),
    DependsOn(String, OptionValue),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OptionChange {
    pub(crate) name: String,
    pub(crate) old_value: OptionValue,
    pub(crate) new_value: OptionValue,
    pub(crate) timestamp: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct OptionChangeTracker {
    pub(crate) history: Vec<OptionChange>,
}

impl OptionChangeTracker {
    #[must_use]
    pub(crate) fn record(
        &mut self,
        name: impl Into<String>,
        old_value: OptionValue,
        new_value: OptionValue,
    ) -> OptionChange {
        let change = OptionChange {
            name: name.into(),
            old_value,
            new_value,
            timestamp: current_timestamp(),
        };
        self.history.push(change.clone());
        change
    }

    pub(crate) fn clear(&mut self) {
        self.history.clear();
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct OptionProfile {
    pub(crate) name: String,
    pub(crate) description: String,
    pub(crate) overrides: BTreeMap<String, OptionValue>,
}

impl OptionProfile {
    #[must_use]
    pub(crate) fn new(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: description.into(),
            overrides: BTreeMap::new(),
        }
    }

    pub(crate) fn apply_to(
        &self,
        file_options: &mut FileOptions<'_>,
    ) -> Result<usize, OptionError> {
        let mut staged = file_options.clone();
        for (name, value) in &self.overrides {
            staged.set(name, value.clone())?;
        }
        *file_options = staged;
        Ok(self.overrides.len())
    }

    #[must_use]
    pub(crate) fn from_file_options(
        file_options: &FileOptions<'_>,
        registry: &OptionsRegistry,
    ) -> Self {
        let mut profile = Self::new(
            "captured-profile",
            "Captured from file-level option overrides",
        );
        for decl in registry.all_options() {
            if let Some(value) = file_options.get(decl.name()) {
                if value != decl.default() {
                    profile
                        .overrides
                        .insert(decl.name().to_string(), value.clone());
                }
            }
        }
        profile
    }

    pub(crate) fn to_json_string(&self) -> Result<String, ExtOptionsError> {
        serde_json::to_string_pretty(&StoredProfile::from(self)).map_err(|error| {
            ExtOptionsError::Serialization {
                message: error.to_string(),
            }
        })
    }

    pub(crate) fn from_json_str(input: &str) -> Result<Self, ExtOptionsError> {
        let profile: StoredProfile =
            serde_json::from_str(input).map_err(|error| ExtOptionsError::Deserialization {
                message: error.to_string(),
            })?;
        Ok(profile.into())
    }

    pub(crate) fn save_to_path(&self, path: impl AsRef<Path>) -> Result<(), ExtOptionsError> {
        let path = path.as_ref();
        fs::write(path, self.to_json_string()?).map_err(|error| ExtOptionsError::WriteProfile {
            path: path.display().to_string(),
            message: error.to_string(),
        })
    }

    pub(crate) fn load_from_path(path: impl AsRef<Path>) -> Result<Self, ExtOptionsError> {
        let path = path.as_ref();
        let input = fs::read_to_string(path).map_err(|error| ExtOptionsError::ReadProfile {
            path: path.display().to_string(),
            message: error.to_string(),
        })?;
        Self::from_json_str(&input)
    }
}

#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum ExtOptionsError {
    #[error(transparent)]
    Base(#[from] OptionError),
    #[error("option '{name}' has incompatible constraint '{constraint}' for type {actual}")]
    ConstraintTypeMismatch {
        name: String,
        constraint: &'static str,
        actual: &'static str,
    },
    #[error("option '{name}' has an invalid nat range constraint {min}..={max}")]
    InvalidNatRange { name: String, min: u64, max: u64 },
    #[error("option '{name}' must declare at least one allowed string value")]
    EmptyStringChoices { name: String },
    #[error("option '{name}' must be in range {min}..={max}, got {value}")]
    OutOfRange {
        name: String,
        value: u64,
        min: u64,
        max: u64,
    },
    #[error("option '{name}' must be one of {allowed:?}, got {value}")]
    NotAllowed {
        name: String,
        value: String,
        allowed: Vec<String>,
    },
    #[error("option '{name}' requires '{dep_name}' = {required}, got {actual}")]
    DependencyNotMet {
        name: String,
        dep_name: String,
        required: String,
        actual: String,
    },
    #[error("failed to serialize option profile: {message}")]
    Serialization { message: String },
    #[error("failed to deserialize option profile: {message}")]
    Deserialization { message: String },
    #[error("failed to read option profile '{path}': {message}")]
    ReadProfile { path: String, message: String },
    #[error("failed to write option profile '{path}': {message}")]
    WriteProfile { path: String, message: String },
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ValidatedRegistry {
    pub(crate) registry: OptionsRegistry,
    pub(crate) categories: BTreeMap<String, OptionCategory>,
    pub(crate) constraints: BTreeMap<String, Vec<OptionConstraint>>,
}

impl ValidatedRegistry {
    #[must_use]
    pub(crate) fn new(registry: OptionsRegistry) -> Self {
        let categories = registry
            .all_options()
            .map(|decl| (decl.name().to_string(), infer_category(decl.name())))
            .collect();
        Self {
            registry,
            categories,
            constraints: BTreeMap::new(),
        }
    }

    #[must_use]
    pub(crate) fn registry(&self) -> &OptionsRegistry {
        &self.registry
    }

    #[must_use]
    pub(crate) fn category_of(&self, name: &str) -> Option<OptionCategory> {
        if self.registry.is_registered(name) {
            Some(match self.categories.get(name) {
                Some(category) => *category,
                None => infer_category(name),
            })
        } else {
            None
        }
    }

    pub(crate) fn categorize_option(
        &mut self,
        name: &str,
        category: OptionCategory,
    ) -> Result<(), ExtOptionsError> {
        ensure_registered(&self.registry, name)?;
        self.categories.insert(name.to_string(), category);
        Ok(())
    }

    pub(crate) fn add_constraint(
        &mut self,
        name: &str,
        constraint: OptionConstraint,
    ) -> Result<(), ExtOptionsError> {
        let decl = self
            .registry
            .get_option(name)
            .ok_or_else(|| OptionError::UnknownOption {
                name: name.to_string(),
            })?;
        let constraint = normalize_constraint(name, decl, &self.registry, constraint)?;
        if matches!(constraint, OptionConstraint::None) {
            self.constraints.remove(name);
        } else {
            self.constraints
                .entry(name.to_string())
                .or_default()
                .push(constraint);
        }
        Ok(())
    }

    pub(crate) fn validate_with_constraints(
        &self,
        name: &str,
        value: &OptionValue,
    ) -> Result<(), ExtOptionsError> {
        let defaults = FileOptions::new(self.registry());
        self.validate_with_file_options(name, value, &defaults)
    }

    pub(crate) fn validate_with_file_options(
        &self,
        name: &str,
        value: &OptionValue,
        file_options: &FileOptions<'_>,
    ) -> Result<(), ExtOptionsError> {
        self.registry.validate_option(name, value)?;
        let constraints = match self.constraints.get(name) {
            Some(values) => values.as_slice(),
            None => &[],
        };
        for constraint in constraints {
            match constraint {
                OptionConstraint::None => {}
                OptionConstraint::NatRange(min, max) => {
                    if let OptionValue::Nat(actual) = value {
                        if actual < min || actual > max {
                            return Err(ExtOptionsError::OutOfRange {
                                name: name.to_string(),
                                value: *actual,
                                min: *min,
                                max: *max,
                            });
                        }
                    }
                }
                OptionConstraint::StringOneOf(allowed) => {
                    if let OptionValue::String(actual) = value {
                        if !allowed.iter().any(|choice| choice == actual) {
                            return Err(ExtOptionsError::NotAllowed {
                                name: name.to_string(),
                                value: actual.clone(),
                                allowed: allowed.clone(),
                            });
                        }
                    }
                }
                OptionConstraint::DependsOn(dep_name, required_value) => {
                    let actual = file_options.get(dep_name).cloned().ok_or_else(|| {
                        OptionError::UnknownOption {
                            name: dep_name.clone(),
                        }
                    })?;
                    if &actual != required_value {
                        return Err(ExtOptionsError::DependencyNotMet {
                            name: name.to_string(),
                            dep_name: dep_name.clone(),
                            required: required_value.to_string(),
                            actual: actual.to_string(),
                        });
                    }
                }
            }
        }
        Ok(())
    }

    pub(crate) fn apply_profile(
        &self,
        profile: &OptionProfile,
        file_options: &mut FileOptions<'_>,
    ) -> Result<usize, ExtOptionsError> {
        let mut staged = file_options.clone();
        for (name, value) in &profile.overrides {
            staged.set(name, value.clone())?;
        }
        for (name, value) in &profile.overrides {
            self.validate_with_file_options(name, value, &staged)?;
        }
        *file_options = staged;
        Ok(profile.overrides.len())
    }
}

#[must_use]
pub(crate) fn infer_category(name: &str) -> OptionCategory {
    if name.starts_with("pp.") {
        OptionCategory::Pp
    } else if name.starts_with("trace.") {
        OptionCategory::Trace
    } else if name.starts_with("linter.") {
        OptionCategory::Linter
    } else if name.starts_with("tactic.")
        || name.starts_with("aesop.")
        || name.starts_with("simp.")
        || name.starts_with("mathverse.")
        || name.starts_with("linarith.")
        || name.starts_with("ring.")
    {
        OptionCategory::Tactic
    } else if name.starts_with("kernel.") || name == "maxHeartbeats" || name == "maxRecDepth" {
        OptionCategory::Kernel
    } else if name.starts_with("elab.") || name == "autoImplicit" || name == "relaxedAutoImplicit" {
        OptionCategory::Elaboration
    } else {
        OptionCategory::Custom
    }
}

#[must_use]
pub(crate) fn diff_options(
    a: &FileOptions<'_>,
    b: &FileOptions<'_>,
    registry: &OptionsRegistry,
) -> Vec<OptionChange> {
    let mut changes = Vec::new();
    let timestamp = current_timestamp();
    for decl in registry.all_options() {
        if let (Some(old_value), Some(new_value)) = (a.get(decl.name()), b.get(decl.name())) {
            if old_value != new_value {
                changes.push(OptionChange {
                    name: decl.name().to_string(),
                    old_value: old_value.clone(),
                    new_value: new_value.clone(),
                    timestamp,
                });
            }
        }
    }
    changes
}

#[must_use]
pub(crate) fn generate_option_docs(registry: &ValidatedRegistry) -> String {
    let mut grouped: BTreeMap<OptionCategory, Vec<&OptionDecl>> = BTreeMap::new();
    for decl in registry.registry.all_options() {
        grouped
            .entry(
                registry
                    .category_of(decl.name())
                    .unwrap_or(OptionCategory::Custom),
            )
            .or_default()
            .push(decl);
    }
    let mut docs = String::new();
    let _ = writeln!(docs, "# Option Reference\n");
    let _ = writeln!(docs, "| Category | Count |\n| --- | ---: |");
    for (category, decls) in &grouped {
        let _ = writeln!(docs, "| {} | {} |", category.title(), decls.len());
    }
    for (category, decls) in grouped {
        let _ = writeln!(docs, "\n## {}\n", category.title());
        let _ = writeln!(
            docs,
            "| Name | Type | Default | Constraints | Description |"
        );
        let _ = writeln!(docs, "| --- | --- | --- | --- | --- |");
        for decl in decls {
            let constraints = match registry.constraints.get(decl.name()) {
                Some(values) => format_constraints(values),
                None => "none".to_string(),
            };
            let _ = writeln!(
                docs,
                "| `{}` | `{}` | {} | {} | {} |",
                decl.name(),
                decl.default().kind_name(),
                escape_markdown_cell(&decl.default().to_string()),
                escape_markdown_cell(&constraints),
                escape_markdown_cell(decl.description())
            );
        }
    }
    docs
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct StoredProfile {
    name: String,
    description: String,
    overrides: BTreeMap<String, StoredValue>,
}

impl From<&OptionProfile> for StoredProfile {
    fn from(profile: &OptionProfile) -> Self {
        let overrides = profile
            .overrides
            .iter()
            .map(|(name, value)| (name.clone(), StoredValue::from(value)))
            .collect();
        Self {
            name: profile.name.clone(),
            description: profile.description.clone(),
            overrides,
        }
    }
}

impl From<StoredProfile> for OptionProfile {
    fn from(profile: StoredProfile) -> Self {
        let overrides = profile
            .overrides
            .into_iter()
            .map(|(name, value)| (name, OptionValue::from(value)))
            .collect();
        Self {
            name: profile.name,
            description: profile.description,
            overrides,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value")]
enum StoredValue {
    Bool(bool),
    Nat(u64),
    String(String),
    Name(String),
}

impl From<&OptionValue> for StoredValue {
    fn from(value: &OptionValue) -> Self {
        match value {
            OptionValue::Bool(value) => Self::Bool(*value),
            OptionValue::Nat(value) => Self::Nat(*value),
            OptionValue::String(value) => Self::String(value.clone()),
            OptionValue::Name(value) => Self::Name(value.clone()),
        }
    }
}

impl From<StoredValue> for OptionValue {
    fn from(value: StoredValue) -> Self {
        match value {
            StoredValue::Bool(value) => Self::Bool(value),
            StoredValue::Nat(value) => Self::Nat(value),
            StoredValue::String(value) => Self::String(value),
            StoredValue::Name(value) => Self::Name(value),
        }
    }
}

fn ensure_registered(registry: &OptionsRegistry, name: &str) -> Result<(), OptionError> {
    if registry.is_registered(name) {
        Ok(())
    } else {
        Err(OptionError::UnknownOption {
            name: name.to_string(),
        })
    }
}

fn normalize_constraint(
    name: &str,
    decl: &OptionDecl,
    registry: &OptionsRegistry,
    constraint: OptionConstraint,
) -> Result<OptionConstraint, ExtOptionsError> {
    match constraint {
        OptionConstraint::None => Ok(OptionConstraint::None),
        OptionConstraint::NatRange(min, max) => {
            if decl.default().kind_name() != "Nat" {
                Err(ExtOptionsError::ConstraintTypeMismatch {
                    name: name.to_string(),
                    constraint: "NatRange",
                    actual: decl.default().kind_name(),
                })
            } else if min > max {
                Err(ExtOptionsError::InvalidNatRange {
                    name: name.to_string(),
                    min,
                    max,
                })
            } else {
                Ok(OptionConstraint::NatRange(min, max))
            }
        }
        OptionConstraint::StringOneOf(mut allowed) => {
            if decl.default().kind_name() != "String" {
                return Err(ExtOptionsError::ConstraintTypeMismatch {
                    name: name.to_string(),
                    constraint: "StringOneOf",
                    actual: decl.default().kind_name(),
                });
            }
            allowed.sort();
            allowed.dedup();
            if allowed.is_empty() {
                Err(ExtOptionsError::EmptyStringChoices {
                    name: name.to_string(),
                })
            } else {
                Ok(OptionConstraint::StringOneOf(allowed))
            }
        }
        OptionConstraint::DependsOn(dep_name, required_value) => {
            ensure_registered(registry, &dep_name)?;
            registry.validate_option(&dep_name, &required_value)?;
            Ok(OptionConstraint::DependsOn(dep_name, required_value))
        }
    }
}

fn format_constraints(constraints: &[OptionConstraint]) -> String {
    let mut rendered = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        rendered.push(match constraint {
            OptionConstraint::None => "none".to_string(),
            OptionConstraint::NatRange(min, max) => format!("NatRange({min}, {max})"),
            OptionConstraint::StringOneOf(allowed) => {
                format!("StringOneOf({})", allowed.join(", "))
            }
            OptionConstraint::DependsOn(name, value) => format!("DependsOn({name}, {value})"),
        });
    }
    if rendered.is_empty() {
        "none".to_string()
    } else {
        rendered.join("; ")
    }
}

fn escape_markdown_cell(input: &str) -> String {
    input.replace('|', "\\|").replace('\n', "<br>")
}

fn current_timestamp() -> u64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_secs(),
        Err(_) => 0,
    }
}
