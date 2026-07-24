// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strict kernel gate for clean-Native shards.

use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use clean_kernel::{Environment, Expr, ExprVisitor, LevelVec, Name};
use thiserror::Error;

use super::native_gate_helpers::{
    build_declaration, collect_native_shards, decode_decl_kind, is_foundational_axiom_name,
    proof_quality_violation, reconstruct_value, NativeDeclKind, ReconstructedValue,
};
use crate::shard::ShardReader;
use crate::shard_reconstruct::{reconstruct_from_shard_with_level_lists, reconstruct_level_params};
use crate::types::{AxiomProfile, ImportConfidence, SourceSystem};

/// Aggregate result from running the native shard gate.
#[must_use]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct NativeGateReport {
    pub violations: Vec<NativeGateViolation>,
    pub checked: usize,
}

/// Per-declaration gate violation.
#[must_use]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeGateViolation {
    WrongSourceSystem {
        name: String,
        found: u8,
    },
    NonKernelVerifiedProvenance {
        name: String,
        found: u8,
    },
    NonEmptyAxiomProfile {
        name: String,
        found: u64,
    },
    ContainsSorry {
        name: String,
    },
    NonFoundationalAxiom {
        name: String,
    },
    OpaqueDeclaration {
        name: String,
    },
    DefinitionDeclaration {
        name: String,
    },
    AxiomDependent {
        name: String,
        axioms: Vec<String>,
    },
    RejectedDependency {
        name: String,
        dependencies: Vec<String>,
    },
    DuplicateDeclaration {
        name: String,
        index: usize,
    },
    KernelRejected {
        name: String,
        error: String,
    },
    ReconstructFailed {
        name: String,
        error: String,
    },
    MissingValue {
        name: String,
    },
}

impl NativeGateViolation {
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::WrongSourceSystem { name, .. }
            | Self::NonKernelVerifiedProvenance { name, .. }
            | Self::NonEmptyAxiomProfile { name, .. }
            | Self::ContainsSorry { name }
            | Self::NonFoundationalAxiom { name }
            | Self::OpaqueDeclaration { name }
            | Self::DefinitionDeclaration { name }
            | Self::AxiomDependent { name, .. }
            | Self::RejectedDependency { name, .. }
            | Self::DuplicateDeclaration { name, .. }
            | Self::KernelRejected { name, .. }
            | Self::ReconstructFailed { name, .. }
            | Self::MissingValue { name } => name,
        }
    }

    #[must_use]
    pub fn reason(&self) -> String {
        match self {
            Self::WrongSourceSystem { found, .. } => format!(
                "wrong source_system {found}; expected CleanNative ({})",
                SourceSystem::CleanNative as u8
            ),
            Self::NonKernelVerifiedProvenance { found, .. } => format!(
                "non-kernel-verified provenance {found}; expected KernelVerified ({})",
                ImportConfidence::KernelVerified as u8
            ),
            Self::NonEmptyAxiomProfile { found, .. } => {
                format!(
                    "native kernel-verified declaration has non-empty axiom_profile 0x{found:x}"
                )
            }
            Self::ContainsSorry { .. } => "declaration contains sorry/sorryAx".to_string(),
            Self::NonFoundationalAxiom { .. } => {
                "non-foundational axiom in native shard".to_string()
            }
            Self::OpaqueDeclaration { .. } => "opaque declaration in native shard".to_string(),
            Self::DefinitionDeclaration { .. } => {
                "definition declaration in native shard".to_string()
            }
            Self::AxiomDependent { axioms, .. } => {
                format!("depends on non-foundational axioms: {}", axioms.join(", "))
            }
            Self::RejectedDependency { dependencies, .. } => {
                format!(
                    "depends on declaration(s) already rejected by native gate: {}",
                    dependencies.join(", ")
                )
            }
            Self::DuplicateDeclaration { index, .. } => {
                format!("duplicate native declaration name at constant index {index}")
            }
            Self::KernelRejected { error, .. } => format!("kernel rejected declaration: {error}"),
            Self::ReconstructFailed { error, .. } => format!("reconstruction failed: {error}"),
            Self::MissingValue { .. } => "missing value for non-axiom declaration".to_string(),
        }
    }
}

impl fmt::Display for NativeGateViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.reason())
    }
}

/// Errors returned by the native shard gate.
#[derive(Debug, Error)]
pub enum NativeGateError {
    #[error("I/O error reading {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("shard read error: {0}")]
    ShardRead(String),
    #[error("no native shards found in {0}")]
    NoNativeShard(PathBuf),
}

/// Verify a single `clean-native.mathverse` shard.
pub fn verify_native_shard(path: &Path) -> Result<NativeGateReport, NativeGateError> {
    let bytes = fs::read(path).map_err(|source| NativeGateError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    let reader = ShardReader::from_bytes(&bytes)
        .map_err(|error| NativeGateError::ShardRead(error.to_string()))?;
    let mut env = native_replay_environment();
    let mut rejected_names = HashSet::new();
    let mut seen_names = HashSet::new();
    Ok(verify_native_reader(
        &reader,
        &mut env,
        &mut rejected_names,
        &mut seen_names,
    ))
}

/// Verify every `clean-native.mathverse` shard under `dir`.
pub fn verify_native_shard_dir(dir: &Path) -> Result<NativeGateReport, NativeGateError> {
    let mut shard_paths = Vec::new();
    collect_native_shards(dir, &mut shard_paths)?;
    shard_paths.sort();

    if shard_paths.is_empty() {
        return Err(NativeGateError::NoNativeShard(dir.to_path_buf()));
    }

    let mut report = NativeGateReport::default();
    let mut env = native_replay_environment();
    let mut rejected_names = HashSet::new();
    let mut seen_names = HashSet::new();
    for path in shard_paths {
        let bytes = fs::read(&path).map_err(|source| NativeGateError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        let reader = ShardReader::from_bytes(&bytes)
            .map_err(|error| NativeGateError::ShardRead(error.to_string()))?;
        let shard_report =
            verify_native_reader(&reader, &mut env, &mut rejected_names, &mut seen_names);
        report.checked += shard_report.checked;
        report.violations.extend(shard_report.violations);
    }
    Ok(report)
}

fn native_replay_environment() -> Environment {
    // Use `with_prelude()` so foundational types (True, True.intro, Eq, Nat, etc.)
    // referenced by reconstructed declarations resolve. A shard produced by
    // `build-native` over a live kernel with `with_prelude` needs the same baseline
    // to round-trip through `env.add_decl`.
    Environment::with_prelude()
}

fn verify_native_reader(
    reader: &ShardReader,
    env: &mut Environment,
    rejected_names: &mut HashSet<String>,
    seen_names: &mut HashSet<String>,
) -> NativeGateReport {
    let mut report = NativeGateReport {
        checked: reader.constants.len(),
        violations: Vec::new(),
    };

    for (index, header) in reader.constants.iter().enumerate() {
        let decl_violations =
            verify_single_header(reader, header, index, env, rejected_names, seen_names);
        if !decl_violations.is_empty() {
            rejected_names.insert(decl_violations[0].name().to_string());
        }
        report.violations.extend(decl_violations);
    }

    report
}

/// Verify a single constant header and return any violations it produced.
///
/// Returns an empty vec iff the declaration cleanly round-trips through the
/// kernel and is tagged `Constructive`.
fn verify_single_header(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    index: usize,
    env: &mut Environment,
    rejected_names: &HashSet<String>,
    seen_names: &mut HashSet<String>,
) -> Vec<NativeGateViolation> {
    let mut decl_violations = Vec::new();

    let name = match resolve_constant_name(reader, header, index) {
        Ok(name) => name,
        Err(violation) => {
            decl_violations.push(violation);
            return decl_violations;
        }
    };

    if !seen_names.insert(name.clone()) {
        decl_violations.push(NativeGateViolation::DuplicateDeclaration { name, index });
        return decl_violations;
    }

    check_source_system(header, &name, &mut decl_violations);
    check_import_confidence(header, &name, &mut decl_violations);
    check_axiom_profile(header, &name, &mut decl_violations);

    let decl_kind = match decode_decl_kind(header, &name) {
        Ok(kind) => kind,
        Err(violation) => {
            decl_violations.push(violation);
            return decl_violations;
        }
    };

    check_decl_kind_allowed(decl_kind, &name, &mut decl_violations);

    let Some((type_, level_params, value)) =
        reconstruct_decl_parts(reader, header, &name, &mut decl_violations)
    else {
        return decl_violations;
    };

    if type_.has_sorry() {
        decl_violations.push(NativeGateViolation::ContainsSorry { name: name.clone() });
    }

    if value.as_ref().is_some_and(|expr| expr.has_sorry()) {
        decl_violations.push(NativeGateViolation::ContainsSorry { name: name.clone() });
    }

    check_rejected_dependencies(
        &name,
        &type_,
        value.as_ref(),
        rejected_names,
        &mut decl_violations,
    );

    if !decl_violations.is_empty() {
        return decl_violations;
    }

    let kernel_name = Name::from_string(&name);
    let Some(declaration) = build_declaration(
        decl_kind,
        &kernel_name,
        level_params,
        type_,
        value,
        &name,
        &mut decl_violations,
    ) else {
        return decl_violations;
    };

    match env.add_decl(declaration) {
        Ok(()) => {
            if let Some(violation) = proof_quality_violation(env, &kernel_name, &name) {
                decl_violations.push(violation);
            }
        }
        Err(error) => {
            decl_violations.push(NativeGateViolation::KernelRejected {
                name: name.clone(),
                error: error.to_string(),
            });
        }
    }

    decl_violations
}

fn check_rejected_dependencies(
    name: &str,
    type_: &Expr,
    value: Option<&Expr>,
    rejected_names: &HashSet<String>,
    violations: &mut Vec<NativeGateViolation>,
) {
    let mut constants = collect_expr_constants(type_);
    if let Some(value) = value {
        constants.extend(collect_expr_constants(value));
    }

    let mut dependencies = constants
        .into_iter()
        .filter(|constant| rejected_names.contains(constant))
        .collect::<Vec<_>>();
    dependencies.sort();
    dependencies.dedup();

    if !dependencies.is_empty() {
        violations.push(NativeGateViolation::RejectedDependency {
            name: name.to_string(),
            dependencies,
        });
    }
}

fn collect_expr_constants(expr: &Expr) -> HashSet<String> {
    struct ConstCollector;

    impl ExprVisitor for ConstCollector {
        type Result = HashSet<String>;

        fn combine(&self, mut a: Self::Result, b: Self::Result) -> Self::Result {
            a.extend(b);
            a
        }

        fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> Self::Result {
            HashSet::from([name.to_string()])
        }
    }

    ConstCollector.visit_expr(expr)
}

fn resolve_constant_name(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    index: usize,
) -> Result<String, NativeGateViolation> {
    reader
        .strings
        .get(header.name_idx as usize)
        .cloned()
        .ok_or_else(|| NativeGateViolation::ReconstructFailed {
            name: format!("#{index}"),
            error: format!(
                "string index {} out of bounds for shard with {} strings",
                header.name_idx,
                reader.strings.len()
            ),
        })
}

fn check_source_system(
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    violations: &mut Vec<NativeGateViolation>,
) {
    if header.source_system != SourceSystem::CleanNative as u8 {
        violations.push(NativeGateViolation::WrongSourceSystem {
            name: name.to_string(),
            found: header.source_system,
        });
    }
}

fn check_import_confidence(
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    violations: &mut Vec<NativeGateViolation>,
) {
    if header.import_confidence != ImportConfidence::KernelVerified as u8 {
        violations.push(NativeGateViolation::NonKernelVerifiedProvenance {
            name: name.to_string(),
            found: header.import_confidence,
        });
    }
}

fn check_axiom_profile(
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    violations: &mut Vec<NativeGateViolation>,
) {
    if header.axiom_profile != AxiomProfile::NONE {
        violations.push(NativeGateViolation::NonEmptyAxiomProfile {
            name: name.to_string(),
            found: header.axiom_profile.0,
        });
    }
}

fn check_decl_kind_allowed(
    decl_kind: NativeDeclKind,
    name: &str,
    violations: &mut Vec<NativeGateViolation>,
) {
    match decl_kind {
        NativeDeclKind::Axiom => {
            if is_foundational_axiom_name(name) {
                violations.push(NativeGateViolation::KernelRejected {
                    name: name.to_string(),
                    error: "foundational axiom present in native shard".to_string(),
                });
            } else {
                violations.push(NativeGateViolation::NonFoundationalAxiom {
                    name: name.to_string(),
                });
            }
        }
        NativeDeclKind::Definition => {
            violations.push(NativeGateViolation::DefinitionDeclaration {
                name: name.to_string(),
            });
        }
        NativeDeclKind::Opaque => {
            violations.push(NativeGateViolation::OpaqueDeclaration {
                name: name.to_string(),
            });
        }
        NativeDeclKind::Theorem => {}
    }
}

/// Reconstruct `(type, level_params, value)` for a header, or `None` when any
/// reconstruction step fails (the violation is recorded in `violations`).
fn reconstruct_decl_parts(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    violations: &mut Vec<NativeGateViolation>,
) -> Option<(Expr, Vec<Name>, Option<Expr>)> {
    let type_ = match reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        header.type_idx,
    ) {
        Ok(expr) => expr,
        Err(error) => {
            violations.push(NativeGateViolation::ReconstructFailed {
                name: name.to_string(),
                error,
            });
            return None;
        }
    };

    let level_params = match reconstruct_level_params(
        &reader.strings,
        header.level_params_start,
        header.level_params_count,
    ) {
        Ok(params) => params,
        Err(error) => {
            violations.push(NativeGateViolation::ReconstructFailed {
                name: name.to_string(),
                error,
            });
            return None;
        }
    };

    let value = match reconstruct_value(reader, header, name, violations) {
        ReconstructedValue::Present(expr) => Some(expr),
        ReconstructedValue::Missing => None,
        ReconstructedValue::Failed => return None,
    };

    Some((type_, level_params, value))
}
