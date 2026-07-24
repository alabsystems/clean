// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Internal helpers for the native shard gate: declaration building,
//! proof-quality mapping, reconstruction, decl-kind decoding, shard discovery,
//! and the foundational-axiom allowlist.
//!
//! Split out of `native_gate.rs` to keep each file under the project-wide
//! 500-line cap. Only `pub(super)` symbols are visible to `native_gate`.

use std::fs;
use std::path::{Path, PathBuf};

use clean_kernel::{is_foundational_axiom, Declaration, Environment, Name, ProofQuality};

use super::native_gate::{NativeGateError, NativeGateViolation};
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;
use crate::types::{DeclKind, NO_VALUE};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NativeDeclKind {
    Theorem,
    Axiom,
    Definition,
    Opaque,
}

pub(super) enum ReconstructedValue {
    Present(clean_kernel::Expr),
    Missing,
    Failed,
}

pub(super) fn build_declaration(
    decl_kind: NativeDeclKind,
    kernel_name: &Name,
    level_params: Vec<Name>,
    type_: clean_kernel::Expr,
    value: Option<clean_kernel::Expr>,
    report_name: &str,
    violations: &mut Vec<NativeGateViolation>,
) -> Option<Declaration> {
    match decl_kind {
        NativeDeclKind::Axiom => Some(Declaration::Axiom {
            name: kernel_name.clone(),
            level_params,
            type_,
        }),
        NativeDeclKind::Theorem => value.map(|value| Declaration::Theorem {
            name: kernel_name.clone(),
            level_params,
            type_,
            value,
        }),
        NativeDeclKind::Definition => value.map(|value| Declaration::Definition {
            name: kernel_name.clone(),
            level_params,
            type_,
            value,
            is_reducible: false,
        }),
        NativeDeclKind::Opaque => value.map(|value| Declaration::Opaque {
            name: kernel_name.clone(),
            level_params,
            type_,
            value,
        }),
    }
    .or_else(|| {
        if !matches!(decl_kind, NativeDeclKind::Axiom) {
            violations.push(NativeGateViolation::MissingValue {
                name: report_name.to_string(),
            });
        }
        None
    })
}

pub(super) fn proof_quality_violation(
    env: &Environment,
    name: &Name,
    report_name: &str,
) -> Option<NativeGateViolation> {
    match env.proof_quality(name) {
        Some(ProofQuality::Constructive) => None,
        Some(ProofQuality::AxiomDependent { axioms, .. }) => {
            let axioms = axioms.into_iter().map(|axiom| axiom.to_string()).collect();
            Some(NativeGateViolation::AxiomDependent {
                name: report_name.to_string(),
                axioms,
            })
        }
        Some(ProofQuality::NotATheorem) => None,
        Some(ProofQuality::Unchecked) => Some(NativeGateViolation::KernelRejected {
            name: report_name.to_string(),
            error: "declaration remained unchecked after add_decl".to_string(),
        }),
        None => Some(NativeGateViolation::KernelRejected {
            name: report_name.to_string(),
            error: "declaration missing from environment after add_decl".to_string(),
        }),
        _ => Some(NativeGateViolation::KernelRejected {
            name: report_name.to_string(),
            error: "unexpected proof quality classification".to_string(),
        }),
    }
}

pub(super) fn reconstruct_value(
    reader: &ShardReader,
    header: &crate::types::MathverseConstantHeader,
    name: &str,
    violations: &mut Vec<NativeGateViolation>,
) -> ReconstructedValue {
    if header.value_idx == NO_VALUE {
        return ReconstructedValue::Missing;
    }

    match reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        header.value_idx,
    ) {
        Ok(expr) => ReconstructedValue::Present(expr),
        Err(error) => {
            violations.push(NativeGateViolation::ReconstructFailed {
                name: name.to_string(),
                error,
            });
            ReconstructedValue::Failed
        }
    }
}

pub(super) fn decode_decl_kind(
    header: &crate::types::MathverseConstantHeader,
    name: &str,
) -> Result<NativeDeclKind, NativeGateViolation> {
    match header.decl_kind() {
        Ok(DeclKind::Theorem) => Ok(NativeDeclKind::Theorem),
        Ok(DeclKind::Axiom) => Ok(NativeDeclKind::Axiom),
        Ok(DeclKind::Definition) => Ok(NativeDeclKind::Definition),
        Ok(DeclKind::Opaque) => Ok(NativeDeclKind::Opaque),
        Ok(other) => Err(NativeGateViolation::ReconstructFailed {
            name: name.to_string(),
            error: format!("unsupported declaration kind {other:?}"),
        }),
        Err(raw) => Err(NativeGateViolation::ReconstructFailed {
            name: name.to_string(),
            error: format!("unknown declaration kind {raw}"),
        }),
    }
}

pub(super) fn collect_native_shards(
    dir: &Path,
    out: &mut Vec<PathBuf>,
) -> Result<(), NativeGateError> {
    let entries = fs::read_dir(dir).map_err(|source| NativeGateError::Io {
        path: dir.to_path_buf(),
        source,
    })?;

    for entry in entries {
        let entry = entry.map_err(|source| NativeGateError::Io {
            path: dir.to_path_buf(),
            source,
        })?;
        let path = entry.path();
        if path.is_dir() {
            collect_native_shards(&path, out)?;
        } else if path
            .file_name()
            .is_some_and(|file_name| file_name == "clean-native.mathverse")
        {
            out.push(path);
        }
    }

    Ok(())
}

/// Classify `name` as a Lean 4 foundational axiom.
///
/// Delegates to `clean_kernel::is_foundational_axiom` as the single source of
/// truth for the foundational whitelist (#3561). Prior to consolidation this
/// module carried its own hard-coded `matches!(...)` copy which drifted from
/// the canonical `axiom_audit::FOUNDATIONAL_AXIOMS` list — missing Rat
/// min/max, Fin.castSucc/Fin.last, the Rat ring / field axiom batches
/// (#3551/#3555), `Nat.le_refl`, and still contained `sorryAx` / `Eq.symm` /
/// `Eq.trans` / `Eq.subst` after #3554/#3559 removed them from the canonical
/// list. The single-source-of-truth invariant is pinned by
/// `test_native_gate_foundational_axioms_delegates_to_canonical` in
/// `shard_verify::tests`.
pub(super) fn is_foundational_axiom_name(name: &str) -> bool {
    is_foundational_axiom(&Name::from_string(name))
}
