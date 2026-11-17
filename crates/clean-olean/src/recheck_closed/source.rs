// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual fresh replay bound to immutable original source records. This is
//! logical evidence over an explicit consumer base, not frontend custody or a
//! native capability. Original runtime metadata is never regenerated here.

use super::{ImportedConeGate, ImportedConeVerdict};
use clean_kernel::{ConstantInfo, DeclarationVerification, Environment, Name};
use std::collections::BTreeSet;
use std::sync::Arc;

#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReplayedSourceError {
    #[error("source replay requires a root")]
    EmptyRoots,
    #[error("source replay refused: {0}")]
    Replay(String, Box<ImportedConeVerdict>),
    #[error("{0:?} is outside the actual source replay")]
    Outside(Name),
    #[error("source replay belongs to a different original source snapshot")]
    ForeignSource,
    #[error("source replay belongs to a different consumer base/configuration/world")]
    ForeignBase,
    #[error("source replay roots differ from the requested context")]
    DifferentRoots,
    #[error("original source record or metadata differs at {0:?}")]
    SourceChanged(Name),
    #[error("actual replay did not fully kernel-admit {0:?}")]
    NotKernelChecked(Name),
}

/// A fresh actual kernel replay and its exact original source snapshot. No
/// constructor accepts favorable hashes, a verdict or a "checked" Boolean.
/// `base` has the same explicit consumer trust meaning as ImportedConeGate.
/// This object grants neither source ownership nor native selection rights.
#[derive(Debug, Clone)]
pub struct ReplayedImportedSource {
    original: Arc<Environment>,
    base: Arc<Environment>,
    roots: BTreeSet<Name>,
    gate: ImportedConeGate,
    members: BTreeSet<Name>,
    verdict: ImportedConeVerdict,
}

impl ReplayedImportedSource {
    pub fn check(
        base: Arc<Environment>,
        source: Arc<Environment>,
        roots: BTreeSet<Name>,
    ) -> Result<Self, ReplayedSourceError> {
        if roots.is_empty() {
            return Err(ReplayedSourceError::EmptyRoots);
        }
        let original = source;
        // Never reuse an earlier admitted-name cache as original-record
        // authority: this check runs on a fresh gate and frozen source copy.
        let mut gate = ImportedConeGate::new(&base);
        let verdict = gate.check(&original, &roots);
        if !verdict.passed(false) {
            return Err(ReplayedSourceError::Replay(
                verdict.refusal_summary(false),
                Box::new(verdict),
            ));
        }
        let mut members: BTreeSet<_> = gate.admitted_names().cloned().collect();
        for root in &roots {
            members.extend(
                original
                    .dependency_closure(root)
                    .map_err(|_| ReplayedSourceError::Outside(root.clone()))?,
            );
        }
        Ok(Self {
            original,
            base,
            roots,
            gate,
            members,
            verdict,
        })
    }

    /// Require the exact immutable source/base identities and exact root set.
    /// Equal rows from another source or another consumer base grant nothing.
    pub fn require_context(
        &self,
        base: &Arc<Environment>,
        source: &Arc<Environment>,
        roots: &BTreeSet<Name>,
    ) -> Result<(), ReplayedSourceError> {
        if !Arc::ptr_eq(&self.base, base) {
            return Err(ReplayedSourceError::ForeignBase);
        }
        if !Arc::ptr_eq(&self.original, source) {
            return Err(ReplayedSourceError::ForeignSource);
        }
        if self.roots != *roots {
            return Err(ReplayedSourceError::DifferentRoots);
        }
        Ok(())
    }
    pub fn roots(&self) -> &BTreeSet<Name> {
        &self.roots
    }
    pub fn verdict(&self) -> &ImportedConeVerdict {
        &self.verdict
    }
    pub fn members(&self) -> &BTreeSet<Name> {
        &self.members
    }
    /// Actual original data, including its original imported provenance.
    pub fn original_environment(&self) -> &Environment {
        &self.original
    }
    /// Actual kernel-generated records are available for logical provenance;
    /// they must not replace original records in a runtime layout comparison.
    pub fn checked_environment(&self) -> &Environment {
        self.gate.environment()
    }

    /// Match actual compiler input to the immutable original, preserving every
    /// original role, source flag, provenance and represented runtime attribute.
    pub fn require_record(
        &self,
        current: &Environment,
        name: &Name,
    ) -> Result<(), ReplayedSourceError> {
        if !self.members.contains(name) {
            return Err(ReplayedSourceError::Outside(name.clone()));
        }
        if !same_original_record(&self.original, current, name) {
            return Err(ReplayedSourceError::SourceChanged(name.clone()));
        }
        Ok(())
    }

    /// Require actual source-record evidence: fresh admission, or the same
    /// fully checked logical declaration and family already held by the base.
    /// A type-only base-stub upgrade does not check an original definition value.
    /// Original records remain immutable in their separate source snapshot.
    pub fn checked_constant<'a>(
        &'a self,
        name: &Name,
    ) -> Result<&'a ConstantInfo, ReplayedSourceError> {
        if !self.members.contains(name) {
            return Err(ReplayedSourceError::Outside(name.clone()));
        }
        let checked = self.checked_environment();
        if !self.gate.has_source_record_evidence(&self.original, name)
            || checked.declaration_verification(name)
                != Some(DeclarationVerification::FullKernelCheck)
            || checked.constant_needs_recheck(name)
            || checked.is_staged_header(name)
        {
            return Err(ReplayedSourceError::NotKernelChecked(name.clone()));
        }
        checked
            .get_const(name)
            .ok_or_else(|| ReplayedSourceError::NotKernelChecked(name.clone()))
    }
}

fn same_original_record(a: &Environment, b: &Environment, name: &Name) -> bool {
    let fields = a.get_structure_field_names(name);
    a.get_const(name) == b.get_const(name)
        && a.get_inductive(name) == b.get_inductive(name)
        && a.get_constructor(name) == b.get_constructor(name)
        && a.get_recursor(name) == b.get_recursor(name)
        && a.get_quot(name) == b.get_quot(name)
        && fields == b.get_structure_field_names(name)
        && fields.unwrap_or_default().iter().all(|field| {
            a.get_structure_field_default(name, field) == b.get_structure_field_default(name, field)
        })
        && a.get_structure_parents(name) == b.get_structure_parents(name)
        && a.get_implemented_by(name) == b.get_implemented_by(name)
        && a.get_extern(name) == b.get_extern(name)
        && a.get_matcher_info(name) == b.get_matcher_info(name)
        && a.is_unsafe(name) == b.is_unsafe(name)
        && a.is_partial(name) == b.is_partial(name)
        && a.is_noncomputable(name) == b.is_noncomputable(name)
        && a.is_staged_header(name) == b.is_staged_header(name)
        && a.get_constant_origin(name) == b.get_constant_origin(name)
        && a.declaration_verification(name) == b.declaration_verification(name)
        && clean_kernel::env::csimp::rules_for(a, Some(name))
            == clean_kernel::env::csimp::rules_for(b, Some(name))
}
#[cfg(test)]
mod tests;
