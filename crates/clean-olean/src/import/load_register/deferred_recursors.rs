// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Artifact-local staging. A queued record grants no executable authority.

use super::*;
use crate::import::artifact_ledger::{self, ArtifactKey, PartRecord};
use crate::import::{DeferredRecursor, DeferredRecursorStatus};
use clean_kernel::env::DeclarationVerification;

pub(crate) struct DeferredRecursors {
    artifact: ArtifactKey,
    private_only: HashSet<Name>,
    pending: Vec<(usize, usize, PartRecord)>,
}

pub(super) struct RecursorStaging<'a> {
    pub queue: &'a mut DeferredRecursors,
    pub summary_ordinal: usize,
    pub records: &'a HashMap<Name, (usize, PartRecord)>,
}

impl DeferredRecursors {
    /// Called only after read_plan validates every part of a complete module
    /// artifact. The allow-set contains exact typed PRIVATE-ONLY declarations,
    /// not spelling rules or caller-supplied safety/elimination flags.
    pub(crate) fn new(module: &str, private_only: HashSet<Name>) -> Self {
        Self {
            artifact: Some(module.to_owned()),
            private_only,
            pending: Vec::new(),
        }
    }

    pub(super) fn stage(
        &mut self,
        env: &Environment,
        summary_ordinal: usize,
        summary: &mut LoadSummary,
        source_ordinal: usize,
        record: &PartRecord,
        error: &clean_kernel::env::EnvError,
    ) -> bool {
        let PartRecord::Recursor(rec, _, _, _) = record else {
            return false;
        };
        let Some(ind) = env.get_inductive(&rec.inductive_name) else {
            return false;
        };
        if !artifact_ledger::declared_by_this_artifact(env, &rec.inductive_name, &self.artifact)
            || ind
                .all_names
                .iter()
                .any(|name| !artifact_ledger::declared_by_this_artifact(env, name, &self.artifact))
        {
            return false;
        }
        let missing = artifact_ledger::missing_family_type_dependencies(env, &rec.inductive_name);
        if missing.is_empty() || missing.iter().any(|name| !self.private_only.contains(name)) {
            return false;
        }
        let row = summary.deferred_recursors.len();
        summary.deferred_recursors.push(DeferredRecursor {
            name: rec.name.clone(),
            source_constant_ordinal: source_ordinal,
            missing_dependencies: missing,
            initial_refusal: format!("structural validation failed: {error}"),
            status: DeferredRecursorStatus::Pending,
        });
        // One entry per original converted record. No synthetic or repeated
        // retry work is appended; the input's record count bounds this queue.
        self.pending.push((summary_ordinal, row, record.clone()));
        true
    }

    pub(crate) fn finish(
        self,
        env: &Environment,
        summaries: &mut [LoadSummary],
    ) -> Result<(), ImportError> {
        let mut first = None;
        for (summary_ordinal, row_ordinal, record) in self.pending {
            let summary = &mut summaries[summary_ordinal];
            let row = &mut summary.deferred_recursors[row_ordinal];
            let checked = matches!(
                env.declaration_verification(&row.name),
                Some(
                    DeclarationVerification::StructuralOnly
                        | DeclarationVerification::FullKernelCheck
                )
            );
            let resolved = checked
                && env.get_recursor(&row.name).is_some()
                && artifact_ledger::declared_by_this_artifact(env, &row.name, &self.artifact)
                && row.missing_dependencies.iter().all(|name| {
                    artifact_ledger::declared_by_this_artifact(env, name, &self.artifact)
                })
                && artifact_ledger::agrees_with_environment(env, &record);
            if resolved {
                row.status = DeferredRecursorStatus::Resolved;
            } else {
                let reason = format!("no exact same-artifact, strictly admitted authoritative recursor with all private dependencies resident; early check: {}", row.initial_refusal);
                row.status = DeferredRecursorStatus::Refused(reason.clone());
                if first.is_none() {
                    first = Some(ImportError::DeferredRecursorRefused {
                        module: self.artifact.as_deref().unwrap_or("<unnamed>").to_owned(),
                        part: summary
                            .module_name
                            .as_deref()
                            .unwrap_or("<unnamed>")
                            .to_owned(),
                        ordinal: row.source_constant_ordinal,
                        name: row.name.to_string(),
                        reason,
                    });
                }
            }
        }
        first.map_or(Ok(()), Err)
    }
}

/// Revisit ONLY this artifact's resident families, after its own definitions
/// are available. The kernel ignores anything not StructuralOnly and applies
/// its unchanged field-sort criterion; unknown inference stays restrictive.
pub(crate) fn refresh_artifact_families(
    env: &mut Environment,
    artifact: &ArtifactKey,
    names: impl Iterator<Item = Name>,
) {
    let targets: Vec<_> = names
        .filter_map(|name| {
            if !artifact_ledger::declared_by_this_artifact(env, &name, artifact) {
                return None;
            }
            let ind = env.get_inductive(&name)?;
            let ctors = ind
                .constructor_names
                .iter()
                .map(|name| {
                    let ctor = env.get_constructor(name)?;
                    Some(Constructor {
                        name: ctor.name.clone(),
                        type_: ctor.type_.clone(),
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            Some((name, ctors))
        })
        .collect();
    env.recompute_imported_large_elim(targets);
}
