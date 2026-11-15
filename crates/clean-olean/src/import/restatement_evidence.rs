// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Private identity observations, sealed only after a whole artifact completes.
//! They never certify an incoming duplicate proof body. Replay must admit the
//! canonical resident theorem, including its proposition header and value.

use super::artifact_ledger::{self, ArtifactCompletion, PartRecord};
use super::load_parse::LoadModule;
use super::LoadSummary;
use crate::{ConstantKind, DefinitionSafety};
use clean_kernel::env::{ConstantInfo, ConstantKind as KernelKind, Environment};
use clean_kernel::name::Name;
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub(crate) struct CompletedCanonicalTheorem {
    artifact: String,
    info: ConstantInfo,
}

impl CompletedCanonicalTheorem {
    pub(crate) fn name(&self) -> &Name {
        &self.info.name
    }
    pub(crate) fn artifact(&self) -> &str {
        &self.artifact
    }
    fn current(&self, env: &Environment) -> bool {
        artifact_ledger::declaring_artifact(env, &self.info.name)
            == Some(Some(self.artifact.clone()))
            && !env.is_unsafe(&self.info.name)
            && env
                .get_const(&self.info.name)
                .is_some_and(|c| c.kind == KernelKind::Theorem && c.value.is_some())
            && artifact_ledger::agrees_with_environment(
                env,
                &PartRecord::Constant {
                    info: self.info.clone(),
                    safety: Some(DefinitionSafety::Safe),
                },
            )
    }
    fn same(&self, other: &Self) -> bool {
        self.artifact == other.artifact
            && self.info.name == other.info.name
            && self.info.kind == other.info.kind
            && self.info.level_params == other.info.level_params
            && self.info.type_ == other.info.type_
            && self.info.value == other.info.value
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PendingRestatement {
    canonical: CompletedCanonicalTheorem,
    incoming_theorem: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct TheoremRestatementCertificate {
    authoritative_part: String,
    canonical: CompletedCanonicalTheorem,
    incoming_theorem: bool,
}

impl TheoremRestatementCertificate {
    pub(crate) fn authoritative_part(&self) -> &str {
        &self.authoritative_part
    }
    pub(crate) fn name(&self) -> &Name {
        self.canonical.name()
    }
    pub(crate) fn canonical_artifact(&self) -> &str {
        self.canonical.artifact()
    }
    pub(crate) fn incoming_theorem(&self) -> bool {
        self.incoming_theorem
    }
    pub(crate) fn matches(&self, env: &Environment, canonical: &CompletedCanonicalTheorem) -> bool {
        self.canonical.same(canonical) && canonical.current(env)
    }
}

/// Called only after the maintained duplicate converter matched the incoming
/// theorem/axiom's universe parameters and type to the resident declaration.
/// This observation is deliberately not a completion certificate.
pub(super) fn matched(
    env: &Environment,
    name: &Name,
    incoming_theorem: bool,
) -> Option<PendingRestatement> {
    let artifact = artifact_ledger::declaring_artifact(env, name)??;
    let info = env.get_const(name)?;
    if info.kind != KernelKind::Theorem || info.value.is_none() || env.is_unsafe(name) {
        return None;
    }
    Some(PendingRestatement {
        canonical: CompletedCanonicalTheorem {
            artifact,
            info: info.clone(),
        },
        incoming_theorem,
    })
}

/// Seal observations using the actual successful ledger transition and the raw
/// authoritative part selected by the maintained whole-artifact reader. The
/// index is in this load's part summaries, not inferred from a label suffix.
pub(super) fn complete(
    env: &Environment,
    completion: Option<ArtifactCompletion>,
    authoritative: Option<(&LoadModule, usize)>,
    summaries: &mut [LoadSummary],
) {
    let (Some(receipt), Some((raw, authoritative_index))) = (completion, authoritative) else {
        return;
    };
    let Some(artifact) = receipt.artifact().as_ref() else {
        return;
    };
    let Some(final_part) = summaries
        .get(authoritative_index)
        .and_then(|s| s.stored_declarations.as_ref())
    else {
        return;
    };
    if final_part.artifact.as_ref() != Some(artifact) {
        return;
    }
    let Some(authoritative_part) = final_part.part.clone() else {
        return;
    };
    let final_theorems: BTreeSet<Name> = raw
        .constants
        .iter()
        .filter(|c| c.kind == ConstantKind::Theorem && c.value_ptr != 0)
        .map(|c| c.kernel_name.clone())
        .collect();
    let completed: Vec<_> = receipt
        .theorems()
        .iter()
        .filter(|info| final_theorems.contains(&info.name))
        .map(|info| CompletedCanonicalTheorem {
            artifact: artifact.clone(),
            info: info.clone(),
        })
        .filter(|record| record.current(env))
        .collect();
    let final_matches: Vec<_> = final_part
        .pending_restatements
        .iter()
        .filter(|pending| {
            pending.incoming_theorem && final_theorems.contains(pending.canonical.name())
        })
        .cloned()
        .collect();
    let mut certificates = Vec::new();
    for final_match in final_matches {
        let name = final_match.canonical.name();
        let mut occurrences = Vec::new();
        let mut parts = BTreeSet::new();
        let mut valid = final_match.canonical.current(env);
        for (index, summary) in summaries.iter().enumerate() {
            let Some(part) = summary.stored_declarations.as_ref() else {
                valid = false;
                continue;
            };
            if part.artifact.as_ref() != Some(artifact) {
                valid = false;
                continue;
            }
            let originals: Vec<_> = part
                .declarations
                .iter()
                .filter(|(key, _)| key == name)
                .collect();
            if originals.is_empty() {
                continue;
            }
            let pending: Vec<_> = part
                .pending_restatements
                .iter()
                .filter(|p| p.canonical.name() == name)
                .collect();
            if originals.len() != 1
                || originals[0].1 != Some(DefinitionSafety::Safe)
                || !parts.insert(part.part.clone())
                || part.part.is_none()
                || pending.len() != 1
            {
                valid = false;
                continue;
            }
            let pending = pending[0];
            if !pending.canonical.same(&final_match.canonical)
                || (!pending.incoming_theorem
                    && (!receipt.module_system() || index == authoritative_index))
            {
                valid = false;
                continue;
            }
            occurrences.push((
                index,
                TheoremRestatementCertificate {
                    authoritative_part: authoritative_part.clone(),
                    canonical: pending.canonical.clone(),
                    incoming_theorem: pending.incoming_theorem,
                },
            ));
        }
        if valid {
            certificates.extend(occurrences);
        }
    }
    if let Some(part) = summaries
        .get_mut(authoritative_index)
        .and_then(|s| s.stored_declarations.as_mut())
    {
        part.completed_theorems = completed;
    }
    for (index, certificate) in certificates {
        if let Some(part) = summaries
            .get_mut(index)
            .and_then(|s| s.stored_declarations.as_mut())
        {
            part.certified_restatements.push(certificate);
        }
    }
}
