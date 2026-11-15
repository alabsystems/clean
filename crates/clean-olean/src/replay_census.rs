// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Artifact-backed, full-roster replay accounting. A runtime declaration's
//! explicit refusal is not kernel admission or proof authority. All names,
//! including these refused declarations, remain in the same dependency graph.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::Environment;

use crate::import::LoadSummary;
use crate::replay_order::ReplayRefusal;
use crate::verify_batch_full::{typecheck_constants_full_ordered, ReplayScope};
use crate::DefinitionSafety;

/// One original declaration's outcome. Only `Admitted` supplies admission.
#[derive(Debug, Clone)]
pub enum DeclarationReplayVerdict {
    /// The canonical resident name is safe and the kernel replay admitted it.
    /// Certified duplicate theorem bodies are not replayed; see `restatements`.
    Admitted,
    /// The artifact explicitly marks this runtime declaration unsafe/partial;
    /// replay refused it for exactly that reason. It supplies no authority.
    NotReplayable {
        /// The artifact's original safety, not the environment's stub marks.
        safety: DefinitionSafety,
        /// The actual, typed refusal from the unchanged replay graph.
        refusal: ReplayRefusal,
    },
    /// A fatal declaration-level failure, including incomplete loader state.
    Failed(CensusFailure),
}

/// Why a declaration cannot satisfy the artifact-backed replay contract.
#[derive(Debug, Clone)]
pub enum CensusFailure {
    /// The unchanged replay engine refused the declaration.
    Replay(ReplayRefusal),
    /// The loader did not register the original declaration completely.
    Loader(String),
    /// No original artifact record backs this requested declaration.
    MissingStoredDeclaration,
    /// Original stored safety could not be established.
    UnknownStoredSafety,
    /// No scheduled verdict exists for this declaration.
    MissingReplayVerdict,
    /// A declaration registry has inconsistent typed rows.
    RegistryAccounting,
    /// A stored runtime declaration unexpectedly received admission.
    RuntimeAdmitted,
}

/// A structural failure of the complete census, never an accepted runtime row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CensusAccountingError {
    /// No artifact population was selected; this is not a full corpus census.
    EmptyModuleSet,
    /// A requested module has no original artifact-backed load evidence.
    MissingModule(String),
    /// A stored declaration is absent from the caller's full roster.
    MissingTarget(String),
    /// A requested declaration is absent from the original stored roster.
    ExtraTarget(String),
    /// A name is repeated in one part or has uncertified different owners.
    DuplicateDeclaration(String),
    /// The replay's aggregate and per-name accounting disagree.
    ReplayAccounting,
}

/// One certified identity occurrence, never an admission of its incoming body.
#[derive(Debug, Clone)]
pub struct TheoremRestatementOccurrence {
    /// Unique logical name, counted once in the census.
    pub name: String,
    /// Artifact and exact part that restated the canonical theorem.
    pub artifact: String,
    /// Loader-bound part identity, not inferred from its suffix.
    pub part: String,
    /// Actual completed authoritative part, which must remain in this census.
    pub authoritative_part: String,
    /// Artifact whose resident proof must actually replay in this same graph.
    pub canonical_artifact: String,
    /// False for an exported value-free part completed by its private theorem.
    pub incoming_theorem: bool,
    /// Actual canonical-name admission; never incoming-body validation.
    pub canonical_admitted: bool,
}

/// Complete results, with the original denominator and every per-name verdict.
#[derive(Debug)]
pub struct DeclarationReplayCensus {
    verdicts: BTreeMap<String, DeclarationReplayVerdict>,
    accounting: Vec<CensusAccountingError>,
    restatements: Vec<TheoremRestatementOccurrence>,
}

impl DeclarationReplayCensus {
    /// Loader-certified occurrences and the actual canonical-name verdict.
    /// No incoming restatement proof body receives an additional admission.
    pub fn restatements(&self) -> &[TheoremRestatementOccurrence] {
        &self.restatements
    }

    /// All names in the original/requested union, including fatal missing rows.
    pub fn seen(&self) -> usize {
        self.verdicts.len()
    }
    /// Actual safe kernel admissions only.
    pub fn admitted(&self) -> usize {
        self.verdicts
            .values()
            .filter(|v| matches!(v, DeclarationReplayVerdict::Admitted))
            .count()
    }
    /// Explicit runtime refusals, never kernel admissions or proof authority.
    pub fn not_replayable(&self) -> usize {
        self.verdicts
            .values()
            .filter(|v| matches!(v, DeclarationReplayVerdict::NotReplayable { .. }))
            .count()
    }
    /// Fatal per-name outcomes; `seen = admitted + not_replayable + failed_declarations`.
    pub fn failed_declarations(&self) -> usize {
        self.verdicts
            .values()
            .filter(|v| matches!(v, DeclarationReplayVerdict::Failed(_)))
            .count()
    }
    /// Fatal declaration outcomes plus structural census errors.
    pub fn failures(&self) -> usize {
        self.failed_declarations() + self.accounting.len()
    }
    /// Every name has its required outcome and no accounting error occurred.
    /// This does not mean the runtime declarations were admitted.
    pub fn is_complete(&self) -> bool {
        self.failures() == 0
    }
    /// Full typed outcomes, retaining refused runtime rows.
    pub fn verdicts(&self) -> &BTreeMap<String, DeclarationReplayVerdict> {
        &self.verdicts
    }
    /// Fatal full-roster accounting problems.
    pub fn accounting_errors(&self) -> &[CensusAccountingError] {
        &self.accounting
    }
}

/// Replay a FULL artifact-backed module roster in the existing ordered engine.
///
/// `modules` are original artifact labels, not a safety/name allowlist. Original
/// safety comes from records captured by the loader before conversion. A safe
/// declaration left as an unsafe loader stub is therefore a failure. Every
/// original and requested name stays in the same replay graph, so a safe user
/// of an unsafe/partial declaration is refused normally. The trusted imports
/// outside this module set retain the existing local replay scope.
///
/// This is a full-census API, not a spot-check API. Missing/extra targets,
/// duplicate declarations, absent metadata and incomplete loads are fatal.
pub fn replay_declaration_census(
    env: &Environment,
    summaries: &[LoadSummary],
    modules: &BTreeSet<String>,
    targets: &BTreeSet<String>,
    max_heartbeats: u32,
) -> DeclarationReplayCensus {
    let mut accounting = Vec::new();
    if modules.is_empty() {
        accounting.push(CensusAccountingError::EmptyModuleSet);
    }
    let mut found_modules = BTreeSet::new();
    let mut original = BTreeMap::new();
    let mut owners = BTreeMap::new();
    let mut part_names = BTreeSet::new();
    let mut loader_failures = BTreeMap::new();
    let mut invalid_metadata = BTreeSet::new();
    let mut already_declared = BTreeMap::new();
    let mut restatements = Vec::new();
    let mut completed = BTreeMap::new();
    for part in summaries
        .iter()
        .filter_map(|summary| summary.stored_declarations.as_ref())
    {
        let Some(artifact) = part
            .artifact
            .as_ref()
            .filter(|artifact| modules.contains(*artifact))
        else {
            continue;
        };
        for record in &part.completed_theorems {
            if record.artifact() != artifact
                || completed
                    .insert((artifact.clone(), record.name().clone()), record)
                    .is_some()
            {
                invalid_metadata.insert(record.name().to_string());
            }
        }
    }
    for summary in summaries {
        let Some(part) = &summary.stored_declarations else {
            continue;
        };
        let Some(artifact) = &part.artifact else {
            continue;
        };
        if !modules.contains(artifact) {
            continue;
        }
        found_modules.insert(artifact.clone());
        let mut certified = BTreeSet::new();
        for certificate in &part.certified_restatements {
            let name = certificate.name();
            let label = name.to_string();
            let canonical = certificate.canonical_artifact();
            let occurrence_count = part
                .declarations
                .iter()
                .filter(|(key, safety)| key == name && *safety == Some(DefinitionSafety::Safe))
                .count();
            let tuple_count = summary
                .restated_declarations
                .iter()
                .filter(|(key, _, theorem)| {
                    key == name && *theorem == certificate.incoming_theorem()
                })
                .count();
            let certificate_count = part
                .certified_restatements
                .iter()
                .filter(|other| other.name() == name)
                .count();
            let valid = occurrence_count == 1
                && tuple_count == 1
                && certificate_count == 1
                && summary
                    .restated_declarations
                    .iter()
                    .filter(|(key, _, _)| key == name)
                    .count()
                    == 1
                && part.part.is_some()
                && modules.contains(canonical)
                && summaries
                    .iter()
                    .filter_map(|row| row.stored_declarations.as_ref())
                    .any(|final_part| {
                        final_part.artifact.as_ref() == Some(artifact)
                            && final_part.part.as_deref() == Some(certificate.authoritative_part())
                            && final_part
                                .declarations
                                .iter()
                                .filter(|(key, safety)| {
                                    key == name && *safety == Some(DefinitionSafety::Safe)
                                })
                                .count()
                                == 1
                            && final_part
                                .certified_restatements
                                .iter()
                                .any(|final_certificate| {
                                    final_certificate.name() == name
                                        && final_certificate.incoming_theorem()
                                        && final_certificate.canonical_artifact() == canonical
                                        && final_certificate.authoritative_part()
                                            == certificate.authoritative_part()
                                })
                    })
                && owners.get(&label) == Some(&(canonical.to_owned(), name.clone()))
                && original.get(&label) == Some(&Some(DefinitionSafety::Safe))
                && completed
                    .get(&(canonical.to_owned(), name.clone()))
                    .is_some_and(|record| certificate.matches(env, record));
            if valid {
                certified.insert(name.clone());
                restatements.push(TheoremRestatementOccurrence {
                    name: label,
                    artifact: artifact.clone(),
                    part: part.part.clone().unwrap_or_default(),
                    canonical_artifact: canonical.to_owned(),
                    authoritative_part: certificate.authoritative_part().to_owned(),
                    incoming_theorem: certificate.incoming_theorem(),
                    canonical_admitted: false,
                });
            }
        }
        for (name, safety) in &part.declarations {
            let label = name.to_string();
            let repeated_part =
                !part_names.insert((artifact.clone(), part.part.clone(), name.clone()));
            let foreign = owners
                .get(&label)
                .is_some_and(|owner| owner != &(artifact.clone(), name.clone()));
            if repeated_part || (foreign && !certified.contains(name)) {
                invalid_metadata.insert(label.clone());
                accounting.push(CensusAccountingError::DuplicateDeclaration(label.clone()));
            }
            // A lateral restatement never replaces the first canonical owner,
            // its original safety, or its proof. Only that artifact's parts can
            // complete its original record under the existing loader ledger.
            if !foreign {
                owners
                    .entry(label.clone())
                    .or_insert_with(|| (artifact.clone(), name.clone()));
                if completed.contains_key(&(artifact.clone(), name.clone())) {
                    if *safety != Some(DefinitionSafety::Safe) {
                        invalid_metadata.insert(label.clone());
                    }
                    original.insert(label, Some(DefinitionSafety::Safe));
                } else {
                    original.insert(label, *safety);
                }
            }
        }
        // Public added-name diagnostics cannot erase a loader refusal from
        // this or another artifact. Valid restatements are reconciled only by
        // their private completed-family evidence above, never by a later name.

        for skipped in &summary.skipped_constants {
            loader_failures.insert(skipped.name.clone(), skipped.reason.clone());
        }
        for (name, reason) in &summary.refused_completions {
            loader_failures.insert(name.to_string(), reason.clone());
        }
        for (name, reason) in &summary.shadowed_declarations {
            already_declared.insert(name.to_string(), reason.clone());
            loader_failures.insert(name.to_string(), reason.clone());
        }
        for (name, reason, _) in &summary.restated_declarations {
            if !certified.contains(name) {
                loader_failures.insert(
                    name.to_string(),
                    format!("uncertified restatement held by {reason}"),
                );
            }
        }
    }
    for module in modules.difference(&found_modules) {
        accounting.push(CensusAccountingError::MissingModule(module.clone()));
    }
    let stored: BTreeSet<String> = original.keys().cloned().collect();
    for name in stored.difference(targets) {
        accounting.push(CensusAccountingError::MissingTarget(name.clone()));
    }
    for name in targets.difference(&stored) {
        accounting.push(CensusAccountingError::ExtraTarget(name.clone()));
    }
    let all: BTreeSet<String> = stored.union(targets).cloned().collect();
    let none = BTreeSet::new();
    // Missing/unknown/ambiguous original evidence cannot supply authority to
    // another local declaration, even if its environment row looks valid.
    let not_admitted = loader_failures
        .keys()
        .cloned()
        .chain(invalid_metadata)
        .chain(
            original
                .iter()
                .filter(|(_, safety)| safety.is_none())
                .map(|(name, _)| name.clone()),
        )
        .chain(targets.difference(&stored).cloned())
        .collect();
    let scope = ReplayScope {
        prerequisites: &none,
        not_admitted: &not_admitted,
        already_declared: &already_declared,
    };
    let replay = typecheck_constants_full_ordered(env, &all, &scope, max_heartbeats);
    let mut ordered = BTreeMap::new();
    for (name, verdict) in replay.verdicts {
        if ordered.insert(name.to_string(), verdict).is_some() {
            accounting.push(CensusAccountingError::ReplayAccounting);
        }
    }
    if replay.pass + replay.fail != all.len() || replay.errors.keys().any(|n| !all.contains(n)) {
        accounting.push(CensusAccountingError::ReplayAccounting);
    }
    let accounting_invalid: BTreeSet<String> = replay
        .accounting_invalid
        .iter()
        .map(ToString::to_string)
        .collect();
    let verdicts: BTreeMap<String, DeclarationReplayVerdict> = all.into_iter().map(|label| {
        let outcome = if let Some(reason) = loader_failures.get(&label) {
            DeclarationReplayVerdict::Failed(CensusFailure::Loader(reason.clone()))
        } else if accounting_invalid.contains(&label) {
            DeclarationReplayVerdict::Failed(CensusFailure::RegistryAccounting)
        } else {
            match (original.get(&label), ordered.remove(&label)) {
                (None, _) => DeclarationReplayVerdict::Failed(CensusFailure::MissingStoredDeclaration),
                (Some(None), _) => DeclarationReplayVerdict::Failed(CensusFailure::UnknownStoredSafety),
                (_, None) => DeclarationReplayVerdict::Failed(CensusFailure::MissingReplayVerdict),
                (Some(Some(DefinitionSafety::Safe)), Some(Ok(()))) => DeclarationReplayVerdict::Admitted,
                (Some(Some(_)), Some(Ok(()))) => DeclarationReplayVerdict::Failed(CensusFailure::RuntimeAdmitted),
                (Some(Some(safety)), Some(Err(refusal))) => {
                    let expected = match safety { DefinitionSafety::Unsafe => Some("unsafe"), DefinitionSafety::Partial => Some("partial"), _ => None };
                    if matches!(&refusal, ReplayRefusal::NotReplayable { name, safety } if name.to_string() == label && Some(*safety) == expected) {
                        DeclarationReplayVerdict::NotReplayable { safety: *safety, refusal }
                    } else {
                        DeclarationReplayVerdict::Failed(CensusFailure::Replay(refusal))
                    }
                }
            }
        };
        (label, outcome)
    }).collect();
    for occurrence in &mut restatements {
        occurrence.canonical_admitted = matches!(
            verdicts.get(&occurrence.name),
            Some(DeclarationReplayVerdict::Admitted)
        );
    }
    DeclarationReplayCensus {
        verdicts,
        accounting,
        restatements,
    }
}

#[cfg(test)]
mod tests;
