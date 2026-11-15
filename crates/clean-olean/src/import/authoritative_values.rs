// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R142's invariant over one loaded artifact (docs/DECISIONS.md R142): every
//! declaration the artifact's AUTHORITATIVE part (`.olean.private` for a
//! module-system artifact, `.olean` otherwise — the part Lean's importer, and
//! `leanchecker`, reads) states with a value is resident after the load, as
//! this artifact's own declaration, with its value.
//!
//! R131 refused one path to the opposite: a value-free stub whose completion
//! the KERNEL refused. Its verification found the same outcome by others — a
//! private value Clean's converter cannot read (a metavariable, a free
//! variable), a stub whose name an import already holds as an axiom, and a
//! value an eliding load drops before the checked upgrade — each leaving a
//! declaration resident that Lean does not read. The rule here does not
//! enumerate paths: whatever kept the value out, the declaration is named.
//!
//! Value EQUALITY needs no comparison here: an artifact the reader's rule
//! admits states one record per name across its parts
//! (`artifact::check_artifact_parts`), so a resident value of this artifact's
//! is the authoritative part's.

use hashbrown::HashSet;

use super::artifact_ledger::{declared_by_this_artifact, ArtifactKey};
use super::load_parse::LoadModule;
use super::load_register::{is_typed_compiler_ir_name, stored_unsafe_or_partial};
use super::{LoadSummary, OleanImportPolicy};
use crate::payload::CleanPayload;
use crate::ConstantKind;
use clean_kernel::env::{ConstantKind as KernelConstantKind, Environment};
use clean_kernel::name::Name;

/// The declarations `authoritative` (a part of `artifact`) states with a value
/// that `env` does not hold as `artifact`'s own declaration with its value,
/// each with the reason, in the part's order. `parts` are the summaries of the
/// artifact's parts this load just pushed. A value the policy elides at
/// registration counts as held when the declaration is resident in its own
/// kind (completed, then elided). A name the part's own Clean payload declares
/// is the payload's. An `unsafe` or `partial` declaration is not one: Lean's
/// replay never admits it, and the loader marks a stub it could not complete
/// `unsafe` so no safe declaration may use it (`skipped_not_replayable`).
///
/// Two drops are already named, each by a record of its own:
///
/// - a declaration listed in `LoadSummary::shadowed_declarations` (a resident
///   constant that is not this artifact's holds the name, and Lean refuses the
///   name as already declared). Every re-check lane refuses it from that record,
///   with its holder, and every use of it (the replay's `AlreadyDeclared`,
///   verify-batch's in-run check);
/// - a THEOREM listed in `LoadSummary::restated_declarations` over a resident
///   THEOREM with its universe parameters and type: Lean merges the two
///   (`finalizeImport`'s `subsumesInfo`; its replay skips the duplicate
///   theorem), and by proof irrelevance no value of it is ever read. Over a
///   resident AXIOM, Lean's theorem replaces the axiom, so its value must be
///   resident, and a resident axiom is named here (R131's S1-shadow: an
///   import's axiom standing for a module's theorem whose value the kernel
///   refuses).
pub(super) fn unmet(
    env: &Environment,
    artifact: &ArtifactKey,
    authoritative: &LoadModule,
    parts: &[LoadSummary],
    policy: OleanImportPolicy,
) -> Vec<(Name, String)> {
    let elision = policy.proof_elision();
    let shadowed: HashSet<&Name> = parts
        .iter()
        .flat_map(|s| s.shadowed_declarations.iter().map(|(name, _)| name))
        .collect();
    let restated_theorems: HashSet<&Name> = parts
        .iter()
        .flat_map(|s| s.restated_declarations.iter())
        .filter(|(_, _, incoming_theorem)| *incoming_theorem)
        .map(|(name, _, _)| name)
        .collect();
    let payload: HashSet<Name> = authoritative
        .clean_payload
        .as_ref()
        .map(CleanPayload::declared_names)
        .unwrap_or_default();
    authoritative
        .constants
        .iter()
        .filter(|c| {
            c.value_ptr != 0
                && matches!(
                    c.kind,
                    ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
                )
                && !is_typed_compiler_ir_name(&c.kernel_name)
                && !payload.contains(&c.kernel_name)
                && !stored_unsafe_or_partial(&c.kind, c.definition_safety)
        })
        .filter_map(|c| {
            let name = &c.kernel_name;
            let reason = match env.get_const(name) {
                None => Some("it is not resident"),
                Some(_) if shadowed.contains(name) => None,
                Some(resident) if !declared_by_this_artifact(env, name, artifact) => {
                    if restated_theorems.contains(name)
                        && resident.kind == KernelConstantKind::Theorem
                    {
                        None
                    } else if resident.kind == KernelConstantKind::Axiom {
                        Some(
                            "another declaration holds the name as a value-free axiom (an \
                             import's, or the checker's), which Lean's theorem replaces",
                        )
                    } else {
                        Some("another declaration holds the name (an import's, or the checker's)")
                    }
                }
                Some(resident) if resident.kind == KernelConstantKind::Axiom => Some(
                    "its value-free stub stands in its place: the value did not convert, or the \
                     kernel refused it",
                ),
                Some(resident) if resident.value.is_none() && !elision.elides(resident.kind) => {
                    Some("it is resident without its value")
                }
                Some(_) => None,
            };
            reason.map(|r| (name.clone(), r.to_string()))
        })
        .collect()
}
