// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Diagnostics for batch refusals.
//!
//! The reader of these messages is an AI programmer, so every one of them names
//! the fix WITH OPTIONS, in order of preference, and says what each option
//! costs. "This is a cycle" is a fact; "put both declarations in one `mutual`
//! block, or break the recursion, or state one as an `axiom` and accept the
//! disclosure" is an instruction.

use super::schedule::{PROOF_CYCLE_OPTIONS, UNSUPPORTED_SCC_OPTIONS};
use super::{BatchRejection, PublishAuditIssue};

/// Render one refusal.
#[must_use]
pub fn rejection(rejection: &BatchRejection) -> String {
    match rejection {
        BatchRejection::NameCollision {
            name,
            first,
            second,
        } => format!(
            "error: `{name}` is declared twice in this batch\n  \
             note: first at {:?} (unit {}), again at {:?} (unit {})\n  \
             help: header-first checking builds ONE name index for the whole \
             batch, so two declarations cannot share a canonical name — rename \
             one, or move one into its own `namespace` so the qualified names \
             differ",
            first.span, first.unit.0, second.span, second.unit.0
        ),
        BatchRejection::HeaderNotStable { names, iterations } => format!(
            "error: the signature index did not settle after {iterations} \
             iterations\n  \
             note: signatures still changing: {}\n  \
             note: each iteration re-elaborates EVERY signature against the \
             complete index from the previous one; a signature that keeps \
             changing means its meaning depends on which other signatures are \
             present, which is exactly the source-order dependence header-first \
             checking exists to remove\n  \
             help: two ways forward — (1) write the result type of the \
             declarations named above explicitly, so their signature does not \
             depend on inference against a moving index; (2) if they genuinely \
             refer to each other at the TYPE level, that is not expressible \
             here: introduce a third declaration both can depend on",
            join(names)
        ),
        BatchRejection::ProofCycle { names, .. } => format!(
            "error: these proofs depend on each other: {}\n  \
             note: a proof cycle is not a mutual definition. `{}` is only as \
             proved as `{}`, and `{}` only as `{}`. Neither is proved.\n  \
             help: {}",
            cycle_arrow(names),
            names.first().map_or_else(String::new, ToString::to_string),
            names.get(1).map_or_else(String::new, ToString::to_string),
            names.get(1).map_or_else(String::new, ToString::to_string),
            names.first().map_or_else(String::new, ToString::to_string),
            numbered(PROOF_CYCLE_OPTIONS)
        ),
        BatchRejection::SignatureCycle { names, .. } => format!(
            "error: these declarations' TYPES depend on each other: {}\n  \
             note: a type cannot be elaborated before the types it mentions, and \
             Clean has no mutual form for signatures — the one atomic mutual \
             shape, a parameterless `mutual inductive`, is checked as a single \
             declaration and would not appear here\n  \
             help: {}",
            cycle_arrow(names),
            numbered(UNSUPPORTED_SCC_OPTIONS)
        ),
        BatchRejection::UnsupportedScc { names, options, .. } => format!(
            "error: these declarations depend on each other, and Clean cannot \
             check a mutual group that is not written as one block: {}\n  \
             note: the cycle is {}\n  \
             help: {}",
            join(names),
            cycle_arrow(names),
            numbered(options)
        ),
        BatchRejection::HeaderTypeDivergence {
            name,
            staged,
            registered,
            ..
        } => format!(
            "error: `{name}` was registered with a different signature than the \
             one other declarations were elaborated against\n  \
             note: staged     {staged}\n  \
             note: registered {registered}\n  \
             note: this is a source-to-kernel fidelity failure, not a style \
             issue: something in this batch resolved `{name}` against a \
             signature the kernel does not hold\n  \
             help: two ways forward — (1) write `{name}`'s universe parameters \
             and result type explicitly, so the signature does not change when \
             its body is elaborated (a declared type whose level metavariables \
             are solved FROM the body is the usual cause); (2) if `{name}` uses \
             well-founded recursion, its type can be produced by body lowering \
             — give it an explicit `termination_by` and an explicit result type",
        ),
        BatchRejection::StagedReference {
            subject, staged, ..
        } => format!(
            "error: `{subject}` still refers to declarations that are only \
             signatures: {}\n  \
             note: a staged header is a name and a type with no value. It is \
             never citable — the authoritative environment does not contain it \
             — so `{subject}` cannot be registered while it depends on one.\n  \
             help: this normally means a dependency cycle that the scheduler \
             could not name; check whether {} and `{subject}` need each other",
            join(staged),
            join(staged)
        ),
        BatchRejection::Elaboration { name, error, .. } => match name {
            Some(name) => format!("error: `{name}` did not elaborate: {error}"),
            None => format!("error: a declaration did not elaborate: {error}"),
        },
        BatchRejection::PublishAudit { issues } => format!(
            "error: the publish audit refused this batch; nothing was \
             registered\n{}",
            issues
                .iter()
                .map(|issue| format!("  - {}", audit_issue(issue)))
                .collect::<Vec<_>>()
                .join("\n")
        ),
    }
}

/// Render one publish-audit issue.
#[must_use]
pub fn audit_issue(issue: &PublishAuditIssue) -> String {
    match issue {
        PublishAuditIssue::StagedHeaderInPublishEnv { names } => format!(
            "a provisional header reached the authoritative environment: {}. \
             This is unreachable by construction — headers are only ever added \
             to the staging environment — so it means the two environments were \
             merged somewhere. Do not relax this check; find the merge.",
            join(names)
        ),
        PublishAuditIssue::TrustDebt { name, marker } => format!(
            "`{name}` reaches the incomplete-proof marker `{marker}`. Finish the \
             proof, or state the missing step as an `axiom` so it is disclosed \
             by name in the certification closure."
        ),
        PublishAuditIssue::UnsanctionedAxiom { name, axiom } => format!(
            "`{name}` depends on the axiom `{axiom}`, which is neither a \
             certification foundation nor declared in this batch."
        ),
        PublishAuditIssue::MissingDeclaration { name } => {
            format!("`{name}` was reported as registered but is not in the environment.")
        }
    }
}

fn join<T: std::fmt::Display>(items: &[T]) -> String {
    items
        .iter()
        .map(|item| format!("`{item}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn cycle_arrow<T: std::fmt::Display>(names: &[T]) -> String {
    names
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" -> ")
}

fn numbered(options: &[&str]) -> String {
    let mut out = String::from("ways forward, in order of preference —");
    for (index, option) in options.iter().enumerate() {
        out.push_str(&format!("\n        {}. {option}", index + 1));
    }
    out
}
