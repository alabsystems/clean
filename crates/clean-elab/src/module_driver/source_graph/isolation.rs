// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! The source frontend's existing complete body-effect and outcome comparison.

use crate::ElabResult;
use clean_kernel::Environment;

/// What one file's OWN declarations did, measured from the environment right
/// after its imports to the environment after its last declaration.
///
/// Both halves are compared between the file's elaboration next to modules it
/// does not import and its elaboration in exactly its own import closure
/// ([`ModuleElaboration::disagreement`]):
///
/// * `effect` covers EVERY component of the environment — instances,
///   attributes, simp/aesop sets, structure metadata, options, extension
///   entries, prelude flags — not only the constants the file added. The
///   constants-only comparison let `attribute [instance] c` register P's root
///   `c` next to P and `N.c` without it, with the same constants both ways
///   (round-24 verification of ff6c33c2c).
/// * `outcomes` says how each of its top-level declarations ELABORATED
///   ([`ElabOutcome`]): a file that fails in its own closure (Lean cannot
///   compile it) may elaborate cleanly next to a stranger that supplies what
///   it lacks (`attribute [instance] N.c` where only an unimported sibling
///   defines `N.c`), and the failed command changes nothing the effect would
///   see. Credit decisions (the imported-cone gate, `sorry`) are not part of
///   it: they depend on the run, not on the environment the file saw.
#[derive(Clone, Debug)]
pub struct ModuleElaboration {
    pub effect: clean_kernel::env::EnvEffect,
    pub outcomes: Vec<ElabOutcome>,
}

/// How one top-level declaration elaborated: refused outright, or elaborated
/// with this many failed leaves (members of a `namespace` / `section` /
/// `mutual` block). Compared between a module's elaboration next to modules
/// it does not import and in exactly its own import closure, by `clean check`
/// and by `clean project check`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ElabOutcome {
    Refused,
    Elaborated { failed_leaves: usize },
}

impl ElabOutcome {
    pub fn of(result: &Result<crate::RegisteredElabResult, crate::ElabError>) -> Self {
        match result {
            Ok(registered) => Self::of_registered(registered),
            Err(_) => Self::Refused,
        }
    }

    /// The outcome of a declaration that elaborated.
    pub fn of_registered(registered: &crate::RegisteredElabResult) -> Self {
        let mut leaves: Vec<&ElabResult> = Vec::new();
        registered.result.leaf_decls(&mut leaves);
        Self::Elaborated {
            failed_leaves: leaves
                .iter()
                .filter(|leaf| {
                    matches!(
                        leaf,
                        ElabResult::Failed { .. } | ElabResult::Diagnosed { .. }
                    )
                })
                .count(),
        }
    }
}

/// The first position where two elaborations' [`ElabOutcome`] sequences
/// differ, described; `None` when they are the same.
pub fn elab_outcome_difference(own: &[ElabOutcome], other: &[ElabOutcome]) -> Option<String> {
    let position = own
        .iter()
        .zip(other)
        .position(|(a, b)| a != b)
        .or_else(|| (own.len() != other.len()).then(|| own.len().min(other.len())))?;
    let show = |outcome: Option<&ElabOutcome>| match outcome {
        None => "absent".to_string(),
        Some(ElabOutcome::Refused) => "refused".to_string(),
        Some(ElabOutcome::Elaborated { failed_leaves: 0 }) => "elaborated".to_string(),
        Some(ElabOutcome::Elaborated { failed_leaves }) => {
            format!("elaborated with {failed_leaves} failed member(s)")
        }
    };
    Some(format!(
        "its top-level declaration #{} is {} in its own import closure but {} next to \
         modules it does not import",
        position + 1,
        show(own.get(position)),
        show(other.get(position))
    ))
}

impl ModuleElaboration {
    /// Compare an elaboration in its own import closure with the same body
    /// beside other modules. Includes failed commands and all environment data.
    pub fn disagreement(&self, shared: &Self, shared_after: &Environment) -> Option<String> {
        elab_outcome_difference(&self.outcomes, &shared.outcomes)
            .or_else(|| self.effect.disagreement(&shared.effect, shared_after))
    }
}
