// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lazy, on-demand resolution of Mathverse names after a CORPUS-level import.
//!
//! # What this buys
//!
//! `import Mathverse.<Corpus>.<Constant>` installs exactly one constant, so
//! twenty lemmas needed twenty import lines. After
//!
//! ```text
//! import Mathverse.Mathlib
//! theorem t (x y : Nat) : x = y ∨ x ≠ y := eq_or_ne x y
//! ```
//!
//! the corpus is *armed* and any name in it resolves on first use.
//!
//! # Shape: REQUEST, then LOAD — the split is forced
//!
//! `ElabCtx` holds `env: &'a Environment` — an immutable borrow for its whole
//! lifetime (`infer/mod.rs`). Nothing inside term elaboration can install a
//! constant. So the elaborator only ever *asks*:
//!
//! 1. an already-failing resolution path mints
//!    [`ElabError::MathverseNameAvailable`] instead of `UnknownIdent`, but only
//!    when a corpus is armed AND the name is absent from the environment AND
//!    the installed library offers it;
//! 2. `elaborate_general_and_register` (`lib.rs`), which owns
//!    `&mut Environment`, catches that request and hands it to
//!    `mathverse_lazy_retry`, which runs the gated loader and re-elaborates
//!    the whole declaration.
//!
//! # The gate is the SAME gate
//!
//! The load is `mathverse_import::load_gated_constant`, the identical function
//! the eager `import Mathverse.<Corpus>.<Constant>` arm calls: same corpus
//! provenance check, same `mathverse_load_named` →`load_candidate_closure`,
//! same `TrustGate` (default `Strict`) over the full transitive closure, same
//! fail-closed residency re-check. There is one loader body and lazy resolution
//! did not add a second one.
//!
//! # Zero cost when disarmed
//!
//! Arming is an ENVIRONMENT OPTION written by the corpus-level import arm, not
//! the thread-local `mathverse_library_installed()` flag — a thread-local would
//! arm files that never mentioned Mathverse (any embedder that calls
//! `set_mathverse_library` at startup). With no `import Mathverse.…` in the
//! file the option is absent, [`ElabCtx::mathverse_lazy_request`] returns after
//! one hash probe on an already-failing path, no library lookup happens, and
//! the error is byte-identical to before.
//!
//! # Termination
//!
//! Two independent guards:
//!
//! - **Progress.** A request is minted only for a name that is NOT resident. A
//!   granted request ends with that name resident (the loader's fail-closed
//!   re-check proves it), so the same name can never be requested twice and
//!   each round strictly grows the environment.
//! - **Budget.** [`MATHVERSE_LAZY_LOAD_BUDGET`] caps gated loads per
//!   declaration. Exhaustion is a named error, never a loop.

use crate::error::ElabError;

/// Environment option written by `import Mathverse.<Corpus>`; its value is the
/// comma-separated list of armed corpus tags (`"Mathlib"`, `"Mathlib,Isabelle"`,
/// `"Any"`).
///
/// An environment option, not a thread-local: arming must travel with the FILE
/// that asked for it. `FileContext::apply_options_to_env` is purely additive, so
/// the flag survives every later declaration in the file.
pub(crate) const MATHVERSE_ARMED_OPTION: &str = "mathverse.armed";

/// Gated loads a single declaration may trigger through lazy resolution.
///
/// Eight. Each load costs a full transitive-closure trust walk (hundreds of
/// milliseconds), so this is a cost bound, not a termination bound —
/// termination comes from the progress rule above. A declaration citing more
/// than eight not-yet-resident library names fails with a named error telling
/// the user to import the extras eagerly.
pub(crate) const MATHVERSE_LAZY_LOAD_BUDGET: u8 = 8;

/// The library name a failed elaboration asked the driver to install, if any.
///
/// Unwraps the tactic sandwich: a term elaborated inside a tactic block comes
/// back as `TacticFailed(UpstreamElabError { source })`, and `exact`-style
/// tactics can nest that more than once. The `by`-block boundary may also add
/// the [`ElabError::InTactic`] attribution wrapper, which is transparent by
/// contract ("changes the message, never the verdict"), so it is looked
/// through too.
pub(crate) fn requested_name(err: &ElabError) -> Option<&str> {
    match err {
        ElabError::MathverseNameAvailable { name } => Some(name.as_str()),
        ElabError::TacticFailed(crate::tactic::TacticError::UpstreamElabError { source })
        | ElabError::InTactic { source, .. } => requested_name(source),
        _ => None,
    }
}

/// Corpus tags armed for this environment, or `None` when disarmed.
///
/// `Any`/`All` anywhere in the list disables the provenance check, exactly as
/// `import Mathverse.Any.<name>` does on the eager path.
#[cfg(any(feature = "mathverse-library", test))]
pub(crate) fn armed_tags(raw: Option<&Option<String>>) -> Option<Vec<String>> {
    let value = raw?.as_ref()?;
    let tags: Vec<String> = value
        .split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty())
        .map(ToString::to_string)
        .collect();
    (!tags.is_empty()).then_some(tags)
}

/// Add `tag` to the armed corpus list already stored in `existing`, preserving
/// order and rejecting duplicates. Returns the new option value.
#[cfg(any(feature = "mathverse-library", test))]
pub(crate) fn arm_tag(existing: Option<&Option<String>>, tag: &str) -> String {
    let mut tags = armed_tags(existing).unwrap_or_default();
    if !tags.iter().any(|t| t == tag) {
        tags.push(tag.to_string());
    }
    tags.join(",")
}

/// Does the installed Mathverse Library offer `name` at all?
///
/// Deliberately corpus-BLIND: a name the library has under the wrong corpus
/// must still produce a request, so the loader can report the provenance
/// mismatch ("the installed library's `List.append_assoc` is Isabelle") instead
/// of letting it present as a bare `Unknown identifier`. One hash probe.
#[cfg(feature = "mathverse-library")]
pub(crate) fn library_offers(name: &str) -> bool {
    crate::tactic::mathverse_use::mathverse_constant_source_system(name).is_some()
}

/// Without the `mathverse-library` feature there is no library to resolve
/// against, so nothing is ever requested and no code path changes.
#[cfg(not(feature = "mathverse-library"))]
pub(crate) fn library_offers(_name: &str) -> bool {
    false
}

#[cfg(test)]
mod tests {
    use super::{arm_tag, armed_tags, requested_name, ElabError};

    #[test]
    fn test_armed_tags_disarmed_states_return_none() {
        assert_eq!(armed_tags(None), None);
        assert_eq!(armed_tags(Some(&None)), None);
        assert_eq!(armed_tags(Some(&Some(String::new()))), None);
        assert_eq!(armed_tags(Some(&Some(" , ".to_string()))), None);
    }

    #[test]
    fn test_armed_tags_splits_and_trims_corpus_list() {
        assert_eq!(
            armed_tags(Some(&Some("Mathlib".to_string()))),
            Some(vec!["Mathlib".to_string()])
        );
        assert_eq!(
            armed_tags(Some(&Some("Mathlib, Isabelle".to_string()))),
            Some(vec!["Mathlib".to_string(), "Isabelle".to_string()])
        );
    }

    #[test]
    fn test_arm_tag_accumulates_without_duplicating() {
        assert_eq!(arm_tag(None, "Mathlib"), "Mathlib");
        let armed = Some(Some("Mathlib".to_string()));
        assert_eq!(arm_tag(armed.as_ref(), "Mathlib"), "Mathlib");
        assert_eq!(arm_tag(armed.as_ref(), "Isabelle"), "Mathlib,Isabelle");
    }

    #[test]
    fn test_requested_name_unwraps_the_tactic_sandwich() {
        let marker = ElabError::MathverseNameAvailable {
            name: "eq_or_ne".to_string(),
        };
        assert_eq!(requested_name(&marker), Some("eq_or_ne"));

        let wrapped = ElabError::TacticFailed(crate::tactic::TacticError::UpstreamElabError {
            source: Box::new(marker),
        });
        assert_eq!(requested_name(&wrapped), Some("eq_or_ne"));

        // The `by`-block attribution wrapper is transparent as well.
        let attributed = ElabError::InTactic {
            tactic: "exact".to_string(),
            chain: "`exact`".to_string(),
            span_start: 0,
            span_end: 5,
            source: Box::new(wrapped),
        };
        assert_eq!(requested_name(&attributed), Some("eq_or_ne"));

        // Every other error is left alone — no retry is requested.
        assert_eq!(
            requested_name(&ElabError::UnknownIdent("typo".to_string())),
            None
        );
    }
}
