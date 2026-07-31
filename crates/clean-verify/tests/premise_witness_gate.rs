// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The premise-satisfiability ratchet — vacuity firewall item 9.
//!
//! # What this gate is for
//!
//! `def_eq_fuel_complete` passed a census of 0 axioms / 0 domain axioms / 0
//! `DerivedProved` debt and proved nothing, because its `hnf` premise is false
//! (`hnf_is_false`). Nine declarations inherited that premise. **Zero axioms is
//! not zero assumptions** — an axiom-closure walk answers "what does this trust?"
//! and structurally cannot answer "can anything satisfy what this assumes?".
//!
//! This gate answers a weaker but mechanical version of the second question: for
//! every predicate assumed as a hypothesis anywhere in the spec, does *any*
//! registered definition conclude it?
//!
//! # Honest limits, restated here so nobody has to read the library to find them
//!
//! Head-only, therefore a **necessary condition and not a sufficient one**. On the
//! case that motivated it, `iota_immune` itself would have passed, because
//! `iota_immune_sort_witness` concludes it at a *sort* while
//! `nf_head.neutral`'s field needs it at an *application*. It would have flagged
//! `const_whnf` and `iota_neutral`, which is enough to have started the
//! investigation — but a green run here is not a proof of non-vacuity, and must
//! never be reported as one.
//!
//! The stronger rule is a positive witness per **constructor arm** of every
//! predicate used in hypothesis position — the Guard-4 non-vacuity discipline
//! lifted from environments to predicates. `nf_head_neutral_app_witness` is what
//! satisfying that looks like for one arm.
//!
//! # Bootstrapping
//!
//! The baseline is a measurement, so it has to be taken once:
//!
//! ```sh
//! PREMISE_WITNESS_BLESS=1 cargo test --offline -p clean-verify \
//!     --test premise_witness_gate
//! ```
//!
//! That writes `data/premise_witness_ratchet.json`. It is deliberately an
//! explicit, env-gated act rather than an automatic self-blessing: a ratchet that
//! quietly rewrites its own baseline enforces nothing. Thereafter the list may
//! only shrink.

use std::collections::BTreeSet;
use std::path::PathBuf;

use clean_verify::premise_witness::unwitnessed_premises;
use clean_verify::test_utils::build_spec_with_stack;

fn golden_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../data/premise_witness_ratchet.json")
}

/// Predicates that are assumed but never concluded may only DECREASE.
///
/// A new entry means a fresh premise was introduced that nothing in the tree can
/// satisfy — which is how `hnf` got in. Either supply a witness, or add the name
/// with a justification so the addition is a visible, reviewable diff.
#[test]
fn unwitnessed_premises_only_shrink() {
    let spec = build_spec_with_stack();
    let live = unwitnessed_premises(&spec);
    let live_names: BTreeSet<String> = live.iter().map(|u| u.predicate.clone()).collect();

    let path = golden_path();
    if std::env::var("PREMISE_WITNESS_BLESS").is_ok() {
        // PRESERVE the existing `_comment`. It holds the curated justifications —
        // which entries are genuine open obligations, which are data-type noise —
        // and a bless that overwrote them would destroy the only human analysis in
        // the file, quietly, every time the list was re-measured.
        let kept_comment = std::fs::read_to_string(&path)
            .ok()
            .and_then(|raw| serde_json::from_str::<serde_json::Value>(&raw).ok())
            .and_then(|v| v["_comment"].as_str().map(str::to_string));
        let body = serde_json::to_string_pretty(&serde_json::json!({
            "_comment": kept_comment.unwrap_or_else(|| {
                "Premise-satisfiability ratchet (vacuity firewall item 9). \
                 Predicates ASSUMED as a hypothesis somewhere in the clean-verify spec that NO \
                 registered definition concludes. Head-only: a necessary condition, not a \
                 sufficient one — see crates/clean-verify/src/premise_witness.rs. This list may \
                 only shrink. Supply a witness, or add the name here with a justification."
                    .to_string()
            }),
            "count": live_names.len(),
            "unwitnessed": live_names.iter().collect::<Vec<_>>(),
            "carriers": live.iter().map(|u| serde_json::json!({
                "predicate": u.predicate,
                "assumed_by": u.carriers,
            })).collect::<Vec<_>>(),
        }))
        .expect("ratchet json serializes");
        std::fs::write(&path, body + "\n").expect("write ratchet baseline");
        eprintln!(
            "BLESSED {} unwitnessed predicate(s) into {}",
            live_names.len(),
            path.display()
        );
        return;
    }

    let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "missing premise-satisfiability baseline {} ({e}).\n\
             Take the measurement once with:\n  \
             PREMISE_WITNESS_BLESS=1 cargo test --offline -p clean-verify \
             --test premise_witness_gate",
            path.display()
        )
    });
    let golden: serde_json::Value = serde_json::from_str(&raw).expect("baseline is valid json");
    let allowed: BTreeSet<String> = golden["unwitnessed"]
        .as_array()
        .expect("`unwitnessed` is an array")
        .iter()
        .map(|v| v.as_str().expect("`unwitnessed` holds strings").to_string())
        .collect();

    let new: Vec<&String> = live_names.difference(&allowed).collect();
    assert!(
        new.is_empty(),
        "PREMISE-SATISFIABILITY RATCHET VIOLATION: {} predicate(s) are ASSUMED as a \
         hypothesis in the clean-verify spec but NOTHING in the spec concludes them:\n  {}\n\n\
         A conditional theorem whose premises cannot be satisfied is not a weak result, it is a \
         NON-result — and it passes the axiom census, the domain-axiom count and the \
         DerivedProved-debt count while looking green. That is exactly how the def-eq \
         completeness capstone came to be vacuous (see hnf_is_false). Zero axioms is not zero \
         assumptions.\n\n\
         EITHER:\n  \
         (1) SUPPLY a witness — register a definition concluding the predicate (see \
         iota_immune_of_dead_const_head / nf_head_neutral_app_witness for the pattern); OR\n  \
         (2) if the premise is genuinely open, add the name to \
         data/premise_witness_ratchet.json with a justification naming what would discharge it, \
         so the addition is a visible, reviewable diff.",
        new.len(),
        new.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n  ")
    );

    // Report progress: names that were unwitnessed and now are not.
    let fixed: Vec<&String> = allowed.difference(&live_names).collect();
    if !fixed.is_empty() {
        eprintln!(
            "{} predicate(s) gained a witness since the baseline; \
             re-bless to tighten the ratchet:\n  {}",
            fixed.len(),
            fixed
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join("\n  ")
        );
    }
}
