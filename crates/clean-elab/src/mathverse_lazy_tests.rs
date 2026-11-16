// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lazy Mathverse resolution: ONE corpus-level import, then any name in the
//! corpus resolves on demand.
//!
//! The gap these tests close: `import Mathverse.<Corpus>.<Constant>` is
//! per-constant, so twenty lemmas needed twenty import lines. After
//! `import Mathverse.Mathlib` a citation resolves with no import line of its
//! own.
//!
//! Each deliverable test states the BEFORE (same source, corpus armed but the
//! elaborator hooks removed by construction — i.e. an absent name) and the
//! AFTER, so a regression shows up as a specific half failing.
//!
//! What is deliberately pinned here:
//!
//! * DISARMED is byte-identical — a file that wrote no `import Mathverse.…`
//!   still reports `Unknown identifier`, with no Mathverse string, EVEN WHEN a
//!   library is installed on the thread (`test_..._disarmed_...`);
//! * a below-`Strict` name fails CLOSED with the trust reason, never as
//!   `Unknown identifier` (`test_..._below_strict_...`);
//! * a genuinely absent name terminates with the ordinary error and does not
//!   loop (`test_..._absent_...`);
//! * the retry is BOUNDED at exactly
//!   [`MATHVERSE_LAZY_LOAD_BUDGET`](crate::mathverse_lazy::MATHVERSE_LAZY_LOAD_BUDGET)
//!   gated loads per declaration — 8 resolve, 9 is a named error
//!   (`test_..._budget_...`);
//! * dotted names work, which is the whole value: 96.6% of the shipped
//!   corpus's kernel-verified Lean4 constants are dotted
//!   (`test_..._dotted_...`).

#![cfg(feature = "mathverse-library")]

use clean_kernel::{Environment, Name};
use clean_mathverse::types::{ImportConfidence, SourceSystem};

use crate::mathverse_lazy::{MATHVERSE_ARMED_OPTION, MATHVERSE_LAZY_LOAD_BUDGET};
use crate::mathverse_term_resolution_tests::install_library_with_rows;
use crate::tactic::mathverse_use::{clear_mathverse_library, set_mathverse_library};
use crate::{ElabError, ElabResult};

// ---------------------------------------------------------------------------
// Fixture
// ---------------------------------------------------------------------------

/// Every row is `∀ (p : Prop), p → p`, so the only thing that varies is name,
/// corpus and trust — which is what makes the refusal tests mean something.
fn install_lazy_library() {
    let mut rows: Vec<(String, SourceSystem, ImportConfidence)> = vec![
        // Bare name.
        (
            "lazy_id_thm".to_string(),
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
        ),
        // Dotted, prefix is NOT a resident value — resolves through the
        // qualified-name fallback.
        (
            "LazyProbe.dotted_thm".to_string(),
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
        ),
        // Dotted, prefix IS a resident value (`Nat` is an inductive in the
        // prelude) — resolves through the type-valued-receiver namespace
        // lookup, a completely different dead end.
        (
            "Nat.lazy_probe_thm".to_string(),
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
        ),
        // Present, spelled right, below `Strict`.
        (
            "lazy_untrusted_thm".to_string(),
            SourceSystem::Lean4,
            ImportConfidence::Axiomatized,
        ),
        // Present and trusted, but from the other corpus.
        (
            "lazy_isabelle_thm".to_string(),
            SourceSystem::Isabelle,
            ImportConfidence::KernelVerified,
        ),
    ];
    // Nine trusted rows for the budget tests: eight must resolve in one
    // declaration, the ninth must not.
    for i in 0..=MATHVERSE_LAZY_LOAD_BUDGET {
        rows.push((
            format!("lazy_budget_{i}"),
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
        ));
    }

    let borrowed: Vec<(&str, SourceSystem, ImportConfidence)> = rows
        .iter()
        .map(|(name, system, confidence)| (name.as_str(), *system, *confidence))
        .collect();
    install_library_with_rows(&borrowed);
}

fn elab(env: &mut Environment, src: &str) -> Result<ElabResult, ElabError> {
    let decl = clean_parser::parse_decl(src).expect("fixture source parses");
    crate::elaborate_decl_and_register(env, &decl)
}

fn resident(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

/// `set_mathverse_library` is thread-local and these tests share a thread, so
/// every test installs its own library and clears it at the end.
struct LazyFixture;

impl LazyFixture {
    fn new() -> Self {
        install_lazy_library();
        Self
    }
}

impl Drop for LazyFixture {
    fn drop(&mut self) {
        clear_mathverse_library();
    }
}

// ---------------------------------------------------------------------------
// (a) The deliverable
// ---------------------------------------------------------------------------

/// ONE corpus-level import, then a citation with NO import line of its own.
///
/// BEFORE: `import Mathverse.Mathlib` alone left `lazy_id_thm` unresolved.
/// AFTER: the same two lines elaborate and kernel-register.
#[test]
fn test_lazy_resolution_needs_no_per_constant_import_line() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();

    // Arming installs NOTHING. That is the "load nothing yet" half of the
    // contract: the cost of a corpus import stays the cost of opening the
    // library, not of loading it.
    let armed = elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");
    assert!(matches!(armed, ElabResult::Skipped));
    assert!(
        !resident(&env, "lazy_id_thm"),
        "a corpus-level import must arm the corpus and load no constant"
    );
    assert_eq!(
        env.get_option(MATHVERSE_ARMED_OPTION),
        Some(&Some("Mathlib".to_string())),
        "the corpus tag must be recorded so the probe can enforce provenance"
    );

    // The deliverable: no `import Mathverse.Mathlib.lazy_id_thm` anywhere.
    let after = elab(
        &mut env,
        "theorem lazy_uses (q : Prop) (hq : q) : q := lazy_id_thm q hq",
    )
    .expect("an armed corpus must resolve a library name on demand");
    match after {
        ElabResult::Theorem { ref name, .. } => assert_eq!(name.to_string(), "lazy_uses"),
        other => panic!("expected a registered theorem, got {other:?}"),
    }
    assert!(
        resident(&env, "lazy_uses"),
        "the proof that cites library content must itself be registered"
    );
    assert!(
        resident(&env, "lazy_id_thm"),
        "the cited constant must have been installed through the gate, not faked"
    );
}

/// Dotted names — the shape 96.6% of the corpus actually has.
///
/// Both dotted regimes in one test, because they fail at completely different
/// places in `elab_proj`: `LazyProbe.dotted_thm` (prefix is a pure namespace)
/// dead-ends at the qualified-name fallback, `Nat.lazy_probe_thm` (prefix is a
/// resident inductive) dead-ends at the type-valued-receiver namespace lookup.
#[test]
fn test_lazy_resolution_covers_both_dotted_regimes() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");

    elab(
        &mut env,
        "theorem lazy_dotted_ns (q : Prop) (hq : q) : q := LazyProbe.dotted_thm q hq",
    )
    .expect("a dotted name whose prefix is a pure namespace must resolve lazily");
    assert!(resident(&env, "LazyProbe.dotted_thm"));

    elab(
        &mut env,
        "theorem lazy_dotted_value (q : Prop) (hq : q) : q := Nat.lazy_probe_thm q hq",
    )
    .expect("a dotted name whose prefix is a RESIDENT type must resolve lazily too");
    assert!(resident(&env, "Nat.lazy_probe_thm"));
}

/// Both corpora armed at once, from one library — the cross-system claim, now
/// without per-constant import lines.
#[test]
fn test_lazy_resolution_serves_two_armed_corpora_at_once() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("Mathlib corpus import succeeds");
    elab(&mut env, "import Mathverse.Isabelle").expect("Isabelle corpus import succeeds");
    assert_eq!(
        env.get_option(MATHVERSE_ARMED_OPTION),
        Some(&Some("Mathlib,Isabelle".to_string())),
        "arming must ACCUMULATE, not overwrite"
    );

    elab(
        &mut env,
        "theorem lazy_cross (q : Prop) (hq : q) : q := lazy_isabelle_thm q (lazy_id_thm q hq)",
    )
    .expect("one declaration must resolve names from both armed corpora");
    assert!(resident(&env, "lazy_id_thm"));
    assert!(resident(&env, "lazy_isabelle_thm"));
}

// ---------------------------------------------------------------------------
// (b) Disarmed
// ---------------------------------------------------------------------------

/// A file that wrote no `import Mathverse.…` must behave exactly as before —
/// EVEN THOUGH a library is installed on this thread and HAS the name.
///
/// This is why arming is an environment option and not the thread-local
/// `mathverse_library_installed()` flag: an embedder that installs a library at
/// startup must not silently arm every file it elaborates.
#[test]
fn test_lazy_resolution_disarmed_reports_a_plain_unknown_identifier() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    assert!(
        crate::mathverse_lazy::library_offers("lazy_id_thm"),
        "precondition: the installed library HAS the name the file will cite"
    );

    let err = elab(
        &mut env,
        "theorem disarmed_use (q : Prop) (hq : q) : q := lazy_id_thm q hq",
    )
    .expect_err("a disarmed file must not resolve library names");
    let msg = err.to_string();
    assert!(
        msg.starts_with("Unknown identifier: lazy_id_thm"),
        "disarmed must report a plain unknown identifier, got: {msg}"
    );
    assert!(
        !msg.contains("Mathverse"),
        "a disarmed file must not mention Mathverse at all, got: {msg}"
    );
    assert!(
        !resident(&env, "lazy_id_thm"),
        "a disarmed file must install nothing"
    );
}

/// Disarmed, with NO library installed at all: the same message. Pins that the
/// probe's first gate is the option, not the library.
#[test]
fn test_lazy_resolution_disarmed_without_library_is_unchanged() {
    clear_mathverse_library();
    let mut env = Environment::with_prelude();
    let err = elab(
        &mut env,
        "theorem no_lib_use (q : Prop) (hq : q) : q := lazy_id_thm q hq",
    )
    .expect_err("no library, no arming, no resolution");
    let msg = err.to_string();
    assert!(
        msg.starts_with("Unknown identifier: lazy_id_thm"),
        "got: {msg}"
    );
    assert!(!msg.contains("Mathverse"), "got: {msg}");
}

// ---------------------------------------------------------------------------
// (c) Fail closed
// ---------------------------------------------------------------------------

/// A name the library HAS but the gate REFUSES must surface the TRUST reason.
///
/// Collapsing it into `Unknown identifier` would turn a soundness refusal into
/// a spelling complaint — and would make the refusal indistinguishable from a
/// typo exactly where it matters most.
#[test]
fn test_lazy_resolution_below_strict_fails_closed_with_the_trust_reason() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");

    let err = elab(
        &mut env,
        "theorem untrusted_use (q : Prop) (hq : q) : q := lazy_untrusted_thm q hq",
    )
    .expect_err("Strict must refuse an Axiomatized constant reached lazily");
    let msg = err.to_string();
    assert!(
        matches!(err, ElabError::MathverseImportFailed { .. }),
        "expected a Mathverse gate refusal, got {err:?}"
    );
    assert!(
        msg.contains("lazy_untrusted_thm"),
        "the refusal must name the constant asked for: {msg}"
    );
    assert!(
        !msg.contains("Unknown identifier"),
        "a trust refusal must never be reported as an unknown identifier: {msg}"
    );
    assert!(
        !resident(&env, "lazy_untrusted_thm"),
        "a refused citation must leave the environment untouched"
    );
}

/// A name present under the WRONG corpus is a provenance error, not a miss.
///
/// The library's name index is global and last-writer-wins — on the shipped
/// corpus 41 names (`List.append_assoc`, `Nat.le_trans`, …) resolve to
/// Isabelle even though Lean4 declares them too. An `import Mathverse.Mathlib`
/// file must be TOLD that, not silently handed the other corpus's declaration
/// and not fobbed off with `Unknown identifier`.
#[test]
fn test_lazy_resolution_wrong_corpus_reports_provenance_not_a_miss() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("only Mathlib is armed");

    let err = elab(
        &mut env,
        "theorem wrong_corpus_use (q : Prop) (hq : q) : q := lazy_isabelle_thm q hq",
    )
    .expect_err("an Isabelle name must not resolve under a Mathlib-only arming");
    let msg = err.to_string();
    assert!(
        matches!(err, ElabError::MathverseImportFailed { .. }),
        "expected a provenance refusal, got {err:?}"
    );
    assert!(
        msg.contains("Isabelle") && msg.contains("Lean4"),
        "the refusal must name both the corpus asked for and the one found: {msg}"
    );
    assert!(!resident(&env, "lazy_isabelle_thm"));
}

// ---------------------------------------------------------------------------
// (d) Termination
// ---------------------------------------------------------------------------

/// A genuinely absent name terminates in ONE round with the ordinary error.
///
/// The probe is corpus-blind but library-gated: an absent name never mints a
/// request, so no retry happens and no Mathverse string appears.
#[test]
fn test_lazy_resolution_absent_name_terminates_with_the_ordinary_error() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");

    let err = elab(
        &mut env,
        "theorem absent_use (q : Prop) (hq : q) : q := no_such_lazy_name q hq",
    )
    .expect_err("an absent name must still fail");
    let msg = err.to_string();
    assert!(
        msg.starts_with("Unknown identifier: no_such_lazy_name"),
        "a typo must still read as a typo even while armed, got: {msg}"
    );
    assert!(!msg.contains("Mathverse"), "got: {msg}");

    // The dotted spelling of an absent name must terminate the same way.
    let err = elab(
        &mut env,
        "theorem absent_dotted_use (q : Prop) (hq : q) : q := NoSuch.lazy_name q hq",
    )
    .expect_err("an absent dotted name must still fail");
    assert!(
        !err.to_string().contains("Mathverse"),
        "got: {}",
        err.to_string()
    );
}

/// Exactly [`MATHVERSE_LAZY_LOAD_BUDGET`] lazily-resolved constants in one
/// declaration is fine.
#[test]
fn test_lazy_resolution_budget_admits_exactly_the_cap() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");

    let src = nested_citation(MATHVERSE_LAZY_LOAD_BUDGET, "at_cap");
    elab(&mut env, &src).expect("the cap itself must be admitted");
    for i in 0..MATHVERSE_LAZY_LOAD_BUDGET {
        assert!(resident(&env, &format!("lazy_budget_{i}")));
    }
}

/// One more than the cap is a NAMED error that says what to do, not a loop and
/// not a resolution miss.
#[test]
fn test_lazy_resolution_budget_refuses_one_over_the_cap() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");

    let src = nested_citation(MATHVERSE_LAZY_LOAD_BUDGET + 1, "over_cap");
    let err = elab(&mut env, &src).expect_err("one over the cap must be refused");
    let msg = err.to_string();
    assert!(
        matches!(err, ElabError::MathverseImportFailed { .. }),
        "expected the budget error, got {err:?}"
    );
    assert!(
        msg.contains(&format!("more than {MATHVERSE_LAZY_LOAD_BUDGET}")),
        "the error must state the cap: {msg}"
    );
    assert!(
        msg.contains("import Mathverse."),
        "the error must say how to proceed: {msg}"
    );
}

/// `lazy_budget_0 q (lazy_budget_1 q (… hq))` — `count` distinct library names
/// in one declaration, each `∀ p, p → p`, so the whole term has type `q`.
fn nested_citation(count: u8, name: &str) -> String {
    let mut body = "hq".to_string();
    for i in (0..count).rev() {
        body = format!("lazy_budget_{i} q ({body})");
    }
    format!("theorem lazy_{name} (q : Prop) (hq : q) : q := {body}")
}

// ---------------------------------------------------------------------------
// Interaction with the eager surface
// ---------------------------------------------------------------------------

/// A per-constant import still works, and a corpus import after it does not
/// disturb what is already resident.
#[test]
fn test_lazy_resolution_leaves_the_eager_per_constant_import_intact() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib.lazy_id_thm").expect("eager import still succeeds");
    assert!(resident(&env, "lazy_id_thm"));
    assert_eq!(
        env.get_option(MATHVERSE_ARMED_OPTION),
        None,
        "a per-constant import must NOT arm the corpus — arming is opt-in"
    );

    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");
    elab(
        &mut env,
        "theorem eager_then_lazy (q : Prop) (hq : q) : q := lazy_id_thm q hq",
    )
    .expect("the already-resident constant resolves without any retry");
}

/// A resident name is never re-requested. This is the PROGRESS rule that makes
/// the retry terminate independently of the budget, so pin it directly.
#[test]
fn test_lazy_resolution_never_requests_a_resident_name() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");
    elab(&mut env, "import Mathverse.Mathlib.lazy_id_thm").expect("eager import succeeds");

    // `lazy_id_thm` is resident, so this failure is a TYPE error and must be
    // reported as one — a re-request would have produced a Mathverse message
    // (and, with a name that can never become "more resident", a loop).
    let err = elab(
        &mut env,
        "theorem resident_mismatch (q r : Prop) (hq : q) : r := lazy_id_thm q hq",
    )
    .expect_err("an ill-typed use of a resident constant must be refused");
    let msg = err.to_string();
    assert!(
        !msg.contains("Mathverse"),
        "a resident name must never be re-requested: {msg}"
    );
}

/// Set-option trust widening still applies to the lazy path, because it is the
/// same gate: `relaxed` remains unreachable from source.
#[test]
fn test_lazy_resolution_cannot_reach_the_relaxed_trust_gate() {
    let _fixture = LazyFixture::new();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib").expect("corpus import succeeds");
    env.set_option("mathverse.trust".to_string(), Some("relaxed".to_string()));

    let err = elab(
        &mut env,
        "theorem relaxed_use (q : Prop) (hq : q) : q := lazy_untrusted_thm q hq",
    )
    .expect_err("`relaxed` is deliberately not reachable from source");
    assert!(
        err.to_string().contains("not available from source"),
        "got: {}",
        err.to_string()
    );
}
