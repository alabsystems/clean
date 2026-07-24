// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean auto prove` (SMT/ATP automation entry point).
//!
//! Epic #3436 Phase 4, issue #3454. The top-level `auto` verb is a nested
//! aggregator so that future automation verbs (`auto premise`, `auto smt`,
//! `auto atp`, …) can drop in without reshaping the clap tree. The descriptor
//! is registered as `Stability::Experimental` because `clean-auto`
//! intentionally does not yet commit to a stable library API — see issue
//! #3454 for the input-schema decision that blocks a full stable surface.
//!
//! Design: `designs/2026-04-18-cli-orphan-inventory.md` §4.4 and
//! `designs/2026-04-18-unified-cli-feature-index.md`.
//!
//! The module is gated behind the `cli` Cargo feature so non-CLI consumers of
//! `clean-auto` keep a minimal dependency graph (no clap, no
//! `clean-features`).
//!
//! # Input schema (Experimental MVP)
//!
//! The issue lists three candidate input formats (`.lean` snippet, SMT-LIB
//! S-expression, JSON of kernel `Expr`). The MVP intentionally defers that
//! decision by exposing a small bundled *demo catalog* via
//! `--demo <NAME>` / `--list` (mirroring `clean verify rust --example
//! <NAME>` / `--list`). Each demo constructs a kernel goal in Rust,
//! calls [`AutomationEngine::auto_prove`] with a caller-controlled budget
//! (`--budget <MS>`), and prints the outcome. When the goal/hypothesis
//! encoding decision lands on the issue, this module grows `--goal <FILE>`
//! / `--hypotheses <FILE>` flags without reshaping the existing surface.

use std::time::Duration;

use clap::{Args, Subcommand};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_kernel::{env::Declaration, BinderInfo, Environment, Expr, Level, Name};

use crate::AutomationEngine;

#[path = "cli_premise.rs"]
mod cli_premise;

pub use cli_premise::{
    rank_goal as rank_premise_goal, run as run_premise, PremiseArgs, PremiseClassification,
    PremiseCliError, PremiseEnvironment, RankedPremise, PREMISE_FEATURES,
};

// -- Arguments ----------------------------------------------------------------

/// Top-level `clean auto` aggregator. Nested so sibling verbs (premise
/// selection, standalone SMT, ATP) can drop in without churn.
#[derive(Debug, clap::Args)]
pub struct AutoArgs {
    /// Verb under `clean auto`.
    #[command(subcommand)]
    pub command: AutoCommands,
}

/// Verbs under `clean auto <verb>`.
///
/// `#[non_exhaustive]` so Phase 4+ additions (e.g. `auto premise`,
/// `auto smt`) can land without breaking downstream tooling.
#[derive(Debug, Subcommand)]
#[non_exhaustive]
pub enum AutoCommands {
    /// Prove a bundled demo goal via the clean-auto AutomationEngine
    /// (Experimental).
    Prove(AutoProveArgs),
    /// Rank candidate premises for a free-text goal string (Experimental).
    Premise(PremiseArgs),
}

/// Arguments for `clean auto prove`.
///
/// The MVP exposes a small named-demo catalog (`--demo <NAME>`) and a
/// `--list` flag that prints the catalog. Exactly one of the two must be
/// supplied. `--budget <MS>` controls the AutomationEngine timeout;
/// `--verbose` prints per-stage detail.
#[derive(Debug, Clone, Args)]
pub struct AutoProveArgs {
    /// Name of a bundled demo goal to prove (see `--list`).
    #[arg(long, value_name = "NAME", conflicts_with = "list")]
    pub demo: Option<String>,
    /// List every bundled demo goal and exit.
    #[arg(long)]
    pub list: bool,
    /// Search budget in milliseconds (default: 5000).
    #[arg(long, value_name = "MS", default_value_t = 5_000)]
    pub budget: u64,
    /// Print per-stage detail (proof term snippet, elapsed time).
    #[arg(short, long)]
    pub verbose: bool,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean auto prove` dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum AutoCliError {
    /// Caller passed neither `--demo <NAME>` nor `--list`.
    #[error("`clean auto prove` requires either --demo <NAME> or --list")]
    NoAction,
    /// Requested demo name is not in the bundled catalog.
    #[error("unknown demo `{name}`; run `clean auto prove --list` to see known names")]
    UnknownDemo {
        /// Name that was requested.
        name: String,
    },
    /// AutomationEngine exhausted its budget without producing a proof.
    ///
    /// Not a hard error in the CLI sense — the command still exits non-zero
    /// so shell callers can detect "no proof found" without parsing stdout.
    #[error("no proof found for demo `{name}` within {budget_ms} ms")]
    NoProof {
        /// Demo name that failed to prove.
        name: String,
        /// Budget (in ms) the caller supplied.
        budget_ms: u64,
    },
}

// -- Demo catalog -------------------------------------------------------------

/// One bundled demo goal. Self-contained — every demo owns its goal
/// construction (`build`) because each demo may want a bespoke minimal
/// environment. The catalog is tiny on purpose (Experimental): it exercises
/// the end-to-end [`AutomationEngine::auto_prove`] path without depending on
/// kernel stdlib `.olean` loading.
pub struct Demo {
    /// CLI-visible name (`--demo <NAME>`).
    pub name: &'static str,
    /// One-line description printed by `--list`.
    pub description: &'static str,
    /// Construct the environment and the goal expression.
    pub build: fn() -> (Environment, Expr),
}

/// Return the bundled demo catalog.
///
/// Kept as a function rather than a `const` because the bodies allocate
/// kernel `Expr` / `Environment` state on call.
#[must_use]
pub fn catalog() -> &'static [Demo] {
    DEMOS
}

const DEMOS: &[Demo] = &[Demo {
    name: "eq_refl",
    description: "Prove `Eq A a a` via reflexivity (SMT equality lane).",
    build: build_eq_refl_demo,
}];

/// Build the `Eq A a a` goal with a minimal environment containing `Eq`,
/// `Eq.refl`, a carrier type `A`, and a constant `a : A`.
///
/// Mirrors the `setup_env_with_eq` fixture in `crates/clean-auto/src/tests.rs`
/// so the CLI exercises the same SMT equality lane covered by unit tests.
fn build_eq_refl_demo() -> (Environment, Expr) {
    let mut env = Environment::new();

    // Eq : {α : Sort u} → α → α → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .expect("invariant: literal Eq axiom declaration kernel-checks");

    // Eq.refl : ∀ {α : Sort u} (a : α), Eq a a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .expect("invariant: literal Eq.refl axiom declaration kernel-checks");

    // A : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("invariant: literal A axiom declaration kernel-checks");

    // a : A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .expect("invariant: literal a axiom declaration kernel-checks");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    // Goal: Eq A a a (instantiated at level 1 — matches the test fixture).
    let goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            a.clone(),
        ),
        a,
    );
    (env, goal)
}

/// Print the bundled catalog in a human-readable layout.
pub fn print_catalog() {
    println!("Clean auto prove — bundled demo catalog:");
    for demo in catalog() {
        println!("  {:<12} {}", demo.name, demo.description);
    }
}

// -- Public entry points ------------------------------------------------------

/// Dispatch entry point for `clean auto prove`. Called from the top-level
/// `clean-cli` binary via `cmd_auto::handle_auto_prove`.
pub fn run(args: AutoProveArgs) -> Result<(), AutoCliError> {
    if args.list {
        print_catalog();
        return Ok(());
    }
    let Some(name) = args.demo.as_deref() else {
        return Err(AutoCliError::NoAction);
    };
    let demo =
        catalog()
            .iter()
            .find(|d| d.name == name)
            .ok_or_else(|| AutoCliError::UnknownDemo {
                name: name.to_owned(),
            })?;

    let (env, goal) = (demo.build)();
    let engine = AutomationEngine::new();
    let start = std::time::Instant::now();
    let outcome = engine.auto_prove(&env, &goal, Duration::from_millis(args.budget), None);
    let elapsed = start.elapsed();

    match outcome {
        Some(proof) => {
            println!("Clean auto prove --demo {name}: VERIFIED");
            println!("  description: {}", demo.description);
            println!("  elapsed: {} ms", elapsed.as_millis());
            if args.verbose {
                println!("  engine_reported_ms: {}", proof.time_ms());
                // proof_text() may be multi-line; print as indented block.
                let text = proof.proof_text();
                if !text.is_empty() {
                    println!("  proof_text:");
                    for line in text.lines() {
                        println!("    {line}");
                    }
                }
            }
            Ok(())
        }
        None => {
            println!(
                "Clean auto prove --demo {name}: NO PROOF within {} ms",
                args.budget
            );
            Err(AutoCliError::NoProof {
                name: name.to_owned(),
                budget_ms: args.budget,
            })
        }
    }
}

// -- Feature descriptor registry ---------------------------------------------

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "CLI orphan inventory — clean-auto",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3454: Reference = Reference {
    kind: RefKind::Issue,
    label: "Add clean auto prove (Experimental)",
    target: "#3454",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-auto",
    target: "clean-auto",
};

/// Feature descriptors surfaced by the automation crate.
///
/// Registered into the top-level CLI by
/// `clean-cli/src/registry.rs::all_features()`. The path is nested
/// (`["auto", "prove"]`) so sibling automation verbs (`auto premise`,
/// `auto smt`, …) can drop in without rewriting the top-level clap tree.
const PROVE_FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["auto", "prove"],
    domain_root: Some("auto"),
    alternative_forms: &[],
    feature_gate: None,
    summary: "Prove a bundled demo goal via clean-auto AutomationEngine (Experimental)",
    description: "\
Run a bundled demo goal through the clean-auto AutomationEngine — the same \
SMT / superposition / premise-selection pipeline exercised by the crate's \
unit tests. Pass `--list` to enumerate the catalog, or `--demo <NAME>` to \
prove one goal. `--budget <MS>` sets the search timeout (default 5000 ms); \
`--verbose` prints the engine-reported time and a proof-term snippet. \
Marked `Stability::Experimental` because the crate does not yet commit to \
a stable library API and because the long-term CLI input schema — issue \
#3454 lists three candidates (`.lean`, SMT-LIB, JSON `Expr`) — is an open \
decision. Once that decision lands, this verb grows `--goal <FILE>` / \
`--hypotheses <FILE>` without reshaping the existing surface. Part of \
Epic #3436 (#3454).",
    category: Category::Proof,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean auto prove --list",
            what: "list every bundled demo goal the automation engine can prove",
        },
        Example {
            cmd: "clean auto prove --demo eq_refl",
            what: "prove the bundled `Eq A a a` reflexivity goal",
        },
        Example {
            cmd: "clean auto prove --demo eq_refl --budget 2000 --verbose",
            what: "prove the reflexivity demo with a 2-second budget and print per-stage detail",
        },
    ],
    see_also: &["verify-c", "verify rust", "check"],
    references: &[
        DESIGN_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3454,
        CRATE_REF,
    ],
}];

pub const FEATURES: &[FeatureDescriptor] = &[PROVE_FEATURES[0], PREMISE_FEATURES[0]];

/// Compile-time assertion that [`FEATURES`] is non-empty. Guards against
/// accidentally shipping an empty descriptor array, which would silently
/// disappear from `clean features` without any drift-test failure.
const _: () = {
    assert!(
        !FEATURES.is_empty(),
        "clean-auto cli must expose at least one FeatureDescriptor"
    );
    let _: &[FeatureDescriptor] = FEATURES;
};

#[cfg(test)]
mod tests;
