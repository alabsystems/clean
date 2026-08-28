// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! THE DEFAULT-PRELUDE AXIOM CENSUS AND RATCHET.
//!
//! # The coverage hole this closes
//!
//! CLAUDE.md's first soundness rule is that "prove" means a theorem's
//! transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`, and that the
//! domain-specific axiom count is a first-class metric that only goes down.
//! Two artifacts enforce that today and **neither one looks at the environment
//! `clean check` actually loads**:
//!
//! * `data/soundness_tcb.json` (C2 of the Soundness Certificate) pins a
//!   3-axiom trusted base — `{Classical.choice, Quot.sound, propext}` — over
//!   [`Environment::soundness_certificate_env`], which is `Environment::new()`
//!   plus the NN/math overlays. It never calls `with_prelude()`.
//! * `data/axiom_audit.json` scopes its `total_domain_axioms = 0` to that same
//!   `soundness_tcb_mirror`, i.e. the kernel trusted base.
//!
//! The environment a user gets from a bare `clean check file.lean` is
//! `Environment::with_prelude()` plus three CLI-side registrars
//! (`init_monad_list_insts`, `init_io_ops`, `init_ulift` —
//! `crates/clean-cli/src/cmd_core.rs:66-104`). Measured at the commit that
//! added this file, it held **300** `Axiom`-kind constants, 293 of them
//! non-foundational — including three real Mathlib theorems asserted as axioms
//! (`Nat.lt_succ_iff`, `Nat.mul_lt_mul`, `Nat.mul_lt_mul_right`) and the four
//! trust markers. Neither artifact above moves by one when an axiom is added
//! there. This module is that missing coverage.
//!
//! **#49 (2026-08-27).** Four of the six asserted propositions that census
//! found were drained: those three Mathlib lemmas and the `instIrreflNatLt`
//! instance are now kernel-checked declarations with empty axiom closures
//! (`nat_lt_succ_iff_proof.rs`, `nat_mul_lt_mul_proof.rs`,
//! `nat_irrefl_instance_proof.rs`). The live census is **296** axioms, 289
//! non-foundational, **2** asserted propositions — `Fact.mk` and `Fact.out`,
//! which are deliberately value-less stubs so a source or `.olean`
//! redeclaration of Mathlib's genuine `class Fact` can discharge them
//! (`clean-elab/src/register.rs`; `Environment::discharge_axiom_stub_for_inductive_import`
//! only ever removes a value-less `Axiom`). Giving `Fact` real content would
//! retire both and break that discharge, so they stay pinned here rather than
//! being quietly proved.
//!
//! # Not a second taxonomy
//!
//! The buckets come from [`super::soundness_certificate::partition_axioms`] —
//! the same partition C2 uses — so "foundational", "admitted domain", "trust
//! marker" and "builtin quotient primitive" mean exactly what they mean in the
//! certificate. This module adds exactly one distinction the certificate does
//! not need, because on its overlay env the `other` bucket is empty:
//!
//! * **`debt_proposition`** — an axiom whose type is a `Prop`. This asserts a
//!   mathematical statement the kernel never checked. It is genuine
//!   domain-specific debt in CLAUDE.md's sense: a proof reaching one is not a
//!   proof.
//! * **`debt_signature`** — an axiom whose type is data (`Sort u`, `u ≠ 0`) or
//!   a type former. This is an uninterpreted symbol — a declared name with no
//!   definition, the shape `Set.union` / `Subgroup.carrier` / `IO` have. It
//!   asserts no proposition, so it cannot make a false statement provable on
//!   its own; it is API-completeness debt, and it is counted separately rather
//!   than being laundered into the same number as the propositions.
//!
//! The split is computed by the kernel (`infer_type` of the declared type,
//! `is_def_eq` against `Sort 0`), never by reading a name.
//!
//! # What the gate refuses
//!
//! 1. **A new non-foundational axiom.** Every live name outside the
//!    foundational and builtin-quotient buckets must be pinned in
//!    `data/prelude_axiom_ratchet.json`. Adding one to any `init_*` reddens
//!    this test.
//! 2. **A rising count.** Each bucket's live size must be `<=` its baseline,
//!    so the census is monotone down.
//! 3. **A widened foundation.** The live foundational set must be a subset of
//!    the pinned one — promoting a domain axiom into `FOUNDATIONAL_AXIOMS` is
//!    the cheap way to make this gate green, and it is refused.
//! 4. **A theorem that reaches debt.** THE LOAD-BEARING CLAIM: every
//!    `Theorem`-kind constant in the default environment must have an empty
//!    `axiom_deps` (its non-foundational transitive closure), except for names
//!    explicitly pinned in `theorems_reaching_debt`. Measured at the commit
//!    that added this file: **0 of 336**; after #49, **0 of 339**. A theorem
//!    the repo calls proved whose closure reaches an asserted proposition would
//!    be a trust claim that needs correcting, and this is the check that says
//!    so.
//! 5. **Vacuity, three ways.** (a) Floors on declarations and theorems, so a
//!    failed or tiny environment fails instead of reporting an empty census as
//!    a pass. (b) A floor on `theorems_reaching_foundational`: if the closure
//!    walk silently started returning empty sets, refusal 4 would go green for
//!    the wrong reason, so the gate requires that a large number of theorems
//!    DO reach a foundational axiom. (c) A ceiling on value-less
//!    `Theorem`-kind constants — those have no proof term for the walk to
//!    follow, so an empty closure says nothing about them.
//!
//! # Falsifiability
//!
//! Two always-on positive controls in this file drive the **real** predicate
//! functions ([`new_axiom_problems`], [`theorem_debt_problems`]) against a
//! deliberately-corrupted environment, in the same cargo invocation as the
//! gate:
//!
//! * `..._refuses_a_theorem_that_wraps_a_prelude_axiom` registers
//!   `theorem PreludeAxiomProbe.wrapsFactOut : <type of Fact.out>
//!   := Fact.out` — kernel-accepted, and *exactly* the shape CLAUDE.md
//!   names as "NOT a proof" — and requires refusal 4 to fire naming
//!   `Fact.out`. (It wrapped `Nat.lt_succ_iff` until #49 proved that one; the
//!   control asserts its target is still an axiom, so it fails loudly rather
//!   than going vacuous when its target is drained.)
//! * `..._refuses_a_newly_planted_axiom` registers a fresh `Prop`-typed axiom
//!   and requires refusal 1 to fire and the census to route it to
//!   `debt_proposition`.
//!
//! Neither needs a tree mutation, neither can drift away from the gate (same
//! file, same invocation), and both fail if the predicate is gutted.
//!
//! # Regenerating
//!
//! ```text
//! CLEAN_PRELUDE_AXIOM_RATCHET_UPDATE=1 \
//!   cargo test -p clean-kernel --lib -- prelude_axiom_ratchet
//! ```
//!
//! writes the measured census back into `data/prelude_axiom_ratchet.json` for
//! review. A raise is a reviewed, diff-visible event; a fall needs no review
//! and is exactly what draining the debt looks like.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use super::axiom_audit::is_foundational_axiom;
use super::soundness_certificate::partition_axioms;
use super::types::{ConstantKind, Declaration};
use super::Environment;
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// The checked-in ratchet. Read at RUNTIME (not `include_str!`) so replaying a
/// mutation arm costs no `clean-kernel` recompile.
fn ratchet_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../data/prelude_axiom_ratchet.json")
}

/// Build the environment a bare `clean check <file>` loads.
///
/// This is `Environment::with_prelude()` plus the three registrars the CLI
/// applies before it elaborates a single line, mirrored from
/// `crates/clean-cli/src/cmd_core.rs:66-104` (`PreludeMode::Builtin`, the
/// default). Censusing `with_prelude()` alone would UNDER-count: `init_io_ops`
/// registers a family of `IO.*` axioms that every default `clean check` run
/// carries (11 constants, measured).
///
/// The kernel cannot depend on `clean-cli`, so the mirror is by construction,
/// and `prelude_axiom_census_mirrors_the_cli_check_environment` pins the fact
/// that each mirrored registrar is reachable and contributes.
fn check_default_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_monad_list_insts()
        .expect("invariant: init_monad_list_insts is idempotent on with_prelude()");
    env.init_io_ops()
        .expect("invariant: init_io_ops is idempotent on with_prelude()");
    env.init_ulift()
        .expect("invariant: init_ulift is idempotent on with_prelude()");
    env
}

/// The measured census of one environment.
#[derive(Debug, Default)]
struct PreludeAxiomCensus {
    total_declarations: usize,
    theorems: usize,
    /// `Theorem`-kind constants with no stored proof value
    /// (`ProofQuality::Unchecked`). The closure walk has no proof term to
    /// follow for these, so their empty `axiom_deps` proves nothing.
    theorems_without_value: usize,
    /// Theorems whose closure reaches at least one FOUNDATIONAL axiom. This is
    /// the liveness control on the walk itself.
    theorems_reaching_foundational: usize,
    /// Every `Axiom`-kind constant, builtin quotient primitives included.
    axioms_total: usize,
    /// Kernel-implemented quotient primitives (`Quot`, `Quot.mk`, `Quot.lift`,
    /// `Quot.ind`) — part of the kernel checker, not the axiom allowlist.
    quotient_primitives: BTreeSet<String>,
    /// `is_foundational_axiom` — the logical foundation.
    foundational: BTreeSet<String>,
    /// `sorry` / `sorryAx` / `trustedArith` / `trustedAy`.
    trust_markers: BTreeSet<String>,
    /// `ADMITTED_DOMAIN_AXIOMS`.
    admitted_domain: BTreeSet<String>,
    /// Non-foundational, `Prop`-typed: an asserted mathematical statement.
    debt_proposition: BTreeSet<String>,
    /// Non-foundational, data-typed: an uninterpreted symbol.
    debt_signature: BTreeSet<String>,
    /// Non-foundational axioms whose type the kernel could not classify.
    /// Counted separately and NEVER folded into either debt bucket — an
    /// unclassifiable type is the absence of information, not a signature.
    unknown_sort: BTreeSet<String>,
    /// Theorem name -> the sorted non-foundational axioms its transitive
    /// closure reaches. Empty for a genuinely proved theorem.
    theorems_reaching_debt: BTreeMap<String, Vec<String>>,
}

impl PreludeAxiomCensus {
    /// Every non-foundational, non-quotient-primitive axiom name — the set the
    /// ratchet pins by name.
    fn pinned_names(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        for set in [
            &self.trust_markers,
            &self.admitted_domain,
            &self.debt_proposition,
            &self.debt_signature,
            &self.unknown_sort,
        ] {
            out.extend(set.iter().cloned());
        }
        out
    }

    fn non_foundational_total(&self) -> usize {
        self.pinned_names().len()
    }
}

/// Classify one axiom's declared type as `Prop` / data / unknown.
///
/// `infer_type` of a declaration's TYPE yields its sort. `Fact.out`'s
/// type is a `∀`-telescope ending in the bound `p : Prop`, whose sort is
/// `Sort 0` by impredicativity, so the axiom asserts a proposition. (The
/// worked example here used to be `Nat.lt_succ_iff` — a `∀`-telescope over an
/// `Iff` — until #49 proved it.) `Set.union`'s type is a
/// telescope over `Set α`, whose sort is `Sort (u+1)`, so the axiom declares an
/// uninterpreted symbol. The comparison goes through `is_def_eq` rather than a
/// syntactic `is_prop`, so an unnormalized `imax` sort is still recognized.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AxiomTypeClass {
    Proposition,
    Signature,
    Unknown,
}

fn classify_axiom_type(env: &Environment, ty: &Expr) -> AxiomTypeClass {
    let tc = TypeChecker::new(env);
    match tc.infer_type(ty) {
        Ok(sort) => {
            if tc.is_def_eq(&sort, &Expr::prop()) {
                AxiomTypeClass::Proposition
            } else {
                AxiomTypeClass::Signature
            }
        }
        Err(_) => AxiomTypeClass::Unknown,
    }
}

/// Census `env` through the certificate's own axiom partition.
fn census(env: &Environment) -> PreludeAxiomCensus {
    let partition = partition_axioms(env);
    let mut out = PreludeAxiomCensus {
        quotient_primitives: partition.builtin_quot.iter().cloned().collect(),
        foundational: partition.foundational.iter().cloned().collect(),
        trust_markers: partition.trust.iter().cloned().collect(),
        admitted_domain: partition.admitted_domain.iter().cloned().collect(),
        ..PreludeAxiomCensus::default()
    };

    // The certificate's `other` bucket — the names that are neither
    // foundational, nor admitted-domain, nor trust markers, nor quotient
    // primitives — is exactly this surface's debt. Split it by type.
    let other: BTreeSet<String> = partition.other.iter().cloned().collect();

    let constants: Vec<_> = env
        .constants()
        .map(|c| (c.name.clone(), c.kind, c.type_.clone(), c.value.is_some()))
        .collect();
    out.total_declarations = constants.len();

    for (name, kind, ty, has_value) in &constants {
        match kind {
            ConstantKind::Axiom => {
                out.axioms_total += 1;
                let s = name.to_string();
                if other.contains(&s) {
                    match classify_axiom_type(env, ty) {
                        AxiomTypeClass::Proposition => {
                            out.debt_proposition.insert(s);
                        }
                        AxiomTypeClass::Signature => {
                            out.debt_signature.insert(s);
                        }
                        AxiomTypeClass::Unknown => {
                            out.unknown_sort.insert(s);
                        }
                    }
                }
            }
            ConstantKind::Theorem => {
                out.theorems += 1;
                if !has_value {
                    out.theorems_without_value += 1;
                }
                // `axiom_deps` is the transitive closure MINUS the
                // foundational axioms — precisely CLAUDE.md's "prove" rule.
                if let Some(deps) = env.axiom_deps(name) {
                    if !deps.is_empty() {
                        let mut v: Vec<String> = deps.iter().map(ToString::to_string).collect();
                        v.sort();
                        out.theorems_reaching_debt.insert(name.to_string(), v);
                    }
                }
                // Liveness control: the SAME walk, complementary half.
                if env
                    .foundational_axiom_deps(name)
                    .is_some_and(|f| !f.is_empty())
                {
                    out.theorems_reaching_foundational += 1;
                }
            }
            _ => {}
        }
    }

    out
}

// ═══════════════════════════ the ratchet file ═══════════════════════════

fn load_ratchet() -> serde_json::Value {
    let path = ratchet_path();
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("cannot parse {}: {e}", path.display()))
}

fn pinned_set(ratchet: &serde_json::Value, key: &str) -> BTreeSet<String> {
    ratchet
        .get(key)
        .and_then(serde_json::Value::as_array)
        .map(|a| {
            a.iter()
                .filter_map(|v| v.as_str().map(ToOwned::to_owned))
                .collect()
        })
        .unwrap_or_default()
}

fn pinned_usize(ratchet: &serde_json::Value, key: &str) -> usize {
    let n = ratchet
        .get(key)
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_else(|| panic!("data/prelude_axiom_ratchet.json is missing `{key}`"));
    usize::try_from(n).unwrap_or(usize::MAX)
}

// ═══════════════════════════ the gate predicates ═════════════════════════
//
// Both refusals are FUNCTIONS returning the problems they found, so the
// positive controls below can drive the real predicate against a corrupted
// environment instead of re-implementing it.

/// Refusals 1-3: a new non-foundational axiom, a risen count, a widened
/// foundation.
fn new_axiom_problems(c: &PreludeAxiomCensus, r: &serde_json::Value) -> Vec<String> {
    let mut problems = Vec::new();

    let mut pinned = pinned_set(r, "trust_markers");
    pinned.extend(pinned_set(r, "admitted_domain"));
    pinned.extend(pinned_set(r, "debt_proposition"));
    pinned.extend(pinned_set(r, "debt_signature"));
    pinned.extend(pinned_set(r, "unknown_sort"));

    let live = c.pinned_names();
    let added: Vec<&String> = live.difference(&pinned).collect();
    if !added.is_empty() {
        problems.push(format!(
            "NEW NON-FOUNDATIONAL AXIOM in the DEFAULT `clean check` environment: {added:?}"
        ));
    }

    for (key, live_count) in [
        ("baseline_axioms_total", c.axioms_total),
        ("baseline_non_foundational", c.non_foundational_total()),
        ("baseline_debt_proposition", c.debt_proposition.len()),
        ("baseline_debt_signature", c.debt_signature.len()),
        ("baseline_unknown_sort", c.unknown_sort.len()),
        ("baseline_trust_markers", c.trust_markers.len()),
        ("baseline_admitted_domain", c.admitted_domain.len()),
    ] {
        let baseline = pinned_usize(r, key);
        if live_count > baseline {
            problems.push(format!(
                "RATCHET `{key}` rose: live {live_count} > baseline {baseline}"
            ));
        }
    }

    let pinned_foundational = pinned_set(r, "foundational");
    let widened: Vec<&String> = c.foundational.difference(&pinned_foundational).collect();
    if !widened.is_empty() {
        problems.push(format!(
            "FOUNDATIONAL_AXIOMS WIDENED: {widened:?} is now classified foundational and was not"
        ));
    }

    problems
}

/// Refusal 4: a theorem whose non-foundational closure is non-empty and not
/// pinned.
fn theorem_debt_problems(c: &PreludeAxiomCensus, r: &serde_json::Value) -> Vec<String> {
    let allowed: BTreeSet<String> = r
        .get("theorems_reaching_debt")
        .and_then(serde_json::Value::as_object)
        .map(|o| o.keys().cloned().collect())
        .unwrap_or_default();

    c.theorems_reaching_debt
        .iter()
        .filter(|(name, _)| !allowed.contains(*name))
        .map(|(name, deps)| format!("{name} -> {deps:?}"))
        .collect()
}

/// `(definitions, definitions whose non-foundational closure is non-empty)`.
///
/// A whole-environment BFS per definition, so it is measured on demand rather
/// than inside [`census`] — see
/// `prelude_axiom_census_definition_exposure_does_not_grow`.
fn definition_exposure(env: &Environment) -> (usize, BTreeMap<String, Vec<String>>) {
    let names: Vec<Name> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Definition)
        .map(|c| c.name.clone())
        .collect();
    let mut exposed = BTreeMap::new();
    for n in &names {
        if let Some(deps) = env.axiom_deps(n) {
            if !deps.is_empty() {
                let mut v: Vec<String> = deps.iter().map(ToString::to_string).collect();
                v.sort();
                exposed.insert(n.to_string(), v);
            }
        }
    }
    (names.len(), exposed)
}

/// Serialize the measured census in the ratchet's on-disk shape.
fn census_as_ratchet(
    c: &PreludeAxiomCensus,
    doc: &serde_json::Value,
    exposure: &(usize, BTreeMap<String, Vec<String>>),
) -> String {
    let debt_map: serde_json::Map<String, serde_json::Value> = c
        .theorems_reaching_debt
        .iter()
        .map(|(k, v)| (k.clone(), serde_json::json!(v)))
        .collect();
    let value = serde_json::json!({
        "_schema": "clean-prelude-axiom-ratchet-v1",
        "_doc": doc.clone(),
        "baseline_axioms_total": c.axioms_total,
        "baseline_non_foundational": c.non_foundational_total(),
        "baseline_debt_proposition": c.debt_proposition.len(),
        "baseline_debt_signature": c.debt_signature.len(),
        "baseline_unknown_sort": c.unknown_sort.len(),
        "baseline_trust_markers": c.trust_markers.len(),
        "baseline_admitted_domain": c.admitted_domain.len(),
        "ceiling_theorems_without_value": c.theorems_without_value,
        "ceiling_definitions_reaching_debt": exposure.1.len(),
        "floor_total_definitions": exposure.0,
        "floor_total_declarations": c.total_declarations,
        "floor_theorems": c.theorems,
        "floor_theorems_reaching_foundational": c.theorems_reaching_foundational,
        "foundational": c.foundational.iter().collect::<Vec<_>>(),
        "quotient_primitives": c.quotient_primitives.iter().collect::<Vec<_>>(),
        "trust_markers": c.trust_markers.iter().collect::<Vec<_>>(),
        "admitted_domain": c.admitted_domain.iter().collect::<Vec<_>>(),
        "debt_proposition": c.debt_proposition.iter().collect::<Vec<_>>(),
        "debt_signature": c.debt_signature.iter().collect::<Vec<_>>(),
        "unknown_sort": c.unknown_sort.iter().collect::<Vec<_>>(),
        "theorems_reaching_debt": serde_json::Value::Object(debt_map),
        "definitions_reaching_debt": serde_json::Value::Object(
            exposure
                .1
                .iter()
                .map(|(k, v)| (k.clone(), serde_json::json!(v)))
                .collect::<serde_json::Map<String, serde_json::Value>>(),
        ),
    });
    format!(
        "{}\n",
        serde_json::to_string_pretty(&value).unwrap_or_default()
    )
}

fn maybe_update(env: &Environment, c: &PreludeAxiomCensus) {
    if std::env::var("CLEAN_PRELUDE_AXIOM_RATCHET_UPDATE").as_deref() != Ok("1") {
        return;
    }
    let path = ratchet_path();
    let doc = std::fs::read_to_string(&path)
        .ok()
        .and_then(|t| serde_json::from_str::<serde_json::Value>(&t).ok())
        .and_then(|v| v.get("_doc").cloned())
        .unwrap_or(serde_json::Value::Null);
    std::fs::write(&path, census_as_ratchet(c, &doc, &definition_exposure(env)))
        .unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
    eprintln!("REGENERATED {}", path.display());
}

/// Refusal 5 — the three anti-vacuity guards, shared by both gate tests.
fn assert_not_vacuous(c: &PreludeAxiomCensus, r: &serde_json::Value) {
    let floor_decls = pinned_usize(r, "floor_total_declarations");
    let floor_theorems = pinned_usize(r, "floor_theorems");
    let floor_foundational = pinned_usize(r, "floor_theorems_reaching_foundational");
    let ceiling_valueless = pinned_usize(r, "ceiling_theorems_without_value");
    assert!(
        c.total_declarations >= floor_decls,
        "VACUITY: the default check environment holds {} declarations, floor is {floor_decls}. \
         The census measured almost nothing; fix the environment, do not lower the floor.",
        c.total_declarations
    );
    assert!(
        c.theorems >= floor_theorems,
        "VACUITY: the default check environment holds {} theorems, floor is {floor_theorems}.",
        c.theorems
    );
    assert!(
        c.theorems_reaching_foundational >= floor_foundational,
        "VACUITY: only {} theorems reach a FOUNDATIONAL axiom (floor {floor_foundational}). \
         The axiom-closure walk has gone blind, so 'no theorem reaches debt' would be green \
         for the wrong reason.",
        c.theorems_reaching_foundational
    );
    assert!(
        c.theorems_without_value <= ceiling_valueless,
        "VACUITY: {} Theorem-kind constants carry NO proof value (ceiling {ceiling_valueless}). \
         A value-less theorem gives the closure walk nothing to follow, so its empty axiom_deps \
         is not evidence of a proof.",
        c.theorems_without_value
    );
}

// ═══════════════════════════════ the gate ═══════════════════════════════

#[test]
fn prelude_axiom_ratchet_no_new_non_foundational_axiom() {
    let env = check_default_env();
    let c = census(&env);
    maybe_update(&env, &c);
    let r = load_ratchet();

    assert_not_vacuous(&c, &r);

    let problems = new_axiom_problems(&c, &r);
    assert!(
        problems.is_empty(),
        "DEFAULT-PRELUDE AXIOM RATCHET:\n  {}\n\
         Every proof measured against this prelude can reach these axioms, and CLAUDE.md's \
         \"prove\" rule is closure ⊆ FOUNDATIONAL_AXIOMS. Either give the constant a real \
         kernel-checked value, or record the change in data/prelude_axiom_ratchet.json in a \
         reviewed diff (regenerate with CLEAN_PRELUDE_AXIOM_RATCHET_UPDATE=1). Counts are \
         flat-or-down; never raise a baseline to green a build.",
        problems.join("\n  ")
    );
}

#[test]
fn prelude_axiom_ratchet_no_theorem_rests_on_prelude_debt() {
    let env = check_default_env();
    let c = census(&env);
    let r = load_ratchet();

    assert_not_vacuous(&c, &r);

    let offenders = theorem_debt_problems(&c, &r);
    assert!(
        offenders.is_empty(),
        "A THEOREM IN THE DEFAULT `clean check` ENVIRONMENT RESTS ON NON-FOUNDATIONAL \
         PRELUDE DEBT:\n  {}\n\
         By CLAUDE.md's first soundness rule that theorem is not proved. Either discharge \
         the axiom it reaches, or pin the pair in data/prelude_axiom_ratchet.json's \
         `theorems_reaching_debt` with a reviewed justification.",
        offenders.join("\n  ")
    );

    // The crispest form of the claim, and the one that survives a future pin:
    // nothing the environment calls PROVED may reach an ASSERTED PROPOSITION.
    // A `theorems_reaching_debt` entry is a reviewed exception for a SIGNATURE
    // axiom (an uninterpreted symbol); it is never a licence to rest on an
    // unproved mathematical statement.
    assert!(
        reaches_no_asserted_proposition(&c.theorems_reaching_debt, &r).is_empty(),
        "A THEOREM RESTS ON AN ASSERTED PROPOSITION (a debt_proposition axiom), not merely \n\
         on an uninterpreted symbol:\n  {}\n\
         That theorem is not proved in CLAUDE.md's sense and no ratchet pin makes it one.",
        reaches_no_asserted_proposition(&c.theorems_reaching_debt, &r).join("\n  ")
    );
}

/// The subset of a `name -> reached axioms` map whose reached set contains an
/// axiom the ratchet classifies as `debt_proposition` — an asserted
/// mathematical statement rather than an uninterpreted symbol.
fn reaches_no_asserted_proposition(
    reached: &BTreeMap<String, Vec<String>>,
    r: &serde_json::Value,
) -> Vec<String> {
    let props = pinned_set(r, "debt_proposition");
    reached
        .iter()
        .filter(|(_, deps)| deps.iter().any(|d| props.contains(d)))
        .map(|(name, deps)| format!("{name} -> {deps:?}"))
        .collect()
}

// ═══════════════════════ always-on positive controls ═════════════════════

/// Refusal 4 must fire on the exact shape CLAUDE.md calls "NOT a proof".
///
/// `Declaration::Theorem` wrapping `Declaration::Axiom` type-checks — the
/// kernel accepts it, which is the whole problem — so only the closure audit
/// can object. The wrapper is built from the axiom's own declared type and
/// level parameters, so it is well-typed by construction for any axiom.
#[test]
fn prelude_axiom_ratchet_refuses_a_theorem_that_wraps_a_prelude_axiom() {
    let mut env = check_default_env();

    // #49 RETARGET: this control used to wrap `Nat.lt_succ_iff`, which is now a
    // kernel-checked Theorem (`nat_lt_succ_iff_proof.rs`), so it can no longer
    // serve as the axiom to wrap. `Fact.out` is the remaining
    // `debt_proposition` entry with the plainest type. When the `Fact` triple is
    // retired too, retarget again — do NOT weaken the precondition.
    let target = Name::from_string("Fact.out");
    let info = env
        .get_const(&target)
        .cloned()
        .expect("Fact.out is registered by the default prelude");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "control precondition: Fact.out must still be an AXIOM in the default prelude. \
         If it has been PROVED, retarget this control at another debt_proposition entry."
    );

    let probe = Name::from_string("PreludeAxiomProbe.wrapsFactOut");
    let levels: Vec<Level> = info
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    env.add_decl(Declaration::Theorem {
        name: probe.clone(),
        level_params: info.level_params.clone(),
        type_: info.type_.clone(),
        value: Expr::const_(target.clone(), levels),
    })
    .expect("a theorem restating an axiom's own type by its own name is well-typed");

    let c = census(&env);
    let r = load_ratchet();

    let deps = c
        .theorems_reaching_debt
        .get(&probe.to_string())
        .unwrap_or_else(|| {
            panic!(
                "THE GATE IS BLIND: a Theorem whose proof value IS the axiom `Fact.out` \
                 was not reported as reaching debt. {} theorems reach debt in this probe env.",
                c.theorems_reaching_debt.len()
            )
        });
    assert!(
        deps.iter().any(|d| d == "Fact.out"),
        "the wrapper's reported closure {deps:?} does not name the axiom it wraps"
    );

    let offenders = theorem_debt_problems(&c, &r);
    assert!(
        offenders.iter().any(|o| o.contains(&probe.to_string())),
        "refusal 4 did not fire on the planted wrapper; problems were {offenders:?}"
    );
}

/// Refusal 1 must fire on a freshly planted axiom, and the census must put it
/// in the right bucket.
///
/// The two plants pin the distinction the whole `debt_proposition` /
/// `debt_signature` split rests on, and it is easy to get backwards (this
/// control caught it being backwards once):
///
/// * `axiom h : True` — the type `True` is a `Prop`, so `h` is an ASSERTED
///   PROOF of a proposition the kernel never checked. `debt_proposition`.
/// * `axiom P : Prop` — the type `Prop` is a `Sort 1`, so `P` is an
///   uninterpreted PROPOSITION SYMBOL. It asserts nothing and cannot make a
///   false statement provable on its own. `debt_signature`.
#[test]
fn prelude_axiom_ratchet_refuses_a_newly_planted_axiom() {
    let mut env = check_default_env();

    let asserted = Name::from_string("PreludeAxiomProbe.plantedProposition");
    env.add_decl(Declaration::Axiom {
        name: asserted.clone(),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), Vec::<Level>::new()),
    })
    .expect("`axiom _ : True` is a well-formed declaration on the default prelude");

    let symbol = Name::from_string("PreludeAxiomProbe.plantedSymbol");
    env.add_decl(Declaration::Axiom {
        name: symbol.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("`axiom _ : Prop` is a well-formed declaration");

    let c = census(&env);
    let r = load_ratchet();

    assert!(
        c.debt_proposition.contains(&asserted.to_string()),
        "`axiom _ : True` was not classified as debt_proposition; it landed in \
         signature={} unknown={}",
        c.debt_signature.contains(&asserted.to_string()),
        c.unknown_sort.contains(&asserted.to_string())
    );
    assert!(
        c.debt_signature.contains(&symbol.to_string()),
        "`axiom _ : Prop` was not classified as debt_signature; it landed in \
         proposition={} unknown={}",
        c.debt_proposition.contains(&symbol.to_string()),
        c.unknown_sort.contains(&symbol.to_string())
    );

    let problems = new_axiom_problems(&c, &r);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("NEW NON-FOUNDATIONAL AXIOM")),
        "refusal 1 did not fire on a planted axiom; problems were {problems:?}"
    );
    assert!(
        problems
            .iter()
            .any(|p| p.contains("baseline_debt_proposition")),
        "refusal 2 did not fire on a risen debt_proposition count; problems were {problems:?}"
    );
}

/// How EXPOSED a user proof is: how many of the prelude's own definitions
/// already reach non-foundational debt.
///
/// Refusal 4 answers "does anything the prelude calls PROVED rest on debt?"
/// and the measured answer is no. That is a narrower fact than it reads as,
/// because a user's theorem inherits the closure of every constant it
/// mentions: `Set.union` is itself an axiom here, so `theorem foo : ... (A ∪ B)
/// ...` reaches debt on its first line without the user writing an axiom name.
/// This measures that exposure surface directly and ratchets it, so the honest
/// statement stays honest as definitions are added.
///
/// Kept out of [`census`] deliberately: it is a whole-environment BFS per
/// definition over ~1300 definitions, four times the cost of the theorem scan,
/// and the two gate tests do not need it.
#[test]
fn prelude_axiom_census_definition_exposure_does_not_grow() {
    let env = check_default_env();
    let r = load_ratchet();

    let (total, exposed) = definition_exposure(&env);

    let floor_total = pinned_usize(&r, "floor_total_definitions");
    let ceiling = pinned_usize(&r, "ceiling_definitions_reaching_debt");
    assert!(
        total >= floor_total,
        "VACUITY: {total} definitions in the default environment, floor is {floor_total}"
    );

    let pinned: BTreeSet<String> = r
        .get("definitions_reaching_debt")
        .and_then(serde_json::Value::as_object)
        .map(|o| o.keys().cloned().collect())
        .unwrap_or_default();
    let newly: Vec<String> = exposed
        .iter()
        .filter(|(name, _)| !pinned.contains(*name))
        .map(|(name, deps)| format!("{name} -> {deps:?}"))
        .collect();
    assert!(
        newly.is_empty(),
        "A DEFINITION IN THE DEFAULT `clean check` ENVIRONMENT NOW REACHES NON-FOUNDATIONAL \
         DEBT:\n  {}\n\
         Every user theorem that mentions it inherits that closure and stops being a proof \
         under CLAUDE.md's rule, WITHOUT the user ever writing an axiom name. Discharge the \
         axiom, or pin the definition in data/prelude_axiom_ratchet.json.",
        newly.join("\n  ")
    );
    assert!(
        exposed.len() <= ceiling,
        "DEFINITION EXPOSURE ROSE: {} of {total} definitions reach non-foundational debt \
         (ceiling {ceiling}). It only goes down.",
        exposed.len()
    );
    // Measured at the commit that added this file: all 15 exposed definitions
    // reach only SIGNATURE axioms (`Bind.bind`, `Monad`, `Pure.pure`,
    // `Nat.shiftRight`, `Set.mem`). NONE reaches one of the six asserted
    // propositions, so those six are unreachable unless a user names them.
    // That is the whole content of "no proof here rests on unproved
    // mathematics", and it is enforced rather than described.
    let via_prop = reaches_no_asserted_proposition(&exposed, &r);
    assert!(
        via_prop.is_empty(),
        "A DEFINITION NOW REACHES AN ASSERTED PROPOSITION:\n  {}\n\
         Every user theorem that mentions it silently rests on unproved mathematics.",
        via_prop.join("\n  ")
    );
    eprintln!(
        "PRELUDE DEFINITION EXPOSURE: {}/{total} reach non-foundational debt",
        exposed.len()
    );
}

/// The census must keep measuring the CLI's environment, not a subset of it.
///
/// `check_default_env` mirrors three registrars the kernel cannot call through
/// `clean-cli`. If one of them stops contributing — renamed, folded into
/// `with_prelude`, or dropped from the check path — the mirror silently starts
/// censusing a smaller environment than the one users get. This pins that each
/// mirrored registrar is still reachable and that the CLI-side environment is
/// strictly larger than the bare prelude.
#[test]
fn prelude_axiom_census_mirrors_the_cli_check_environment() {
    let bare = Environment::with_prelude();
    let full = check_default_env();
    assert!(
        full.constants().count() > bare.constants().count(),
        "check_default_env() added nothing over Environment::with_prelude(): the CLI mirror \
         (init_monad_list_insts / init_io_ops / init_ulift) has gone inert, so this census \
         measures a SMALLER environment than a bare `clean check` loads."
    );
    // `init_io_ops` is the registrar that adds axioms rather than definitions;
    // its absence would silently shrink the axiom census.
    let io_axioms = full
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom && c.name.to_string().starts_with("IO."))
        .count();
    assert!(
        io_axioms > 0,
        "no `IO.*` axioms in the mirrored check environment — init_io_ops contributed nothing"
    );
}

/// Every trust marker in the default environment must be classified as debt,
/// never as foundational. This is the #3554 regression in census form.
#[test]
fn prelude_axiom_census_trust_markers_are_not_foundational() {
    let env = check_default_env();
    let c = census(&env);
    assert!(
        !c.trust_markers.is_empty(),
        "VACUITY: no trust markers found in the default environment, so this test proves \
         nothing. `sorry` / `sorryAx` are registered by init_sorry / init_sorry_ax."
    );
    for m in &c.trust_markers {
        assert!(
            !c.foundational.contains(m),
            "trust marker {m} is classified foundational in the default environment"
        );
        let name = Name::from_string(m);
        assert!(
            !is_foundational_axiom(&name),
            "is_foundational_axiom({m}) is true — the #3554 classifier bug is back"
        );
    }
}
