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
//! **KR1 slice 1 (2026-10-22, `docs/DECISIONS.md` R132).** The `Fact` triple
//! and the 163 `SetTheory.*` symbols left the default prelude for the opt-in
//! stub theory (`env/stub_theory.rs`, `Environment::init_stub_theory`): the
//! non-foundational count fell from 267 to 101 and the default prelude has
//! no asserted proposition left. A source or `.olean` `class Fact` now
//! registers directly, with no stub to discharge. The wrap control below opts
//! its probe environment into the stub theory to keep a value-less
//! proposition to wrap.
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
//! * **`debt_signature`** — an axiom whose type is data (`Sort u`, `u ≠ 0`) and
//!   WITNESSED inhabited by [`super::axiom_inhabitation`]: an uninterpreted
//!   symbol — a declared name with no definition, the shape `Set.union` /
//!   `Subgroup.carrier` / `IO.println` have. Every witnessed axiom holds in ONE
//!   fixed model of the whole environment, so together they cannot make a false
//!   statement provable; it is API-completeness debt, counted separately rather
//!   than laundered into the same number as the propositions.
//! * **`debt_inhabitation`** — an axiom whose type is data but NOT witnessed
//!   inhabited. The sort alone decides nothing: until 2026-09-28 this census
//!   filed `Pure.pure : {m} → {α} → α → m α` as a signature because its sort is
//!   `Type (max (u+1) v)`, and it proved `False`
//!   (`docs/issues/2026-09-28-prelude-pure-proves-false.md`). An unwitnessed
//!   inhabitation claim is treated exactly like an asserted proposition.
//!
//! The split is computed by the kernel (`infer_type` of the declared type,
//! `is_def_eq` against `Sort 0`, then the inhabitation witness), never by
//! reading a name.
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
use super::axiom_inhabitation::inhabitation_witness;
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

/// Mirror the default production check constructor's checked List and ULift
/// registrars. IO/control/admission signatures are explicit optional fragments;
/// they must not be counted as default declarations (F3). The elaborator's
/// production-constructor test independently checks this mirror at runtime.
fn check_default_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_monad_list_insts()
        .expect("invariant: init_monad_list_insts is idempotent on with_prelude()");
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
    /// Non-foundational, data-typed, and WITNESSED inhabited in the census
    /// model (`axiom_inhabitation.rs`): an uninterpreted symbol.
    debt_signature: BTreeSet<String>,
    /// Non-foundational, data-typed, and NOT witnessed inhabited: the type
    /// claims an inhabitant the census cannot exhibit in any model it knows.
    /// `Pure.pure`'s old type (`{m} → {α} → α → m α`) is the reason this
    /// bucket exists — it proved `False`, and the old split called it a
    /// signature because its SORT is not `Prop`.
    debt_inhabitation: BTreeSet<String>,
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
            &self.debt_inhabitation,
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
///
/// A data-typed axiom is a SIGNATURE only when
/// [`super::axiom_inhabitation::inhabitation_witness`] exhibits why its type is
/// inhabited in the census model; otherwise it is an INHABITATION claim. The
/// sort alone cannot decide it: `Pure.pure`'s old type lives in
/// `Type (max (u+1) v)` and proved `False`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AxiomTypeClass {
    Proposition,
    Signature,
    Inhabitation,
    Unknown,
}

fn classify_axiom_type(env: &Environment, ty: &Expr) -> AxiomTypeClass {
    let tc = TypeChecker::new(env);
    match tc.infer_type(ty) {
        Ok(sort) => {
            if tc.is_def_eq(&sort, &Expr::prop()) {
                AxiomTypeClass::Proposition
            } else if inhabitation_witness(env, ty).is_ok() {
                AxiomTypeClass::Signature
            } else {
                AxiomTypeClass::Inhabitation
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
                        AxiomTypeClass::Inhabitation => {
                            out.debt_inhabitation.insert(s);
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
    pinned.extend(pinned_set(r, "debt_inhabitation"));
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
        ("baseline_debt_inhabitation", c.debt_inhabitation.len()),
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

    // A name pinned as a SIGNATURE that the witness criterion now refuses is
    // a MISCLASSIFICATION, whatever the counts say: it is the exact error the
    // old sort-only split made on `Pure.pure`.
    let pinned_signature = pinned_set(r, "debt_signature");
    let misclassified: Vec<&String> = c
        .debt_inhabitation
        .intersection(&pinned_signature)
        .collect();
    if !misclassified.is_empty() {
        problems.push(format!(
            "PINNED AS debt_signature BUT NOT WITNESSED INHABITED: {misclassified:?} — the type \
             claims an inhabitant the census cannot exhibit, so it is not an uninterpreted symbol"
        ));
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
        "baseline_debt_inhabitation": c.debt_inhabitation.len(),
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
        "debt_inhabitation": c.debt_inhabitation.iter().collect::<Vec<_>>(),
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
    let mut props = pinned_set(r, "debt_proposition");
    // An unwitnessed inhabitation claim is treated exactly like an asserted
    // proposition: it may be what makes a statement provable.
    props.extend(pinned_set(r, "debt_inhabitation"));
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
    // serve as the axiom to wrap. It then wrapped `Fact.out`, the last
    // `debt_proposition` entry with the plainest type.
    //
    // KR1 slice 1 (R132): `Fact` moved, with `SetTheory.*`, out of the default
    // prelude into the opt-in stub theory, so the default prelude has NO
    // asserted proposition left to wrap. The control now opts the probe
    // environment into that theory and wraps `Fact.out` there: the gate's
    // predicate is the same function over the same census, so it must still
    // name the wrapped axiom. The precondition is not weakened: `Fact.out`
    // must be ABSENT from the default prelude and an AXIOM once opted in.
    let target = Name::from_string("Fact.out");
    assert!(
        env.get_const(&target).is_none(),
        "control precondition: Fact.out is no longer in the default prelude (R132)"
    );
    env.init_stub_theory()
        .expect("the opt-in stub theory initializes on the default prelude");
    let info = env
        .get_const(&target)
        .cloned()
        .expect("Fact.out is registered by the opt-in stub theory");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "control precondition: Fact.out must still be an AXIOM in the stub theory. \
         If it has been PROVED, retarget this control at another asserted proposition."
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
/// mentions: `IO.bind` is itself an axiom here, so a theorem about an `IO`
/// action reaches debt on its first line without the user writing an axiom
/// name (until KR1 increment 3, R143, `Set.union` was one too, and `A ∪ B`
/// did the same).
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
/// The mirror's checked registrars remain live, while IO is absent by default.
/// An explicitly opted-in IO context is the non-vacuous classifier control.
#[test]
fn prelude_axiom_census_mirrors_the_cli_check_environment() {
    let bare = Environment::with_prelude();
    let full = check_default_env();
    assert!(
        full.constants().count() > bare.constants().count(),
        "check_default_env() added nothing over Environment::with_prelude(): the CLI mirror \
         (init_monad_list_insts / init_ulift) has gone inert, so this census \
         measures a SMALLER environment than a bare `clean check` loads."
    );
    // Default construction must omit IO, and explicit opt-in must retain it.
    assert!(full.get_const(&Name::from_string("IO")).is_none());
    let mut opted = full.clone();
    opted
        .init_io_stub_theory()
        .expect("explicit IO stub theory");
    let io_axioms = opted
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom && c.name.to_string().starts_with("IO."))
        .count();
    assert!(
        io_axioms > 0,
        "no `IO.*` axioms in the mirrored check environment — init_io_ops contributed nothing"
    );
}

/// Explicitly opted-in trust markers must be classified as debt, never as
/// foundational; the default environment must have none. This is the #3554 regression in census form.
#[test]
fn prelude_axiom_census_trust_markers_are_not_foundational() {
    let mut env = check_default_env();
    assert!(census(&env).trust_markers.is_empty());
    env.init_admission_stub_theory()
        .expect("explicit admission stub theory");
    let c = census(&env);
    assert_eq!(c.trust_markers.len(), 4);
    assert!(
        !c.trust_markers.is_empty(),
        "VACUITY: no trust markers found in the opted-in environment, so this test proves \
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

/// THE ARM THAT IS RED ON THE OLD, SORT-ONLY SPLIT.
///
/// Until 2026-09-28 the default prelude carried
/// `axiom Pure.pure : {m : Type u → Type v} → {α : Type u} → α → m α`, and this
/// census filed it under `debt_signature` — "an uninterpreted symbol that
/// asserts no proposition" — because the SORT of that type is
/// `Type (max (u+1) v)`, not `Prop`. It proved `False`
/// (`Empty.elim (Pure.pure (fun _ => Empty) Nat 0)`;
/// `docs/issues/2026-09-28-prelude-pure-proves-false.md`). This arm plants the
/// OLD `Pure.pure` and `Bind.bind` types under fresh names and requires the
/// census to refuse them the signature bucket, and the gate to refuse them;
/// with the sort-only classifier restored it fails on its first assertion
/// (demonstrated in the issue file).
///
/// Controls pin the other direction, so the criterion cannot pass by refusing
/// everything: an uninterpreted type former and an axiom of type `Nat` stay
/// signatures, and an axiom of type `Empty` — a closed data type with no
/// inhabitant, which the sort-only split ALSO called a signature — is refused.
#[test]
fn prelude_axiom_ratchet_refuses_signature_for_an_uninhabitable_type() {
    use crate::expr::BinderInfo;
    let mut env = check_default_env();
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let ty_u = Expr::sort(Level::succ(u.clone()));
    let ty_v = Expr::sort(Level::succ(v.clone()));
    let kind = Expr::pi(BinderInfo::Default, ty_u.clone(), ty_v);
    let lps = vec![Name::from_string("u"), Name::from_string("v")];

    // {m : Type u → Type v} → {α : Type u} → α → m α           (old Pure.pure)
    let old_pure = Expr::pi(
        BinderInfo::Implicit,
        kind.clone(),
        Expr::pi(
            BinderInfo::Implicit,
            ty_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::app(Expr::bvar(2), Expr::bvar(1)),
            ),
        ),
    );
    // {m} → {α β : Type u} → m α → (α → m β) → m β           (old Bind.bind)
    let old_bind = Expr::pi(
        BinderInfo::Implicit,
        kind.clone(),
        Expr::pi(
            BinderInfo::Implicit,
            ty_u.clone(),
            Expr::pi(
                BinderInfo::Implicit,
                ty_u.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::bvar(2), Expr::bvar(1)),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(2),
                            Expr::app(Expr::bvar(4), Expr::bvar(2)),
                        ),
                        Expr::app(Expr::bvar(4), Expr::bvar(2)),
                    ),
                ),
            ),
        ),
    );
    let planted: [(&str, Vec<Name>, Expr); 5] = [
        ("PreludeAxiomProbe.oldPurePure", lps.clone(), old_pure),
        ("PreludeAxiomProbe.oldBindBind", lps, old_bind),
        (
            "PreludeAxiomProbe.carrier",
            vec![],
            Expr::pi(
                BinderInfo::Default,
                Expr::sort(Level::succ(Level::zero())),
                Expr::sort(Level::succ(Level::zero())),
            ),
        ),
        (
            "PreludeAxiomProbe.someNat",
            vec![],
            Expr::const_(Name::from_string("Nat"), Vec::<Level>::new()),
        ),
        (
            "PreludeAxiomProbe.someEmpty",
            vec![],
            Expr::const_(Name::from_string("Empty"), Vec::<Level>::new()),
        ),
    ];
    for (name, level_params, type_) in planted {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params,
            type_,
        })
        .unwrap_or_else(|e| panic!("planting {name} must be well-formed: {e:?}"));
    }

    let c = census(&env);
    for refused in [
        "PreludeAxiomProbe.oldPurePure",
        "PreludeAxiomProbe.oldBindBind",
        "PreludeAxiomProbe.someEmpty",
    ] {
        assert!(
            !c.debt_signature.contains(refused),
            "{refused} was classed debt_signature (\"asserts no proposition\"); its type is \
             inhabited in no model, so that is the Pure.pure misclassification again"
        );
        assert!(
            c.debt_inhabitation.contains(refused),
            "{refused} did not land in debt_inhabitation (prop={} unknown={})",
            c.debt_proposition.contains(refused),
            c.unknown_sort.contains(refused)
        );
    }
    for kept in ["PreludeAxiomProbe.carrier", "PreludeAxiomProbe.someNat"] {
        assert!(
            c.debt_signature.contains(kept),
            "control {kept} is witnessed inhabited and must stay a signature; the criterion \
             is refusing too much"
        );
    }

    let r = load_ratchet();
    let problems = new_axiom_problems(&c, &r);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("baseline_debt_inhabitation")),
        "refusal 2 did not fire on a risen debt_inhabitation count; problems were {problems:?}"
    );

    // And a ratchet that PINS the old type as a signature — the checked-in
    // file before this fix, in miniature — is refused by name.
    let mut stale = r.clone();
    if let Some(sig) = stale
        .get_mut("debt_signature")
        .and_then(serde_json::Value::as_array_mut)
    {
        sig.push(serde_json::json!("PreludeAxiomProbe.oldPurePure"));
    }
    let stale_problems = new_axiom_problems(&c, &stale);
    assert!(
        stale_problems.iter().any(|p| p
            .contains("PINNED AS debt_signature BUT NOT WITNESSED INHABITED")
            && p.contains("PreludeAxiomProbe.oldPurePure")),
        "a ratchet pinning the old Pure.pure type as a signature was not refused; problems \
         were {stale_problems:?}"
    );
}

/// The default prelude registers no axiom the census cannot witness except
/// the ones the ratchet names, and NONE of the monad family: the class-based
/// hierarchy leaves no `Pure.pure` / `Bind.bind` / `StateT.*` /
/// `MonadExcept.throw` / `OptionT.*` axiom behind.
#[test]
fn prelude_axiom_census_has_no_monad_inhabitation_axiom() {
    let env = check_default_env();
    let c = census(&env);
    for name in [
        "Pure.pure",
        "Bind.bind",
        "Monad",
        "StateT.pure",
        "StateT.get",
        "StateT.set",
        "StateT.modify",
        "StateT.modifyGet",
        "MonadExcept.throw",
        "MonadExcept.tryCatch",
        "OptionT",
        "OptionT.run",
        "OptionT.fail",
        "ExceptT",
        "ExceptT.run",
        "StateM",
        "StateM.pure",
    ] {
        let kind = env.get_const(&Name::from_string(name)).map(|ci| ci.kind);
        assert_ne!(
            kind,
            Some(ConstantKind::Axiom),
            "{name} is still a value-less AXIOM in the default prelude"
        );
    }
    assert!(
        c.debt_inhabitation
            .iter()
            .all(|n| !n.starts_with("Pure.") && !n.starts_with("Bind.")),
        "debt_inhabitation still names a monad operation: {:?}",
        c.debt_inhabitation
    );
}
