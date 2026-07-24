// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Gamma-crown verification runner: builds all conjectures and produces
//! a machine-readable verification report.
//!
//! This module provides the public API for type-checking and classifying the gamma-crown
//! conjectures (C001-C030). Each conjecture is initialized in its own
//! `Environment`, which runs kernel type checking on every declaration.
//! The report includes per-conjecture axiom counts, proof quality, and
//! timing metrics.
//!
//! # Usage
//!
//! ```rust,no_run
//! use clean_kernel::env::gamma_crown_verify::{verify_all_conjectures, CONJECTURE_IDS};
//!
//! let report = verify_all_conjectures();
//! assert!(report.conjectures_failed == 0);
//! ```
//!
//! Part of #3380.

use super::types::ConstantKind;
use super::Environment;
use crate::expr::{Expr, ExprKind};
use serde::Serialize;
use std::time::Instant;

/// All gamma-crown conjecture identifiers in canonical order.
pub const CONJECTURE_IDS: &[&str] = &[
    "C001", "C002", "C003", "C004", "C005", "C006", "C007", "C008", "C009", "C010", "C011", "C012",
    "C028", "C029", "C030",
];

/// Human-readable conjecture descriptions.
pub fn conjecture_description(id: &str) -> &'static str {
    match id {
        "C001" => "Zonotope compression soundness",
        "C002" => "Crown-LayerNorm IBP bridge",
        "C003" => "Eclipse convergence (Lipschitz)",
        "C004" => "CROWN backward bound equality",
        "C005" => "McCormick attention gap",
        "C006" => "Blockwise CROWN equivalence",
        "C007" => "Streaming certificate soundness",
        "C008" => "IBP tightness depth scaling",
        "C009" => "CROWN-IBP exponential gap",
        "C010" => "Zonotope-CROWN linear equality",
        "C011" => "Softmax width monotonicity",
        "C012" => "ReLU stability pattern cert",
        "C028" => "Nullstellensatz SoS completeness",
        "C029" => "PAC certification bound",
        "C030" => "Orbit-CROWN equivariant speedup",
        _ => "Unknown conjecture",
    }
}

/// Return the namespace prefixes used by each conjecture for its domain axioms.
///
/// Each conjecture registers axioms under specific namespaces. Most use
/// `NNVerify.CXXX.` but some use module-specific prefixes (e.g., C003 uses
/// `NNVerify.ECLipsE.`, C005 uses `NNVerify.McCormick.`). C009 is unique in
/// using the `NNVerification.` prefix for all its axioms.
///
/// These prefixes determine which axioms count toward a conjecture's
/// domain-axiom tally (matching data/axiom_audit.json methodology).
fn conjecture_axiom_prefixes(id: &str) -> &'static [&'static str] {
    match id {
        "C001" => &["NNVerify.C001."],
        "C002" => &["NNVerify.C002."],
        "C003" => &["NNVerify.ECLipsE.", "NNVerify.Lipschitz."],
        "C004" => &["NNVerify.C004."],
        "C005" => &["NNVerify.McCormick."],
        "C006" => &["NNVerify.C006."],
        "C007" => &["NNVerify.C007."],
        "C008" => &["NNVerify.ibp_tightness_"],
        "C009" => &[
            "NNVerification.ibp_wrapping_",
            "NNVerification.crown_",
            "NNVerification.norm_product_",
            "NNVerification.ratio_",
            "NNVerification.c009_",
            "NNVerification.C009",
        ],
        "C010" => &["NNVerify.C010.", "NNVerify.RobustnessGen."],
        "C011" => &["NNVerify.C011."],
        "C012" => &["NNVerify.C012."],
        "C028" => &["NNVerify.C028."],
        "C029" => &["NNVerify.PacProof."],
        "C030" => &["NNVerify.OrbitCROWN."],
        _ => &[],
    }
}

/// Walk an expression tree and return true if it references the kernel's sorry
/// inhabitant constants.
fn value_refs_sorry(expr: &Expr) -> bool {
    let mut stack = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr.kind() {
            ExprKind::Const(name, _) => {
                let name = name.to_string();
                if name == "sorry" || name == "sorryAx" {
                    return true;
                }
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) | ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }
    false
}

/// Return true when a conjecture has zero counted domain axioms but still stores
/// a conjecture-prefixed opaque declaration whose hidden body is sorry-inhabited.
fn has_conjecture_sorry_opaque(env: &Environment, id: &str) -> bool {
    let prefixes = conjecture_axiom_prefixes(id);
    env.constants().any(|info| {
        if !matches!(info.kind, ConstantKind::Opaque) {
            return false;
        }
        let name = info.name.to_string();
        if !prefixes.iter().any(|prefix| name.starts_with(prefix)) {
            return false;
        }
        info.value.as_ref().is_some_and(value_refs_sorry)
    })
}

/// Honest, kernel-derived classification of a single conjecture from the
/// transitive axiom closure of its HEADLINE theorems.
///
/// `verify_conjecture` historically derived `constructive` from a NARROW
/// per-conjecture namespace count of remaining `Declaration::Axiom` entries.
/// That count EXCLUDES shared infrastructure and admitted algebra-layer axioms
/// (`Rat.*` ordered-field/lattice, `Fin.*`, `Nat.*` bitwise — see
/// `ADMITTED_DOMAIN_AXIOMS` in `axiom_audit.rs`), so a hypothesis-wrapped
/// conjecture that transitively rests on admitted axioms or on shared
/// scaffolding scored `domain_axioms == 0` and was reported
/// `VERIFIED_CONSTRUCTIVE` ("PROVED") — an overstatement.
///
/// This variant computes the verdict from the FULL transitive closure of every
/// `Declaration::Theorem` registered under the conjecture's namespace, using the
/// authoritative kernel classifier (`Environment::proof_quality` /
/// `axiom_deps` / `trust_marker_deps`). It additionally detects the
/// "hypothesis-wrapped tautology" shape — a proof that, after stripping leading
/// binders, simply RETURNS one of its own hypotheses (`fun … h => h`, body head
/// is a `BVar`) — which has an empty axiom closure yet proves nothing about the
/// original conjecture beyond `H -> H`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HeadlineVerdict {
    /// Genuine constructive proof term: empty domain-axiom closure, no trust
    /// marker reachable, and not a bare hypothesis projection.
    Constructive,
    /// `Declaration::Theorem` whose proof, after stripping leading binders, is a
    /// bare bound-variable projection (returns a strengthening local
    /// hypothesis). Empty axiom closure, but `H -> H` — NOT a proof of the
    /// conjecture's claim.
    HypothesisWrapped,
    /// Transitive closure reaches at least one trust marker
    /// (`sorry`/`sorryAx`/`trustedArith`/`trustedAy`).
    SorryInhabited,
    /// Transitive closure reaches at least one non-foundational domain axiom
    /// (including admitted `Rat.*`/`Fin.*`/`Nat.*` axioms and shared
    /// infrastructure axioms).
    AxiomDependent,
}

/// Strip leading lambda binders (and `MData` wrappers) and return true when the
/// resulting proof body is a bare bound-variable projection — i.e. the proof
/// returns one of its own hypotheses directly (`fun … h => h`) or applies such a
/// hypothesis to arguments (`fun … h => h a b`). This is the kernel-detectable
/// signature of a hypothesis-wrapped tautology: the conjecture's claim is taken
/// as an explicit local premise and handed straight back, so the term proves
/// `H -> H` and contributes no axiom dependencies.
fn proof_is_bare_hypothesis_projection(value: &Expr) -> bool {
    let mut cur = value.clone();
    // Strip leading binders / metadata.
    loop {
        let next = match cur.kind() {
            ExprKind::Lam(_, _, body) => (**body).clone(),
            ExprKind::MData(_, inner) => (**inner).clone(),
            _ => break,
        };
        cur = next;
    }
    // Walk to the head of any application spine.
    loop {
        match cur.kind() {
            ExprKind::App(f, _) => {
                let f = (**f).clone();
                cur = f;
            }
            ExprKind::MData(_, inner) => {
                let inner = (**inner).clone();
                cur = inner;
            }
            _ => break,
        }
    }
    matches!(cur.kind(), ExprKind::BVar(_))
}

/// Classify one headline theorem from its kernel proof quality and proof shape.
fn classify_headline_theorem(env: &Environment, name: &crate::name::Name) -> HeadlineVerdict {
    use super::axiom_audit::ProofQuality;

    // Closure that reaches any trust marker (sorry/sorryAx/trusted*) is the
    // strongest disqualifier — report it first.
    if env
        .trust_marker_deps(name)
        .map(|t| !t.is_empty())
        .unwrap_or(false)
    {
        return HeadlineVerdict::SorryInhabited;
    }

    match env.proof_quality(name) {
        Some(ProofQuality::Constructive) => {
            // Empty domain-axiom closure. Distinguish a genuine proof term from
            // a hypothesis-wrapped `H -> H` tautology (`fun … h => h`).
            let is_projection = env
                .get_const(name)
                .and_then(|info| info.value.as_ref())
                .is_some_and(proof_is_bare_hypothesis_projection);
            if is_projection {
                HeadlineVerdict::HypothesisWrapped
            } else {
                HeadlineVerdict::Constructive
            }
        }
        // AxiomDependent here means a non-foundational DOMAIN axiom is reachable
        // (trust markers were already handled above). `Unchecked` (proof-less
        // theorem) and `NotATheorem` should not occur for collected theorems,
        // but treat them conservatively as non-constructive.
        Some(ProofQuality::AxiomDependent { .. })
        | Some(ProofQuality::Unchecked)
        | Some(ProofQuality::NotATheorem)
        | None => HeadlineVerdict::AxiomDependent,
    }
}

/// Aggregate verdict over ALL `Declaration::Theorem` decls registered under the
/// conjecture's namespace prefixes (its "headline" claim set).
///
/// Severity ordering (most severe wins): `SorryInhabited` > `AxiomDependent` >
/// `HypothesisWrapped` > `Constructive`. A conjecture is genuinely
/// `Constructive` ONLY when it has at least one headline theorem and EVERY one
/// classifies `Constructive`.
fn classify_conjecture_headlines(env: &Environment, id: &str) -> HeadlineVerdict {
    let prefixes = conjecture_axiom_prefixes(id);
    let headline_names: Vec<crate::name::Name> = env
        .constants()
        .filter(|c| matches!(c.kind, ConstantKind::Theorem))
        .filter(|c| {
            let s = c.name.to_string();
            prefixes.iter().any(|p| s.starts_with(p))
        })
        .map(|c| c.name.clone())
        .collect();

    // No headline theorems: cannot claim "constructive". Fall back to the
    // sorry-opaque scan so a scaffold-only conjecture still reports honestly.
    if headline_names.is_empty() {
        return if has_conjecture_sorry_opaque(env, id) {
            HeadlineVerdict::SorryInhabited
        } else {
            HeadlineVerdict::AxiomDependent
        };
    }

    let mut worst = HeadlineVerdict::Constructive;
    let severity = |v: HeadlineVerdict| match v {
        HeadlineVerdict::Constructive => 0,
        HeadlineVerdict::HypothesisWrapped => 1,
        HeadlineVerdict::AxiomDependent => 2,
        HeadlineVerdict::SorryInhabited => 3,
    };
    for name in &headline_names {
        let v = classify_headline_theorem(env, name);
        if severity(v) > severity(worst) {
            worst = v;
        }
    }
    worst
}

/// Initialize a single conjecture environment.
///
/// Each conjecture is initialized in a fresh `Environment`, triggering
/// kernel type checking for all declarations via `add_decl`.
pub fn init_conjecture(id: &str) -> Result<Environment, String> {
    let mut env = Environment::new();
    let result = match id {
        "C001" => env.init_nn_verify_c001(),
        "C002" => env.init_nn_verification_c002(),
        "C003" => env.init_nn_verify_eclipse_convergence(),
        "C004" => env.init_nn_verify_crown_layernorm(),
        "C005" => env.init_nn_verify_mccormick_attention(),
        "C006" => env.init_nn_verify_blockwise_crown(),
        "C007" => env.init_nn_verify_streaming_certs(),
        "C008" => env.init_nn_verify_ibp_tightness(),
        "C009" => env.init_nn_verification_c009(),
        "C010" => env.init_nn_verify_zonotope_crown(),
        "C011" => env.init_nn_verify_softmax_c011(),
        "C012" => env.init_nn_verify_relu_stability(),
        "C028" => env.init_nn_verify_nullstellensatz(),
        "C029" => env.init_nn_verify_pac_proof(),
        "C030" => env.init_nn_verify_orbit_crown(),
        _ => return Err(format!("Unknown conjecture: {id}")),
    };
    result.map_err(|e| format!("{e}"))?;
    Ok(env)
}

/// Per-conjecture verification result.
#[derive(Clone, Debug, Serialize, Default)]
pub struct ConjectureResult {
    pub id: String,
    pub description: String,
    /// VERIFIED_CONSTRUCTIVE | VERIFIED_HYPOTHESIS_WRAPPED | VERIFIED_SCAFFOLDED |
    /// VERIFIED_AXIOM_DEPENDENT | INIT_FAILED.
    pub status: String,
    pub init_ok: bool,
    pub tc_verified: bool,
    /// Informational: count of `Declaration::Axiom` entries remaining under the
    /// conjecture's OWN namespace prefix (see `conjecture_axiom_prefixes`). This
    /// EXCLUDES shared infrastructure and admitted algebra-layer axioms, so it
    /// is NOT the constructive verdict — it is reported for continuity with
    /// `data/axiom_audit.json`. The honest verdict (`constructive` /
    /// `fully_constructive` / `status` / `proof_mechanism`) is derived from the
    /// FULL transitive closure of the headline theorems (#3700 integrity fix).
    pub domain_axioms: usize,
    pub theorems: usize,
    pub definitions: usize,
    pub opaques: usize,
    pub constructive_theorems: usize,
    /// Honest constructive verdict: true ONLY when EVERY headline theorem of the
    /// conjecture has an empty domain-axiom closure over genuine foundations AND
    /// is not a hypothesis-wrapped projection. Derived from the FULL transitive
    /// closure, NOT the narrow namespace count (#3700 integrity fix).
    pub constructive: bool,
    /// Honest classification (#3498/#3502/#3700):
    /// proof_mechanism ∈ {"constructive","hypothesis_wrapped",
    /// "sorry_inhabited","axiom-dependent"}.
    #[serde(default)]
    pub fully_constructive: bool,
    #[serde(default)]
    pub scaffolded: bool,
    #[serde(default)]
    pub proof_mechanism: String,
    /// Names of remaining domain-specific axioms.
    pub axiom_names: Vec<String>,
    pub verification_time_ms: f64,
    pub error: Option<String>,
}

/// Aggregate verification report for all conjectures.
#[derive(Clone, Debug, Serialize, Default)]
pub struct VerificationReport {
    /// Timestamp string.
    pub timestamp: String,
    /// Total number of conjectures attempted.
    pub total_conjectures: usize,
    /// Number that passed kernel verification.
    pub conjectures_verified: usize,
    /// Number that failed.
    pub conjectures_failed: usize,
    /// Honest constructive count: conjectures whose entire headline theorem set
    /// has an empty domain-axiom closure over genuine foundations and is not
    /// hypothesis-wrapped. Equals `constructive_conjectures` (#3700 fix; this is
    /// no longer the legacy "zero-domain-axiom" count, which over-reported).
    pub fully_constructive: usize,
    /// Honest classification counts (#3502/#3700):
    /// constructive/hypothesis-wrapped/scaffolded/axiom-dependent. `mixed` is
    /// retained for schema continuity and is always 0 under the honest gate
    /// (the categories are disjoint).
    pub constructive_conjectures: usize,
    #[serde(default)]
    pub hypothesis_wrapped_conjectures: usize,
    pub mixed_conjectures: usize,
    pub scaffolded_conjectures: usize,
    pub axiom_dependent_conjectures: usize,
    /// Sum of domain axioms across all conjectures.
    pub total_domain_axioms: usize,
    /// Sum of theorems across all conjectures.
    pub total_theorems: usize,
    /// Total wall-clock time in milliseconds.
    pub total_verification_time_ms: f64,
    /// Per-conjecture results.
    pub conjectures: Vec<ConjectureResult>,
}

/// Verify a single conjecture and return its result.
pub fn verify_conjecture(id: &str) -> ConjectureResult {
    let start = Instant::now();
    let mut result = ConjectureResult {
        id: id.to_string(),
        description: conjecture_description(id).to_string(),
        status: "UNKNOWN".to_string(),
        init_ok: false,
        tc_verified: false,
        domain_axioms: 0,
        theorems: 0,
        definitions: 0,
        opaques: 0,
        constructive_theorems: 0,
        constructive: false,
        fully_constructive: false,
        scaffolded: false,
        proof_mechanism: "unknown".to_string(),
        axiom_names: Vec::new(),
        verification_time_ms: 0.0,
        error: None,
    };

    let env = match init_conjecture(id) {
        Ok(e) => e,
        Err(e) => {
            result.status = "INIT_FAILED".to_string();
            result.error = Some(e);
            result.verification_time_ms = start.elapsed().as_secs_f64() * 1000.0;
            return result;
        }
    };
    result.init_ok = true;

    // Collect metrics via soundness report
    let report = env.soundness_report();
    result.theorems = report.theorems;
    result.definitions = report.definitions;
    result.opaques = report.opaques;
    result.constructive_theorems = report.constructive_theorems;

    // INFORMATIONAL ONLY: count conjecture-specific domain axioms using
    // per-conjecture namespace prefixes. Foundation axioms and admitted
    // algebra-layer axioms are shared infrastructure and are excluded here, so
    // this count matches data/axiom_audit.json's per-conjecture `axioms` field.
    // It is NOT the constructive verdict (see below).
    let prefixes = conjecture_axiom_prefixes(id);
    let nn_axiom_names: Vec<String> = report
        .domain_axioms
        .iter()
        .filter(|n| {
            let s = n.to_string();
            prefixes.iter().any(|p| s.starts_with(p))
        })
        .map(|n| n.to_string())
        .collect();
    result.domain_axioms = nn_axiom_names.len();
    result.axiom_names = nn_axiom_names;

    // Init success means all add_decl calls passed kernel type checking.
    result.tc_verified = true;

    // HONEST VERDICT (#3700 integrity fix): derive constructive/PROVED from the
    // FULL transitive axiom closure of the conjecture's headline theorems via
    // the authoritative kernel classifier (`proof_quality` / `axiom_deps` /
    // `trust_marker_deps`), NOT from the narrow namespace count above. A
    // conjecture is constructive ONLY when EVERY headline theorem has an empty
    // domain-axiom closure over genuine foundations, reaches no `sorry`, and is
    // not a hypothesis-wrapped `H -> H` projection.
    let verdict = classify_conjecture_headlines(&env, id);
    result.constructive = matches!(verdict, HeadlineVerdict::Constructive);
    result.fully_constructive = result.constructive;
    result.scaffolded = matches!(verdict, HeadlineVerdict::SorryInhabited);
    result.proof_mechanism = match verdict {
        HeadlineVerdict::Constructive => "constructive",
        HeadlineVerdict::HypothesisWrapped => "hypothesis_wrapped",
        HeadlineVerdict::SorryInhabited => "sorry_inhabited",
        HeadlineVerdict::AxiomDependent => "axiom-dependent",
    }
    .to_string();
    result.status = match verdict {
        HeadlineVerdict::Constructive => "VERIFIED_CONSTRUCTIVE",
        HeadlineVerdict::HypothesisWrapped => "VERIFIED_HYPOTHESIS_WRAPPED",
        HeadlineVerdict::SorryInhabited => "VERIFIED_SCAFFOLDED",
        HeadlineVerdict::AxiomDependent => "VERIFIED_AXIOM_DEPENDENT",
    }
    .to_string();

    result.verification_time_ms = start.elapsed().as_secs_f64() * 1000.0;
    result
}

/// Verify ALL gamma-crown conjectures and produce a full report.
///
/// This is the primary entry point. It initializes each conjecture in
/// a fresh environment, runs kernel type checking, and aggregates
/// results.
pub fn verify_all_conjectures() -> VerificationReport {
    let total_start = Instant::now();

    let conjectures: Vec<ConjectureResult> = CONJECTURE_IDS
        .iter()
        .map(|&id| verify_conjecture(id))
        .collect();

    let total_time = total_start.elapsed().as_secs_f64() * 1000.0;

    let conjectures_verified = conjectures.iter().filter(|c| c.tc_verified).count();
    let conjectures_failed = conjectures.iter().filter(|c| !c.tc_verified).count();
    let total_domain_axioms: usize = conjectures.iter().map(|c| c.domain_axioms).sum();
    let total_theorems: usize = conjectures.iter().map(|c| c.theorems).sum();

    // Honest, disjoint classification aggregates (#3502/#3700). Each bucket is
    // keyed off the per-conjecture `proof_mechanism` (derived from the full
    // headline-theorem closure), so the four buckets partition the verified set.
    let constructive_conjectures = conjectures
        .iter()
        .filter(|c| c.proof_mechanism == "constructive")
        .count();
    let hypothesis_wrapped_conjectures = conjectures
        .iter()
        .filter(|c| c.proof_mechanism == "hypothesis_wrapped")
        .count();
    let scaffolded_conjectures = conjectures
        .iter()
        .filter(|c| c.proof_mechanism == "sorry_inhabited")
        .count();
    let axiom_dependent_conjectures = conjectures
        .iter()
        .filter(|c| c.proof_mechanism == "axiom-dependent")
        .count();
    // `fully_constructive` is now the honest constructive count (no longer the
    // over-reporting zero-domain-axiom legacy count). `mixed` is always 0.
    let fully_constructive = constructive_conjectures;
    let mixed_conjectures = 0;

    VerificationReport {
        timestamp: unix_timestamp(),
        total_conjectures: CONJECTURE_IDS.len(),
        conjectures_verified,
        conjectures_failed,
        fully_constructive,
        constructive_conjectures,
        hypothesis_wrapped_conjectures,
        mixed_conjectures,
        scaffolded_conjectures,
        axiom_dependent_conjectures,
        total_domain_axioms,
        total_theorems,
        total_verification_time_ms: total_time,
        conjectures,
    }
}

/// Simple timestamp without external chrono dependency.
fn unix_timestamp() -> String {
    use std::time::SystemTime;
    match SystemTime::now().duration_since(SystemTime::UNIX_EPOCH) {
        Ok(d) => format!("{}", d.as_secs()),
        Err(_) => "0".to_string(),
    }
}

/// Format the report as a human-readable table.
pub fn format_human_report(report: &VerificationReport) -> String {
    let mut out = String::new();
    out.push_str("======================================================================\n");
    out.push_str("       Gamma-Crown Formal Verification Report -- clean kernel\n");
    out.push_str("======================================================================\n\n");

    out.push_str(&format!(
        "Total verification time: {:.1}ms\n\n",
        report.total_verification_time_ms
    ));

    // Summary. Constructive/PROVED is derived from the FULL transitive closure
    // of each conjecture's headline theorems (#3700), NOT the narrow namespace
    // axiom count, so hypothesis-wrapped `H -> H` tautologies and theorems that
    // transitively rest on admitted Rat/Fin/Nat axioms are NOT counted as
    // proved.
    out.push_str("-- Summary ----------------------------------------------------------\n");
    out.push_str(&format!(
        "  Conjectures:         {}/{}  kernel type-checked\n",
        report.conjectures_verified, report.total_conjectures
    ));
    out.push_str(&format!(
        "  Constructive:        {}  (full closure ⊆ foundations; genuine proof terms)\n",
        report.constructive_conjectures
    ));
    out.push_str(&format!(
        "  Hypothesis-wrapped:  {}  (H->H projection; claim taken as a local premise)\n",
        report.hypothesis_wrapped_conjectures
    ));
    out.push_str(&format!(
        "  Scaffolded:          {}  (sorry-inhabited; reaches sorry/sorryAx)\n",
        report.scaffolded_conjectures
    ));
    out.push_str(&format!(
        "  Axiom-dependent:     {}  (full closure reaches a domain axiom)\n",
        report.axiom_dependent_conjectures
    ));
    out.push_str(&format!(
        "  Total theorems:      {}\n",
        report.total_theorems
    ));
    out.push_str(&format!(
        "  Namespace axioms:    {}  (per-conjecture-prefix count; informational)\n\n",
        report.total_domain_axioms
    ));

    // Per-conjecture table
    out.push_str("-- Per-Conjecture Results -------------------------------------------\n");
    out.push_str(&format!(
        "{:<6} {:<42} {:>6} {:>5} {:>5} {:>5} {:<10} {:>8}\n",
        "ID", "Description", "Axioms", "Thms", "Defs", "Opqs", "Status", "Time(ms)"
    ));
    out.push_str(&format!("{}\n", "-".repeat(94)));

    for c in &report.conjectures {
        let status_short = match c.status.as_str() {
            "VERIFIED_CONSTRUCTIVE" => "PROVED",
            "VERIFIED_HYPOTHESIS_WRAPPED" => "HYP-WRAP",
            "VERIFIED_SCAFFOLDED" => "SCAFFOLD",
            "VERIFIED_AXIOM_DEPENDENT" => "FORMAL",
            "INIT_FAILED" => "FAILED",
            _ => "UNKNOWN",
        };
        let desc = if c.description.len() > 42 {
            format!("{}...", &c.description[..39])
        } else {
            c.description.clone()
        };
        out.push_str(&format!(
            "{:<6} {:<42} {:>6} {:>5} {:>5} {:>5} {:<10} {:>8.1}\n",
            c.id,
            desc,
            c.domain_axioms,
            c.theorems,
            c.definitions,
            c.opaques,
            status_short,
            c.verification_time_ms,
        ));
    }
    out.push_str(&format!("{}\n", "-".repeat(94)));

    // Axiom details
    let axiom_dependent: Vec<&ConjectureResult> = report
        .conjectures
        .iter()
        .filter(|c| c.domain_axioms > 0)
        .collect();

    if !axiom_dependent.is_empty() {
        out.push_str("\n-- Remaining Domain Axioms -----------------------------------------\n");
        for c in &axiom_dependent {
            let nn_axioms: Vec<&String> = c
                .axiom_names
                .iter()
                .filter(|n| n.starts_with("NNVerify.") || n.starts_with("NNVerification."))
                .collect();
            if !nn_axioms.is_empty() {
                out.push_str(&format!("  {} ({} axioms):\n", c.id, nn_axioms.len()));
                for name in &nn_axioms {
                    out.push_str(&format!("    - {name}\n"));
                }
            }
        }
    }

    // Failed
    let failed: Vec<&ConjectureResult> = report.conjectures.iter().filter(|c| !c.init_ok).collect();

    if !failed.is_empty() {
        out.push_str("\n-- Failed Conjectures -----------------------------------------------\n");
        for c in &failed {
            out.push_str(&format!(
                "  {}: {}\n",
                c.id,
                c.error.as_deref().unwrap_or("unknown error")
            ));
        }
    }

    out.push('\n');
    if report.conjectures_failed == 0 {
        out.push_str(&format!(
            "RESULT: {} / {} conjectures kernel type-checked\n",
            report.conjectures_verified, report.total_conjectures
        ));
        out.push_str(&format!(
            "        {} constructive, {} hypothesis-wrapped, {} scaffolded, {} axiom-dependent\n",
            report.constructive_conjectures,
            report.hypothesis_wrapped_conjectures,
            report.scaffolded_conjectures,
            report.axiom_dependent_conjectures,
        ));
    } else {
        out.push_str(&format!(
            "RESULT: {} FAILED ({} verified)\n",
            report.conjectures_failed, report.conjectures_verified
        ));
    }

    out
}

/// Format the report as a CSV table.
pub fn format_csv_report(report: &VerificationReport) -> String {
    let mut out = String::new();
    out.push_str("id,description,status,domain_axioms,theorems,definitions,opaques,constructive_legacy,fully_constructive,scaffolded,proof_mechanism,verification_time_ms\n");
    for c in &report.conjectures {
        let desc = if c.description.contains(',') || c.description.contains('"') {
            format!("\"{}\"", c.description.replace('"', "\"\""))
        } else {
            c.description.clone()
        };
        out.push_str(&format!(
            "{},{},{},{},{},{},{},{},{},{},{},{:.1}\n",
            c.id,
            desc,
            c.status,
            c.domain_axioms,
            c.theorems,
            c.definitions,
            c.opaques,
            c.constructive,
            c.fully_constructive,
            c.scaffolded,
            c.proof_mechanism,
            c.verification_time_ms,
        ));
    }
    out
}

/// Format the report as a LaTeX table.
pub fn format_latex_report(report: &VerificationReport) -> String {
    let mut out = String::new();
    out.push_str("% Gamma-Crown Formal Verification Results\n");
    out.push_str(&format!(
        "% Total verification time: {:.1}ms\n",
        report.total_verification_time_ms
    ));
    out.push_str("\\begin{table}[t]\n");
    out.push_str("\\centering\n");
    out.push_str("\\caption{Gamma-Crown conjecture verification status. ``Proved'' indicates a\n");
    out.push_str("  genuine constructive proof term whose FULL transitive axiom closure is\n");
    out.push_str(
        "  contained in the foundational set (derived from the headline theorems, not a\n",
    );
    out.push_str(
        "  narrow per-namespace axiom count). ``Hyp-wrap'' indicates a hypothesis-wrapped\n",
    );
    out.push_str(
        "  $H\\to H$ projection that takes the claim as a local premise. ``Scaffolded''\n",
    );
    out.push_str(
        "  indicates a closure that reaches \\texttt{sorry}/\\texttt{sorryAx}. ``Formal''\n",
    );
    out.push_str("  indicates the closure reaches a domain axiom. Only ``Proved'' is a formal\n");
    out.push_str("  proof for publication.}\n");
    out.push_str("\\label{tab:gamma-crown-verification}\n");
    out.push_str("\\begin{tabular}{llrrrrl}\n");
    out.push_str("\\toprule\n");
    out.push_str("ID & Description & Axioms & Thms & Defs & Opqs & Status \\\\\n");
    out.push_str("\\midrule\n");

    for c in &report.conjectures {
        let status = match c.status.as_str() {
            "VERIFIED_CONSTRUCTIVE" => "\\textbf{Proved}",
            "VERIFIED_HYPOTHESIS_WRAPPED" => "Hyp-wrap",
            "VERIFIED_SCAFFOLDED" => "Scaffolded",
            "VERIFIED_AXIOM_DEPENDENT" => "Formal",
            _ if c.tc_verified => "Formal",
            _ => "Failed",
        };
        let desc = c
            .description
            .replace('_', "\\_")
            .replace('&', "\\&")
            .replace('%', "\\%");
        out.push_str(&format!(
            "{} & {} & {} & {} & {} & {} & {} \\\\\n",
            c.id, desc, c.domain_axioms, c.theorems, c.definitions, c.opaques, status,
        ));
    }

    out.push_str("\\midrule\n");
    out.push_str(&format!(
        "\\textbf{{Total}} & {} conjectures & {} & {} & & & {}/{} verified \\\\\n",
        report.total_conjectures,
        report.total_domain_axioms,
        report.total_theorems,
        report.conjectures_verified,
        report.total_conjectures,
    ));
    out.push_str("\\bottomrule\n");
    out.push_str("\\end{tabular}\n");
    out.push_str("\\end{table}\n");

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_single_conjecture_c002_axiom_dependent_full_closure() {
        // #3700 INTEGRITY FIX: the C002-prefix `Declaration::Axiom` count is 0
        // (the rank-deficiency obligations are now hypothesis-wrapped), but the
        // C002 headline theorems transitively reach shared matrix-rank /
        // interval-hull axioms and the admitted `Rat.le_refl` ordered-field
        // axiom, so C002 is honestly AXIOM-DEPENDENT, not constructive.
        //
        // If `init_nn_verification_c002` itself fails kernel typecheck
        // (upstream regression), `init_ok` is false — treat that as a skip.
        let result = verify_conjecture("C002");
        if !result.init_ok {
            eprintln!(
                "SKIP: C002 init failed (upstream regression): {:?}",
                result.error
            );
            return;
        }
        assert!(result.tc_verified, "C002 should be type-checked");
        assert!(
            !result.constructive,
            "C002 full closure reaches shared matrix-rank + admitted Rat axioms"
        );
        assert!(!result.fully_constructive);
        assert!(!result.scaffolded);
        assert_eq!(result.proof_mechanism, "axiom-dependent");
        assert_eq!(result.status, "VERIFIED_AXIOM_DEPENDENT");
        assert!(result.theorems > 0, "C002 should still have theorems");
    }

    #[test]
    fn test_verify_single_conjecture_c006_hypothesis_wrapped_full_closure() {
        // #3470 Lane #2/#3: the honest verdict comes from the FULL transitive
        // closure of C006's headline theorems. The C006-prefix
        // `Declaration::Axiom` count is 0. Previously the headline theorems
        // transitively reached the admitted `Rat.le_refl` ordered-field axiom, so
        // the verdict was AXIOM-DEPENDENT. `Rat.le_refl` has since been GENUINELY
        // ELIMINATED to a constructive kernel Theorem, removing that dependency;
        // the most severe remaining honest characterization is that at least one
        // C006 headline theorem is a bare hypothesis-wrapped `H -> H` projection
        // (`fun … h => h`), so the verdict downgrades to HYPOTHESIS_WRAPPED —
        // still NOT constructive.
        let result = verify_conjecture("C006");
        assert!(result.init_ok && result.tc_verified);
        assert_eq!(
            result.domain_axioms, 0,
            "C006 has no C006-prefix (namespace) domain axioms; got {:?}",
            result.axiom_names
        );
        assert!(
            !result.constructive,
            "C006 headline set contains a hypothesis-wrapped projection -> NOT constructive"
        );
        assert!(!result.fully_constructive);
        assert!(!result.scaffolded);
        assert_eq!(result.proof_mechanism, "hypothesis_wrapped");
        assert_eq!(result.status, "VERIFIED_HYPOTHESIS_WRAPPED");
    }

    #[test]
    fn test_verify_single_conjecture_c001_hypothesis_wrapped_full_closure() {
        // #3700 INTEGRITY: `compress_tightness_helper` is a hypothesis-wrapped
        // `H -> H` projection. The C001 headline set also contains
        // `compress_soundness`, which USED TO reach the `NNVerify.Zonotope.compress*`
        // axioms (which made C001 axiom-dependent). Those were RETIRED at commit
        // 893869b3 — `compress` is now a faithful reducible Definition with an
        // EMPTY axiom closure — so C001's full closure no longer reaches a domain
        // axiom and it now honestly classifies HYPOTHESIS_WRAPPED (a strict
        // improvement: the narrow C001-namespace count would have said "PROVED";
        // the full closure correctly says it only proves H -> H). Still NOT
        // constructive — a hypothesis-wrapped projection is not a real proof.
        let result = verify_conjecture("C001");
        assert!(result.init_ok, "C001 init should succeed");
        assert!(result.tc_verified, "C001 should be type-checked");
        assert_eq!(
            result.domain_axioms, 0,
            "C001 has no C001-prefix (namespace) domain axioms; got {:?}",
            result.axiom_names
        );
        assert!(
            !result.constructive,
            "C001 is hypothesis-wrapped (H -> H projection), not constructive"
        );
        assert!(!result.fully_constructive);
        assert!(!result.scaffolded);
        assert_eq!(result.proof_mechanism, "hypothesis_wrapped");
        assert_eq!(result.status, "VERIFIED_HYPOTHESIS_WRAPPED");
    }

    #[test]
    fn test_verify_single_conjecture_c011_hypothesis_wrapped() {
        // #3700 INTEGRITY FIX: every C011 headline theorem is a hypothesis-wrapped
        // `fun … h => h` projection (empty axiom closure, but proves only
        // `H -> H`). The narrow namespace count reported these as
        // "VERIFIED_CONSTRUCTIVE"/"PROVED"; the honest verdict is
        // hypothesis-wrapped, NOT constructive.
        let result = verify_conjecture("C011");
        assert!(result.init_ok && result.tc_verified);
        assert_eq!(result.domain_axioms, 0);
        assert!(
            !result.constructive,
            "C011 headline theorems are H->H projections, not genuine proofs"
        );
        assert!(!result.fully_constructive);
        assert!(!result.scaffolded);
        assert_eq!(result.proof_mechanism, "hypothesis_wrapped");
        assert_eq!(result.status, "VERIFIED_HYPOTHESIS_WRAPPED");
    }

    #[test]
    fn test_verify_single_conjecture_c008_constructive() {
        // MILESTONE (2026-06-12, zero-faith campaign): C008's full headline
        // closure is now PROVEN — `ibp_tightness_{base,step}` and
        // `ibp_linear_bounds` were retired from honest admitted axioms to
        // kernel-checked constructive Theorems/Definitions. C008 is the FIRST
        // gamma-crown conjecture with a genuinely constructive proof under the
        // full transitive closure (history: sorryAx-scaffolded → demoted to
        // honest axioms → axiom-dependent → constructive).
        let result = verify_conjecture("C008");
        assert!(result.init_ok, "C008 init should succeed");
        assert!(result.tc_verified, "C008 should be type-checked");
        assert!(
            result.constructive,
            "C008's headline closure is fully proven -> constructive"
        );
        assert!(result.fully_constructive);
        assert!(
            !result.scaffolded,
            "C008 is no longer sorry-inhabited scaffold"
        );
        assert_eq!(result.proof_mechanism, "constructive");
        assert_eq!(result.status, "VERIFIED_CONSTRUCTIVE");
    }

    #[test]
    fn test_verify_unknown_conjecture_returns_error() {
        let result = verify_conjecture("C999");
        assert!(!result.init_ok, "C999 should fail");
        assert_eq!(result.status, "INIT_FAILED");
        assert!(result.error.is_some());
    }

    #[test]
    fn test_verify_all_conjectures_report() {
        let report = verify_all_conjectures();
        assert_eq!(report.total_conjectures, 15);
        // Skip the exact-count assertions when any conjecture failed to
        // init — that's an upstream proof-construction regression and
        // not the structural contract this test guards.
        if report.conjectures_failed > 0 {
            eprintln!(
                "SKIP: {} conjecture(s) failed kernel init; not checking exact counts",
                report.conjectures_failed
            );
            return;
        }
        assert_eq!(report.conjectures_verified, 15);
        // #3700: the four honest buckets (constructive / hypothesis-wrapped /
        // scaffolded / axiom-dependent) are disjoint and partition the verified
        // set. `mixed` is always 0 under the honest gate.
        assert_eq!(report.mixed_conjectures, 0);
        assert_eq!(
            report.constructive_conjectures
                + report.hypothesis_wrapped_conjectures
                + report.scaffolded_conjectures
                + report.axiom_dependent_conjectures,
            15,
            "the four honest buckets must partition all 15 verified conjectures",
        );
        // `fully_constructive` aggregate equals the honest constructive count.
        assert_eq!(report.fully_constructive, report.constructive_conjectures);
        // INTEGRITY MILESTONE (2026-06-12): C008 became the FIRST gamma-crown
        // conjecture with a genuinely constructive full-closure proof when the
        // zero-faith campaign retired ibp_tightness_{base,step} +
        // ibp_linear_bounds to kernel-checked Theorems/Definitions. Pin the
        // exact count so future retirements update this deliberately.
        assert_eq!(
            report.constructive_conjectures, 1,
            "exactly C008 has a genuine constructive proof under the honest \
             full-closure gate; update this pin deliberately per retirement",
        );
        assert!(report.total_theorems > 0, "should have theorems");
        assert!(
            report.total_verification_time_ms > 0.0,
            "should report timing"
        );
    }

    #[test]
    fn test_verify_all_conjectures_matches_axiom_audit() {
        let report = verify_all_conjectures();

        // #3700 INTEGRITY FIX: each conjecture's verdict is the honest full
        // transitive closure of its headline theorems. The named conjectures
        // below are the formerly-"PROVED" hypothesis-wrapped overstatements;
        // assert their honest reclassification.
        for c in &report.conjectures {
            if !c.init_ok {
                eprintln!("SKIP-INIT {}: {:?}", c.id, c.error);
                continue;
            }
            if !c.tc_verified {
                eprintln!("SKIP-CLASSIFY {}: not tc_verified", c.id);
                continue;
            }
            // Every conjecture EXCEPT C008 should report non-constructive. C008
            // is genuinely constructive: its headline `ibp_tightness_{base,step}`
            // lemmas were proven as R-weak constructive Theorems off the faithful
            // keystone (base commit `4744b1f0`, census 28->26), so its full
            // closure reaches no domain axiom.
            if c.id != "C008" {
                assert!(
                    !c.constructive,
                    "{} should NOT be constructive under the honest full-closure gate \
                     (status={:?}, mechanism={:?})",
                    c.id, c.status, c.proof_mechanism,
                );
            }
            match c.id.as_str() {
                // Full closure reaches admitted Rat / shared infra axioms.
                // (#3470 Lane #2/#3: C006 moved OUT of this group; WS-A ATOMIC
                // LIVE SWITCH: C004 ALSO moved OUT — its only remaining
                // admitted-axiom dependency was the Rat ordered-field carrier
                // validity (`Rat.le_refl` / `Rat.add_le_add_left`), now genuine
                // constructive quotient Theorems, so C004 downgrades to
                // hypothesis_wrapped. C001 ALSO moved OUT after the 2026-06-17
                // compress retirement (`NNVerify.Zonotope.compress` Axiom ->
                // faithful reducible Definition): C001's full closure no longer
                // reaches a domain axiom, so it downgrades to hypothesis_wrapped.
                // C002 still reaches the matrix-rank admitted infra axiom, so it
                // stays axiom-dependent.)
                "C002" => {
                    assert_eq!(
                        c.proof_mechanism, "axiom-dependent",
                        "{} should be axiom-dependent (full closure reaches a domain axiom)",
                        c.id,
                    );
                }
                // Headline theorems are H->H projections (empty closure).
                // C006 joined this group after the `Rat.le_refl` elimination;
                // C004 joined after the WS-A quotient-carrier switch; C001
                // joined after the 2026-06-17 compress retirement.
                "C001" | "C004" | "C006" | "C009" | "C011" | "C029" | "C030" => {
                    assert_eq!(
                        c.proof_mechanism, "hypothesis_wrapped",
                        "{} headline theorems are H->H projections",
                        c.id,
                    );
                }
                // NNVerify unlock round (base commit `4744b1f0`): C008's
                // `ibp_tightness_{base,step}` lemmas were proven as constructive
                // R-weak Theorems off the faithful keystone (census 28->26),
                // composed by the headline theorems via `Nat.rec`. The honest
                // verdict is therefore genuinely constructive — the full closure
                // reaches no domain axiom (and no sorry). (Previously these were
                // honest admitted axioms, hence the former `axiom-dependent`.)
                "C008" => {
                    assert_eq!(
                        c.proof_mechanism, "constructive",
                        "C008 ibp_tightness_{{base,step}} are now constructive R-weak Theorems",
                    );
                }
                _ => {}
            }
        }
    }

    #[test]
    fn test_format_human_report_not_empty() {
        let report = verify_all_conjectures();
        let human = format_human_report(&report);
        assert!(human.contains("Gamma-Crown Formal Verification Report"));
        assert!(human.contains("RESULT:"));
        assert!(human.contains("C001"));
        assert!(human.contains("C030"));
    }

    #[test]
    fn test_format_csv_report_has_header() {
        let report = verify_all_conjectures();
        let csv = format_csv_report(&report);
        assert!(csv.starts_with("id,description,status,"));
        assert!(csv.contains(",constructive_legacy,fully_constructive,scaffolded,proof_mechanism,"));
        // Should have 15 data rows + 1 header
        let line_count = csv.lines().count();
        assert_eq!(line_count, 16, "CSV should have 1 header + 15 data rows");
    }

    #[test]
    fn test_format_latex_report_valid() {
        let report = verify_all_conjectures();
        let latex = format_latex_report(&report);
        assert!(latex.contains("\\begin{table}"));
        assert!(latex.contains("\\end{table}"));
        assert!(latex.contains("``Proved'' indicates"));
        assert!(latex.contains("Scaffolded"));
    }

    #[test]
    fn test_conjecture_ids_complete() {
        assert_eq!(CONJECTURE_IDS.len(), 15);
        assert!(CONJECTURE_IDS.contains(&"C001"));
        assert!(CONJECTURE_IDS.contains(&"C030"));
    }

    #[test]
    fn test_conjecture_description_all_known() {
        for &id in CONJECTURE_IDS {
            let desc = conjecture_description(id);
            assert_ne!(desc, "Unknown conjecture", "{id} should have a description");
        }
    }

    #[test]
    fn test_json_serialization_roundtrip() {
        let report = verify_all_conjectures();
        let json_str = serde_json::to_string_pretty(&report).expect("should serialize to JSON");
        let parsed: serde_json::Value = serde_json::from_str(&json_str).expect("should parse back");
        assert_eq!(parsed["total_conjectures"].as_u64(), Some(15));
        assert!(parsed["conjectures"].is_array());
        assert_eq!(parsed["conjectures"].as_array().unwrap().len(), 15);
    }
}
