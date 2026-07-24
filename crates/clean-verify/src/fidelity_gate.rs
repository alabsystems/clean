// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential model-vs-kernel fidelity gate.
//!
//! ## What this is
//!
//! The self-verification metatheorems in this crate now use a nine-constructor
//! `KExpr` *model* of the kernel, while this differential inference gate covers
//! only the closed six-constructor subset named below. The claim "the model
//! agrees with the deployed Rust kernel on type inference" was HISTORICALLY
//! recorded as the total-equality axiom `bootstrap_model_fidelity`
//! (`model_infer_type e ctx = kernel_infer_type e ctx`). That axiom was RETIRED
//! by the opaque-constant re-architecture (the relational restatement — see
//! `crate::bootstrap::spec_registration`): a total equality between two *total*
//! functions masquerades a *partial* inference algorithm, forcing agreement even
//! on ill-typed junk. The faithful spec-level representation of the Rust
//! algorithm is now the inductive `KernelInfers` relation, with its soundness
//! obligation `bootstrap_infer_sound` against the declarative `TypingCtxConv`.
//!
//! This module is the **empirical, large-corpus, fail-closed, continuously-
//! checked differential gate** that corroborates the *faithfulness* of that
//! reflection: it runs the real Rust kernel against the reflected micro-checker
//! and measures agreement (a ratchetable fidelity metric). It replaces the old
//! "~5-term, test-justified" corpus once exercised by
//! [`crate::bootstrap_checker::BootstrapChecker::reflection_check`].
//!
//! The unit under test is
//! [`crate::bootstrap_checker::BootstrapChecker::recheck_kernel_inference`]: it
//! runs the *real* `clean_kernel::TypeChecker::infer_type`, then independently
//! re-infers with the small code-independent micro-checker, and asserts
//! definitional-equality agreement (a `KernelDisagreement` on mismatch). The
//! gate drives that unit over two corpus sources.
//!
//! ## Honest framing (empirical corroboration, not a kernel proof)
//!
//! The model ↔ Rust-implementation bridge **cannot become a kernel `Theorem`**:
//! by Gödelian / level constraints the kernel cannot internally prove that the
//! Rust source equals the reflected model. (This is exactly why the total-
//! equality `bootstrap_model_fidelity` axiom was the wrong shape and was retired
//! in favor of the relational `KernelInfers` / `bootstrap_infer_sound`
//! restatement, whose soundness *is* an in-kernel obligation.) What this gate
//! buys is purely the strongest *honest* empirical corroboration available for
//! the claim that the reflection is faithful to the deployed kernel:
//!
//! - "5-term test" → "large-corpus, fail-closed, continuously-checked gate";
//! - "bare `known_drift_max = 15` ceiling" → an **enumerated, justified
//!   allowlist** of known divergences (zero, for the closed 6-ctor fragment);
//! - a **measurable fidelity number** (checked / agreed / known-divergent /
//!   excluded / supported-fragment coverage) that can be ratcheted.
//!
//! ## The supported fragment
//!
//! The micro-checker gate only accepts the closed core
//! `{Sort, BVar, Pi, Lam, App, Let}` (with `MData` stripped transparently). Every
//! corpus term is partitioned by [`in_supported_fragment`] into:
//!
//! - **supported** → fed to `recheck_kernel_inference` and *must agree*;
//! - **excluded** → counted (never silently skipped) with the rejecting
//!   constructor name as the reason, driving an exclusion histogram.
//!
//! `Const`/`Lit`/`Proj`/`FVar`/`SProp`/`Squash`/`Cubical*`/`ZFC*` are all
//! out of fragment.
//!
//! ## Check mode, not infer-only (a finding this gate surfaced)
//!
//! The micro-checker is a *full* checker: it always validates App argument
//! types and Lam/Pi domain sorts. The kernel's *default* `infer_type` runs the
//! Lean-4 `infer_only = true` fast path, which deliberately **skips** those
//! checks. Running the always-checking micro-checker against the infer-only
//! kernel produces a whole family of "divergences" — not just the documented
//! ≤15 let-universe cases (which live in the excluded `Let`), but also App
//! argument mismatches and Lam-domain-non-sort cases inside the gated
//! `{Sort, BVar, Pi, Lam, App}` fragment. The first run of this gate's fuzz arm
//! caught ~13 of them per 512 terms.
//!
//! **These are not soundness bugs and not genuine model↔kernel disagreements.**
//! They are the infer-only fast-path permissiveness gap: the kernel's *check
//! mode* (`infer_only = false`, the path `Environment::add_decl` uses to admit
//! declarations) enforces exactly the checks the micro-checker performs.
//! Check mode is the soundness-relevant deployed contract, so the gate compares
//! the micro-checker against the kernel **in check mode** (see
//! [`KernelVerdict`]) — apples-to-apples. With that comparison the
//! known-divergence allowlist for the gated fragment is (and, on the current
//! tree, stays) **empty**, and that emptiness is itself the honest claim.

use crate::bootstrap_checker::BootstrapChecker;
use clean_kernel::{Declaration, Environment, Expr, ExprKind, Name, TypeChecker};
use std::collections::BTreeMap;

/// The six constructors the micro-checker (and therefore the gate's supported
/// fragment) models. Used for the supported-fragment coverage vector.
/// `Let` joined the fragment with the let-promotion surgery (task #28): the
/// spec `KExpr` now has a genuine `let_` constructor with zeta reduction, and
/// the bootstrap checker mirrors the kernel's Let rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FragmentCtor {
    Sort,
    BVar,
    Pi,
    Lam,
    App,
    Let,
}

impl FragmentCtor {
    /// All six constructors, in coverage-report order.
    pub const ALL: [FragmentCtor; 6] = [
        FragmentCtor::Sort,
        FragmentCtor::BVar,
        FragmentCtor::Pi,
        FragmentCtor::Lam,
        FragmentCtor::App,
        FragmentCtor::Let,
    ];

    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            FragmentCtor::Sort => "Sort",
            FragmentCtor::BVar => "BVar",
            FragmentCtor::Pi => "Pi",
            FragmentCtor::Lam => "Lam",
            FragmentCtor::App => "App",
            FragmentCtor::Let => "Let",
        }
    }
}

/// Supported-fragment predicate.
///
/// Returns `Ok(())` when `e` (after stripping `MData`) is in the closed
/// `{Sort, BVar, Pi, Lam, App, Let}` fragment **and** is well scoped (every
/// `BVar` index is bound by an enclosing `Lam`/`Pi`/`Let`, i.e. the term is closed at
/// `scope_depth = 0`). Otherwise returns `Err(reason)` where `reason` names the
/// out-of-fragment constructor (or `"bvar-escape"` for an unbound de Bruijn
/// index). The `Err` reason is the single source of truth for the exclusion
/// histogram — out-of-fragment terms are *counted*, never silently skipped.
pub fn in_supported_fragment(e: &Expr, scope_depth: u32) -> Result<(), &'static str> {
    match e.strip_mdata().kind() {
        ExprKind::Sort(_) => Ok(()),
        ExprKind::BVar(idx) => {
            if *idx < scope_depth {
                Ok(())
            } else {
                Err("bvar-escape")
            }
        }
        ExprKind::App(f, a) => {
            in_supported_fragment(f.as_ref(), scope_depth)?;
            in_supported_fragment(a.as_ref(), scope_depth)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            in_supported_fragment(ty.as_ref(), scope_depth)?;
            in_supported_fragment(body.as_ref(), scope_depth + 1)
        }
        ExprKind::Const(_, _) => Err("Const"),
        ExprKind::Let(_, ty, val, body, _) => {
            in_supported_fragment(ty.as_ref(), scope_depth)?;
            in_supported_fragment(val.as_ref(), scope_depth)?;
            in_supported_fragment(body.as_ref(), scope_depth + 1)
        }
        ExprKind::Lit(_) => Err("Lit"),
        ExprKind::Proj(_, _, _) => Err("Proj"),
        ExprKind::FVar(_) => Err("FVar"),
        ExprKind::SProp => Err("SProp"),
        ExprKind::Squash(_) => Err("Squash"),
        ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::CubicalPath { .. }
        | ExprKind::CubicalPathLam { .. }
        | ExprKind::CubicalPathApp { .. }
        | ExprKind::CubicalHComp { .. }
        | ExprKind::CubicalTransp { .. }
        | ExprKind::CubicalCoe { .. } => Err("Cubical"),
        ExprKind::ZFCSet(_) | ExprKind::ZFCMem { .. } | ExprKind::ZFCComprehension { .. } => {
            Err("ZFC")
        }
        // MData is stripped above; this arm is unreachable in practice but keeps
        // the match exhaustive without a wildcard (so new ExprKind variants
        // force a compile error rather than being silently treated as
        // in-fragment).
        ExprKind::MData(_, inner) => in_supported_fragment(inner.as_ref(), scope_depth),
    }
}

/// Records which of the six fragment constructors a (supported, closed) term
/// exercises. Used to compute supported-fragment coverage.
fn record_coverage(e: &Expr, cov: &mut [bool; 6]) {
    match e.strip_mdata().kind() {
        ExprKind::Sort(_) => cov[0] = true,
        ExprKind::BVar(_) => cov[1] = true,
        ExprKind::Pi(_, ty, body) => {
            cov[2] = true;
            record_coverage(ty.as_ref(), cov);
            record_coverage(body.as_ref(), cov);
        }
        ExprKind::Lam(_, ty, body) => {
            cov[3] = true;
            record_coverage(ty.as_ref(), cov);
            record_coverage(body.as_ref(), cov);
        }
        ExprKind::App(f, a) => {
            cov[4] = true;
            record_coverage(f.as_ref(), cov);
            record_coverage(a.as_ref(), cov);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            cov[5] = true;
            record_coverage(ty.as_ref(), cov);
            record_coverage(val.as_ref(), cov);
            record_coverage(body.as_ref(), cov);
        }
        // Out-of-fragment terms never reach here (they are excluded first).
        _ => {}
    }
}

/// A stable, deterministic structural digest of an `Expr`, used as the
/// allowlist key for fuzz-generated terms (the Debug string embeds verbose,
/// brittle detail; surface strings are not available for synthesized terms).
///
/// The digest is a 64-bit FNV-1a hash over a canonical byte serialization of
/// the constructor skeleton (`Sort` levels are folded to a coarse shape tag, so
/// the key is stable across runs and does not depend on `Arc` identities).
#[must_use]
pub fn structural_key(e: &Expr) -> u64 {
    fn fold(e: &Expr, h: &mut u64) {
        const PRIME: u64 = 0x0000_0100_0000_01B3;
        let mut byte = |b: u8, h: &mut u64| {
            *h ^= u64::from(b);
            *h = h.wrapping_mul(PRIME);
        };
        match e.strip_mdata().kind() {
            ExprKind::Sort(_) => byte(1, h),
            ExprKind::BVar(i) => {
                byte(2, h);
                for b in i.to_le_bytes() {
                    byte(b, h);
                }
            }
            ExprKind::App(f, a) => {
                byte(3, h);
                fold(f.as_ref(), h);
                fold(a.as_ref(), h);
            }
            ExprKind::Lam(_, ty, body) => {
                byte(4, h);
                fold(ty.as_ref(), h);
                fold(body.as_ref(), h);
            }
            ExprKind::Pi(_, ty, body) => {
                byte(5, h);
                fold(ty.as_ref(), h);
                fold(body.as_ref(), h);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                byte(6, h);
                fold(ty.as_ref(), h);
                fold(val.as_ref(), h);
                fold(body.as_ref(), h);
            }
            // Out-of-fragment shapes get a single distinguishing tag; they are
            // never keyed in practice (excluded before the gate runs).
            _ => byte(255, h),
        }
    }
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    fold(e, &mut h);
    h
}

/// One enumerated, reviewed, justified known divergence between the model and
/// the Rust kernel **within the supported fragment**.
///
/// A divergence may pass the gate *only* if its `key` appears here, with a
/// written `root_cause` and `note`. Widening the allowlist is allowed *only* by
/// adding a specific reviewed key — never by category or pattern. This mirrors
/// the `add_decl_unchecked` ratchet discipline.
#[derive(Debug, Clone, Copy)]
pub struct KnownDivergence {
    /// Stable structural key of the divergent term (see [`structural_key`]).
    pub key: u64,
    /// Single-phrase root cause (e.g. the deliberate infer-only permissiveness).
    pub root_cause: &'static str,
    /// Why this specific divergence is sound / expected.
    pub note: &'static str,
}

/// The enumerated known-divergence allowlist for the closed 6-ctor fragment.
///
/// **It is intentionally empty.** There is no known divergence within
/// `{Sort, BVar, Pi, Lam, App, Let}` — the gate compares against the kernel in
/// CHECK mode, where the kernel's Let rule (annotation is a sort, value has the
/// annotated type, body typed through the zeta substitution) is exactly what
/// the bootstrap checker mirrors, so the historical `infer_only` Let
/// permissiveness divergence does not arise. The gate's job is to keep the
/// list empty: any *new* divergence in the gated fragment fails the gate until
/// a reviewer adds a specific key here with a justification (or fixes the bug).
pub const KNOWN_DIVERGENCES: &[KnownDivergence] = &[];

/// Look up a structural key in the allowlist.
#[must_use]
pub fn known_divergence_for(key: u64) -> Option<&'static KnownDivergence> {
    KNOWN_DIVERGENCES.iter().find(|d| d.key == key)
}

/// Outcome of running the gate over one corpus term.
#[derive(Debug, Clone, PartialEq, Eq)]
enum TermOutcome {
    /// In-fragment; model and kernel agreed (both inferred a def-eq type, or
    /// both rejected).
    Agreed,
    /// In-fragment; model and kernel disagreed, but the term's structural key is
    /// on the explicit allowlist.
    KnownDivergent,
    /// In-fragment; model and kernel disagreed and the key is NOT allowlisted.
    /// This is the fail-closed signal.
    NewDivergence { key: u64, detail: String },
    /// Out of the supported fragment; counted with the rejecting ctor reason.
    Excluded(&'static str),
}

/// The kernel's check-mode inferred type for a term, or a rejection.
///
/// ## Why check mode, not the default `infer_type`
///
/// The micro-checker ([`BootstrapChecker::infer_type`]) is a *full* checker: it
/// unconditionally validates App argument types and Lam/Pi domain sorts. The
/// kernel's default `infer_type` runs `infer_only = true` — a deliberate Lean-4
/// fast path (`type_checker.cpp` `infer_app` / `infer_lambda`) that **skips**
/// those checks, on the contract that the caller has already established
/// well-typedness. Comparing the always-checking micro-checker against the
/// infer-only kernel therefore surfaces the *infer-only permissiveness gap* as
/// "divergences" — but these are NOT soundness bugs and NOT genuine
/// model↔kernel disagreements: the kernel's **check mode** (`infer_only =
/// false`, the path `Environment::add_decl` uses to admit declarations) does
/// enforce exactly the checks the micro-checker performs. Check mode is the
/// soundness-relevant deployed contract, so the gate compares the micro-checker
/// against the kernel in check mode (apples-to-apples) via the kernel's
/// type-returning check-mode entry point
/// [`TypeChecker::infer_type_full`].
fn kernel_check_infer(e: &Expr) -> Result<Expr, clean_kernel::KernelTypeError> {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    tc.infer_type_full(e)
}

/// Run the differential check on a single corpus term.
///
/// Partitions by [`in_supported_fragment`]; for supported terms, requires
/// model/kernel **agreement** between the always-checking micro-checker
/// ([`BootstrapChecker::infer_type`]) and the kernel in **check mode**
/// ([`kernel_check_infer`]):
///
/// - micro accepts with `m` & kernel infers `k` def-eq to `m` → `Agreed`.
/// - micro accepts but kernel infers a type not def-eq to `m` → divergence.
/// - micro accepts but kernel check-mode rejects → divergence (model too
///   permissive).
/// - micro rejects & kernel check-mode also rejects → `Agreed`
///   (agreement-on-rejection).
/// - micro rejects but kernel check-mode accepts → divergence (model too
///   strict).
///
/// Allowlisted divergences become `KnownDivergent`; all others are the
/// fail-closed `NewDivergence`.
fn check_term(checker: &BootstrapChecker, e: &Expr) -> TermOutcome {
    if let Err(reason) = in_supported_fragment(e, 0) {
        return TermOutcome::Excluded(reason);
    }

    let key = structural_key(e);
    let divergent = |detail: String| match known_divergence_for(key) {
        Some(_) => TermOutcome::KnownDivergent,
        None => TermOutcome::NewDivergence { key, detail },
    };

    match (checker.infer_type(e), kernel_check_infer(e)) {
        // Both accept: agree iff the inferred types are def-eq (kernel decides
        // def-eq, the soundness-relevant relation).
        (Ok(micro_ty), Ok(kernel_ty)) => {
            let env = Environment::new();
            let tc = TypeChecker::new(&env);
            if tc.is_def_eq(&micro_ty, &kernel_ty) {
                TermOutcome::Agreed
            } else {
                divergent(format!(
                    "type mismatch: kernel(check)={kernel_ty:?} micro={micro_ty:?}"
                ))
            }
        }
        // Both reject: agreement-on-rejection.
        (Err(_), Err(_)) => TermOutcome::Agreed,
        // Micro accepts but kernel check-mode rejects: model too permissive.
        (Ok(micro_ty), Err(kernel_err)) => divergent(format!(
            "micro accepted with {micro_ty:?} but kernel(check) rejected ({kernel_err})"
        )),
        // Kernel accepts but micro rejects: model too strict.
        (Err(micro_err), Ok(kernel_ty)) => divergent(format!(
            "micro rejected ({micro_err}) but kernel(check) accepted with {kernel_ty:?}"
        )),
    }
}

/// A measurable, ratchetable fidelity metric for one gate run.
///
/// Invariant the gate enforces (fail-closed):
/// `terms_supported == terms_agreed + terms_known_divergent`, with
/// `new_divergences` empty. Any unaccounted disagreement aborts the gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FidelityMetric {
    /// Every corpus term considered, from both sources.
    pub terms_total: usize,
    /// Terms in the supported fragment (fed to the differential check).
    pub terms_supported: usize,
    /// Supported terms where model and kernel agreed.
    pub terms_agreed: usize,
    /// Supported terms divergent but on the explicit allowlist.
    pub terms_known_divergent: usize,
    /// Terms outside the supported fragment (counted, not silently skipped).
    pub terms_excluded_unsupported: usize,
    /// Per-reason histogram of excluded terms (ctor name → count).
    pub exclusion_histogram: BTreeMap<String, usize>,
    /// Which of {Sort, BVar, Pi, Lam, App, Let} were exercised by supported terms.
    pub fragment_coverage: [bool; 6],
    /// NEW divergences (not allowlisted). Non-empty ⇒ the gate must FAIL.
    pub new_divergences: Vec<NewDivergenceReport>,
}

/// A single new (non-allowlisted) divergence — the fail-closed evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewDivergenceReport {
    /// Structural key (paste into [`KNOWN_DIVERGENCES`] only after review).
    pub key: u64,
    /// Human-readable detail of the disagreement.
    pub detail: String,
}

impl FidelityMetric {
    fn new() -> Self {
        Self {
            terms_total: 0,
            terms_supported: 0,
            terms_agreed: 0,
            terms_known_divergent: 0,
            terms_excluded_unsupported: 0,
            exclusion_histogram: BTreeMap::new(),
            fragment_coverage: [false; 6],
            new_divergences: Vec::new(),
        }
    }

    /// Fold one term's outcome into the metric.
    fn observe(&mut self, e: &Expr, outcome: TermOutcome) {
        self.terms_total += 1;
        match outcome {
            TermOutcome::Agreed => {
                self.terms_supported += 1;
                self.terms_agreed += 1;
                record_coverage(e, &mut self.fragment_coverage);
            }
            TermOutcome::KnownDivergent => {
                self.terms_supported += 1;
                self.terms_known_divergent += 1;
                record_coverage(e, &mut self.fragment_coverage);
            }
            TermOutcome::NewDivergence { key, detail } => {
                self.terms_supported += 1;
                record_coverage(e, &mut self.fragment_coverage);
                self.new_divergences
                    .push(NewDivergenceReport { key, detail });
            }
            TermOutcome::Excluded(reason) => {
                self.terms_excluded_unsupported += 1;
                *self
                    .exclusion_histogram
                    .entry(reason.to_string())
                    .or_insert(0) += 1;
            }
        }
    }

    /// The gate verdict: true iff there are NO new (non-allowlisted)
    /// divergences. This is the fail-closed condition — a single brand-new
    /// divergence makes it false.
    #[must_use]
    pub fn passed(&self) -> bool {
        self.new_divergences.is_empty()
    }

    /// Supported-fragment coverage = how many of the 6 ctors were exercised.
    #[must_use]
    pub fn coverage_count(&self) -> usize {
        self.fragment_coverage.iter().filter(|c| **c).count()
    }

    /// Human-readable one-block summary for the test log / audit lane.
    #[must_use]
    pub fn report(&self) -> String {
        use std::fmt::Write as _;
        let mut s = String::new();
        let _ = writeln!(s, "── model↔kernel fidelity gate ──────────────────");
        let _ = writeln!(s, "  terms_total              = {}", self.terms_total);
        let _ = writeln!(s, "  terms_supported          = {}", self.terms_supported);
        let _ = writeln!(s, "  terms_agreed             = {}", self.terms_agreed);
        let _ = writeln!(
            s,
            "  terms_known_divergent    = {} (allowlist size = {})",
            self.terms_known_divergent,
            KNOWN_DIVERGENCES.len()
        );
        let _ = writeln!(
            s,
            "  terms_excluded_unsupported = {}",
            self.terms_excluded_unsupported
        );
        if !self.exclusion_histogram.is_empty() {
            let _ = writeln!(s, "  exclusion histogram:");
            for (reason, count) in &self.exclusion_histogram {
                let _ = writeln!(s, "      {reason:<10} = {count}");
            }
        }
        let covered: Vec<&str> = FragmentCtor::ALL
            .iter()
            .zip(self.fragment_coverage.iter())
            .filter(|(_, c)| **c)
            .map(|(ctor, _)| ctor.name())
            .collect();
        let _ = writeln!(
            s,
            "  supported-fragment coverage = {}/5 [{}]",
            self.coverage_count(),
            covered.join(", ")
        );
        let _ = writeln!(
            s,
            "  new_divergences (fail-closed) = {}",
            self.new_divergences.len()
        );
        for d in &self.new_divergences {
            let _ = writeln!(s, "      key={:#018x} : {}", d.key, d.detail);
        }
        let _ = writeln!(
            s,
            "  VERDICT: {}",
            if self.passed() { "PASS" } else { "FAIL" }
        );
        s
    }
}

/// Run the gate over an arbitrary slice of corpus terms.
///
/// This is the corpus-agnostic engine; corpus *sources* (fuzz, olean) live in
/// the test module / `crate::bootstrap_checker` callers. It never panics on an
/// excluded term — it counts it.
#[must_use]
pub fn run_gate(terms: &[Expr]) -> FidelityMetric {
    let checker = BootstrapChecker::new();
    let mut metric = FidelityMetric::new();
    for term in terms {
        let outcome = check_term(&checker, term);
        metric.observe(term, outcome);
    }
    metric
}

/// Anonymous non-dependent let node (Expr::let_ is deprecated in favor of
/// the explicit-name constructor; the gate only needs the anonymous shape).
fn let_anon(ty: Expr, val: Expr, body: Expr) -> Expr {
    Expr::let_named(clean_kernel::Name::anon(), ty, val, body, false)
}

/// A deterministic, proptest-free corpus of small closed in-fragment terms,
/// built by systematic enumeration over the `{Sort, BVar, Pi, Lam, App, Let}`
/// fragment up to a small depth. Available in normal (non-test) builds so a
/// `clean audit` lane can run the gate reproducibly (the proptest fuzz arm
/// lives in the test module and is only built under `cfg(test)`).
#[must_use]
pub fn deterministic_core_corpus() -> Vec<Expr> {
    use clean_kernel::{BinderInfo, Level};

    // A small palette of sorts (Prop, Type 0, Type 1) plus, under a binder, the
    // innermost bound variable. We enumerate closed terms by tracking the
    // available binder depth, mirroring the fuzz generator's scope discipline
    // but exhaustively over a tiny grid.
    fn sorts() -> Vec<Expr> {
        vec![
            Expr::sort(Level::zero()),                           // Prop
            Expr::sort(Level::succ(Level::zero())),              // Type 0
            Expr::sort(Level::succ(Level::succ(Level::zero()))), // Type 1
        ]
    }

    // Closed atoms at a given binder depth: sorts always; bound vars when in
    // scope.
    fn atoms(depth: u32) -> Vec<Expr> {
        let mut v = sorts();
        for i in 0..depth {
            v.push(Expr::bvar(i));
        }
        v
    }

    let mut corpus: Vec<Expr> = Vec::new();

    // Depth-0 atoms (closed): just the sorts.
    corpus.extend(sorts());

    // Depth-1 compounds over closed atoms.
    let a0 = atoms(0); // closed atoms (sorts only)
    let a1 = atoms(1); // atoms with one binder in scope (sorts + BVar 0)
    for ty in &a0 {
        for body in &a1 {
            // λ (x : ty). body  and  Π (x : ty), body — body may use BVar 0.
            corpus.push(Expr::lam(BinderInfo::Default, ty.clone(), body.clone()));
            corpus.push(Expr::pi(BinderInfo::Default, ty.clone(), body.clone()));
        }
    }
    // Applications of closed atoms (mostly ill-typed → agreement-on-rejection).
    for f in &a0 {
        for x in &a0 {
            corpus.push(Expr::app(f.clone(), x.clone()));
        }
    }
    // A few well-typed applications: (λ x:S. x) S' .
    for s in &sorts() {
        for s2 in &sorts() {
            corpus.push(Expr::app(
                Expr::lam(BinderInfo::Default, s.clone(), Expr::bvar(0)),
                s2.clone(),
            ));
        }
    }
    // Nested binders: λ (x:S). λ (y:x). y  and  Π (x:S), Π (y:x), x .
    for s in &sorts() {
        corpus.push(Expr::lam(
            BinderInfo::Default,
            s.clone(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ));
        corpus.push(Expr::pi(
            BinderInfo::Default,
            s.clone(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ));
    }

    // Let bindings (the 6th fragment ctor, task #28): well-typed
    // `let x : Type_(n+1) := S in x` and `let x : S := y in body` shapes, plus
    // ill-typed annotation mismatches (agreement-on-rejection).
    for s in &sorts() {
        // let x : typeof(S) := S in x — well-typed zeta shape.
        corpus.push(let_anon(
            Expr::sort(Level::succ(match s.kind() {
                clean_kernel::ExprKind::Sort(l) => l.clone(),
                _ => Level::zero(),
            })),
            s.clone(),
            Expr::bvar(0),
        ));
        // let x : S := S in x — annotation mismatch (S : succ S, not S).
        corpus.push(let_anon(s.clone(), s.clone(), Expr::bvar(0)));
        // λ (x:S). let y : S := x in y — let under a binder using the lambda var.
        corpus.push(Expr::lam(
            BinderInfo::Default,
            s.clone(),
            let_anon(s.clone(), Expr::bvar(0), Expr::bvar(0)),
        ));
        // let x := S in (λ (y:x). y) — let value used as a type downstream.
        corpus.push(let_anon(
            Expr::sort(Level::succ(match s.kind() {
                clean_kernel::ExprKind::Sort(l) => l.clone(),
                _ => Level::zero(),
            })),
            s.clone(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ));
    }

    corpus
}

/// Run the fidelity gate over the deterministic core corpus and return the
/// metric. Intended entry point for a `clean audit` fidelity lane: a CLI can
/// print `metric.report()` and use `metric.passed()` as the exit verdict.
///
/// Fail-closed: `metric.passed()` is `false` iff any supported term produced a
/// new (non-allowlisted) model↔kernel divergence.
#[must_use]
pub fn audit_fidelity() -> FidelityMetric {
    run_gate(&deterministic_core_corpus())
}

/// STEP-FIDELITY gate (the (F) brick of the whnf reducer-universal composition):
/// over every in-fragment term of the deterministic corpus, the REAL kernel's
/// `TypeChecker::whnf` must agree STRUCTURALLY with the micro-checker's
/// independent `whnf` (beta + zeta). Unlike the inference gate there is no
/// rejection lane — whnf is total on the fragment (ill-typed stuck applications
/// simply stay stuck, identically on both sides).
///
/// Returns `Ok(count_of_agreed_terms)`, or the FIRST divergence as a formatted
/// error (fail-closed for an audit lane).
pub fn audit_whnf_fidelity() -> Result<usize, String> {
    let checker = BootstrapChecker::new();
    let mut agreed = 0usize;
    for term in &deterministic_core_corpus() {
        if in_supported_fragment(term, 0).is_err() {
            continue; // defensive: the corpus is in-fragment by construction
        }
        match checker.recheck_kernel_whnf(term) {
            Ok(_) => agreed += 1,
            Err(e) => {
                return Err(format!("whnf step-fidelity divergence on {term:?}: {e:?}"));
            }
        }
    }
    Ok(agreed)
}

// ────────────────────────────────────────────────────────────────────────────
// DELTA step fidelity — the (F) brick beyond the const-free fragment.
//
// The env-less micro-checker deliberately excludes `Const`; extending the STEP
// comparison to delta needs an environment on BOTH sides. Rather than
// env-ifying the auditable micro-checker, the comparator below is a
// self-contained ~20-line delta-aware micro whnf over an EXPLICIT definition
// table (name -> (value, is_reducible)), mirrored EXACTLY into a real
// `Environment` via `add_decl` for the kernel side. Reducible definitions
// unfold (transitively, through beta/zeta of what they expose); opaque
// (`is_reducible: false`) definitions stay stuck — on both sides, structurally.
// ────────────────────────────────────────────────────────────────────────────

/// A tiny, auditable delta-aware weak-head reducer over an explicit definition
/// table: beta + zeta + delta(reducible-only). The comparator for
/// [`audit_whnf_delta_fidelity`] — code-independent from the kernel's reducer.
fn micro_whnf_delta(defs: &BTreeMap<String, (Expr, bool)>, expr: &Expr) -> Expr {
    match expr.strip_mdata().kind() {
        ExprKind::App(fun, arg) => {
            let fn_whnf = micro_whnf_delta(defs, fun.as_ref());
            match fn_whnf.strip_mdata().kind() {
                ExprKind::Lam(_, _, body) => {
                    micro_whnf_delta(defs, &body.instantiate(arg.as_ref()))
                }
                _ => Expr::app(fn_whnf, arg.as_ref().clone()),
            }
        }
        ExprKind::Let(_, _, val, body, _) => {
            micro_whnf_delta(defs, &body.instantiate(val.as_ref()))
        }
        // Delta: a REDUCIBLE definition's head unfolds to its value; an opaque
        // one is a stuck (neutral) head and stays put.
        ExprKind::Const(name, _) => match defs.get(&name.to_string()) {
            Some((value, true)) => micro_whnf_delta(defs, value),
            _ => expr.strip_mdata().clone(),
        },
        _ => expr.strip_mdata().clone(),
    }
}

/// DELTA STEP-FIDELITY gate: over a corpus of const-headed terms (bare
/// reducible/opaque consts, a two-hop reducible chain, a function-valued
/// definition applied to an argument — delta THEN beta — and consts under
/// binders), the REAL kernel's `whnf` on an environment holding the definitions
/// must agree STRUCTURALLY with [`micro_whnf_delta`] over the same table.
///
/// Returns `Ok(count_of_agreed_terms)` or the first divergence, fail-closed.
pub fn audit_whnf_delta_fidelity() -> Result<usize, String> {
    use clean_kernel::{BinderInfo, Level};

    let prop = Expr::sort(Level::zero());
    let sort1 = Expr::sort(Level::succ(Level::zero()));
    let id_prop = Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0));

    // The definition table: (name, type, value, unfolds_in_whnf).
    //
    // MEASURED transparency semantics this gate documents (its first run caught
    // the distinction): the kernel's `whnf` unfolds EVERY `Declaration::
    // Definition` at default transparency — `is_reducible: false` does NOT make
    // whnf stick (it only gates `TransparencyMode::Reducible`). What genuinely
    // stays stuck in whnf is `Declaration::Opaque` (value sealed). So the table
    // distinguishes Definitions (unfold) from Opaques (stuck), and the micro
    // reducer mirrors exactly that.
    let definitions: Vec<(&str, Expr, Expr)> = vec![
        ("FidelityGate.DeltaRed", sort1.clone(), prop.clone()),
        (
            "FidelityGate.DeltaChain",
            sort1.clone(),
            Expr::const_str("FidelityGate.DeltaRed"),
        ),
        (
            "FidelityGate.DeltaFn",
            Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
            id_prop.clone(),
        ),
    ];
    let opaques: Vec<(&str, Expr, Expr)> = vec![
        ("FidelityGate.DeltaOpaque", sort1.clone(), prop.clone()),
        (
            "FidelityGate.DeltaFnOpaque",
            Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
            id_prop,
        ),
    ];

    // The kernel side: a real Environment with the SAME declarations.
    let mut env = Environment::new();
    let mut defs: BTreeMap<String, (Expr, bool)> = BTreeMap::new();
    for (name, ty, value) in &definitions {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty.clone(),
            value: value.clone(),
            is_reducible: true,
        })
        .map_err(|e| format!("register {name}: {e}"))?;
        defs.insert((*name).to_string(), (value.clone(), true));
    }
    for (name, ty, value) in &opaques {
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty.clone(),
            value: value.clone(),
        })
        .map_err(|e| format!("register opaque {name}: {e}"))?;
        defs.insert((*name).to_string(), (value.clone(), false));
    }

    // Const-headed corpus: bare heads, the chain, delta-then-beta redexes, an
    // opaque application (stuck), and consts under a binder / as an argument.
    let corpus = vec![
        Expr::const_str("FidelityGate.DeltaRed"),
        Expr::const_str("FidelityGate.DeltaOpaque"),
        Expr::const_str("FidelityGate.DeltaChain"),
        Expr::app(Expr::const_str("FidelityGate.DeltaFn"), prop.clone()),
        Expr::app(Expr::const_str("FidelityGate.DeltaFnOpaque"), prop.clone()),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            prop.clone(),
            Expr::const_str("FidelityGate.DeltaRed"),
        ),
        Expr::app(
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                sort1.clone(),
                Expr::bvar(0),
            ),
            Expr::const_str("FidelityGate.DeltaRed"),
        ),
        let_anon(
            sort1,
            Expr::const_str("FidelityGate.DeltaChain"),
            Expr::bvar(0),
        ),
    ];

    let tc = TypeChecker::with_mode(&env, env.mode());
    let mut agreed = 0usize;
    for term in &corpus {
        let kernel = tc.whnf(term);
        let micro = micro_whnf_delta(&defs, term);
        if kernel != micro {
            return Err(format!(
                "delta step-fidelity divergence on {term:?}: kernel {kernel:?} vs micro {micro:?}"
            ));
        }
        agreed += 1;
    }
    Ok(agreed)
}

// ────────────────────────────────────────────────────────────────────────────
// IOTA step fidelity — the (F) brick for recursor-on-constructor reduction.
// ────────────────────────────────────────────────────────────────────────────

/// One constructor arm of a micro recursor rule: the constructor's name, its
/// field count, and whether the (single, last) field is recursive (gets an IH).
struct MicroRecArm {
    ctor: &'static str,
    num_fields: usize,
    recursive: bool,
}

/// A micro recursor rule: `<rec> motive minor_0 … minor_{n-1} major` reduces,
/// when `whnf(major)` is `ctor_i fields…`, to `minor_i fields… (ih?)` — the IH
/// being the same recursor spine over the recursive field. Mirrors the kernel's
/// iota for the simple param-free single-motive recursors the corpus registers.
struct MicroRecRule {
    arms: Vec<MicroRecArm>,
}

/// [`micro_whnf_delta`] extended with IOTA over an explicit recursor table —
/// still a small auditable reducer, code-independent from the kernel's.
fn micro_whnf_iota(
    defs: &BTreeMap<String, (Expr, bool)>,
    recs: &BTreeMap<String, MicroRecRule>,
    expr: &Expr,
) -> Expr {
    let e = expr.strip_mdata();
    // Recursor spine? `<rec> motive minors… major`.
    let rec_rule = match e.get_app_fn().strip_mdata().kind() {
        ExprKind::Const(head, _) => recs.get(&head.to_string()),
        _ => None,
    };
    if let Some(rule) = rec_rule {
        let args: Vec<Expr> = e.get_app_args().iter().map(|a| (**a).clone()).collect();
        let expect = 2 + rule.arms.len(); // motive + minors + major
        if args.len() == expect {
            let major = micro_whnf_iota(defs, recs, &args[expect - 1]);
            let major_head = major.get_app_fn().strip_mdata().clone();
            if let ExprKind::Const(cname, _) = major_head.kind() {
                for (i, arm) in rule.arms.iter().enumerate() {
                    if cname.to_string() == arm.ctor {
                        let fields: Vec<Expr> =
                            major.get_app_args().iter().map(|a| (**a).clone()).collect();
                        if fields.len() != arm.num_fields {
                            return e.clone(); // arity mismatch: stuck, fail closed
                        }
                        let mut reduct = args[1 + i].clone(); // minor_i
                        for f in &fields {
                            reduct = Expr::app(reduct, f.clone());
                        }
                        if arm.recursive {
                            // IH: the same recursor spine over the recursive field
                            // (the single field, by this table's construction).
                            let mut ih = e.get_app_fn().strip_mdata().clone();
                            for a in &args[..expect - 1] {
                                ih = Expr::app(ih, a.clone());
                            }
                            ih = Expr::app(ih, fields[0].clone());
                            reduct = Expr::app(reduct, ih);
                        }
                        return micro_whnf_iota(defs, recs, &reduct);
                    }
                }
            }
            // Major is not a known constructor: the recursor is STUCK.
            return e.clone();
        }
    }
    match e.kind() {
        ExprKind::App(fun, arg) => {
            let fn_whnf = micro_whnf_iota(defs, recs, fun.as_ref());
            match fn_whnf.strip_mdata().kind() {
                ExprKind::Lam(_, _, body) => {
                    micro_whnf_iota(defs, recs, &body.instantiate(arg.as_ref()))
                }
                _ => Expr::app(fn_whnf, arg.as_ref().clone()),
            }
        }
        ExprKind::Let(_, _, val, body, _) => {
            micro_whnf_iota(defs, recs, &body.instantiate(val.as_ref()))
        }
        ExprKind::Const(name, _) => match defs.get(&name.to_string()) {
            Some((value, true)) => micro_whnf_iota(defs, recs, value),
            _ => e.clone(),
        },
        _ => e.clone(),
    }
}

/// IOTA STEP-FIDELITY gate: register two real inductives (`FGBool`, an enum, and
/// `FGNat`, a recursive datatype) through the REAL kernel's `add_inductive`, then
/// compare the real `whnf` against [`micro_whnf_iota`] on a recursor corpus:
/// recursor-on-constructor for both enum arms, the recursive `succ` arm (whose
/// weak-head reduct exposes the constructor with the IH left UNREDUCED — whnf is
/// weak-head on both sides), the base arm, and a recursor STUCK on a non-ctor
/// major. Fail-closed on the first structural divergence.
pub fn audit_whnf_iota_fidelity() -> Result<usize, String> {
    use clean_kernel::{BinderInfo, Constructor, InductiveDecl, InductiveType, Level, LevelVec};

    let mut env = Environment::new();
    let bool_ref = Expr::const_(Name::from_string("FGBool"), LevelVec::new());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("FGBool"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("FGBool.tt"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("FGBool.ff"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    })
    .map_err(|e| format!("register FGBool: {e}"))?;

    let nat_ref = Expr::const_(Name::from_string("FGNat"), LevelVec::new());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("FGNat"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("FGNat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("FGNat.succ"),
                    type_: Expr::pi(BinderInfo::Default, nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    })
    .map_err(|e| format!("register FGNat: {e}"))?;

    let defs: BTreeMap<String, (Expr, bool)> = BTreeMap::new();
    let mut recs: BTreeMap<String, MicroRecRule> = BTreeMap::new();
    recs.insert(
        "FGBool.rec".to_string(),
        MicroRecRule {
            arms: vec![
                MicroRecArm {
                    ctor: "FGBool.tt",
                    num_fields: 0,
                    recursive: false,
                },
                MicroRecArm {
                    ctor: "FGBool.ff",
                    num_fields: 0,
                    recursive: false,
                },
            ],
        },
    );
    recs.insert(
        "FGNat.rec".to_string(),
        MicroRecRule {
            arms: vec![
                MicroRecArm {
                    ctor: "FGNat.zero",
                    num_fields: 0,
                    recursive: false,
                },
                MicroRecArm {
                    ctor: "FGNat.succ",
                    num_fields: 1,
                    recursive: true,
                },
            ],
        },
    );

    let tt = Expr::const_(Name::from_string("FGBool.tt"), LevelVec::new());
    let ff = Expr::const_(Name::from_string("FGBool.ff"), LevelVec::new());
    let zero = Expr::const_(Name::from_string("FGNat.zero"), LevelVec::new());
    let succ = Expr::const_(Name::from_string("FGNat.succ"), LevelVec::new());
    let one = Expr::app(succ.clone(), zero.clone());
    let u1 = vec![Level::succ(Level::zero())];

    // FGBool.rec .{1} (fun _ => FGBool) ff tt <major> — the `not` fold.
    let bool_motive = Expr::lam(BinderInfo::Default, bool_ref.clone(), bool_ref.clone());
    let bool_rec = |major: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("FGBool.rec"), u1.clone()),
            [bool_motive.clone(), ff.clone(), tt.clone(), major],
        )
    };
    // FGNat.rec .{1} (fun _ => FGNat) zero (fun n ih => succ (succ ih)) <major> — double.
    let nat_motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), nat_ref.clone());
    let double_minor = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::app(succ.clone(), Expr::app(succ.clone(), Expr::bvar(0))),
        ),
    );
    let nat_rec = |major: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("FGNat.rec"), u1.clone()),
            [
                nat_motive.clone(),
                zero.clone(),
                double_minor.clone(),
                major,
            ],
        )
    };

    let corpus = vec![
        bool_rec(tt.clone()),  // iota -> ff (swapped minors)
        bool_rec(ff.clone()),  // iota -> tt
        nat_rec(zero.clone()), // base arm -> zero
        nat_rec(one.clone()),  // recursive arm -> succ (succ (FGNat.rec … zero)), weak-head
        // A recursor STUCK on a non-constructor major (the recursor spine itself).
        bool_rec(Expr::const_(Name::from_string("FGBool"), LevelVec::new())),
    ];

    let tc = TypeChecker::with_mode(&env, env.mode());
    let mut agreed = 0usize;
    for term in &corpus {
        let kernel = tc.whnf(term);
        let micro = micro_whnf_iota(&defs, &recs, term);
        if kernel != micro {
            return Err(format!(
                "iota step-fidelity divergence on {term:?}:\n  kernel {kernel:?}\n  micro  {micro:?}"
            ));
        }
        agreed += 1;
    }
    Ok(agreed)
}

// ────────────────────────────────────────────────────────────────────────────
// NAT-accelerator step fidelity — the (F) brick for the literal-arithmetic
// fast path (`reduce_nat`), one of the whnf_outer_loop's special reduction
// side-steps.
// ────────────────────────────────────────────────────────────────────────────

/// A tiny auditable mirror of the kernel's `reduce_nat` literal accelerator on
/// SMALL naturals: `Nat.succ/pred` (unary) and `Nat.add/sub/mul/div` (binary)
/// over `Literal::Nat` operands, with Lean semantics (truncated `sub`,
/// `n / 0 = 0`). Operands are first micro-whnf'd (so nested accelerations
/// compose); a non-literal operand leaves the spine STUCK. Small-only (`u64`
/// via the corpus) — the corpus stays far from the BigNat multi-limb range, so
/// plain checked u64 arithmetic mirrors the kernel exactly.
fn micro_whnf_nat(expr: &Expr) -> Expr {
    fn nat_of(e: &Expr) -> Option<u64> {
        match e.strip_mdata().kind() {
            ExprKind::Lit(clean_kernel::Literal::Nat(b)) => b.to_u64(),
            _ => None,
        }
    }
    let e = expr.strip_mdata();
    let head = e.get_app_fn().strip_mdata().clone();
    if let ExprKind::Const(name, levels) = head.kind() {
        if levels.is_empty() {
            let args: Vec<Expr> = e.get_app_args().iter().map(|a| (**a).clone()).collect();
            let n = name.to_string();
            if args.len() == 1 {
                if let Some(a) = nat_of(&micro_whnf_nat(&args[0])) {
                    match n.as_str() {
                        "Nat.succ" => return Expr::nat_lit(a + 1),
                        "Nat.pred" => return Expr::nat_lit(a.saturating_sub(1)),
                        _ => {}
                    }
                }
            } else if args.len() == 2 {
                let (x, y) = (
                    nat_of(&micro_whnf_nat(&args[0])),
                    nat_of(&micro_whnf_nat(&args[1])),
                );
                if let (Some(x), Some(y)) = (x, y) {
                    match n.as_str() {
                        "Nat.add" => return Expr::nat_lit(x + y),
                        "Nat.sub" => return Expr::nat_lit(x.saturating_sub(y)),
                        "Nat.mul" => return Expr::nat_lit(x * y),
                        "Nat.div" => {
                            // Lean Nat semantics: division by zero is 0.
                            return Expr::nat_lit(x.checked_div(y).unwrap_or(0));
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    e.clone()
}

/// NAT-ACCELERATOR STEP-FIDELITY gate: the REAL kernel's `whnf` on literal
/// `Nat` arithmetic spines must agree STRUCTURALLY with [`micro_whnf_nat`] —
/// each accelerated op, Lean's truncated-`sub` and `n/0 = 0` edge semantics,
/// a NESTED spine (inner acceleration feeding an outer one), and a STUCK
/// partial application. Fail-closed on the first divergence.
pub fn audit_whnf_nat_fidelity() -> Result<usize, String> {
    let env = Environment::new();
    let nat_c = |s: &str| Expr::const_(Name::from_string(s), clean_kernel::LevelVec::new());
    let lit = Expr::nat_lit;

    let corpus = vec![
        Expr::apps(nat_c("Nat.add"), [lit(2), lit(3)]), // 5
        Expr::apps(nat_c("Nat.mul"), [lit(4), lit(6)]), // 24
        Expr::apps(nat_c("Nat.sub"), [lit(3), lit(5)]), // 0 (truncated)
        Expr::apps(nat_c("Nat.div"), [lit(7), lit(0)]), // 0 (Lean: n/0 = 0)
        Expr::apps(nat_c("Nat.succ"), [lit(7)]),        // 8
        Expr::apps(nat_c("Nat.pred"), [lit(0)]),        // 0 (floored)
        // Nested: Nat.add 2 (Nat.sub 1 2) -> Nat.add 2 0 -> 2.
        Expr::apps(
            nat_c("Nat.add"),
            [lit(2), Expr::apps(nat_c("Nat.sub"), [lit(1), lit(2)])],
        ),
        // STUCK: a partial application (one argument to a binary op).
        Expr::app(nat_c("Nat.add"), lit(2)),
        // A bare literal is already WHNF.
        lit(42),
    ];

    let tc = TypeChecker::with_mode(&env, env.mode());
    let mut agreed = 0usize;
    for term in &corpus {
        let kernel = tc.whnf(term);
        let micro = micro_whnf_nat(term);
        if kernel != micro {
            return Err(format!(
                "nat-accelerator step-fidelity divergence on {term:?}:\n  kernel {kernel:?}\n  micro  {micro:?}"
            ));
        }
        agreed += 1;
    }
    Ok(agreed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Level};

    /// Fixed smoke sub-corpus mirroring the reflection samples so the gate
    /// subsumes the existing axiom-coverage invariant: full 6/6 coverage, all
    /// agreed, zero excluded.
    fn smoke_corpus() -> Vec<Expr> {
        vec![
            Expr::prop(),
            Expr::type_(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            Expr::app(
                Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
                Expr::prop(),
            ),
            // let x : Type 0 := Prop in x — the 6th fragment ctor (task #28).
            super::let_anon(Expr::type_(), Expr::prop(), Expr::bvar(0)),
        ]
    }

    /// Hand-written ill-typed negatives: the gate must observe AGREEMENT on
    /// rejection (both the real kernel and the micro-checker reject).
    fn negative_corpus() -> Vec<Expr> {
        vec![
            // Applying a non-function (Sort) to an argument.
            Expr::app(Expr::prop(), Expr::prop()),
            Expr::app(Expr::type_(), Expr::type_()),
            // Application with a domain mismatch: (λ x:Prop. x) applied to a
            // value whose type is not Prop. `Expr::type_()` has type Sort 1,
            // not Prop, so this is a genuine domain mismatch both sides reject.
            Expr::app(
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
                Expr::type_(),
            ),
            // A Pi whose domain is a non-sort (an application that is not a
            // type) — kernel and micro both reject "expected sort".
            Expr::pi(
                BinderInfo::Default,
                Expr::app(Expr::prop(), Expr::prop()),
                Expr::prop(),
            ),
        ]
    }

    #[test]
    fn test_gate_smoke_corpus_full_coverage_all_agree() {
        let metric = run_gate(&smoke_corpus());
        eprintln!("{}", metric.report());
        assert!(metric.passed(), "smoke corpus must pass the gate");
        assert_eq!(metric.terms_supported, 6);
        assert_eq!(metric.terms_agreed, 6);
        assert_eq!(metric.terms_excluded_unsupported, 0);
        assert_eq!(
            metric.coverage_count(),
            6,
            "smoke corpus should exercise all 6 fragment ctors"
        );
    }

    /// STEP-FIDELITY gate ((F) brick): the REAL kernel whnf agrees STRUCTURALLY
    /// with the micro-checker's independent beta+zeta whnf over the WHOLE
    /// deterministic corpus — redexes (beta, zeta, nested), stuck applications
    /// (ill-typed included: whnf is total), binders, and sorts. Fail-closed on
    /// the first divergence.
    #[test]
    fn test_whnf_step_fidelity_over_deterministic_corpus() {
        let agreed = audit_whnf_fidelity().expect("whnf step fidelity must hold");
        assert!(
            agreed >= deterministic_core_corpus().len(),
            "every corpus term must be whnf-compared (got {agreed})"
        );
    }

    /// DELTA STEP-FIDELITY ((F) beyond the const-free fragment): the real kernel's
    /// whnf agrees structurally with the delta-aware micro reducer over the
    /// const-headed corpus — reducible unfolds (incl. a two-hop chain and
    /// delta-then-beta), opaque stays stuck, and delta does NOT fire under a
    /// binder (whnf is weak-head on both sides).
    #[test]
    fn test_whnf_delta_step_fidelity() {
        let agreed = audit_whnf_delta_fidelity().expect("delta step fidelity must hold");
        assert_eq!(agreed, 8, "all eight const-headed corpus terms must agree");
    }

    /// IOTA STEP-FIDELITY ((F) for recursor-on-constructor): the real kernel's whnf
    /// agrees structurally with the micro iota reducer over the recursor corpus —
    /// enum arms, the recursive succ arm (weak-head: the IH stays unreduced under
    /// the constructor), the base arm, and a stuck non-ctor major.
    #[test]
    fn test_whnf_iota_step_fidelity() {
        let agreed = audit_whnf_iota_fidelity().expect("iota step fidelity must hold");
        assert_eq!(agreed, 5, "all five recursor corpus terms must agree");
    }

    /// NAT-ACCELERATOR STEP-FIDELITY ((F) for the literal-arithmetic fast path):
    /// the real whnf agrees structurally with the micro nat reducer — each op,
    /// Lean's truncated-sub and n/0=0 edges, a nested spine, a stuck partial
    /// application, and a bare literal.
    #[test]
    fn test_whnf_nat_accelerator_step_fidelity() {
        let agreed = audit_whnf_nat_fidelity().expect("nat-accelerator fidelity must hold");
        assert_eq!(agreed, 9, "all nine nat corpus terms must agree");
    }

    /// (F)-COVERAGE SCOPING, machine-checked (not prose): two scope pins for the
    /// step-fidelity gates' β+ζ+δ+ι+nat coverage of the default-mode core
    /// reduction surface.
    ///
    ///   * The default mode is `Constructive` (Lean-4 core), and its cubical layer
    ///     is OFF — so `whnf_core_inner`'s kan arms (hcomp/transp/coe/glue, the
    ///     cubical computation forms) are dead code for every default-mode kernel.
    ///   * `reduce_native` spines (`Lean.reduceBool`/`Lean.reduceNat`) require a
    ///     REGISTERED native reducer; on an unregistered environment they are
    ///     STUCK — and the kernel's whnf must agree with stuckness (identity),
    ///     which is checked here, not assumed.
    ///
    /// SCOPE (open gates, not covered by these pins): the default mode also has
    /// active reduction arms with NO step-fidelity gate yet — projection-on-
    /// constructor (`whnf_reduce_proj`), quotient reduction (`try_quot_reduction`
    /// on `Quot.lift`/`Quot.ind`), and int-literal acceleration (`reduce_int`).
    /// The gates cover the core β+ζ+δ+ι+nat surface, not those arms; extending
    /// (F) to proj/quot/int is standing backlog.
    #[test]
    fn test_step_fidelity_coverage_scope_cubical_off_and_native_stuck() {
        use clean_kernel::LevelVec;
        // 1. The default mode has no cubical layer (pins the dead-arm claim).
        let env = Environment::new();
        assert!(
            !env.mode().has_cubical_layer(),
            "the default kernel mode must have NO cubical layer — the kan reduction \
             arms are dead code in default mode, so the gates cover the active surface"
        );

        // 2. Unregistered native-reducer spines are STUCK — whnf is the identity.
        let tc = TypeChecker::with_mode(&env, env.mode());
        let reduce_bool = Expr::app(
            Expr::const_(Name::from_string("Lean.reduceBool"), LevelVec::new()),
            Expr::const_(
                Name::from_string("FidelityGate.SomeTarget"),
                LevelVec::new(),
            ),
        );
        assert_eq!(
            tc.whnf(&reduce_bool),
            reduce_bool,
            "an unregistered Lean.reduceBool spine must be STUCK under whnf"
        );
        let reduce_nat = Expr::app(
            Expr::const_(Name::from_string("Lean.reduceNat"), LevelVec::new()),
            Expr::const_(
                Name::from_string("FidelityGate.SomeTarget"),
                LevelVec::new(),
            ),
        );
        assert_eq!(
            tc.whnf(&reduce_nat),
            reduce_nat,
            "an unregistered Lean.reduceNat spine must be STUCK under whnf"
        );
    }

    /// The step-fidelity comparison is DISCRIMINATING, not a rubber stamp: a
    /// term whose micro-whnf differs from what the kernel produces would fail.
    /// Since both reducers are correct, we witness discrimination through the
    /// checker API instead: `recheck_kernel_whnf` on a beta redex returns the
    /// REDUCT (proving the comparison inspects real reduction output, not the
    /// input), and the reduct differs from the input.
    #[test]
    fn test_whnf_step_fidelity_is_discriminating() {
        let checker = BootstrapChecker::new();
        // (λ (x : Type 0). x) Prop — reduces to Prop on both sides.
        let redex = Expr::app(
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            Expr::prop(),
        );
        let agreed = checker
            .recheck_kernel_whnf(&redex)
            .expect("beta redex must whnf-agree");
        assert_eq!(agreed, Expr::prop(), "the agreed whnf is the REDUCT");
        assert_ne!(agreed, redex, "the reduction genuinely fired");

        // Zeta: let x : Type 0 := Prop in x — reduces to Prop on both sides.
        let zeta = super::let_anon(Expr::type_(), Expr::prop(), Expr::bvar(0));
        let agreed = checker
            .recheck_kernel_whnf(&zeta)
            .expect("zeta redex must whnf-agree");
        assert_eq!(agreed, Expr::prop(), "the agreed whnf is the zeta reduct");
    }

    #[test]
    fn test_audit_fidelity_lane_passes_fail_closed() {
        // The `clean audit` entry point: deterministic, proptest-free corpus.
        let metric = audit_fidelity();
        eprintln!("{}", metric.report());
        assert!(
            metric.passed(),
            "audit lane produced NEW divergences (fail-closed): {:?}",
            metric.new_divergences
        );
        // The deterministic corpus must actually exercise the gate (not pass
        // vacuously) and cover the whole fragment.
        assert!(metric.terms_supported > 20, "corpus should be non-trivial");
        assert_eq!(
            metric.terms_excluded_unsupported, 0,
            "corpus is in-fragment"
        );
        assert_eq!(
            metric.coverage_count(),
            6,
            "deterministic corpus should exercise all 6 fragment ctors"
        );
        // Exhaustive accounting (fail-closed invariant).
        assert_eq!(
            metric.terms_supported,
            metric.terms_agreed + metric.terms_known_divergent
        );
    }

    #[test]
    fn test_gate_negatives_agree_on_rejection() {
        let metric = run_gate(&negative_corpus());
        eprintln!("{}", metric.report());
        // Every negative is in-fragment (closed 6-ctor) and must be AGREED
        // (both sides reject) — no new divergences.
        assert!(
            metric.passed(),
            "negatives must agree-on-rejection, got new divergences: {:?}",
            metric.new_divergences
        );
        assert_eq!(metric.terms_supported, negative_corpus().len());
        assert_eq!(metric.terms_agreed, negative_corpus().len());
    }

    #[test]
    fn test_supported_fragment_predicate_excludes_with_reason() {
        // Const / Lit are out of fragment with the ctor name as reason
        // (Let joined the fragment with the let promotion, task #28).
        let const_term = Expr::const_(clean_kernel::Name::anon(), Vec::<Level>::new());
        assert_eq!(in_supported_fragment(&const_term, 0), Err("Const"));

        // A closed let is IN fragment; its body binder scopes one bvar.
        assert_eq!(
            in_supported_fragment(&let_anon(Expr::type_(), Expr::prop(), Expr::bvar(0)), 0),
            Ok(())
        );
        // A let whose body escapes its single binder is out (bvar-escape).
        assert_eq!(
            in_supported_fragment(&let_anon(Expr::type_(), Expr::prop(), Expr::bvar(1)), 0),
            Err("bvar-escape")
        );

        let lit_term = Expr::nat_lit(7);
        assert_eq!(in_supported_fragment(&lit_term, 0), Err("Lit"));

        // bvar escape (unbound at scope 0).
        assert_eq!(in_supported_fragment(&Expr::bvar(0), 0), Err("bvar-escape"));
        // bvar bound under a binder is fine.
        assert_eq!(
            in_supported_fragment(
                &Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
                0
            ),
            Ok(())
        );
    }

    #[test]
    fn test_exclusion_histogram_counts_each_reason() {
        let corpus = vec![
            Expr::const_(clean_kernel::Name::anon(), Vec::<Level>::new()),
            Expr::const_(clean_kernel::Name::anon(), Vec::<Level>::new()),
            Expr::nat_lit(1),
            Expr::prop(), // supported
        ];
        let metric = run_gate(&corpus);
        assert_eq!(metric.terms_excluded_unsupported, 3);
        assert_eq!(metric.exclusion_histogram.get("Const"), Some(&2));
        assert_eq!(metric.exclusion_histogram.get("Lit"), Some(&1));
        assert_eq!(metric.terms_supported, 1);
    }

    /// FAIL-CLOSED demonstration WITHOUT mutating the production checker.
    ///
    /// We synthesize the outcome of a divergence whose key is not on the
    /// allowlist and confirm the metric reports FAIL. This proves the gate is
    /// not rigged to pass: a new divergence makes `passed()` false and
    /// populates `new_divergences`. (The end-to-end injection — flipping a
    /// micro-checker rule and observing the real `run_gate` go red — is
    /// demonstrated manually in the build log and reverted; see the gate's
    /// module-level docs and the workflow report.)
    #[test]
    fn test_gate_is_fail_closed_on_unallowlisted_divergence() {
        let mut metric = FidelityMetric::new();
        // A closed in-fragment term whose key is (overwhelmingly likely) not
        // in the empty allowlist.
        let term = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let key = structural_key(&term);
        assert!(
            known_divergence_for(key).is_none(),
            "allowlist must be empty for this fragment"
        );
        metric.observe(
            &term,
            TermOutcome::NewDivergence {
                key,
                detail: "synthetic divergence (test only)".to_string(),
            },
        );
        assert!(
            !metric.passed(),
            "an unallowlisted divergence MUST fail the gate"
        );
        assert_eq!(metric.new_divergences.len(), 1);
    }

    /// The two allowlist-routing branches the gate uses, exercised directly:
    /// a `KnownDivergent` outcome PASSES the gate and is counted in the
    /// `terms_known_divergent` ratchet bucket; a `NewDivergence` outcome FAILS.
    /// Both fold into the same supported-term accounting so the fail-closed
    /// invariant `terms_supported == terms_agreed + terms_known_divergent`
    /// holds for the known branch but is *broken* (caught) for the new branch.
    #[test]
    fn test_known_vs_new_divergence_routing() {
        let term = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let key = structural_key(&term);

        // Known branch: passes, lands in the ratchet bucket, accounting closes.
        let mut known = FidelityMetric::new();
        known.observe(&term, TermOutcome::KnownDivergent);
        assert!(
            known.passed(),
            "an allowlisted divergence must pass the gate"
        );
        assert_eq!(known.terms_known_divergent, 1);
        assert_eq!(
            known.terms_supported,
            known.terms_agreed + known.terms_known_divergent,
            "known divergence keeps the fail-closed accounting closed"
        );

        // New branch: fails, recorded in `new_divergences` (the fail-closed
        // evidence), and the accounting does NOT close (unaccounted term).
        let mut new = FidelityMetric::new();
        new.observe(
            &term,
            TermOutcome::NewDivergence {
                key,
                detail: "routed as new (test)".to_string(),
            },
        );
        assert!(
            !new.passed(),
            "a non-allowlisted divergence must fail the gate"
        );
        assert_eq!(new.new_divergences.len(), 1);
        assert_ne!(
            new.terms_supported,
            new.terms_agreed + new.terms_known_divergent,
            "a new divergence leaves an unaccounted supported term (the fail signal)"
        );
    }

    /// The empty allowlist is a real, checkable claim: no structural key resolves
    /// to a `KnownDivergence`, so every divergence in the gated fragment is NEW
    /// (fail-closed) until a reviewer adds a justified key.
    #[test]
    fn test_allowlist_is_empty_so_all_divergences_are_new() {
        assert!(KNOWN_DIVERGENCES.is_empty());
        let term = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        assert!(known_divergence_for(structural_key(&term)).is_none());
    }

    #[test]
    fn test_structural_key_is_stable_and_distinguishing() {
        let a = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        let b = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        let c = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        // Same structure → same key (stable, Arc-independent).
        assert_eq!(structural_key(&a), structural_key(&b));
        // Different structure → different key.
        assert_ne!(structural_key(&a), structural_key(&c));
    }

    // ── Fuzz corpus: trimmed copy of clean-kernel zfc.rs arb_closed_expr ──
    //
    // The supported fragment is {Sort, BVar, Pi, Lam, App}; the upstream
    // generator also emits Let and nat-literals, which are out of fragment.
    // This trimmed generator drops those arms so every generated term is closed
    // AND in-fragment, maximizing the gate's differential bite.
    mod fuzz {
        use super::*;
        use proptest::prelude::*;

        fn arb_level(depth: u32) -> BoxedStrategy<Level> {
            if depth == 0 {
                Just(Level::zero()).boxed()
            } else {
                prop_oneof![
                    5 => Just(Level::zero()),
                    3 => arb_level(depth - 1).prop_map(Level::succ),
                    1 => (arb_level(depth - 1), arb_level(depth - 1))
                        .prop_map(|(l1, l2)| Level::max(l1, l2)),
                    1 => (arb_level(depth - 1), arb_level(depth - 1))
                        .prop_map(|(l1, l2)| Level::imax(l1, l2)),
                ]
                .boxed()
            }
        }

        /// Closed, in-supported-fragment generator: Sort / BVar / Lam / Pi /
        /// App only. `ctx_depth` tracks available bound variables so every BVar
        /// is bound (term is closed at top level).
        fn arb_fragment_expr(depth: u32, ctx_depth: u32) -> BoxedStrategy<Expr> {
            // A `Sort` leaf and (only when `ctx_depth > 0`) a bound-variable
            // leaf. The BVar arm is built CONDITIONALLY — proptest's
            // `prop_oneof!` treats a 0-weight arm as undefined (it can still be
            // sampled and the `0..0` range panics), so we must not include it at
            // all when there is no enclosing binder. This keeps every generated
            // term closed and in the supported fragment.
            let sort_leaf = arb_level(2).prop_map(Expr::sort).boxed();
            let leaf: BoxedStrategy<Expr> = if ctx_depth > 0 {
                let bvar_leaf = (0..ctx_depth).prop_map(Expr::bvar).boxed();
                prop_oneof![5 => sort_leaf, 3 => bvar_leaf].boxed()
            } else {
                sort_leaf
            };

            if depth == 0 {
                leaf
            } else {
                prop_oneof![
                    4 => leaf,
                    3 => (arb_fragment_expr(depth - 1, ctx_depth), arb_fragment_expr(depth - 1, ctx_depth + 1))
                        .prop_map(|(ty, body)| Expr::lam(BinderInfo::Default, ty, body)),
                    3 => (arb_fragment_expr(depth - 1, ctx_depth), arb_fragment_expr(depth - 1, ctx_depth + 1))
                        .prop_map(|(ty, body)| Expr::pi(BinderInfo::Default, ty, body)),
                    3 => (arb_fragment_expr(depth - 1, ctx_depth), arb_fragment_expr(depth - 1, ctx_depth))
                        .prop_map(|(f, a)| Expr::app(f, a)),
                ]
                .boxed()
            }
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(384))]

            /// The core differential property: for every fuzz-generated closed
            /// in-fragment term, the model and the Rust kernel must AGREE — no
            /// new (non-allowlisted) divergence. This is the large-corpus,
            /// fail-closed heart of the gate.
            #[test]
            fn fuzz_model_kernel_agree_on_fragment(
                expr in (0u32..=4).prop_flat_map(|d| arb_fragment_expr(d, 0))
            ) {
                // Generator invariant: every term is in-fragment and closed.
                prop_assert_eq!(in_supported_fragment(&expr, 0), Ok(()));
                let checker = BootstrapChecker::new();
                let outcome = check_term(&checker, &expr);
                match outcome {
                    TermOutcome::Agreed | TermOutcome::KnownDivergent => {}
                    TermOutcome::NewDivergence { key, detail } => {
                        prop_assert!(
                            false,
                            "NEW model↔kernel divergence (fail-closed): key={:#018x} term={:?} detail={}",
                            key, expr, detail
                        );
                    }
                    TermOutcome::Excluded(reason) => {
                        prop_assert!(false, "generator emitted out-of-fragment term ({reason}): {expr:?}");
                    }
                }
            }
        }

        /// Aggregate fuzz run reported through the metric (a fixed deterministic
        /// batch so the printed fidelity number is reproducible in the log).
        #[test]
        #[allow(clippy::should_implement_trait)]
        fn test_fuzz_batch_metric_passes_fail_closed() {
            use proptest::strategy::ValueTree;
            use proptest::test_runner::TestRunner;
            let mut runner = TestRunner::deterministic();
            let mut corpus = Vec::new();
            for _ in 0..512 {
                let d = (corpus.len() as u32 % 5).min(4);
                let tree = arb_fragment_expr(d, 0)
                    .new_tree(&mut runner)
                    .expect("strategy produces a value");
                corpus.push(tree.current());
            }
            let metric = run_gate(&corpus);
            eprintln!("{}", metric.report());
            assert!(
                metric.passed(),
                "fuzz batch produced NEW divergences: {:?}",
                metric.new_divergences
            );
            // The fuzz arm is the differential bite: it must actually exercise
            // the fragment (not pass vacuously by excluding everything).
            assert_eq!(
                metric.terms_excluded_unsupported, 0,
                "fuzz generator must stay in-fragment"
            );
            assert!(
                metric.terms_supported > 0,
                "fuzz batch must check supported terms"
            );
            assert!(
                metric.coverage_count() >= 4,
                "fuzz batch should exercise at least 4/5 fragment ctors, got {}",
                metric.coverage_count()
            );
        }
    }

    // ── Olean corpus: real constant headers from the deployed `.olean` workload ──
    //
    // The fixtures ship in the main tree (no Lean toolchain / Mathverse shards /
    // network needed). Real stdlib headers are overwhelmingly Const-bearing and
    // universe-polymorphic, so they are EXCLUDED with a count (the honest
    // "detect-and-exclude" behaviour) — they would also fail kernel-side under
    // an empty `Environment`. The custom fixtures (e.g. `Minimal.lean`'s
    // `identity : (α : Type) → α → α`) yield real in-fragment headers. Either
    // way the gate must report the split and never panic on an excluded header.
    mod olean_corpus {
        use super::*;
        use clean_kernel::Environment;
        use std::path::PathBuf;

        /// Fixture .olean files, relative to the crate manifest dir.
        const FIXTURES: &[&str] = &[
            "../../tests/fixtures/olean/v4.13.0/custom/Minimal.olean",
            "../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean",
            "../../tests/fixtures/olean/v4.13.0/custom/Structure.olean",
            "../../tests/fixtures/olean/v4.13.0/stdlib/Init.olean",
            "../../tests/fixtures/olean/v4.13.0/stdlib/Init/Char.olean",
            "../../tests/fixtures/olean/v4.13.0/stdlib/Init/Option.olean",
            "../../tests/fixtures/olean/v4.26.0/custom/StringCompat.olean",
        ];

        /// Collect real constant-header `Expr`s from the fixture `.olean` files.
        /// Loading is best-effort per file: a fixture that fails to load is
        /// skipped (the gate is about agreement on what loads, not about loader
        /// coverage), but at least one must load or the test is meaningless.
        fn collect_olean_headers() -> Vec<Expr> {
            let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let mut headers = Vec::new();
            let mut loaded_files = 0usize;
            for rel in FIXTURES {
                let path = base.join(rel);
                if !path.exists() {
                    continue;
                }
                let mut env = Environment::new();
                match clean_olean::load_olean_file(&mut env, &path) {
                    Ok(_) => {
                        loaded_files += 1;
                        for c in env.constants() {
                            headers.push(c.type_.clone());
                        }
                    }
                    Err(e) => {
                        eprintln!("olean fixture {rel} failed to load (skipped): {e}");
                    }
                }
            }
            assert!(
                loaded_files > 0,
                "no olean fixtures loaded — corpus arm would be vacuous"
            );
            headers
        }

        /// The real deployed-workload arm: every header is partitioned by the
        /// supported-fragment predicate; supported headers must AGREE; excluded
        /// headers are counted with a per-ctor histogram. Fail-closed on any new
        /// divergence among the supported (in-fragment) headers.
        #[test]
        fn test_olean_headers_partitioned_and_supported_agree() {
            let headers = collect_olean_headers();
            assert!(!headers.is_empty(), "expected real olean headers");
            let metric = run_gate(&headers);
            eprintln!("{}", metric.report());

            // Fail-closed: no new model↔kernel divergence among supported (in-
            // fragment) real headers.
            assert!(
                metric.passed(),
                "real olean headers produced NEW divergences (fail-closed): {:?}",
                metric.new_divergences
            );

            // Sanity: total accounting is exhaustive (every header is either
            // supported or excluded-with-reason — nothing silently dropped).
            assert_eq!(
                metric.terms_total,
                metric.terms_supported + metric.terms_excluded_unsupported,
                "every header must be accounted for"
            );
            assert_eq!(
                metric.terms_total,
                headers.len(),
                "metric must see every header"
            );

            // Honest expectation: the realistic majority of stdlib headers are
            // Const-bearing and therefore excluded with a count. We assert the
            // histogram is populated (Const dominates) so a future regression
            // that silently drops headers is caught.
            assert!(
                metric.terms_excluded_unsupported > 0,
                "expected Const-bearing headers to be excluded with a count"
            );
            assert!(
                metric.exclusion_histogram.contains_key("Const"),
                "expected Const in the exclusion histogram, got {:?}",
                metric.exclusion_histogram
            );
        }
    }
}
