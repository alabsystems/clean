// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional-disagreement gate for computable / equational admitted axioms.
//!
//! ## What this is
//!
//! An *axiom* in the clean-verify spec (a [`crate::spec::SpecDefinition`] with
//! `is_axiom: true`) is an ASSUMPTION the kernel does not check for truth — it
//! only checks that the statement is a well-formed type. That is exactly how two
//! FALSE axioms slipped past for a long time before being retired by hand
//! (commit `11e047bd`):
//!
//! - `micro_whnf_beta`:
//!   `forall ty body arg, Eq MicroExpr (micro_whnf (app (lam ty body) arg))
//!    (micro_whnf (micro_instantiate body arg))`
//! - `micro_whnf_idempotent`:
//!   `forall e, Eq MicroExpr (micro_whnf (micro_whnf e)) (micro_whnf e)`
//!
//! Both are equations between COMPUTABLE terms (`micro_whnf` is a recursive spec
//! function the kernel can reduce) — and both are simply UNTRUE for the
//! *single-step* `micro_whnf`. Nothing ever evaluated them, so the falsehood
//! went unnoticed.
//!
//! This module is a conservative executable check complementary to the name ratchet
//! (`crate::axiom_ratchet`, `data/clean_verify_axiom_ratchet.json`): the ratchet
//! pins the *set* of admitted axioms; this gate probes the *statements* of the
//! computable ones. It evaluates every in-scope (computable, equational) admitted
//! axiom on a battery of concrete adversarial inputs and conservatively REJECTS
//! an axiom when the instantiated sides are not definitionally equal.
//!
//! ## Honest scope (the gate's guarantee)
//!
//! Kernel non-convertibility is **not** a proof of propositional inequality.
//! Distinct normal forms can still be propositionally equal, so this gate never
//! calls a non-definitionally-equal pair a logical refutation or a proof that an
//! axiom is false. Instead it enforces the deliberately stricter admission policy:
//!
//! > Every tested concrete instance of a computable equational axiom must close
//! > by definitional equality.
//!
//! A disagreement is therefore sufficient to reject an admission at this gate,
//! but it is only a [`DefinitionalDisagreement`], not a theorem of negation.
//! Conversely, agreement on a finite battery does not prove the universal axiom.
//!
//! ## Coverage boundary (reported, never silent)
//!
//! The source of truth is the live kernel [`clean_kernel::ConstantKind::Axiom`]
//! census, cross-checked against [`Specification::definitions`]. Every
//! spec-owned axiom must map one-to-one to a live kernel axiom with matching
//! cached type metadata. Missing metadata, kind mismatches, type mismatches, and
//! unexpected environment-only domain axioms are fatal setup errors.
//!
//! Environment-only kernel foundations and the default trust-marker constants
//! are counted separately only after the kernel validates their exact canonical
//! signatures, value-less payloads, full-check provenance, safe/total origin,
//! and a fresh strict declaration recheck. They are ambient declarations rather
//! than spec-owned admissions, so this gate does not pretend to evaluate their
//! propositions; the kernel soundness and trust-marker audits own reachability.
//!
//! Every non-ambient live axiom is partitioned into:
//!
//! - **in-scope** — the elaborated type is `forall (xs...), Eq T lhs rhs` and,
//!   for at least one battery instantiation, BOTH `lhs` and `rhs` reduce (via the
//!   kernel's `whnf`) to ground, constructor-headed normal forms (i.e. the axiom
//!   is a genuine equation between computable terms). These are EVALUATED.
//! - **excluded** — counted with an explicit [`ExclusionReason`]:
//!   - `NotEquational` — the body is not `Eq`-headed (an abstract `-> Type` /
//!     `-> Bool` relation, an inference rule, an implication `A -> B`, ...).
//!   - `NonComputable` — `Eq`-headed but the sides stay STUCK on an abstract
//!     constant (e.g. `ProdType.fst`) under every battery instantiation, so there
//!     is nothing to evaluate. (`micro_def_eq` was such an example until the
//!     micro-band drain gave it a computable body — it is now in-scope.)
//!   - `UngeneratableBinder` — a `forall` binder ranges over a type for which the
//!     battery has no closed witnesses (so we cannot instantiate it). The axiom
//!     is reported, not silently skipped.
//!
//! The gate reports its coverage (`in_scope` evaluated, `excluded` with reasons)
//! so the boundary is explicit and honest. The historical module/file name is
//! retained for API stability; its result vocabulary is intentionally not
//! “refutation”.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use clean_kernel::{
    canonical_ambient_axiom_kind, CanonicalAmbientAxiomKind, ConstantInfo, ConstantKind,
    Declaration, DeclarationVerification, Environment, Expr, ExprKind, TypeChecker,
};

use crate::red_env_reflect::{
    committed_name_atom, fidelity_check, COMMITTED_DEF_SCRIPT, COMMITTED_INTERNING_TSV,
    COMMITTED_SKIP_LEDGER,
};
use crate::spec::{SpecDefinition, Specification};

/// Why an admitted axiom is outside the gate's evaluatable scope.
///
/// Each variant carries enough detail for the coverage report to name the
/// specific axiom AND the reason — the boundary is never silent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExclusionReason {
    /// The statement (after peeling `forall` binders) is not headed by `Eq` —
    /// it is an abstract relation, an inference rule, or an implication. Carries
    /// the head symbol observed (or a shape tag).
    NotEquational(String),
    /// `Eq`-headed, but for every battery instantiation at least one side stays
    /// STUCK on an abstract (non-reducible) constant — there is nothing to
    /// compute. Carries the stuck head symbol.
    NonComputable(String),
    /// A `forall` binder ranges over a type the battery cannot witness with
    /// closed terms. Carries the binder-domain description.
    UngeneratableBinder(String),
}

impl ExclusionReason {
    /// A short, stable label for the coverage histogram.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            ExclusionReason::NotEquational(_) => "NotEquational",
            ExclusionReason::NonComputable(_) => "NonComputable",
            ExclusionReason::UngeneratableBinder(_) => "UngeneratableBinder",
        }
    }

    /// The detail string (head symbol / shape / domain).
    #[must_use]
    pub fn detail(&self) -> &str {
        match self {
            ExclusionReason::NotEquational(s)
            | ExclusionReason::NonComputable(s)
            | ExclusionReason::UngeneratableBinder(s) => s,
        }
    }
}

/// A concrete instance whose two sides are not definitionally equal.
///
/// This is sufficient for this gate's conservative rejection policy, but it is
/// not a proof that the instantiated proposition (or its universal closure) is
/// false.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionalDisagreement {
    /// The probed axiom's spec name.
    pub axiom: String,
    /// Human-readable rendering of the instantiation (one `Debug` per binder).
    pub witness: Vec<String>,
    /// The reduced left-hand side that disagrees.
    pub lhs_whnf: String,
    /// The reduced right-hand side that disagrees.
    pub rhs_whnf: String,
}

/// The verdict of one gate run over a spec's admitted axioms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateReport {
    /// Total live kernel constants whose kind is [`ConstantKind::Axiom`].
    pub total_live_axioms: usize,
    /// Total spec definitions marked `is_axiom: true`.
    pub total_spec_axioms: usize,
    /// Environment-only kernel-foundational axioms, counted but owned by the
    /// kernel soundness audit rather than this spec admission gate.
    pub ambient_foundational_axioms: Vec<String>,
    /// Environment-only default trust-marker constants. Their mere ambient
    /// presence is not a spec-census mismatch; reachability is owned by the
    /// trust-marker audit.
    pub ambient_trust_markers: Vec<String>,
    /// Axioms that were EVALUATED (in-scope: computable equations).
    pub evaluated: Vec<String>,
    /// Axioms excluded from evaluation, with their reason.
    pub excluded: BTreeMap<String, ExclusionReason>,
    /// Witnessed definitional disagreements. NON-EMPTY ⇒ conservative reject.
    pub definitional_disagreements: Vec<DefinitionalDisagreement>,
    /// Census, metadata, battery-construction, or elaboration failures.
    /// NON-EMPTY ⇒ fail closed rather than silently evaluate a smaller corpus.
    pub setup_errors: Vec<String>,
}

impl GateReport {
    /// Whether every live kernel axiom is represented exactly once by an
    /// ambient classification or a spec-gate evaluation/exclusion.
    #[must_use]
    pub fn coverage_complete(&self) -> bool {
        self.ambient_foundational_axioms.len()
            + self.ambient_trust_markers.len()
            + self.evaluated.len()
            + self.excluded.len()
            == self.total_live_axioms
    }

    /// The gate verdict: `true` iff there was no definitional disagreement and
    /// the complete live/spec census plus battery setup was valid.
    ///
    /// This is a conservative admission condition, not a logical truth verdict.
    /// An empty in-scope set still passes if the census and metadata are sound;
    /// the coverage report makes that vacuity visible.
    #[must_use]
    pub fn passed(&self) -> bool {
        self.definitional_disagreements.is_empty()
            && self.setup_errors.is_empty()
            && self.coverage_complete()
    }

    /// Histogram of exclusion reasons (label → count).
    #[must_use]
    pub fn exclusion_histogram(&self) -> BTreeMap<&'static str, usize> {
        let mut h = BTreeMap::new();
        for reason in self.excluded.values() {
            *h.entry(reason.label()).or_insert(0) += 1;
        }
        h
    }

    /// Human-readable one-block summary for the test log / audit lane.
    #[must_use]
    pub fn report(&self) -> String {
        use std::fmt::Write as _;
        let mut s = String::new();
        let _ = writeln!(s, "── axiom definitional-disagreement gate ────────");
        let _ = writeln!(
            s,
            "  live kernel axioms        = {}",
            self.total_live_axioms
        );
        let _ = writeln!(
            s,
            "  spec-marked axioms        = {}",
            self.total_spec_axioms
        );
        let _ = writeln!(
            s,
            "  ambient foundations       = {} [{}]",
            self.ambient_foundational_axioms.len(),
            self.ambient_foundational_axioms.join(", ")
        );
        let _ = writeln!(
            s,
            "  ambient trust markers     = {} [{}]",
            self.ambient_trust_markers.len(),
            self.ambient_trust_markers.join(", ")
        );
        let _ = writeln!(
            s,
            "  in-scope (evaluated)      = {} [{}]",
            self.evaluated.len(),
            self.evaluated.join(", ")
        );
        let _ = writeln!(s, "  excluded (with reason)    = {}", self.excluded.len());
        for (label, count) in self.exclusion_histogram() {
            let _ = writeln!(s, "      {label:<20} = {count}");
        }
        let _ = writeln!(
            s,
            "  definitional disagreements (reject) = {}",
            self.definitional_disagreements.len()
        );
        for disagreement in &self.definitional_disagreements {
            let _ = writeln!(
                s,
                "      DEFINITIONAL DISAGREEMENT {} on [{}]: lhs={} =/= rhs={}",
                disagreement.axiom,
                disagreement.witness.join("; "),
                disagreement.lhs_whnf,
                disagreement.rhs_whnf
            );
        }
        let _ = writeln!(
            s,
            "  setup errors (fail-closed) = {}",
            self.setup_errors.len()
        );
        for error in &self.setup_errors {
            let _ = writeln!(s, "      SETUP ERROR: {error}");
        }
        let _ = writeln!(
            s,
            "  complete live coverage     = {}",
            self.coverage_complete()
        );
        let _ = writeln!(
            s,
            "  VERDICT: {}",
            if self.passed() { "PASS" } else { "FAIL" }
        );
        s
    }
}

/// Source strings for closed battery terms, grouped by the inductive type their
/// terms inhabit. The battery DELIBERATELY includes the adversarial shapes the
/// existing oracles cannot build — a beta-contractum that is itself a redex,
/// nested redexes, let-redexes, and multi-step chains — because those are
/// exactly the shapes the retired FALSE axioms hid behind.
///
/// The map key is the head type-constant name (`"MicroExpr"`, `"KExpr"`,
/// `"Nat"`, `"MicroLevel"`, `"Bool"`); the values are clean source strings that
/// elaborate to CLOSED terms of that type in the spec environment.
fn source_terms<const N: usize>(sources: [&str; N]) -> Vec<String> {
    sources.into_iter().map(str::to_string).collect()
}

fn battery() -> Result<BTreeMap<&'static str, Vec<String>>, String> {
    let mut m: BTreeMap<&'static str, Vec<String>> = BTreeMap::new();

    // ── MicroExpr battery ──────────────────────────────────────────────
    // Includes the canonical "contractum is itself a redex" shape and nested
    // / chained redexes — the gap the prompt requires us to fill.
    m.insert(
        "MicroExpr",
        source_terms([
            // atoms / values (already weak-head-normal)
            "MicroExpr.sort MicroLevel.zero",
            "MicroExpr.bvar Nat.zero",
            "MicroExpr.bvar (Nat.succ Nat.zero)",
            // a plain lambda value
            "MicroExpr.lam (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)",
            // a single beta redex: (λ _. bvar0) (sort 0)
            "MicroExpr.app (MicroExpr.lam (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)) (MicroExpr.sort MicroLevel.zero)",
            // ADVERSARIAL: a redex whose one-step contractum is ITSELF a redex.
            //   app (lam _ (app (lam _ (bvar 1)) (sort 0))) (sort 0):
            //   one beta step substitutes (sort 0) for bvar0, leaving the INNER
            //   redex (app (lam _ (bvar 1)) (sort 0)) un-reduced. A second step
            //   reduces further — so single-step micro_whnf is NOT idempotent here.
            "MicroExpr.app (MicroExpr.lam (MicroExpr.sort MicroLevel.zero) (MicroExpr.app (MicroExpr.lam (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar (Nat.succ Nat.zero))) (MicroExpr.sort MicroLevel.zero))) (MicroExpr.sort MicroLevel.zero)",
            // ADVERSARIAL: a let-redex whose zeta-contractum is itself a redex.
            //   let _ := (λ _. bvar0) in (app (bvar0) (sort 0))  →zeta→
            //   app (lam _ (bvar0)) (sort 0)  — still a redex.
            "MicroExpr.let_ (MicroExpr.sort MicroLevel.zero) (MicroExpr.lam (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)) (MicroExpr.app (MicroExpr.bvar Nat.zero) (MicroExpr.sort MicroLevel.zero))",
            // a pi value
            "MicroExpr.pi (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)",
            // an opaque value
            "MicroExpr.opaque_ (MicroExpr.sort MicroLevel.zero)",
        ]),
    );

    // ── KExpr battery ──────────────────────────────────────────────────
    // KExpr is the kernel-expression model (`expr_model.rs`), now a
    // 9-constructor inductive (sort/bvar/app/lam/pi/const/let_/proj/lit), and the
    // PRIMARY object type of the kernel↔micro spec. The battery contains at
    // least one term headed by every live KExpr constructor. Before this entry
    // existed the gate was BLIND to KExpr entirely: every
    // `forall (… : KExpr), Eq …` axiom (e.g.
    // `kernel_to_micro_instantiate`, the `instantiate`/`lift` identities) was
    // excluded as `UngeneratableBinder("KExpr")` and never evaluated.
    //
    // NOTE the constructor signatures differ from MicroExpr: `KExpr.sort`
    // takes `Level`, `KExpr.bvar` takes `Nat`, and `KExpr.const` takes a `Name`
    // and a `ListType Level`. We mirror the MicroExpr battery's
    // adversarial shapes — a beta redex and a redex whose one-step contractum is
    // ITSELF a redex (the shape that exposed the retired micro_whnf falsity).
    let kexpr = committed_name_atom("KExpr")
        .map_err(|e| format!("cannot resolve semantic battery name KExpr: {e}"))?;
    let nat_add = committed_name_atom("Nat.add")
        .map_err(|e| format!("cannot resolve semantic battery name Nat.add: {e}"))?;
    let nat_zero = committed_name_atom("Nat.zero")
        .map_err(|e| format!("cannot resolve semantic battery name Nat.zero: {e}"))?;
    m.insert(
        "KExpr",
        vec![
            // atoms / values (already weak-head-normal)
            "KExpr.sort Level.zero".to_string(),
            "KExpr.sort (Level.succ Level.zero)".to_string(),
            "KExpr.bvar Nat.zero".to_string(),
            "KExpr.bvar (Nat.succ Nat.zero)".to_string(),
            // a const with a literal Name (anonymous) + empty universe list
            "KExpr.const Name.anonymous (ListType.nil Level)".to_string(),
            // A real reflected inductive name (delta/iota-inert), resolved
            // semantically because frequency-ordered tags can move.
            format!("KExpr.const {kexpr} (ListType.nil Level)"),
            // Semantic atoms are resolved through the fully validated committed
            // interning table, never copied numeric tags.
            format!("KExpr.const {nat_add} (ListType.nil Level)"),
            format!("KExpr.const {nat_zero} (ListType.nil Level)"),
            // a plain lambda value: λ (sort 0). bvar0
            "KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)".to_string(),
            // a plain pi value: Π (sort 0). bvar0
            "KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)".to_string(),
            // a plain app over atoms: app (bvar0) (sort 0)
            "KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)".to_string(),
            // a single beta redex: (λ (sort 0). bvar0) (sort 0)
            "KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)".to_string(),
            // ADVERSARIAL: a redex whose one-step contractum is ITSELF a redex.
            //   app (lam _ (app (lam _ (bvar 1)) (sort 0))) (sort 0):
            //   one beta step substitutes (sort 0) for bvar0, leaving the INNER
            //   redex (app (lam _ (bvar 1)) (sort 0)) un-reduced. A second step
            //   reduces further — the de-Bruijn-correct nested-redex shape.
            "KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.sort Level.zero))) (KExpr.sort Level.zero)".to_string(),
            // depth-3 nest: a lambda whose body is an app of a const onto a bvar,
            // wrapped in another lambda — exercises instantiate/lift under two
            // binders without being a redex itself.
            "KExpr.lam (KExpr.sort Level.zero) (KExpr.lam (KExpr.sort (Level.succ Level.zero)) (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))))".to_string(),
            // The remaining live constructors: genuine dependent let, field
            // projection syntax, and natural literal.
            "KExpr.let_ (KExpr.sort Level.zero) (KExpr.lit Nat.zero) (KExpr.bvar Nat.zero)".to_string(),
            "KExpr.proj Name.anonymous Nat.zero (KExpr.lit Nat.zero)".to_string(),
            "KExpr.lit (Nat.succ Nat.zero)".to_string(),
        ],
    );

    // ── Nat battery ────────────────────────────────────────────────────
    m.insert(
        "Nat",
        source_terms([
            "Nat.zero",
            "Nat.succ Nat.zero",
            "Nat.succ (Nat.succ Nat.zero)",
            "Nat.succ (Nat.succ (Nat.succ Nat.zero))",
        ]),
    );

    // ── MicroLevel battery ─────────────────────────────────────────────
    m.insert(
        "MicroLevel",
        source_terms([
            "MicroLevel.zero",
            "MicroLevel.succ MicroLevel.zero",
            "MicroLevel.max MicroLevel.zero (MicroLevel.succ MicroLevel.zero)",
            "MicroLevel.imax MicroLevel.zero (MicroLevel.succ MicroLevel.zero)",
        ]),
    );

    // ── Bool battery ───────────────────────────────────────────────────
    m.insert("Bool", source_terms(["Bool.true", "Bool.false"]));

    Ok(m)
}

/// Maximum battery tuples to try per axiom (caps the combinatorial product so a
/// 3-binder axiom over the 10-element MicroExpr battery does not blow up). The
/// first disagreeing tuple short-circuits, so the cap only bounds the
/// no-disagreement (exhaustive-within-budget) search.
const MAX_TUPLES_PER_AXIOM: usize = 4096;

/// Peel `forall`/`Pi` binders off an elaborated type, returning the list of
/// binder DOMAIN expressions (outermost first) and the final body.
fn peel_pi(ty: &Expr) -> (Vec<Expr>, Expr) {
    let mut domains = Vec::new();
    let mut cur = ty.clone();
    while let ExprKind::Pi(_, dom, body) = cur.kind() {
        domains.push(dom.as_ref().clone());
        cur = body.as_ref().clone();
    }
    (domains, cur)
}

/// If `body` is `@Eq T lhs rhs` (an App spine headed by `Const "Eq"` with three
/// arguments), return `(T, lhs, rhs)`; otherwise `None`.
fn as_eq(body: &Expr) -> Option<(Expr, Expr, Expr)> {
    let head = body.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != "Eq" {
        return None;
    }
    let args = body.get_app_args();
    if args.len() != 3 {
        return None;
    }
    Some(((*args[0]).clone(), (*args[1]).clone(), (*args[2]).clone()))
}

/// The head-symbol name of an expression's WHNF, for stuck-ness diagnosis.
/// Returns `None` when the WHNF is constructor- / sort- / lambda- / pi-headed
/// (i.e. a ground value), `Some(name)` when it is stuck on a `Const`.
fn stuck_head(env: &Environment, e: &Expr) -> Option<String> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => {
            // A ground constructor application (e.g. `MicroExpr.lam …`) has a
            // `Const` head too, but it is a CONSTRUCTOR — not a stuck function.
            // Constructor identity comes from the live environment, not a
            // namespace convention: ordinary definitions/axioms can legally be
            // named under `Nat.*`, `KExpr.*`, etc.
            if env.get_constructor(name).is_some() {
                None
            } else {
                Some(name.to_string())
            }
        }
        // Sorts / binders / bound vars / literals are values, not stuck.
        _ => None,
    }
}

/// Instantiate the (de Bruijn) body of a fully-peeled `forall` with a tuple of
/// closed witness terms supplied in INNERMOST-first order. Substituting BVar(0)
/// with `instantiate` decrements the rest, so applying the witnesses
/// innermost-first leaves a closed term.
fn instantiate_body(body: &Expr, witnesses_innermost_first: &[Expr]) -> Expr {
    let mut cur = body.clone();
    for w in witnesses_innermost_first {
        cur = cur.instantiate(w);
    }
    cur
}

/// Result of attempting to evaluate one axiom against the battery.
enum AxiomOutcome {
    /// In-scope and conservatively rejected: a witnessed non-convertible pair.
    Disagreed(DefinitionalDisagreement),
    /// In-scope, evaluated, and had no disagreement in the bounded battery.
    AgreedWithinBattery,
    /// Out of scope, with the reason.
    Excluded(ExclusionReason),
}

/// Evaluate one admitted axiom against the battery using the kernel.
fn evaluate_axiom(
    spec: &Specification,
    name: &str,
    elaborated_type: &Expr,
    battery: &BTreeMap<&'static str, Vec<Expr>>,
) -> AxiomOutcome {
    let (domains, body) = peel_pi(elaborated_type);

    // Must be an equation.
    let Some((_t, lhs, rhs)) = as_eq(&body) else {
        // Report the observed head / shape for the coverage boundary.
        let shape = match body.get_app_fn().kind() {
            ExprKind::Const(n, _) => format!("head={n}"),
            ExprKind::Pi(_, _, _) => "implication/Pi-body".to_string(),
            ExprKind::Sort(_) => "Sort".to_string(),
            other => format!("{other:?}-headed"),
        };
        return AxiomOutcome::Excluded(ExclusionReason::NotEquational(shape));
    };

    // For each binder, choose the matching battery (keyed on its domain's head
    // type-constant name). If any binder cannot be witnessed, exclude.
    let mut per_binder: Vec<&[Expr]> = Vec::with_capacity(domains.len());
    for dom in &domains {
        let dom_head = match dom.get_app_fn().kind() {
            ExprKind::Const(n, _) => n.to_string(),
            ExprKind::Sort(_) => "Sort".to_string(),
            other => format!("{other:?}"),
        };
        match battery.get(dom_head.as_str()) {
            Some(v) if !v.is_empty() => per_binder.push(v.as_slice()),
            _ => {
                return AxiomOutcome::Excluded(ExclusionReason::UngeneratableBinder(dom_head));
            }
        }
    }

    let env = spec.env();
    let tc = TypeChecker::new(env);

    // Enumerate the (bounded) cartesian product of battery tuples. We track
    // whether ANY tuple yielded a fully-ground (computable) reduction on BOTH
    // sides: if none did, the axiom is NonComputable (stuck on an abstract head).
    let mut any_computable = false;
    let mut last_stuck_head: Option<String> = None;
    let mut tuples_tried = 0usize;

    // Indices into each binder's battery; odometer-style enumeration.
    let mut idx = vec![0usize; per_binder.len()];
    loop {
        if tuples_tried >= MAX_TUPLES_PER_AXIOM {
            break;
        }
        tuples_tried += 1;

        // Build the witness tuple. `domains` is outermost-first; the OUTERMOST
        // binder is the highest de Bruijn index in the body, the INNERMOST is
        // BVar(0). `instantiate_body` consumes innermost-first, so reverse.
        let witnesses_outer_first: Vec<Expr> = idx
            .iter()
            .enumerate()
            .map(|(b, &i)| per_binder[b][i].clone())
            .collect();
        let witnesses_innermost_first: Vec<Expr> =
            witnesses_outer_first.iter().rev().cloned().collect();

        let lhs_inst = instantiate_body(&lhs, &witnesses_innermost_first);
        let rhs_inst = instantiate_body(&rhs, &witnesses_innermost_first);

        let lhs_w = tc.whnf(&lhs_inst);
        let rhs_w = tc.whnf(&rhs_inst);

        let lhs_stuck = stuck_head(env, &lhs_w);
        let rhs_stuck = stuck_head(env, &rhs_w);

        if lhs_stuck.is_none() && rhs_stuck.is_none() {
            // Both sides reduced to ground value heads: a genuine computable
            // comparison. This is the in-scope evaluation.
            any_computable = true;
            if !tc.is_def_eq(&lhs_inst, &rhs_inst) {
                let witness = witnesses_outer_first.iter().map(format_expr).collect();
                return AxiomOutcome::Disagreed(DefinitionalDisagreement {
                    axiom: name.to_string(),
                    witness,
                    lhs_whnf: format_expr(&lhs_w),
                    rhs_whnf: format_expr(&rhs_w),
                });
            }
        } else {
            // At least one side stuck on an abstract head — record it.
            last_stuck_head = lhs_stuck.or(rhs_stuck).or(last_stuck_head);
        }

        // Advance the odometer.
        if per_binder.is_empty() {
            break; // nullary axiom: a single tuple.
        }
        let mut k = per_binder.len();
        let mut wrapped = false;
        loop {
            if k == 0 {
                wrapped = true;
                break;
            }
            k -= 1;
            idx[k] += 1;
            if idx[k] < per_binder[k].len() {
                break;
            }
            idx[k] = 0;
        }
        if wrapped {
            break;
        }
    }

    finish(any_computable, last_stuck_head)
}

/// Decide the final outcome for an axiom with no observed disagreement:
/// in-scope-and-agreed if at least one tuple was computable, otherwise excluded
/// as non-computable.
fn finish(any_computable: bool, last_stuck_head: Option<String>) -> AxiomOutcome {
    if any_computable {
        AxiomOutcome::AgreedWithinBattery
    } else {
        AxiomOutcome::Excluded(ExclusionReason::NonComputable(
            last_stuck_head.unwrap_or_else(|| "no-ground-reduction".to_string()),
        ))
    }
}

/// Render an `Expr` compactly for disagreement-witness reporting.
fn format_expr(e: &Expr) -> String {
    // The kernel `Debug` is verbose but stable and unambiguous; trim to keep
    // the report readable while preserving the structural identity.
    let s = format!("{e:?}");
    let mut chars = s.chars();
    let prefix: String = chars.by_ref().take(240).collect();
    if chars.next().is_some() {
        format!("{prefix}…")
    } else {
        s
    }
}

/// Require the committed semantic-name table and its sibling generated
/// artifacts to be the exact reflection of this live environment before any
/// battery source consumes those semantic atoms.
fn ensure_committed_reflection_is_fresh(env: &Environment) -> Result<(), String> {
    fidelity_check(
        env,
        COMMITTED_DEF_SCRIPT,
        COMMITTED_INTERNING_TSV,
        COMMITTED_SKIP_LEDGER,
    )
    .map(|_| ())
    .map_err(|error| {
        format!(
            "kernel_core_red_env artifacts drift from the live environment; \
             semantic battery atoms are unsafe: {error}"
        )
    })
}

/// Return live `KExpr` constructors not exercised by the resolved KExpr
/// battery. Constructor names come from the live inductive metadata; no
/// hard-coded constructor count or namespace list participates.
fn missing_live_kexpr_constructors(
    env: &Environment,
    kexpr_terms: &[Expr],
) -> Result<Vec<String>, String> {
    let inductive = env
        .get_inductive(&clean_kernel::Name::from_string("KExpr"))
        .ok_or_else(|| "live environment has no KExpr inductive metadata".to_string())?;
    let exercised: BTreeSet<_> = kexpr_terms
        .iter()
        .filter_map(|term| match term.get_app_fn().kind() {
            ExprKind::Const(name, _) if env.get_constructor(name).is_some() => Some(name.clone()),
            _ => None,
        })
        .collect();
    Ok(inductive
        .constructor_names
        .iter()
        .filter(|constructor| !exercised.contains(*constructor))
        .map(ToString::to_string)
        .collect())
}

/// Resolve battery source strings into closed kernel `Expr`s in the spec
/// environment. Resolution is fail-closed: all declared samples are checked,
/// and any construction or elaboration failure rejects the entire battery
/// instead of silently shrinking the tested corpus.
fn resolve_battery(spec: &Specification) -> Result<BTreeMap<&'static str, Vec<Expr>>, Vec<String>> {
    ensure_committed_reflection_is_fresh(spec.env()).map_err(|error| vec![error])?;

    let mut out: BTreeMap<&'static str, Vec<Expr>> = BTreeMap::new();
    let source_battery = battery().map_err(|error| vec![error])?;
    let mut errors = Vec::new();
    let tc = TypeChecker::new(spec.env());
    for (ty, srcs) in source_battery {
        let mut terms = Vec::new();
        let expected_type = Expr::const_str(ty);
        for src in srcs {
            match spec.elaborate_source(&src, &format!("battery {ty}")) {
                Ok(e) => {
                    if e.has_fvar_quick()
                        || e.has_expr_mvar_quick()
                        || e.has_level_mvar_quick()
                        || e.has_level_param_quick()
                        || e.has_loose_bvars_quick()
                    {
                        errors.push(format!(
                            "{ty} sample {src:?} elaborated to a non-closed expression"
                        ));
                        continue;
                    }
                    match tc.infer_type(&e) {
                        Ok(actual_type) if tc.is_def_eq(&actual_type, &expected_type) => {
                            terms.push(e);
                        }
                        Ok(actual_type) => errors.push(format!(
                            "{ty} sample {src:?} has type {}, expected {ty}",
                            format_expr(&actual_type)
                        )),
                        Err(err) => {
                            errors
                                .push(format!("{ty} sample {src:?} type inference failed: {err}"));
                        }
                    }
                }
                Err(err) => errors.push(format!("{ty} sample {src:?} failed: {err}")),
            }
        }
        out.insert(ty, terms);
    }

    match out.get("KExpr") {
        Some(kexpr_terms) => match missing_live_kexpr_constructors(spec.env(), kexpr_terms) {
            Ok(missing) => errors.extend(missing.into_iter().map(|constructor| {
                format!("KExpr battery does not exercise live constructor {constructor:?}")
            })),
            Err(error) => errors.push(error),
        },
        None => errors.push("resolved battery has no KExpr entry".to_string()),
    }

    if errors.is_empty() {
        Ok(out)
    } else {
        Err(errors)
    }
}

/// Complete, deterministic census used before any battery evaluation.
struct AxiomCensus {
    total_live_axioms: usize,
    total_spec_axioms: usize,
    ambient_foundational_axioms: Vec<String>,
    ambient_trust_markers: Vec<String>,
    /// Every non-ambient live axiom, including unexpected/mismatched ones.
    /// Mismatches remain here so the gate still classifies their live type while
    /// the accompanying setup error makes the overall verdict fail closed.
    candidates: Vec<(String, Expr)>,
    setup_errors: Vec<String>,
}

/// Validate the trust-relevant payload shared by every live axiom, including
/// spec-owned candidates. Ambient axioms go through the stricter canonical
/// validator below, which includes this same floor plus exact signature checks.
fn live_axiom_integrity_errors(env: &Environment, constant: &ConstantInfo) -> Vec<String> {
    let name = constant.name.to_string();
    let mut errors = Vec::new();
    if constant.kind != ConstantKind::Axiom {
        errors.push(format!(
            "live axiom census entry {name:?} has kernel kind {:?}",
            constant.kind
        ));
    }
    if constant.value.is_some() {
        errors.push(format!(
            "live kernel axiom {name:?} carries a value in its kernel payload"
        ));
    }
    if env.declaration_verification(&constant.name)
        != Some(DeclarationVerification::FullKernelCheck)
    {
        errors.push(format!(
            "live kernel axiom {name:?} lacks FullKernelCheck provenance"
        ));
    }
    if env.is_unsafe(&constant.name) {
        errors.push(format!("live kernel axiom {name:?} is marked unsafe"));
    }
    if env.is_partial(&constant.name) {
        errors.push(format!("live kernel axiom {name:?} is marked partial"));
    }
    if env.constant_needs_recheck(&constant.name) {
        errors.push(format!(
            "live kernel axiom {name:?} is marked as needing recheck"
        ));
    }
    let declaration = Declaration::Axiom {
        name: constant.name.clone(),
        level_params: constant.level_params.clone(),
        type_: constant.type_.clone(),
    };
    if let Err(error) = env.check_decl_readonly_strict(&declaration) {
        errors.push(format!(
            "live kernel axiom {name:?} failed strict declaration recheck: {error}"
        ));
    }
    errors
}

/// Cross-check the live kernel axiom census against the spec-definition census.
///
/// The environment is authoritative for what the kernel actually assumes.
/// Spec metadata is authoritative for which of those assumptions this gate
/// claims to own. Any divergence is recorded as a fatal setup error.
fn census_axioms(env: &Environment, definitions: &HashMap<String, SpecDefinition>) -> AxiomCensus {
    let mut live: Vec<_> = env
        .constants()
        .filter(|constant| constant.kind == ConstantKind::Axiom)
        .collect();
    live.sort_by(|a, b| a.name.cmp(&b.name));

    let mut census = AxiomCensus {
        total_live_axioms: live.len(),
        total_spec_axioms: definitions.values().filter(|def| def.is_axiom).count(),
        ambient_foundational_axioms: Vec::new(),
        ambient_trust_markers: Vec::new(),
        candidates: Vec::new(),
        setup_errors: Vec::new(),
    };

    // `is_axiom` describes the installed live declaration, while proof status
    // describes the best candidate known to the promotion pipeline. A
    // DerivedPending candidate may therefore legitimately sit over either a
    // live axiom (the candidate has not been installed because it still has
    // axiom debt) or a value-bearing theorem (whose proof closure has debt).
    // Reject only terminal contradictions before considering kernel ownership.
    let mut metadata: Vec<_> = definitions.iter().collect();
    metadata.sort_by(|a, b| a.0.cmp(b.0));
    for (key, definition) in metadata {
        if definition.is_axiom && definition.proof_status == crate::spec::ProofStatus::DerivedProved
        {
            census.setup_errors.push(format!(
                "spec definition {key:?} is marked is_axiom=true but has impossible \
                 proof_status={}",
                definition.proof_status
            ));
        } else if !definition.is_axiom && definition.proof_status == crate::spec::ProofStatus::Axiom
        {
            census.setup_errors.push(format!(
                "spec definition {key:?} is marked is_axiom=false but has impossible \
                 proof_status=axiom"
            ));
        }
    }

    for constant in live {
        let name = constant.name.to_string();
        if let Some(expected_kind) = canonical_ambient_axiom_kind(&constant.name) {
            if definitions.contains_key(&name) {
                census.setup_errors.push(format!(
                    "kernel-owned ambient axiom {name:?} must not be claimed by \
                     SpecDefinition metadata"
                ));
            }
            match env.validate_canonical_ambient_axiom(&constant.name) {
                Ok(validated_kind) if validated_kind == expected_kind => {}
                Ok(validated_kind) => census.setup_errors.push(format!(
                    "kernel-owned ambient axiom {name:?} classified as {validated_kind:?}, \
                     expected {expected_kind:?}"
                )),
                Err(error) => census.setup_errors.push(format!(
                    "kernel-owned ambient axiom {name:?} failed exact validation: {error}"
                )),
            }
            match expected_kind {
                CanonicalAmbientAxiomKind::CertificationFoundation => {
                    census.ambient_foundational_axioms.push(name);
                }
                CanonicalAmbientAxiomKind::TrustMarker => {
                    census.ambient_trust_markers.push(name);
                }
            }
            continue;
        }

        census
            .setup_errors
            .extend(live_axiom_integrity_errors(env, constant));
        match definitions.get(&name) {
            Some(definition) => {
                if definition.name != name {
                    census.setup_errors.push(format!(
                        "live axiom {name:?} is stored under matching map key but its \
                         SpecDefinition.name is {:?}",
                        definition.name
                    ));
                }
                if !definition.is_axiom {
                    census.setup_errors.push(format!(
                        "live kernel axiom {name:?} is backed by a SpecDefinition with \
                         is_axiom=false"
                    ));
                }
                if definition.value_src.is_some() || definition.elaborated_value.is_some() {
                    census.setup_errors.push(format!(
                        "live kernel axiom {name:?} has value/proof metadata in its \
                         SpecDefinition"
                    ));
                }
                match &definition.elaborated_type {
                    Some(cached_type) if cached_type == &constant.type_ => {}
                    Some(_) => census.setup_errors.push(format!(
                        "live kernel axiom {name:?} has a cached elaborated type that does \
                         not exactly match the kernel declaration type"
                    )),
                    None => census.setup_errors.push(format!(
                        "live kernel axiom {name:?} is missing its cached elaborated type"
                    )),
                }
                census.candidates.push((name, constant.type_.clone()));
            }
            None => {
                census.setup_errors.push(format!(
                    "live non-foundational kernel axiom {name:?} has no backing \
                     SpecDefinition"
                ));
                // Still classify the live statement so the coverage report never
                // silently drops the unexpected axiom.
                census.candidates.push((name, constant.type_.clone()));
            }
        }
    }

    // The reverse direction closes the old flag-only blind spot: every
    // spec-marked axiom must lower to exactly one live ConstantKind::Axiom.
    let mut spec_axioms: Vec<_> = definitions
        .iter()
        .filter(|(_, definition)| definition.is_axiom)
        .collect();
    spec_axioms.sort_by(|a, b| a.0.cmp(b.0));
    let mut seen_definition_names = BTreeSet::new();
    for (key, definition) in spec_axioms {
        if !seen_definition_names.insert(definition.name.clone()) {
            census.setup_errors.push(format!(
                "multiple spec axiom entries claim SpecDefinition.name {:?}",
                definition.name
            ));
        }
        if key != &definition.name {
            census.setup_errors.push(format!(
                "spec axiom map key {key:?} does not match SpecDefinition.name {:?}",
                definition.name
            ));
        }
        if definition.value_src.is_some() || definition.elaborated_value.is_some() {
            census.setup_errors.push(format!(
                "spec axiom {:?} carries value/proof metadata",
                definition.name
            ));
        }
        match env.get_const(&clean_kernel::Name::from_string(&definition.name)) {
            Some(constant) if constant.kind == ConstantKind::Axiom => {
                match &definition.elaborated_type {
                    Some(cached_type) if cached_type == &constant.type_ => {}
                    Some(_) => census.setup_errors.push(format!(
                        "spec axiom {:?} has a cached elaborated type that does not exactly \
                         match the live kernel axiom type",
                        definition.name
                    )),
                    None => census.setup_errors.push(format!(
                        "spec axiom {:?} is missing its cached elaborated type",
                        definition.name
                    )),
                }
            }
            Some(constant) => census.setup_errors.push(format!(
                "spec axiom {:?} lowered to kernel kind {:?}, expected ConstantKind::Axiom",
                definition.name, constant.kind
            )),
            None => census.setup_errors.push(format!(
                "spec axiom {:?} has no live kernel declaration",
                definition.name
            )),
        }
    }

    census.ambient_foundational_axioms.sort();
    census.ambient_trust_markers.sort();
    census.candidates.sort_by(|a, b| a.0.cmp(&b.0));
    census.setup_errors.sort();
    census.setup_errors.dedup();
    census
}

/// Run the definitional-disagreement gate over a built spec's live axioms.
///
/// The kernel environment is the source of truth. The gate cross-checks it
/// bidirectionally against the spec-definition census before evaluating every
/// non-ambient live axiom against the live reducible environment.
#[must_use]
pub fn run_gate(spec: &Specification) -> GateReport {
    let census = census_axioms(spec.env(), spec.definitions());
    let mut report = GateReport {
        total_live_axioms: census.total_live_axioms,
        total_spec_axioms: census.total_spec_axioms,
        ambient_foundational_axioms: census.ambient_foundational_axioms,
        ambient_trust_markers: census.ambient_trust_markers,
        evaluated: Vec::new(),
        excluded: BTreeMap::new(),
        definitional_disagreements: Vec::new(),
        setup_errors: census.setup_errors,
    };

    let battery = match resolve_battery(spec) {
        Ok(battery) => battery,
        Err(errors) => {
            report.setup_errors.extend(
                errors
                    .into_iter()
                    .map(|error| format!("battery setup failed: {error}")),
            );
            report.setup_errors.sort();
            report.setup_errors.dedup();
            return report;
        }
    };

    for (name, ty) in census.candidates {
        match evaluate_axiom(spec, &name, &ty, &battery) {
            AxiomOutcome::Disagreed(disagreement) => {
                report.evaluated.push(name.clone());
                report.definitional_disagreements.push(disagreement);
            }
            AxiomOutcome::AgreedWithinBattery => report.evaluated.push(name.clone()),
            AxiomOutcome::Excluded(reason) => {
                report.excluded.insert(name.clone(), reason);
            }
        }
    }

    report.evaluated.sort();
    report
}

/// Evaluate one explicit statement against the battery, returning a witnessed
/// definitional disagreement if one exists.
///
/// The supplied source must elaborate to a `forall …, Eq …` type to be
/// evaluatable. A returned disagreement records only kernel non-convertibility;
/// it does not prove propositional inequality.
///
/// Returns:
/// - `Ok(Ok(Some(DefinitionalDisagreement)))` — a witnessed non-convertible pair.
/// - `Ok(Ok(None))` — in-scope, no disagreement within the battery budget.
/// - `Ok(Err(reason))` — the statement is out of evaluatable scope (with reason).
/// - `Err(text)` — elaboration of the statement failed.
///
/// # Errors
/// Returns `Err(String)` if the supplied `type_src` fails to elaborate in the
/// spec environment.
pub fn check_statement_for_definitional_disagreement(
    spec: &Specification,
    name: &str,
    type_src: &str,
) -> Result<Result<Option<DefinitionalDisagreement>, ExclusionReason>, String> {
    let battery = resolve_battery(spec)
        .map_err(|errors| format!("battery resolution failed: {}", errors.join("; ")))?;
    let elaborated = spec
        .elaborate_source(
            type_src,
            &format!("check_statement_for_definitional_disagreement {name}"),
        )
        .map_err(|e| format!("elaboration of '{name}' failed: {e}"))?;
    match evaluate_axiom(spec, name, &elaborated, &battery) {
        AxiomOutcome::Disagreed(disagreement) => Ok(Ok(Some(disagreement))),
        AxiomOutcome::AgreedWithinBattery => Ok(Ok(None)),
        AxiomOutcome::Excluded(reason) => Ok(Err(reason)),
    }
}

/// Convenience: build a default spec and run the disagreement gate.
///
/// Fail-closed: `report.passed()` is `false` on a definitional disagreement or
/// any census, metadata, or battery setup error.
///
/// # Errors
/// Returns `SpecError` if the specification fails to build.
pub fn audit_axiom_definitional_disagreement() -> Result<GateReport, crate::spec::SpecError> {
    let spec = Specification::new()?;
    Ok(run_gate(&spec))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    use clean_kernel::env::TrustedEnvExt;
    use clean_kernel::{ConstantInfo, Declaration, Name, Reducibility};

    use crate::spec::{AxiomCategory, ProofStatus};

    fn tracked_axiom(name: &str, elaborated_type: Option<Expr>) -> SpecDefinition {
        SpecDefinition {
            name: name.to_string(),
            type_src: "Prop".to_string(),
            value_src: None,
            is_axiom: true,
            category: AxiomCategory::HelperAxiom,
            proof_status: ProofStatus::Axiom,
            description: "focused census fixture".to_string(),
            elaborated_type,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        }
    }

    fn env_with_axiom(name: &str, type_: Expr) -> Environment {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_,
        })
        .expect("focused axiom declaration should be well formed");
        env
    }

    #[test]
    fn test_kexpr_battery_covers_every_live_constructor() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new().expect("spec builds");
            let resolved = resolve_battery(&spec)
                .unwrap_or_else(|errors| panic!("battery must resolve: {errors:?}"));
            let kexpr_terms = resolved.get("KExpr").expect("KExpr battery should exist");
            let live = spec
                .env()
                .get_inductive(&Name::from_string("KExpr"))
                .expect("KExpr must have live inductive metadata");
            assert!(
                !live.constructor_names.is_empty(),
                "live KExpr must expose constructor metadata"
            );
            let missing = missing_live_kexpr_constructors(spec.env(), kexpr_terms)
                .expect("live KExpr metadata should be available");
            assert!(
                missing.is_empty(),
                "KExpr battery misses live constructors: {missing:?}"
            );
        });
    }

    #[test]
    fn test_stuck_head_uses_live_constructor_metadata_not_namespace_prefixes() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat should initialize");
        let ordinary_nat_name = Name::from_string("Nat.notAConstructor");
        env.add_decl(Declaration::Axiom {
            name: ordinary_nat_name.clone(),
            level_params: Vec::new(),
            type_: Expr::const_str("Nat"),
        })
        .expect("ordinary Nat-namespaced constant should register");

        assert!(
            env.get_constructor(&ordinary_nat_name).is_none(),
            "fixture must be an ordinary constant, not constructor metadata"
        );
        assert_eq!(
            stuck_head(&env, &Expr::const_(ordinary_nat_name, Vec::new())),
            Some("Nat.notAConstructor".to_string()),
            "a Nat.* namespace prefix must not masquerade as a value"
        );
        assert_eq!(
            stuck_head(&env, &Expr::const_str("Nat.zero")),
            None,
            "the live Nat.zero constructor is a ground value"
        );
    }

    #[test]
    fn test_gate_report_rejects_setup_errors() {
        let report = GateReport {
            total_live_axioms: 0,
            total_spec_axioms: 0,
            ambient_foundational_axioms: Vec::new(),
            ambient_trust_markers: Vec::new(),
            evaluated: Vec::new(),
            excluded: BTreeMap::new(),
            definitional_disagreements: Vec::new(),
            setup_errors: vec!["malformed sample".to_string()],
        };
        assert!(!report.passed(), "setup errors must fail the gate closed");
    }

    #[test]
    fn test_gate_report_rejects_incomplete_live_coverage() {
        let report = GateReport {
            total_live_axioms: 1,
            total_spec_axioms: 0,
            ambient_foundational_axioms: Vec::new(),
            ambient_trust_markers: Vec::new(),
            evaluated: Vec::new(),
            excluded: BTreeMap::new(),
            definitional_disagreements: Vec::new(),
            setup_errors: Vec::new(),
        };
        assert!(!report.coverage_complete());
        assert!(
            !report.passed(),
            "an unaccounted live kernel axiom must fail the gate closed"
        );
    }

    #[test]
    fn test_census_missing_cached_type_fails_closed() {
        let env = env_with_axiom("GateFixture.missingType", Expr::prop());
        let definitions = HashMap::from([(
            "GateFixture.missingType".to_string(),
            tracked_axiom("GateFixture.missingType", None),
        )]);
        let census = census_axioms(&env, &definitions);
        assert!(
            census
                .setup_errors
                .iter()
                .any(|error| error.contains("missing its cached elaborated type")),
            "missing cached type must be a fatal census error: {:?}",
            census.setup_errors
        );
        assert!(
            census
                .candidates
                .iter()
                .any(|(name, _)| name == "GateFixture.missingType"),
            "the malformed live axiom must still be classified, not filtered away"
        );
    }

    #[test]
    fn test_census_untracked_live_domain_axiom_fails_closed() {
        let env = env_with_axiom("GateFixture.envOnly", Expr::prop());
        let census = census_axioms(&env, &HashMap::new());
        assert!(
            census
                .setup_errors
                .iter()
                .any(|error| error.contains("GateFixture.envOnly")
                    && error.contains("no backing SpecDefinition")),
            "unexpected environment-only domain axiom must fail closed: {:?}",
            census.setup_errors
        );
        assert!(
            census
                .candidates
                .iter()
                .any(|(name, _)| name == "GateFixture.envOnly"),
            "unexpected live axiom must remain in the evaluation census"
        );
    }

    #[test]
    fn test_census_type_mismatch_fails_closed() {
        let env = env_with_axiom("GateFixture.typeMismatch", Expr::prop());
        let definitions = HashMap::from([(
            "GateFixture.typeMismatch".to_string(),
            tracked_axiom(
                "GateFixture.typeMismatch",
                Some(Expr::sort(clean_kernel::Level::succ(
                    clean_kernel::Level::zero(),
                ))),
            ),
        )]);
        let census = census_axioms(&env, &definitions);
        assert!(
            census
                .setup_errors
                .iter()
                .any(|error| error.contains("does not exactly match the kernel declaration type")),
            "cached/live type mismatch must fail closed: {:?}",
            census.setup_errors
        );
    }

    #[test]
    fn test_census_live_axiom_with_non_axiom_spec_flag_fails_closed() {
        let env = env_with_axiom("GateFixture.flagMismatch", Expr::prop());
        let mut definition = tracked_axiom("GateFixture.flagMismatch", Some(Expr::prop()));
        definition.is_axiom = false;
        let definitions = HashMap::from([("GateFixture.flagMismatch".to_string(), definition)]);
        let census = census_axioms(&env, &definitions);
        assert!(
            census
                .setup_errors
                .iter()
                .any(|error| error.contains("is_axiom=false")),
            "live kind/spec flag mismatch must fail closed: {:?}",
            census.setup_errors
        );
    }

    #[test]
    fn test_census_rejects_impossible_proof_status_metadata() {
        let name = "GateFixture.statusMismatch";
        let env = env_with_axiom(name, Expr::prop());
        let mut definition = tracked_axiom(name, Some(Expr::prop()));
        definition.proof_status = ProofStatus::DerivedProved;
        let definitions = HashMap::from([(name.to_string(), definition)]);
        let census = census_axioms(&env, &definitions);
        assert!(
            census.setup_errors.iter().any(|error| {
                error.contains("is_axiom=true") && error.contains("proof_status=proved")
            }),
            "a live axiom cannot carry a proved proof status: {:?}",
            census.setup_errors
        );

        let mut non_axiom = tracked_axiom("GateFixture.inverseStatus", None);
        non_axiom.is_axiom = false;
        let inverse = census_axioms(
            &Environment::new(),
            &HashMap::from([(non_axiom.name.clone(), non_axiom)]),
        );
        assert!(
            inverse.setup_errors.iter().any(|error| {
                error.contains("is_axiom=false") && error.contains("proof_status=axiom")
            }),
            "a non-axiom cannot carry axiom proof status: {:?}",
            inverse.setup_errors
        );
    }

    #[test]
    fn test_census_accepts_pending_candidate_over_live_axiom() {
        let name = "GateFixture.pendingCandidate";
        let env = env_with_axiom(name, Expr::prop());
        let mut definition = tracked_axiom(name, Some(Expr::prop()));
        definition.proof_status = ProofStatus::DerivedPending;
        definition.axiom_deps =
            HashSet::from(["GateFixture.pendingCandidateDependency".to_string()]);
        let definitions = HashMap::from([(name.to_string(), definition)]);

        let census = census_axioms(&env, &definitions);

        assert!(
            census.setup_errors.is_empty(),
            "a pending proof candidate may remain uninstalled over a live axiom: {:?}",
            census.setup_errors
        );
        assert_eq!(
            census.candidates,
            vec![(name.to_string(), Expr::prop())],
            "the live axiom must remain in the executable gate census"
        );
    }

    #[test]
    fn test_census_rejects_counterfeit_ambient_signature() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("propext"),
            level_params: Vec::new(),
            type_: Expr::prop(),
        })
        .expect("well-formed counterfeit foundation");

        let census = census_axioms(&env, &HashMap::new());
        assert!(
            census.setup_errors.iter().any(|error| {
                error.contains("propext")
                    && error.contains("failed exact validation")
                    && error.contains("statement differs")
            }),
            "ambient names require exact canonical signatures: {:?}",
            census.setup_errors
        );
    }

    #[test]
    fn test_census_rejects_ambient_without_live_provenance() {
        let encoded = Environment::new()
            .to_bincode()
            .expect("serialize focused ambient environment");
        let env =
            Environment::from_bincode(&encoded).expect("deserialize focused ambient environment");

        let census = census_axioms(&env, &HashMap::new());
        assert!(
            census.setup_errors.iter().any(|error| {
                error.contains("\"sorry\"") && error.contains("FullKernelCheck provenance")
            }),
            "deserialization must not mint ambient trust authority: {:?}",
            census.setup_errors
        );
    }

    #[test]
    fn test_census_rejects_value_bearing_live_axiom() {
        let name = "GateFixture.valueBearing";
        let mut env = Environment::default();
        // SOUNDNESS: inside #[cfg(test)] mod tests. Fabricates a deliberately
        // ill-formed VALUE-BEARING "axiom" that the kernel would refuse to admit,
        // precisely so the census can be asserted to REJECT it. The bypass is what
        // makes the negative fixture constructible; it is compiled out of every
        // non-test build and never touches a trust-bearing environment.
        env.extend_constants_unchecked(
            [ConstantInfo::new_with_reducibility(
                Name::from_string(name),
                Vec::new(),
                Expr::prop(),
                Some(Expr::prop()),
                Reducibility::Regular(0),
                ConstantKind::Axiom,
            )]
            .into_iter(),
        );
        let definitions =
            HashMap::from([(name.to_string(), tracked_axiom(name, Some(Expr::prop())))]);

        let census = census_axioms(&env, &definitions);
        assert!(
            census.setup_errors.iter().any(|error| {
                error.contains(name) && error.contains("carries a value in its kernel payload")
            }),
            "an Axiom-kind constant must be value-less: {:?}",
            census.setup_errors
        );
    }

    #[test]
    fn test_census_rejects_structural_provenance_on_spec_axiom() {
        let name = "GateFixture.structural";
        let mut env = Environment::default();
        // SOUNDNESS: inside #[cfg(test)] mod tests. Admits an axiom via the STRUCTURAL
        // path specifically to give it structural (non-kernel-checked) provenance, so
        // the census can be asserted to REJECT that provenance on a spec axiom. The
        // rejection under test is the whole point; compiled out of non-test builds.
        env.add_decl_structural(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_: Expr::prop(),
        })
        .expect("structural axiom fixture");
        let definitions =
            HashMap::from([(name.to_string(), tracked_axiom(name, Some(Expr::prop())))]);

        let census = census_axioms(&env, &definitions);
        assert!(
            census.setup_errors.iter().any(|error| {
                error.contains(name) && error.contains("lacks FullKernelCheck provenance")
            }),
            "every spec-owned live axiom needs full kernel provenance: {:?}",
            census.setup_errors
        );
    }

    #[test]
    fn test_census_spec_axiom_lowered_to_definition_fails_closed() {
        let name = "GateFixture.kindMismatch";
        let mut env = Environment::new();
        let sort_one = Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_: sort_one.clone(),
            value: Expr::prop(),
            is_reducible: true,
        })
        .expect("focused definition declaration should be well formed");
        let definitions = HashMap::from([(name.to_string(), tracked_axiom(name, Some(sort_one)))]);
        let census = census_axioms(&env, &definitions);
        assert!(
            census
                .setup_errors
                .iter()
                .any(|error| error.contains("lowered to kernel kind Definition")),
            "spec axiom lowered to a non-axiom kind must fail closed: {:?}",
            census.setup_errors
        );
    }

    #[test]
    fn test_non_def_eq_result_is_named_only_as_definitional_disagreement() {
        let report = GateReport {
            total_live_axioms: 1,
            total_spec_axioms: 1,
            ambient_foundational_axioms: Vec::new(),
            ambient_trust_markers: Vec::new(),
            evaluated: vec!["probe".to_string()],
            excluded: BTreeMap::new(),
            definitional_disagreements: vec![DefinitionalDisagreement {
                axiom: "probe".to_string(),
                witness: vec!["w".to_string()],
                lhs_whnf: "Nat.zero".to_string(),
                rhs_whnf: "Nat.succ Nat.zero".to_string(),
            }],
            setup_errors: Vec::new(),
        };
        let rendered = report.report();
        assert!(!report.passed());
        assert!(rendered.contains("DEFINITIONAL DISAGREEMENT"));
        assert!(!rendered.contains("REFUTED"));
        assert!(!rendered.contains("FALSE"));
    }

    /// The witness renderer must cut on CHARACTER boundaries: slicing the
    /// `Debug` string at a fixed BYTE offset panics whenever that offset lands
    /// inside a multi-byte character.
    ///
    /// The kernel's `Name` `Debug` truncates each component to 32 characters, so
    /// a single very long name no longer overruns the budget on its own; the
    /// fixture nests multi-byte-named constants until the rendering genuinely
    /// exceeds it. The ASCII head pad (one byte per step) and the application
    /// nesting depth (four bytes per step) together scan the fixed byte cut
    /// across a window wider than the rendering's repeat period, and the final
    /// assertion pins that some iteration really does split a character — the
    /// case a byte slice panics on.
    #[test]
    fn test_format_expr_truncates_unicode_on_char_boundaries() {
        let unicode_name = format!("GateFixture.{}", "λ".repeat(48));
        let atom = Expr::const_(Name::from_string(&unicode_name), Vec::new());

        let mut exercised_a_split_character = false;
        for depth in 6..46usize {
            for pad in 0..4usize {
                let mut expr = Expr::const_str(&format!("GateFixture.head{}", "x".repeat(pad)));
                for _ in 0..depth {
                    expr = Expr::app(expr, atom.clone());
                }

                let raw = format!("{expr:?}");
                assert!(
                    raw.chars().count() > 240,
                    "depth {depth} pad {pad}: fixture must exceed the truncation budget, \
                     got {} chars",
                    raw.chars().count()
                );
                assert!(
                    raw.contains('λ'),
                    "depth {depth} pad {pad}: fixture must be multi-byte"
                );
                exercised_a_split_character |= !raw.is_char_boundary(240);

                let rendered = format_expr(&expr);
                assert!(
                    rendered.ends_with('…'),
                    "depth {depth} pad {pad}: must be truncated"
                );
                assert_eq!(
                    rendered.chars().count(),
                    241,
                    "depth {depth} pad {pad}: 240 characters plus the ellipsis"
                );
                let prefix = rendered.trim_end_matches('…');
                assert!(
                    raw.starts_with(prefix),
                    "depth {depth} pad {pad}: the cut must be a character-boundary prefix"
                );
            }
        }
        assert!(
            exercised_a_split_character,
            "the sweep must straddle a multi-byte character at the byte cut, \
             otherwise it does not regress the panic this renderer avoids"
        );
    }

    /// `as_eq` recognizes an `Eq`-headed body and rejects non-`Eq` ones, by
    /// elaborating two small statements.
    #[test]
    fn test_as_eq_recognizes_eq_headed_body() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new().expect("spec builds");
            // An Eq-headed closed statement.
            let eq = spec
                .elaborate_source(
                    "Eq MicroExpr (MicroExpr.sort MicroLevel.zero) (MicroExpr.sort MicroLevel.zero)",
                    "test eq",
                )
                .expect("elaborates");
            assert!(as_eq(&eq).is_some(), "Eq-headed body must be recognized");

            // A non-Eq body (a type constant).
            let non_eq = spec
                .elaborate_source("MicroExpr", "test non-eq")
                .expect("elaborates");
            assert!(
                as_eq(&non_eq).is_none(),
                "a non-Eq body must not be recognized as an equation"
            );
        });
    }

    /// A computable equation with definitionally equal instances has no
    /// disagreement in the battery: the
    /// retired-but-now-true single-step beta contract
    /// `micro_whnf (app (lam ty body) arg) = micro_instantiate body arg`
    /// must not be rejected by this check.
    #[test]
    fn test_true_single_step_beta_survives() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new().expect("spec builds");
            let outcome = check_statement_for_definitional_disagreement(
                &spec,
                "true_single_step_beta",
                "forall (ty : MicroExpr) (body : MicroExpr) (arg : MicroExpr), \
                 Eq MicroExpr (micro_whnf (MicroExpr.app (MicroExpr.lam ty body) arg)) \
                 (micro_instantiate body arg)",
            )
            .expect("elaborates");
            match outcome {
                Ok(None) => { /* in-scope, no disagreement — correct */ }
                Ok(Some(disagreement)) => {
                    panic!("definitionally equal equation disagreed: {disagreement:?}")
                }
                Err(reason) => panic!("computable equation wrongly excluded: {reason:?}"),
            }
        });
    }

    /// The gate over the live spec passes and reports the complete live/spec
    /// census plus its explicit ambient boundary.
    #[test]
    fn test_live_gate_passes_and_reports_coverage() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new().expect("spec builds");
            let report = run_gate(&spec);
            eprintln!("{}", report.report());
            assert!(
                report.passed(),
                "live disagreement gate failed: disagreements={:?}, setup={:?}",
                report.definitional_disagreements,
                report.setup_errors
            );
            // Every non-ambient live axiom is evaluated or explicitly excluded.
            assert_eq!(
                report.total_live_axioms
                    - report.ambient_foundational_axioms.len()
                    - report.ambient_trust_markers.len(),
                report.evaluated.len() + report.excluded.len(),
                "every non-ambient live axiom must be evaluated or excluded"
            );
            assert!(
                report.total_live_axioms > 0,
                "the live environment must admit some axioms"
            );
        });
    }

    #[test]
    fn test_full_gate_exercises_a_spec_owned_candidate() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new().expect("spec builds");
            let name = "GateFixture.syntheticRefl";
            spec.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: "Eq Nat Nat.zero Nat.zero".to_string(),
                value_src: None,
                is_axiom: true,
                category: AxiomCategory::HelperAxiom,
                proof_status: ProofStatus::Axiom,
                description: "non-vacuous full-gate regression".to_string(),
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })
            .expect("synthetic spec-owned axiom should register");

            let report = run_gate(&spec);
            assert!(
                report.passed(),
                "synthetic full gate failed: {}",
                report.report()
            );
            assert!(
                report.evaluated.iter().any(|candidate| candidate == name),
                "the full gate must actually evaluate its spec-owned candidate: {}",
                report.report()
            );
        });
    }
}
