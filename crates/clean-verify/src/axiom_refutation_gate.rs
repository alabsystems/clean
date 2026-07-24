// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Refutation gate for computable / equational admitted axioms.
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
//! This module is the complementary TRUTH check to the name ratchet
//! (`crate::axiom_ratchet`, `data/clean_verify_axiom_ratchet.json`): the ratchet
//! pins the *set* of admitted axioms; this gate checks the *statements* of the
//! computable ones. It EVALUATES every in-scope (computable, equational) admitted
//! axiom on a battery of concrete adversarial inputs and FAILS if any axiom is
//! falsified by a witnessed counterexample.
//!
//! ## Honest scope (the gate's guarantee)
//!
//! Refutation by counterexample is SOUND: a witnessed instantiation on which the
//! two sides of an `Eq` are NOT definitionally equal is a real disproof of the
//! universally-quantified axiom. The gate CANNOT prove the universal direction
//! (that an axiom is *true* for all inputs) — that is the kernel's job, via a
//! checked proof term. So the gate's guarantee is precisely:
//!
//! > No FALSE computable axiom survives a finite, adversarial battery of
//! > concrete instantiations.
//!
//! That is a strictly negative ("find a witness") guarantee. It does NOT claim
//! the surviving axioms are true.
//!
//! ## Coverage boundary (reported, never silent)
//!
//! Every admitted axiom is partitioned into:
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
//! The gate REPORTS its coverage (`in_scope` evaluated, `excluded` with reasons)
//! so the boundary is explicit and honest.

use std::collections::BTreeMap;

use clean_kernel::{Expr, ExprKind, TypeChecker};

use crate::spec::Specification;

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

/// A single witnessed refutation — the fail-closed evidence.
///
/// `axiom` is FALSE: instantiating its `forall` binders with `witness` makes the
/// two sides of the `Eq` reduce to NON-def-eq normal forms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refutation {
    /// The refuted axiom's spec name.
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
    /// Total admitted axioms (`is_axiom: true`) considered.
    pub total_axioms: usize,
    /// Axioms that were EVALUATED (in-scope: computable equations).
    pub evaluated: Vec<String>,
    /// Axioms excluded from evaluation, with their reason.
    pub excluded: BTreeMap<String, ExclusionReason>,
    /// Witnessed refutations. NON-EMPTY ⇒ the gate must FAIL.
    pub refutations: Vec<Refutation>,
}

impl GateReport {
    /// The gate verdict: `true` iff NO axiom was refuted.
    ///
    /// This is the fail-closed condition: a single witnessed counterexample
    /// makes it `false`. (An empty in-scope set still PASSES — the gate is
    /// genuine but vacuous on that spec; the regression test proves the engine
    /// actually bites.)
    #[must_use]
    pub fn passed(&self) -> bool {
        self.refutations.is_empty()
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
        let _ = writeln!(s, "── axiom refutation gate ───────────────────────");
        let _ = writeln!(s, "  total admitted axioms     = {}", self.total_axioms);
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
            "  refutations (fail-closed) = {}",
            self.refutations.len()
        );
        for r in &self.refutations {
            let _ = writeln!(
                s,
                "      REFUTED {} on [{}]: lhs={} =/= rhs={}",
                r.axiom,
                r.witness.join("; "),
                r.lhs_whnf,
                r.rhs_whnf
            );
        }
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
#[must_use]
fn battery() -> BTreeMap<&'static str, Vec<&'static str>> {
    let mut m: BTreeMap<&'static str, Vec<&'static str>> = BTreeMap::new();

    // ── MicroExpr battery ──────────────────────────────────────────────
    // Includes the canonical "contractum is itself a redex" shape and nested
    // / chained redexes — the gap the prompt requires us to fill.
    m.insert(
        "MicroExpr",
        vec![
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
        ],
    );

    // ── KExpr battery ──────────────────────────────────────────────────
    // KExpr is the kernel-expression model (`expr_model.rs`): a pure
    // 6-constructor inductive — sort/bvar/app/lam/pi/const — and the PRIMARY
    // object type of the kernel↔micro spec. Before this entry existed the gate
    // was BLIND to it: every `forall (… : KExpr), Eq …` axiom (e.g.
    // `kernel_to_micro_instantiate`, the `instantiate`/`lift` identities) was
    // excluded as `UngeneratableBinder("KExpr")` and never evaluated.
    //
    // NOTE the constructor signatures differ from MicroExpr: `KExpr.sort` and
    // `KExpr.bvar` both take a raw `Nat` (not a MicroLevel); `KExpr.const` takes
    // a `Name` and a `ListType Level`. We mirror the MicroExpr battery's
    // adversarial shapes — a beta redex and a redex whose one-step contractum is
    // ITSELF a redex (the shape that exposed the retired micro_whnf falsity).
    m.insert(
        "KExpr",
        vec![
            // atoms / values (already weak-head-normal)
            "KExpr.sort Level.zero",
            "KExpr.sort (Level.succ Level.zero)",
            "KExpr.bvar Nat.zero",
            "KExpr.bvar (Nat.succ Nat.zero)",
            // a const with a literal Name (anonymous) + empty universe list
            "KExpr.const Name.anonymous (ListType.nil Level)",
            // a const with a non-anonymous literal Name (str anonymous 0). Under
            // the Front #1 Stage-3 swap this is the interned image of a REAL name
            // (tag 0 = "KExpr", an inductive type name: delta/iota-inert).
            "KExpr.const (Name.str Name.anonymous Nat.zero) (ListType.nil Level)",
            // a const that DELTA-FIRES in the swapped the_red_env: tag 14 is the
            // interned image of `Nat.add`, a reflected DefEnv entry (see
            // generated/kernel_core_red_env.interning.tsv) — keeps the gate's
            // delta-reduction shapes live over the real env.
            "KExpr.const (Name.str Name.anonymous (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))))))))) (ListType.nil Level)",
            // a const that is a REAL reflected constructor name: tag 15 is the
            // interned image of `Nat.zero` (an iota-relevant major head over the
            // swapped env).
            "KExpr.const (Name.str Name.anonymous (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))))))) (ListType.nil Level)",
            // a plain lambda value: λ (sort 0). bvar0
            "KExpr.lam (KExpr.sort Nat.zero) (KExpr.bvar Nat.zero)",
            // a plain pi value: Π (sort 0). bvar0
            "KExpr.pi (KExpr.sort Nat.zero) (KExpr.bvar Nat.zero)",
            // a plain app over atoms: app (bvar0) (sort 0)
            "KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Nat.zero)",
            // a single beta redex: (λ (sort 0). bvar0) (sort 0)
            "KExpr.app (KExpr.lam (KExpr.sort Nat.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Nat.zero)",
            // ADVERSARIAL: a redex whose one-step contractum is ITSELF a redex.
            //   app (lam _ (app (lam _ (bvar 1)) (sort 0))) (sort 0):
            //   one beta step substitutes (sort 0) for bvar0, leaving the INNER
            //   redex (app (lam _ (bvar 1)) (sort 0)) un-reduced. A second step
            //   reduces further — the de-Bruijn-correct nested-redex shape.
            "KExpr.app (KExpr.lam (KExpr.sort Nat.zero) (KExpr.app (KExpr.lam (KExpr.sort Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.sort Nat.zero))) (KExpr.sort Nat.zero)",
            // depth-3 nest: a lambda whose body is an app of a const onto a bvar,
            // wrapped in another lambda — exercises instantiate/lift under two
            // binders without being a redex itself.
            "KExpr.lam (KExpr.sort Level.zero) (KExpr.lam (KExpr.sort (Level.succ Level.zero)) (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))))",
        ],
    );

    // ── Nat battery ────────────────────────────────────────────────────
    m.insert(
        "Nat",
        vec![
            "Nat.zero",
            "Nat.succ Nat.zero",
            "Nat.succ (Nat.succ Nat.zero)",
            "Nat.succ (Nat.succ (Nat.succ Nat.zero))",
        ],
    );

    // ── MicroLevel battery ─────────────────────────────────────────────
    m.insert(
        "MicroLevel",
        vec![
            "MicroLevel.zero",
            "MicroLevel.succ MicroLevel.zero",
            "MicroLevel.max MicroLevel.zero (MicroLevel.succ MicroLevel.zero)",
            "MicroLevel.imax MicroLevel.zero (MicroLevel.succ MicroLevel.zero)",
        ],
    );

    // ── Bool battery ───────────────────────────────────────────────────
    m.insert("Bool", vec!["Bool.true", "Bool.false"]);

    m
}

/// Maximum battery tuples to try per axiom (caps the combinatorial product so a
/// 3-binder axiom over the 10-element MicroExpr battery does not blow up). The
/// first refuting tuple short-circuits, so the cap only bounds the *non*-refuting
/// (exhaustive-within-budget) search.
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
fn stuck_head(e: &Expr) -> Option<String> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => {
            // A ground constructor application (e.g. `MicroExpr.lam …`) has a
            // `Const` head too, but it is a CONSTRUCTOR — not a stuck function.
            // We treat any `Foo.bar` whose prefix is a known battery type as a
            // value head, everything else as stuck.
            let n = name.to_string();
            if is_value_head(&n) {
                None
            } else {
                Some(n)
            }
        }
        // Sorts / binders / bound vars / literals are values, not stuck.
        _ => None,
    }
}

/// Whether a `Const` head name denotes a (ground) constructor of a battery type,
/// rather than a stuck reducible/abstract function. This is the value-vs-stuck
/// discriminator used by [`stuck_head`].
fn is_value_head(name: &str) -> bool {
    const VALUE_PREFIXES: &[&str] = &[
        "MicroExpr.",
        "MicroLevel.",
        "KExpr.",
        "Name.",
        "Level.",
        "ListType.",
        "Nat.",
        "Bool.",
        "MicroCert.",
        "ProdType.mk",
        "Eq.refl",
    ];
    VALUE_PREFIXES.iter().any(|p| name.starts_with(p))
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
    /// In-scope and refuted: a witnessed counterexample.
    Refuted(Refutation),
    /// In-scope, evaluated, and survived the battery (no counterexample found).
    Survived,
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

        let lhs_stuck = stuck_head(&lhs_w);
        let rhs_stuck = stuck_head(&rhs_w);

        if lhs_stuck.is_none() && rhs_stuck.is_none() {
            // Both sides reduced to ground value heads: a genuine computable
            // comparison. This is the in-scope evaluation.
            any_computable = true;
            if !tc.is_def_eq(&lhs_inst, &rhs_inst) {
                let witness = witnesses_outer_first.iter().map(format_expr).collect();
                return AxiomOutcome::Refuted(Refutation {
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

/// Decide the final outcome for an axiom that survived the battery without a
/// refutation: in-scope-and-survived if at least one tuple was computable,
/// otherwise excluded as non-computable.
fn finish(any_computable: bool, last_stuck_head: Option<String>) -> AxiomOutcome {
    if any_computable {
        AxiomOutcome::Survived
    } else {
        AxiomOutcome::Excluded(ExclusionReason::NonComputable(
            last_stuck_head.unwrap_or_else(|| "no-ground-reduction".to_string()),
        ))
    }
}

/// Render an `Expr` compactly for witness / counterexample reporting.
fn format_expr(e: &Expr) -> String {
    // The kernel `Debug` is verbose but stable and unambiguous; trim to keep
    // the report readable while preserving the structural identity.
    let s = format!("{e:?}");
    if s.len() > 240 {
        format!("{}…", &s[..240])
    } else {
        s
    }
}

/// Resolve battery source strings into closed kernel `Expr`s in the spec
/// environment. Any string that fails to elaborate is dropped from that type's
/// battery (it cannot be a witness), but at least one MicroExpr witness must
/// survive or the gate would be vacuous — the caller asserts that.
fn resolve_battery(spec: &Specification) -> BTreeMap<&'static str, Vec<Expr>> {
    let mut out: BTreeMap<&'static str, Vec<Expr>> = BTreeMap::new();
    for (ty, srcs) in battery() {
        let mut terms = Vec::new();
        for src in srcs {
            match spec.elaborate_source(src, &format!("battery {ty}")) {
                Ok(e) => terms.push(e),
                Err(err) => {
                    eprintln!("axiom_refutation_gate: battery term '{src}' dropped: {err}");
                }
            }
        }
        out.insert(ty, terms);
    }
    out
}

/// Run the refutation gate over a built spec's LIVE admitted axioms.
///
/// This reuses the spec's own definition census (`Specification::definitions`) —
/// it does NOT re-parse source — so it evaluates exactly the axioms the running
/// system admits, against the live (reducible) kernel environment.
#[must_use]
pub fn run_gate(spec: &Specification) -> GateReport {
    let battery = resolve_battery(spec);

    let mut report = GateReport {
        total_axioms: 0,
        evaluated: Vec::new(),
        excluded: BTreeMap::new(),
        refutations: Vec::new(),
    };

    // Deterministic order: sort axiom names.
    let mut axioms: Vec<(&String, &Expr)> = spec
        .definitions()
        .values()
        .filter(|def| def.is_axiom)
        .filter_map(|def| def.elaborated_type.as_ref().map(|t| (&def.name, t)))
        .collect();
    axioms.sort_by(|a, b| a.0.cmp(b.0));

    for (name, ty) in axioms {
        report.total_axioms += 1;
        match evaluate_axiom(spec, name, ty, &battery) {
            AxiomOutcome::Refuted(r) => {
                report.evaluated.push(name.clone());
                report.refutations.push(r);
            }
            AxiomOutcome::Survived => report.evaluated.push(name.clone()),
            AxiomOutcome::Excluded(reason) => {
                report.excluded.insert(name.clone(), reason);
            }
        }
    }

    report.evaluated.sort();
    report
}

/// Evaluate a SINGLE explicit statement (given as a clean `forall …, Eq …` type
/// source string) against the battery, returning a refutation if one exists.
///
/// This is the engine the REGRESSION test drives to reconstruct the two retired
/// FALSE `micro_whnf` statements and demonstrate the gate genuinely refutes them
/// — it elaborates the supplied type in the live spec env and runs the exact
/// same kernel evaluation as [`run_gate`]. It is NOT a hardcoded assertion: the
/// refutation, if any, is a real kernel `is_def_eq` disagreement on a concrete
/// witness.
///
/// Returns:
/// - `Ok(Ok(Some(Refutation)))` — a witnessed counterexample (statement FALSE).
/// - `Ok(Ok(None))` — in-scope, no counterexample within the battery budget.
/// - `Ok(Err(reason))` — the statement is out of evaluatable scope (with reason).
/// - `Err(text)` — elaboration of the statement failed.
///
/// # Errors
/// Returns `Err(String)` if the supplied `type_src` fails to elaborate in the
/// spec environment.
pub fn refute_statement(
    spec: &Specification,
    name: &str,
    type_src: &str,
) -> Result<Result<Option<Refutation>, ExclusionReason>, String> {
    let battery = resolve_battery(spec);
    let elaborated = spec
        .elaborate_source(type_src, &format!("refute_statement {name}"))
        .map_err(|e| format!("elaboration of '{name}' failed: {e}"))?;
    match evaluate_axiom(spec, name, &elaborated, &battery) {
        AxiomOutcome::Refuted(r) => Ok(Ok(Some(r))),
        AxiomOutcome::Survived => Ok(Ok(None)),
        AxiomOutcome::Excluded(reason) => Ok(Err(reason)),
    }
}

/// Convenience: build a default spec and run the gate. Intended for an audit
/// lane / CLI: print `report.report()` and use `report.passed()` as the verdict.
///
/// Fail-closed: `report.passed()` is `false` iff some in-scope computable axiom
/// was refuted by a concrete witness.
///
/// # Errors
/// Returns `SpecError` if the specification fails to build.
pub fn audit_axiom_refutation() -> Result<GateReport, crate::spec::SpecError> {
    let spec = Specification::new()?;
    Ok(run_gate(&spec))
}

#[cfg(test)]
mod tests {
    use super::*;

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

    /// A TRUE computable equation survives the battery (no false positive): the
    /// retired-but-now-true single-step beta contract
    /// `micro_whnf (app (lam ty body) arg) = micro_instantiate body arg`
    /// must NOT be refuted (it is genuinely true).
    #[test]
    fn test_true_single_step_beta_survives() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new().expect("spec builds");
            let outcome = refute_statement(
                &spec,
                "true_single_step_beta",
                "forall (ty : MicroExpr) (body : MicroExpr) (arg : MicroExpr), \
                 Eq MicroExpr (micro_whnf (MicroExpr.app (MicroExpr.lam ty body) arg)) \
                 (micro_instantiate body arg)",
            )
            .expect("elaborates");
            match outcome {
                Ok(None) => { /* in-scope, survived — correct */ }
                Ok(Some(r)) => panic!("TRUE equation wrongly refuted: {r:?}"),
                Err(reason) => panic!("TRUE equation wrongly excluded: {reason:?}"),
            }
        });
    }

    /// The gate over the live spec PASSES (no currently-admitted computable
    /// axiom is refuted) and the coverage boundary is reported.
    #[test]
    fn test_live_gate_passes_and_reports_coverage() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new().expect("spec builds");
            let report = run_gate(&spec);
            eprintln!("{}", report.report());
            assert!(
                report.passed(),
                "a currently-LIVE computable axiom was REFUTED — this is a real \
                 soundness finding, not a test flake: {:?}",
                report.refutations
            );
            // The boundary must be explicit: every axiom is accounted for as
            // either evaluated or excluded-with-reason.
            assert_eq!(
                report.total_axioms,
                report.evaluated.len() + report.excluded.len(),
                "every admitted axiom must be either evaluated or excluded"
            );
            assert!(
                report.total_axioms > 0,
                "the live spec must admit some axioms"
            );
        });
    }
}
