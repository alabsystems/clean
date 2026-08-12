// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Vacuity firewall acceptance gate (crystal jobs **C2** and **C2b**).
//!
//! The C2 gate reads: *the test exists, REJECTS both known-vacuous arms of
//! `KernelInferAccepts` (recorded as expected findings, not failures), PASSES
//! `KernelInfers` and every `ImplInfer` rule; wired into the lib suite.*
//!
//! C2b adds the property that made the finding set *mean* something:
//! **polarity**. A denied name reachable from a constructor field is only
//! vacuity when it sits on the CONCLUSION side — when the constructor hands
//! typing content to whoever eliminates it. Reached through a hypothesis it is
//! the opposite: the constructor DEMANDS typing evidence, which strengthens the
//! premise and is the safe direction. See
//! `designs/2026-07-29-vacuity-firewall-polarity.md` and the
//! `vacuity_firewall` module header for the computation.
//!
//! ## Expected findings vs failures
//!
//! The `KernelInferAccepts` breaches are **not** test failures. They are the
//! recorded, cited defect that motivates retiring that relation as an
//! implementation model — and they are the only evidence that this walker
//! detects anything at all. Pinning them positively means the firewall cannot be
//! quietly weakened: if a future edit makes the walker miss `has_type` inside a
//! constructor field, [`kernel_infer_accepts_findings_and_the_edge_control`]
//! fails.
//!
//! What WOULD be a failure is a NEW `STRICT` finding, a pinned `STRICT` finding
//! silently disappearing, or a `PREMISE-ONLY` finding turning `STRICT` — that
//! last one being exactly how the conflated rule would re-enter.
//!
//! ## The one thing this file proves that no existing check does
//!
//! [`kernel_infer_accepts_findings_and_the_edge_control`] runs the same walk
//! twice, once with the inductive→constructor edge and once without, and shows
//! the `lam` breach exists only with it. Without that edge the walker is
//! `Environment::axiom_deps` in shape, and `axiom_deps` reports the `lam` arm
//! clean — it reaches the *name* `LamInferWitness`, reads that inductive's own
//! type, and stops before `LamInferWitness.mk`'s two `Typing` fields. So the
//! edge is not a refinement; it is the difference between catching the nested
//! witness case and missing it.
//!
//! ## Why the assertions are batched rather than one per test
//!
//! Every `KernelInferAccepts` assertion below needs a spec containing that
//! relation, `Typing`, `has_type` and the witness inductives, and the only
//! bundle that currently builds with all of them is the FULL spec — which takes
//! minutes. The cheaper `ImplementationSoundness` bundle would be the natural
//! choice and is what an earlier revision of this file used, but it **cannot
//! build at HEAD**: `add_env_closed_checkers_depth` registers
//! `bool_false_ne_true_t` (`env_closed_checkers_depth.rs:232`) and is marked
//! `in_impl_soundness: false` (`bundles.rs:907-910`), while
//! `opt_rec_bool_true_inv` in the `defeq_fuel` stage (`in_impl_soundness: true`)
//! references it — so the bundle is internally inconsistent and
//! `build_implementation_soundness_spec_with_stack` panics with
//! `Unknown identifier: bool_false_ne_true_t`. That is a pre-existing defect in
//! that bundle, independent of the firewall; fixing it belongs to whoever owns
//! the stage table, and when it is fixed these assertions can move back onto the
//! cheap bundle unchanged.
//!
//! So the expensive build happens twice in this file, not eight times.

use std::collections::{BTreeMap, BTreeSet};

use clean_verify::test_utils::{build_eval_ir_spec_with_stack, build_spec_with_stack};
use clean_verify::vacuity_firewall::{
    audit_relation, audit_relation_with, discover_relations, env_knows, Breach, Class,
    FirewallConfig, FirewallReport, DENIED_EXACT, DENIED_PREFIX,
};

/// The relation `KernelInferAccepts` claims to be an implementation model of.
const B: &str = "KernelInferAccepts";

/// Layer-2 relations the firewall must clear, plus the prefixes under which
/// newly generated execution relations are discovered.
///
/// `KernelInfers` is the layer-2 typing/inference relation the metatheory lives
/// on; it must pass because its arms are operational (`ctx_lookup`, `whnf_to`,
/// `DefEq`, `instantiate`), never a `Typing` assertion.
///
/// The prefixes cover relations that do not exist yet: job C1's unified
/// `ImplInfer` relation and job C4's `CtxRep` / `ExprRep` bridge. Discovery
/// rather than a hardcoded name means they are audited the moment they are
/// registered, with no edit here — and a rename cannot drop one silently. `IR`
/// covers the EvalIR families from job C3.
///
/// **This list is a standing coverage obligation, and it has already been wrong
/// once.** C4 registered `ExprRep` alongside `CtxRep`
/// (`spec/core_spec/ctx_rep.rs:220`); the `CtxRep` prefix does not match it, so
/// the new bridge relation went unaudited until this line was extended. Prefix
/// discovery removes the per-relation edit, not the obligation to notice a new
/// FAMILY. Registering an execution or bridge relation whose name starts with
/// none of these means adding it here — otherwise the firewall reports clean on
/// a relation it never looked at, which is the one failure mode this whole file
/// is built to rule out.
const MUST_PASS_EXACT: &[&str] = &["KernelInfers"];
const MUST_PASS_PREFIXES: &[&str] = &[
    "ImplInfer",
    "ImplExpr",
    "ImplScoped",
    "ImplFreshLC",
    "ImplLC",
    "CtxRep",
    "ExprRep",
    "IR",
    // Crystal A2's representation relations. They are `Encodes*`, not `IR*`,
    // so the "IR" prefix did NOT reach them — the identical shape of miss that
    // `ImplScoped` is documented for below. Worse here, because A2 relates the
    // machine heap to a `Level`: an EMPTY EncodesLevelArc would make every
    // downstream A4 statement vacuously true while every axiom gate stayed
    // green, which is exactly the failure this file exists to prevent.
    "Encodes",
];

/// The complete set of findings the firewall reports on `KernelInferAccepts`, as
/// `(constructor, denied name, class, depth)`. **Measured**, not predicted.
///
/// Pinned so the finding set cannot grow silently and so a drained arm shows up
/// as a diff rather than as continued silence.
///
/// The result is **broader than the design's §1 diagnosis anticipated**. That
/// section names two vacuous arms, `const` and `lam`. The walker finds five
/// findings across **four of the five arms** — only `sort` is clean — because
/// there are two independent routes to layer 2, and C2b's polarity computation
/// is what separates them:
///
/// 1. **The named defects, all `STRICT`.** `const` writes `has_type` straight
///    into its constructor type as that field's CONCLUSION (depth 0). `lam` and
///    `pi` reach `Typing` inside `LamInferWitness.mk` / `PiInferWitness.mk` —
///    also conclusion-side, because a constructor supplies its fields — the
///    nested-witness case, reachable only via the inductive→constructor edge.
///    These arms hand typing content to consumers; `kernel_infer_inversion`'s
///    `const` minor is literally the identity on that field.
/// 2. **The guard predicates, all `PREMISE-ONLY`.** `const` and `app` both carry
///    a `KernelStateLocalCtxWellFormed st` *hypothesis*, a reducible alias
///    unfolding to `KernelLocalCtxWellFormed env ctx`, whose `cons` constructor
///    demands a real `Typing ty (KExpr.sort u)` domain-is-a-Sort derivation.
///    That is the correct definition of context well-formedness, not smuggled
///    typing content: the arm demands the evidence to be built, it does not
///    supply it. Strengthening, the safe direction.
///
/// Before C2b both routes were reported identically, and route 2 was the
/// documented false positive. It stays in the table because a premise-only path
/// that later becomes positive is precisely how the defect re-enters — and that
/// transition is a hard gate failure below.
const PINNED_FINDINGS: &[(&str, &str, Class, usize)] = &[
    ("KernelInferAccepts.app", "Typing", Class::PremiseOnly, 3),
    ("KernelInferAccepts.const", "Typing", Class::PremiseOnly, 3),
    ("KernelInferAccepts.const", "has_type", Class::Strict, 0),
    ("KernelInferAccepts.lam", "Typing", Class::Strict, 2),
    ("KernelInferAccepts.pi", "Typing", Class::Strict, 2),
];

/// `(ctor, denied) -> (class, depth)` for the measured report.
fn measured(report: &FirewallReport) -> BTreeMap<(String, String), (Class, usize)> {
    report
        .findings()
        .into_iter()
        .map(|f| ((f.ctor, f.denied), (f.class, f.depth)))
        .collect()
}

/// `(ctor, denied) -> (class, depth)` for [`PINNED_FINDINGS`].
fn pinned() -> BTreeMap<(String, String), (Class, usize)> {
    PINNED_FINDINGS
        .iter()
        .map(|(c, d, k, n)| (((*c).to_string(), (*d).to_string()), (*k, *n)))
        .collect()
}

fn pairs_with(
    m: &BTreeMap<(String, String), (Class, usize)>,
    class: Class,
) -> BTreeSet<(String, String)> {
    m.iter()
        .filter(|(_, (k, _))| *k == class)
        .map(|(p, _)| p.clone())
        .collect()
}

/// Breach triples, polarity-free — used only for the naive-vs-full edge control,
/// where the question is *which names were reached*, not how they classify.
fn triples(breaches: &[Breach]) -> BTreeSet<(String, String, usize)> {
    breaches
        .iter()
        .map(|b| (b.ctor.clone(), b.denied.clone(), b.depth))
        .collect()
}

/// GATE CLAUSE 1: the known-vacuous arms are rejected and classified, the
/// premise-only route is labelled rather than counted as a defect — plus the
/// control that proves the added edge is what catches the nested one.
#[test]
fn kernel_infer_accepts_findings_and_the_edge_control() {
    let spec = build_spec_with_stack();

    // ── (a) The instrument is live: every denied name is a name the spec has.
    //
    // A deny list that names nothing is a firewall that rejects nothing while
    // looking exactly like one that works.
    for name in DENIED_EXACT {
        assert!(
            env_knows(spec.env(), name),
            "denied name `{name}` is absent from the live spec env, so the deny list is inert"
        );
    }
    for prefix in DENIED_PREFIX {
        assert!(
            !discover_relations(&spec, &[prefix]).is_empty(),
            "denied prefix `{prefix}` matches no live inductive, so it currently denies nothing"
        );
    }
    assert!(
        env_knows(spec.env(), B),
        "{B} must be registered, or every audit below passes vacuously"
    );

    let full = audit_relation_with(&spec, B, &FirewallConfig::default());
    let naive = audit_relation_with(&spec, B, &FirewallConfig::naive_control());

    // ── (b) The const arm: `has_type` at depth 0, in CONCLUSION position.
    //
    // Its single field is
    // `(KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st ->
    //   KernelInputAdmissible st (KExpr.const n us) -> has_type (KExpr.const n us) T)`
    // — the layer-2 typing judgment as the field's own conclusion, written into
    // an arm whose real job is an operation: look the name up in the environment
    // map and instantiate its universe parameters. Depth 0 means no unfolding was
    // needed to see it; STRICT means the arm supplies it rather than demanding
    // it, which is what makes eliminating the arm return the consumer's own goal.
    let const_hit = full
        .breaches
        .iter()
        .find(|b| b.ctor == "KernelInferAccepts.const" && b.denied == "has_type")
        .unwrap_or_else(|| {
            panic!(
                "the firewall must reject the const arm — it names has_type directly.\n{}",
                full.render()
            )
        });
    assert_eq!(
        const_hit.depth,
        0,
        "the const arm's denied name is written in the constructor type itself, so it must be \
         found at depth 0, not through any unfolding. Got: {}",
        const_hit.render()
    );
    let const_finding = full
        .findings()
        .into_iter()
        .find(|f| f.ctor == "KernelInferAccepts.const" && f.denied == "has_type")
        .expect("the const/has_type finding must survive the fold");
    assert_eq!(
        const_finding.class,
        Class::Strict,
        "the const arm CONCLUDES has_type; classifying it premise-only would mean polarity is \
         computed backwards and the genuine defect is being suppressed. Got: {}",
        const_finding.render()
    );

    // ── (c) The lam arm: `Typing`, reachable ONLY through the witness, and
    // STRICT because a constructor supplies its fields.
    let lam_full: Vec<&Breach> = full
        .breaches
        .iter()
        .filter(|b| b.ctor == "KernelInferAccepts.lam")
        .collect();
    assert!(
        !lam_full.is_empty(),
        "with the inductive->constructor edge the lam arm must be rejected: its \
         LamInferWitness.mk carries two Typing fields.\n{}",
        full.render()
    );
    for b in &lam_full {
        assert_eq!(
            b.denied,
            "Typing",
            "the lam arm reaches `Typing` inside the witness, not the `has_type` alias. Got: {}",
            b.render()
        );
        assert!(
            b.depth >= 1,
            "the lam arm's breach is NOT in the constructor type itself — it is inside the \
             witness inductive's constructor, so depth must be at least 1. Got: {}",
            b.render()
        );
        assert!(
            b.path.iter().any(|n| n == "LamInferWitness"),
            "the witnessing chain must pass through LamInferWitness — that is the nested type \
             the edge exists to open. Got: {}",
            b.render()
        );
    }

    // ── (d) THE CONTROL. Without the edge, the lam breach must vanish.
    assert!(
        !naive
            .breaches
            .iter()
            .any(|b| b.ctor == "KernelInferAccepts.lam"),
        "THE CONTROL FAILED. Without the inductive->constructor edge the walker is \
         axiom_deps-shaped and MUST miss the lam arm; that it found something means the control \
         no longer isolates the edge, so this test has stopped proving the edge is \
         load-bearing.\n{}",
        naive.render()
    );

    // ── (e) The edge strictly increases detection, measured not asserted.
    let full_set = triples(&full.breaches);
    let naive_set = triples(&naive.breaches);
    assert!(
        naive_set.is_subset(&full_set),
        "the naive walk must find a SUBSET of the full walk — adding an edge can only reach \
         more.\n  full: {full_set:?}\n  naive: {naive_set:?}"
    );
    assert!(
        naive_set.len() < full_set.len(),
        "the inductive->constructor edge must catch at least one breach the naive walk misses, \
         or it is not doing anything. full={}, naive={}",
        full_set.len(),
        naive_set.len()
    );
    assert!(
        full.visited > naive.visited,
        "the full walk must reach more names than the naive one. full={}, naive={}",
        full.visited,
        naive.visited
    );

    // ── (f) The complete finding set, pinned WITH its classification.
    //
    // Three of these diffs are soundness events and one is bookkeeping; the
    // messages say which is which, because a gate that cries wolf gets muted.
    let want = pinned();
    let got = measured(&full);
    // Printed under `--nocapture` so the classification is a recorded
    // measurement, not merely a set of assertions that happened not to fire.
    for f in full.findings() {
        println!("FIREWALL {B}: {}", f.render());
    }

    let want_strict = pairs_with(&want, Class::Strict);
    let got_strict = pairs_with(&got, Class::Strict);
    let want_premise = pairs_with(&want, Class::PremiseOnly);
    let got_premise = pairs_with(&got, Class::PremiseOnly);

    // (f.1) A premise-only path that turned positive. This is how the conflated
    // rule would re-enter, and it is the reason premise-only findings are
    // recorded at all rather than dropped.
    let promoted: Vec<_> = want_premise.intersection(&got_strict).collect();
    assert!(
        promoted.is_empty(),
        "PREMISE-ONLY finding(s) on {B} became STRICT: {promoted:?}\nA constructor that used to \
         DEMAND typing evidence now SUPPLIES it. That is the vacuity defect, arriving by the one \
         route this table exists to watch.\n{}",
        full.render()
    );

    // (f.2) Any other new strict finding.
    let new_strict: Vec<_> = got_strict.difference(&want_strict).collect();
    assert!(
        new_strict.is_empty(),
        "NEW STRICT finding(s) on {B}, not in PINNED_FINDINGS: {new_strict:?}\n{}",
        full.render()
    );

    // (f.3) A strict finding that disappeared. Repairs must be deliberate: the
    // failure mode being ruled out is a walker that stopped looking.
    let drained_strict: Vec<_> = want_strict.difference(&got_strict).collect();
    assert!(
        drained_strict.is_empty(),
        "pinned STRICT finding(s) no longer reported on {B}: {drained_strict:?}. If an arm was \
         genuinely fixed, remove it from PINNED_FINDINGS and say so in the commit — but check \
         first that the walker did not simply stop looking.\n{}",
        full.render()
    );

    // (f.4) Premise-only drift. NOT a soundness event — it is pin freshness, so
    // that the table cannot rot into a description of a tree that no longer
    // exists.
    assert_eq!(
        got_premise,
        want_premise,
        "the PREMISE-ONLY set on {B} drifted. This is NOT a vacuity breach: these are denied \
         names reachable only through hypotheses, which strengthens the arm. Update \
         PINNED_FINDINGS deliberately — and if a row moved here from STRICT, say so in the \
         commit, because that is a real repair.\n{}",
        full.render()
    );

    // (f.5) The route behind each finding, pinned by depth. A finding that
    // survives but arrives by a different chain is a changed claim.
    let depth_drift: Vec<String> = want
        .iter()
        .filter_map(|(pair, (_, want_depth))| {
            let (_, got_depth) = got.get(pair)?;
            (got_depth != want_depth).then(|| {
                format!(
                    "{}/{}: pinned depth {want_depth}, measured {got_depth}",
                    pair.0, pair.1
                )
            })
        })
        .collect();
    assert!(
        depth_drift.is_empty(),
        "finding depth(s) changed on {B}: {depth_drift:?}. The classification is unchanged, but \
         the witnessing chain is not the one recorded.\n{}",
        full.render()
    );
}

/// GATE CLAUSE 2: `KernelInfers` passes, and so does every generated relation —
/// including ones that do not exist yet.
///
/// Job C1's `ImplInfer` and job C4's `CtxRep` are audited automatically the
/// moment they are registered, because the target list is discovered from the env
/// by prefix rather than hardcoded.
///
/// These relations are held to `is_pristine` — **no** layer-2 contact at any
/// polarity — not merely to `is_clean`. C2b's premise-only class exists to
/// explain a finding on a relation that already has one; it is not a licence for
/// a freshly generated execution relation to acquire one silently. A first
/// premise-only reach here is reported separately, with the correct severity.
#[test]
fn every_generated_relation_passes_the_firewall() {
    let spec = build_spec_with_stack();

    let mut targets: Vec<String> = MUST_PASS_EXACT.iter().map(|s| (*s).to_string()).collect();
    targets.extend(discover_relations(&spec, MUST_PASS_PREFIXES));
    targets.sort();
    targets.dedup();

    assert!(
        targets.iter().any(|t| t == "KernelInfers"),
        "KernelInfers must be among the audited targets"
    );
    // The two bridge relations C4 registers. Named explicitly because prefix
    // discovery silently covered only one of them until `ExprRep` was added to
    // MUST_PASS_PREFIXES — an unaudited relation and a clean relation look
    // identical from the outside, so the names that MUST be reached are asserted.
    // `ImplScoped` (M4) is listed for the same reason and is its own lesson:
    // it starts with "Impl" but matched NEITHER "ImplInfer" NOR "ImplExpr", so
    // prefix discovery skipped it entirely and this gate reported 16 green
    // without ever looking at it. An unaudited relation and a clean relation
    // are indistinguishable from the outside — hence the explicit name.
    for required in [
        "CtxRep",
        "ExprRep",
        "ImplScoped",
        "ImplLC",
        "ImplFreshLC",
        // Crystal A2. Named explicitly for the same reason as the others, and
        // with the same history: these were registered only in
        // `new_eval_ir_prelude_spec`, so this gate could not have reached them
        // at any prefix until they became Full-bundle stages.
        "EncodesLevelArc",
        "EncodesLiveLevelRef",
    ] {
        assert!(
            targets.iter().any(|t| t == required),
            "{required} must be among the audited targets — it is a live bridge relation, and a \
             prefix list that stops matching it turns this gate into a no-op for it. \
             Found: {targets:?}"
        );
    }
    assert!(
        targets.iter().any(|t| t == "ImplInfer"),
        "ImplInfer must be among the audited targets — it is the relation the crystal's \
         implementation model is being rebuilt on, so it is the one relation whose firewall \
         verdict matters most. Found: {targets:?}"
    );

    let mut strict_dirty: Vec<String> = Vec::new();
    let mut premise_dirty: Vec<String> = Vec::new();
    for name in &targets {
        assert!(
            env_knows(spec.env(), name),
            "{name} must be registered — an absent name audits nothing and would pass vacuously"
        );
        let report = audit_relation(&spec, name);
        // The verdict per relation, printed under `--nocapture`, so the audit is
        // a recorded measurement and not only an assertion that happened not to
        // fire. `visited` is the coverage denominator: a zero there with a clean
        // verdict would be the silent-no-op mode.
        println!(
            "FIREWALL {name}: {} name(s) visited, {} strict, {} premise-only",
            report.visited,
            report.strict_findings().len(),
            report.premise_only_findings().len()
        );
        // Assert the relation's CONSTRUCTORS were scanned, not that names were
        // reached: a closed enum of nullary constructors (`IRBinOp`, `IRFault`,
        // …) legitimately reaches nothing, because every constructor type is
        // just the relation itself and the relation is a permitted operational
        // dependency. `roots` non-empty plus `is_pristine` requiring
        // `unresolved.is_empty()` is what rules out the silent-no-op failure
        // mode here.
        assert!(
            !report.roots.is_empty(),
            "{name}: the audit must have scanned this relation's constructors:\n{}",
            report.render()
        );
        if !report.is_clean() {
            strict_dirty.push(report.render());
        } else if !report.is_pristine() {
            premise_dirty.push(report.render());
        }
    }

    assert!(
        strict_dirty.is_empty(),
        "the vacuity firewall rejected {} of {} generated relation(s) — denied layer-2 names in \
         CONCLUSION position, an unresolved closure, or an undischarged boundary:\n{}",
        strict_dirty.len(),
        targets.len(),
        strict_dirty.join("\n")
    );
    assert!(
        premise_dirty.is_empty(),
        "{} of {} generated relation(s) reached a denied layer-2 name in HYPOTHESIS position. \
         That is not vacuity — the relation demands the evidence rather than supplying it — but \
         these relations are pinned at zero layer-2 contact of any kind, so acquiring the first \
         one has to be a deliberate decision recorded here:\n{}",
        premise_dirty.len(),
        targets.len(),
        premise_dirty.join("\n")
    );
}

/// The firewall fails closed on a name it cannot resolve.
///
/// Not a formality: the failure mode this rules out is a rename turning a real
/// audit into a silent no-op that still reports `is_clean`. Uses the cheap EvalIR
/// bundle — the assertion is about the walker, not about any particular spec.
#[test]
fn an_unknown_relation_is_reported_unresolved_not_clean() {
    let spec = build_eval_ir_spec_with_stack();
    let report = audit_relation(&spec, "ThisRelationDoesNotExist");

    assert!(
        !report.is_clean(),
        "auditing a name the env does not know must NOT come back clean — that is how a rename \
         would turn a real check into a no-op"
    );
    assert!(!report.is_pristine());
    assert_eq!(
        report.unresolved,
        vec!["ThisRelationDoesNotExist".to_string()],
        "the unknown name must be reported as unresolved"
    );
    assert_eq!(report.visited, 0, "nothing should have been walked");
}
