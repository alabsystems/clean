// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! S4 battery — the multi-variable finite-fragment kernel-closed product
//! (blueprint 2026-07-18, slice S4).
//!
//! Corpus: EdgeGate, SinkNoLoss (fabric fixtures), Ring, Cursor, Subscribe,
//! Transact, Kernel, Snapshot (scalar golden models), EvictFull (the Tier-0
//! `Fin n → Bool` shape) — each reconstructed from a hand-written
//! `ty.cert/v1`-shaped certificate and kernel-certified end-to-end, plus the
//! adversarial legs: buggy-dial falsification with replayed traces, name-squat
//! refusal, `_assumed`-vs-conclusion α-discrimination, mutation batteries
//! caught BY THE KERNEL, oversize-enumeration refusal, and truncation-
//! divergence refusal.

use clean_kernel::env::{ConstantKind, Declaration, Environment, ProofQuality};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_tla::finite::{
    encode_finite, register_ty_cert_safety_finite, FiniteError, FiniteMachine, FiniteReport,
    MAX_ENUM_STATES,
};
use clean_tla::ty_cert::{self, TyCert};

const EDGEGATE_JSON: &str = include_str!("fixtures/edgegate.ty.cert.json");

fn cert(
    spec_src: &str,
    invariants: &[&str],
    var_sorts: &[(&str, &str)],
    constants: &[(&str, i64)],
) -> TyCert {
    TyCert {
        schema: "ty.cert/v1".into(),
        verdict: "inductive-safety-safe".into(),
        spec_src: spec_src.into(),
        init: Some("Init".into()),
        next: Some("Next".into()),
        invariants: invariants.iter().map(|s| (*s).to_string()).collect(),
        invariant_j_tla: "TRUE".into(),
        var_sorts: var_sorts
            .iter()
            .map(|(v, s)| ((*v).to_string(), (*s).to_string()))
            .collect(),
        constants: constants
            .iter()
            .map(|(n, v)| ((*n).to_string(), *v))
            .collect(),
        ay_proof_obligations: vec![],
    }
}

fn edgegate_cert(buggy: i64) -> TyCert {
    cert(
        "---- MODULE EdgeGate ----\n\
         EXTENDS Naturals\n\
         CONSTANT Buggy\n\
         VARIABLES granted, decision\n\
         Init == granted = 0 /\\ decision = 0\n\
         Grant == granted <= 0 /\\ granted' = 1 /\\ decision' = (IF 1 + Buggy > 0 THEN 1 ELSE 0)\n\
         Revoke == granted > 0 /\\ granted' = 0 /\\ decision' = (IF 0 + Buggy > 0 THEN 1 ELSE 0)\n\
         Next == Grant \\/ Revoke\n\
         FailClosed == decision <= granted\n\
         ====\n",
        &["FailClosed"],
        &[("granted", "Int"), ("decision", "Int")],
        &[("Buggy", buggy)],
    )
}

fn sink_cert(buggy: i64) -> TyCert {
    cert(
        "---- MODULE SinkNoLoss ----\n\
         EXTENDS Naturals\n\
         CONSTANTS Frame, Buggy\n\
         VARIABLES written, lost\n\
         Init == written = 0 /\\ lost = 0\n\
         Step ==\n\
           /\\ written + lost <= Frame - 1\n\
           /\\ written' = written + 1\n\
           /\\ lost' = (IF Buggy > 0 THEN Frame - written ELSE lost)\n\
         Next == Step\n\
         NoLoss == lost <= 0\n\
         Accounted == written + lost <= Frame\n\
         ====\n",
        &["NoLoss", "Accounted"],
        &[("written", "Int"), ("lost", "Int")],
        &[("Frame", 4), ("Buggy", buggy)],
    )
}

fn ring_cert(max_seq: i64) -> TyCert {
    cert(
        "---- MODULE Ring ----\n\
         EXTENDS Naturals\n\
         CONSTANTS MaxSeq, Cap\n\
         VARIABLES seq, lo\n\
         Init == seq = 0 /\\ lo = 1\n\
         Push ==\n\
           /\\ seq <= MaxSeq - 1\n\
           /\\ seq' = seq + 1\n\
           /\\ lo' = (IF (seq + 1) - lo + 1 > Cap THEN lo + 1 ELSE lo)\n\
         Next == Push\n\
         LenBounded == seq - lo + 1 <= Cap\n\
         ====\n",
        &["LenBounded"],
        &[("seq", "Int"), ("lo", "Int")],
        &[("MaxSeq", max_seq), ("Cap", 3)],
    )
}

fn cursor_cert() -> TyCert {
    cert(
        "---- MODULE Cursor ----\n\
         EXTENDS Naturals\n\
         CONSTANT MaxSeq\n\
         VARIABLES seq, cursor\n\
         Grow == seq <= MaxSeq - 1 /\\ seq' = seq + 1 /\\ UNCHANGED cursor\n\
         Deliver == seq > cursor /\\ cursor' = seq /\\ UNCHANGED seq\n\
         Init == seq = 0 /\\ cursor = 0\n\
         Next == Grow \\/ Deliver\n\
         CursorBounded == cursor <= seq\n\
         ====\n",
        &["CursorBounded"],
        &[("seq", "Int"), ("cursor", "Int")],
        &[("MaxSeq", 4)],
    )
}

fn subscribe_cert(buggy: i64) -> TyCert {
    cert(
        "---- MODULE Subscribe ----\n\
         EXTENDS Naturals\n\
         CONSTANTS MaxSeq, Cap, Buggy\n\
         VARIABLES seq, lo, cursor, lost\n\
         Init == seq = 0 /\\ lo = 1 /\\ cursor = 0 /\\ lost = 0\n\
         Grow ==\n\
           /\\ seq <= MaxSeq - 1\n\
           /\\ seq' = seq + 1\n\
           /\\ lo' = (IF (seq + 1) - lo + 1 > Cap THEN lo + 1 ELSE lo)\n\
         PollGap == lo > cursor + 1 /\\ cursor' = seq\n\
         PollDeliver ==\n\
           /\\ (Buggy = 1 \\/ lo <= cursor + 1)\n\
           /\\ cursor' = seq\n\
           /\\ lost' = (IF lo > cursor + 1 THEN 1 ELSE lost)\n\
         Next == Grow \\/ PollGap \\/ PollDeliver\n\
         NoSilentLoss == lost = 0\n\
         ====\n",
        &["NoSilentLoss"],
        &[
            ("seq", "Int"),
            ("lo", "Int"),
            ("cursor", "Int"),
            ("lost", "Int"),
        ],
        &[("MaxSeq", 4), ("Cap", 2), ("Buggy", buggy)],
    )
}

fn transact_cert() -> TyCert {
    cert(
        "---- MODULE Transact ----\n\
         EXTENDS Naturals\n\
         CONSTANTS MaxSeq, K, Buggy\n\
         VARIABLES seq, tbase, active, lost\n\
         Init == seq = 0 /\\ tbase = 0 /\\ active = 0 /\\ lost = 0\n\
         Write == seq <= MaxSeq - 1 /\\ seq' = seq + 1\n\
         Begin == active = 0 /\\ active' = 1 /\\ tbase' = seq\n\
         CommitClean ==\n\
           /\\ active = 1 /\\ seq = tbase /\\ seq <= MaxSeq - K\n\
           /\\ seq' = seq + K /\\ active' = 0\n\
         Abort == active = 1 /\\ seq > tbase /\\ active' = 0\n\
         BuggyCommit ==\n\
           /\\ active = 1 /\\ seq > tbase /\\ Buggy = 1 /\\ tbase <= MaxSeq - K\n\
           /\\ seq' = tbase + K /\\ active' = 0 /\\ lost' = 1\n\
         Next == Write \\/ Begin \\/ CommitClean \\/ Abort \\/ BuggyCommit\n\
         NoLostUpdate == lost = 0\n\
         ====\n",
        &["NoLostUpdate"],
        &[
            ("seq", "Int"),
            ("tbase", "Int"),
            ("active", "Int"),
            ("lost", "Int"),
        ],
        &[("MaxSeq", 4), ("K", 2), ("Buggy", 0)],
    )
}

fn kernel_cert(buggy: i64) -> TyCert {
    cert(
        "---- MODULE Kernel ----\n\
         EXTENDS Naturals\n\
         CONSTANTS MaxSeq, Buggy\n\
         VARIABLES seq, count\n\
         Init == seq = 0 /\\ count = 0\n\
         Emit ==\n\
           /\\ seq <= MaxSeq - 1\n\
           /\\ count' = count + 1\n\
           /\\ seq' = (IF Buggy = 1 THEN seq + 2 ELSE seq + 1)\n\
         Next == Emit\n\
         SeqIsCount == seq = count\n\
         ====\n",
        &["SeqIsCount"],
        &[("seq", "Int"), ("count", "Int")],
        &[("MaxSeq", 5), ("Buggy", buggy)],
    )
}

fn snapshot_cert() -> TyCert {
    cert(
        "---- MODULE Snapshot ----\n\
         EXTENDS Naturals\n\
         CONSTANTS MaxSeq, Buggy\n\
         VARIABLES seq, snapped, leaked\n\
         Init == seq = 0 /\\ snapped = 0 /\\ leaked = 0\n\
         Snap == snapped = 0 /\\ snapped' = 1\n\
         Write ==\n\
           /\\ seq <= MaxSeq - 1\n\
           /\\ seq' = seq + 1\n\
           /\\ leaked' = (IF Buggy = 1 /\\ snapped = 1 THEN 1 ELSE leaked)\n\
         Next == Snap \\/ Write\n\
         SnapshotIsolated == leaked = 0\n\
         ====\n",
        &["SnapshotIsolated"],
        &[("seq", "Int"), ("snapped", "Int"), ("leaked", "Int")],
        &[("MaxSeq", 4), ("Buggy", 0)],
    )
}

fn evict_full_cert() -> TyCert {
    cert(
        "---- MODULE EvictFull ----\n\
         EXTENDS Naturals\n\
         CONSTANTS MaxSeq, Cap\n\
         VARIABLES seq, lo, live\n\
         Init == seq = 0 /\\ lo = 1 /\\ live = [n \\in 1..MaxSeq |-> FALSE]\n\
         Push ==\n\
           /\\ seq <= MaxSeq - 1\n\
           /\\ seq' = seq + 1\n\
           /\\ lo' = (IF (seq + 1) - lo + 1 > Cap THEN lo + 1 ELSE lo)\n\
           /\\ live' = (IF (seq + 1) - lo + 1 > Cap THEN [n \\in 1..MaxSeq |-> IF n = seq + 1 THEN TRUE ELSE (live[n] /\\ n # lo)] ELSE [live EXCEPT ![seq + 1] = TRUE])\n\
         Next == Push\n\
         EvictOldestContiguous == \\A n \\in 1..MaxSeq : live[n] <=> (lo <= n /\\ n <= seq)\n\
         ====\n",
        &["EvictOldestContiguous"],
        &[("seq", "Int"), ("lo", "Int"), ("live", "[1..MaxSeq -> BOOLEAN]")],
        &[("MaxSeq", 5), ("Cap", 3)],
    )
}

/// Register + assert the full kernel-closed shape, returning the report.
fn certify(cert: &TyCert, thm: &str) -> (Environment, FiniteReport) {
    let mut env = Environment::with_prelude();
    let report = register_ty_cert_safety_finite(&mut env, thm, cert)
        .unwrap_or_else(|e| panic!("{thm}: finite product must certify, got {e}"));

    // The final theorem: a real Theorem, Constructive, clean closure.
    let name = Name::from_string(thm);
    let info = env.get_const(&name).expect("final theorem registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(info.value.is_some(), "Theorem retains its proof term");
    assert_eq!(
        env.proof_quality(&name).expect("proof quality"),
        ProofQuality::Constructive,
        "{thm} must be Constructive"
    );
    for dep in env.axiom_deps(&name).expect("axiom deps") {
        let s = dep.to_string();
        assert!(
            !s.contains("sorry") && !s.contains("Sorry") && !s.contains("trusted"),
            "{thm}: forbidden axiom dep {s}"
        );
    }
    // All four legs registered.
    for leg in &report.registered {
        assert!(
            env.get_const(&Name::from_string(leg)).is_some(),
            "{leg} must be registered"
        );
    }
    eprintln!(
        "[{thm}] states={} leaves={} explore={:.1}ms encode={:.1}ms check={:.1}ms \
         RFL={:.1}ms sound={:.1}ms thm={:.1}ms",
        report.reachable_states,
        report.check_leaf_count,
        report.explore_ms,
        report.encode_ms,
        report.evidence.check_ms,
        report.evidence.rfl_ms,
        report.evidence.sound_ms,
        report.evidence.thm_ms,
    );
    (env, report)
}

// ── the corpus, happy path ─────────────────────────────────────────────────

#[test]
fn test_prelude_carries_finite_vocabulary() {
    let env = Environment::with_prelude();
    for n in [
        "Bool.and",
        "Bool.or",
        "Bool.not",
        "Bool.noConfusion",
        "Bool.and_eq_true_left",
        "Bool.and_eq_true_right",
        "Nat.beq",
        "Nat.ble",
        "Nat.div",
        "Nat.mod",
        "Nat.sub",
        "Nat.mul",
        "Eq.subst",
        "Or.rec",
        "And.left",
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "prelude must carry {n}"
        );
    }
}

#[test]
fn test_edgegate_certifies_end_to_end() {
    let (env, report) = certify(&edgegate_cert(0), "TYEdgeGateSafetyFinite");
    assert_eq!(
        report.reachable_states, 2,
        "EdgeGate reaches (0,0) and (1,1)"
    );

    // The registered type α-matches the independently recomputed conclusion.
    let m = FiniteMachine::from_cert(&edgegate_cert(0)).expect("machine");
    let x = m.explore().expect("explore");
    let enc = encode_finite(&m, &x, "TYEdgeGateSafetyFinite").expect("encode");
    let info = env
        .get_const(&Name::from_string("TYEdgeGateSafetyFinite"))
        .expect("thm");
    assert_eq!(
        info.type_, enc.conclusion,
        "registered type must α-match the recomputed conclusion"
    );
    assert!(!report.fidelity_notes.is_empty(), "fidelity meter present");
}

#[test]
fn test_edgegate_json_fixture_round_trips() {
    let cert = TyCert::from_json(EDGEGATE_JSON).expect("parse edgegate fixture");
    assert_eq!(cert.constants, vec![("Buggy".to_string(), 0)]);
    let (_env, report) = certify(&cert, "TYEdgeGateSafetyFiniteJson");
    assert_eq!(report.reachable_states, 2);
}

#[test]
fn test_ring_certifies_with_exact_reachable_set() {
    let (_env, report) = certify(&ring_cert(6), "TYRingSafetyFinite");
    assert_eq!(report.reachable_states, 7, "MaxSeq=6 ring has 7 states");
    let m = FiniteMachine::from_cert(&ring_cert(6)).expect("machine");
    let x = m.explore().expect("explore");
    let expected: Vec<Vec<i64>> = vec![
        vec![0, 1],
        vec![1, 1],
        vec![2, 1],
        vec![3, 1],
        vec![4, 2],
        vec![5, 3],
        vec![6, 4],
    ];
    assert_eq!(x.reachable, expected, "the recon's exact 7-state set");
}

#[test]
fn test_sink_no_loss_two_invariants_certify() {
    let (_env, report) = certify(&sink_cert(0), "TYSinkNoLossSafetyFinite");
    assert_eq!(report.reachable_states, 5, "written 0..4, lost 0");
}

#[test]
fn test_cursor_unchanged_emission_certifies() {
    let (_env, report) = certify(&cursor_cert(), "TYCursorSafetyFinite");
    assert_eq!(
        report.reachable_states, 15,
        "all (seq,cursor) with cursor<=seq"
    );
}

#[test]
fn test_subscribe_certifies() {
    let (_env, report) = certify(&subscribe_cert(0), "TYSubscribeSafetyFinite");
    assert!(report.reachable_states > 4, "multi-action interleaving");
}

#[test]
fn test_transact_certifies() {
    let (_env, _report) = certify(&transact_cert(), "TYTransactSafetyFinite");
}

#[test]
fn test_kernel_certifies() {
    let (_env, report) = certify(&kernel_cert(0), "TYKernelSafetyFinite");
    assert_eq!(report.reachable_states, 6);
}

#[test]
fn test_snapshot_certifies() {
    let (_env, _report) = certify(&snapshot_cert(), "TYSnapshotSafetyFinite");
}

#[test]
fn test_evict_full_fin_shape_certifies() {
    // The Tier-0 `Fin n → Bool` machine: comprehension, EXCEPT, fn access,
    // ∀/⟺ — the full Tier-0 grammar, kernel-evaluated.
    let (_env, report) = certify(&evict_full_cert(), "TYEvictFullSafetyFinite");
    assert_eq!(report.reachable_states, 6, "deterministic push chain");
    // 2 scalars + 5 live bits = 7 packed slots.
    assert_eq!(report.manifest.len(), 7);
}

// ── falsification (the buggy dial), with replayed traces ───────────────────

#[test]
fn test_edgegate_buggy_dial_yields_replayed_falsification() {
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYEdgeGateBuggy", &edgegate_cert(1))
        .expect_err("Buggy=1 must falsify");
    match &err {
        FiniteError::Falsified {
            invariant,
            trace,
            replay_validated,
        } => {
            assert_eq!(invariant, "FailClosed");
            assert!(*replay_validated, "trace must replay through the relation");
            assert!(trace.len() >= 3, "init, Grant, Revoke: {trace:?}");
            let last = &trace[trace.len() - 1].state;
            assert!(
                last.contains("granted=0") && last.contains("decision=1"),
                "the violating state: {last}"
            );
        }
        other => panic!("expected Falsified, got {other}"),
    }
    // Fail closed: NOTHING registered.
    assert!(env
        .get_const(&Name::from_string("TYEdgeGateBuggy"))
        .is_none());
    assert!(env
        .get_const(&Name::from_string("TYEdgeGateBuggy_sound"))
        .is_none());
}

#[test]
fn test_subscribe_buggy_dial_yields_silent_loss_counterexample() {
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYSubscribeBuggy", &subscribe_cert(1))
        .expect_err("Buggy=1 must falsify silent loss");
    match &err {
        FiniteError::Falsified {
            invariant,
            trace,
            replay_validated,
        } => {
            assert_eq!(invariant, "NoSilentLoss");
            assert!(*replay_validated);
            assert!(
                trace
                    .last()
                    .expect("trace nonempty")
                    .state
                    .contains("lost=1"),
                "silent loss recorded: {trace:?}"
            );
            assert!(
                trace.iter().any(|s| s.action == "PollDeliver"),
                "the buggy delivery fires: {trace:?}"
            );
        }
        other => panic!("expected Falsified, got {other}"),
    }
    assert!(env
        .get_const(&Name::from_string("TYSubscribeBuggy"))
        .is_none());
}

#[test]
fn test_sink_buggy_dial_falsifies() {
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYSinkBuggy", &sink_cert(1))
        .expect_err("Buggy=1 must falsify");
    assert!(
        matches!(
            &err,
            FiniteError::Falsified {
                replay_validated: true,
                ..
            }
        ),
        "got {err}"
    );
}

#[test]
fn test_kernel_buggy_dial_falsifies() {
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYKernelBuggy", &kernel_cert(1))
        .expect_err("Buggy=1 opens a gap");
    match &err {
        FiniteError::Falsified { invariant, .. } => assert_eq!(invariant, "SeqIsCount"),
        other => panic!("expected Falsified, got {other}"),
    }
}

// ── bullet-grouping fidelity (parse false-accept regressions) ──────────────

#[test]
fn test_bulleted_disjunctive_guard_keeps_grouping_and_falsifies() {
    // REGRESSION (false-accept vector): `/\ x = 0 \/ x = 5` on one bullet line
    // + `/\ x' = x + 1` on the next is a guarded update whose guard is the
    // DISJUNCTION. Naive line-joining regrouped it as
    // `x = 0 \/ (x = 5 /\ x' = x + 1)`, silently DROPPING the x=0-guarded
    // transition — and then FALSELY certified `Safety == x # 1` although the
    // true spec reaches x=1. With bullet items parenthesized, the machine must
    // now FALSIFY.
    let c = cert(
        "---- MODULE BulletGuard ----\nVARIABLE x\nInit == x = 0\nAct ==\n  /\\ x = 0 \\/ x = 5\n  /\\ x' = x + 1\nNext == Act\nSafety == x # 1\n====\n",
        &["Safety"],
        &[("x", "Int")],
        &[],
    );
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYBulletGuard", &c)
        .expect_err("the true spec reaches x=1; certifying would be a FALSE ACCEPT");
    match &err {
        FiniteError::Falsified {
            invariant,
            trace,
            replay_validated,
        } => {
            assert_eq!(invariant, "Safety");
            assert!(*replay_validated);
            assert!(
                trace.last().expect("trace nonempty").state.contains("x=1"),
                "the dropped transition must be explored: {trace:?}"
            );
        }
        other => panic!("expected Falsified, got {other}"),
    }
    assert!(env.get_const(&Name::from_string("TYBulletGuard")).is_none());
}

#[test]
fn test_bulleted_forall_empty_domain_does_not_swallow_siblings() {
    // REGRESSION: a `\A` bullet item used to swallow ALL later bullets into
    // its quantified body; with an EMPTY domain (2..1) the swallowed conjuncts
    // were then vacuously TRUE — silently dropping `y <= 2` from the
    // invariant. `y = 3` at init violates the second bullet, so the fixed
    // grouping must FALSIFY (vacuous certification was the bug).
    let c = cert(
        "---- MODULE ForallBullet ----\nVARIABLES x, y\nInit == x = 0 /\\ y = 3\nStay == x <= 0 /\\ x' = x /\\ UNCHANGED y\nNext == Stay\nInv ==\n  /\\ \\A n \\in 2..1 : x <= 5\n  /\\ y <= 2\n====\n",
        &["Inv"],
        &[("x", "Int"), ("y", "Int")],
        &[],
    );
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYForallBullet", &c)
        .expect_err("y=3 violates the second bullet at init");
    assert!(
        matches!(&err, FiniteError::Falsified { invariant, .. } if invariant == "Inv"),
        "got {err}"
    );
    assert!(env
        .get_const(&Name::from_string("TYForallBullet"))
        .is_none());
}

#[test]
fn test_nested_bullets_certify_end_to_end() {
    // `\/`-of-`/\`-bullets (the nested emission shape) reconstructs as two
    // guarded assignments and certifies.
    let c = cert(
        "---- MODULE NestedBullets ----\nVARIABLES a, b\nInit == a = 0 /\\ b = 0\nNext ==\n  \\/ /\\ a <= 2\n     /\\ a' = a + 1\n     /\\ UNCHANGED b\n  \\/ /\\ b <= 2\n     /\\ b' = b + 1\n     /\\ UNCHANGED a\nSafety == a <= 3 /\\ b <= 3\n====\n",
        &["Safety"],
        &[("a", "Int"), ("b", "Int")],
        &[],
    );
    let (_env, report) = certify(&c, "TYNestedBulletsSafetyFinite");
    assert_eq!(report.reachable_states, 16, "a,b independently reach 0..3");
}

#[test]
fn test_duplicate_operator_definition_refused() {
    // Real TLA+ rejects redefinition; last-one-wins would let a second
    // `Safety ==` silently redefine the invariant being certified.
    let c = cert(
        "---- MODULE Dup ----\nVARIABLE x\nInit == x = 0\nBump == x <= 0 /\\ x' = x\nNext == Bump\nSafety == x <= 0\nSafety == x <= 9\n====\n",
        &["Safety"],
        &[("x", "Int")],
        &[],
    );
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYDup", &c)
        .expect_err("duplicate Safety definition must be refused");
    assert!(
        matches!(&err, FiniteError::Parse(m) if m.contains("duplicate")),
        "got {err}"
    );
}

#[test]
fn test_init_comprehension_domain_mismatch_is_typed_refusal() {
    // The Init comprehension's domain (1..3) disagrees with the declared sort
    // domain (1..MaxSeq = 1..5): a typed Fragment refusal, not a slot-vector
    // misalignment (which used to panic downstream in explore).
    let mut c = evict_full_cert();
    c.spec_src = c.spec_src.replace(
        "live = [n \\in 1..MaxSeq |-> FALSE]",
        "live = [n \\in 1..3 |-> FALSE]",
    );
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYInitDomain", &c)
        .expect_err("mismatched Init domain must be refused");
    assert!(
        matches!(&err, FiniteError::Fragment(m) if m.contains("domain size")),
        "got {err}"
    );
}

// ── refusals: bound guard, truncation, name squat ──────────────────────────

#[test]
fn test_oversize_enumeration_refused_with_named_reason() {
    // The S9 conform-at-capacity discipline: the finite product must REFUSE
    // to enumerate a large-capacity instantiation, not attempt it.
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYRingHuge", &ring_cert(9999))
        .expect_err("oversize enumeration must be refused");
    match err {
        FiniteError::StateSpaceBoundExceeded { cap, .. } => assert_eq!(cap, MAX_ENUM_STATES),
        other => panic!("expected StateSpaceBoundExceeded, got {other}"),
    }
}

/// A three-slot cube machine: each of `a, b, c` toggles 0 → `big` once (guard
/// `= 0`), so exactly the 8 corners of `{0, big}³` are reachable — a tiny state
/// space (8 ≪ [`MAX_ENUM_STATES`]) whose PACKED representation is deliberately
/// large: per-slot bound is `big + 1`, so the mixed-radix product is
/// `(big + 1)³`. `big` alone dials the packed product across the
/// [`clean_tla::finite::MAX_PACKED_STATE`] boundary while the enumeration stays
/// trivially small — isolating the packing bound from the enumeration bound.
fn pack_cube_cert(big: i64) -> TyCert {
    cert(
        "---- MODULE PackCube ----\n\
         EXTENDS Naturals\n\
         CONSTANT Big\n\
         VARIABLES a, b, c\n\
         Init == a = 0 /\\ b = 0 /\\ c = 0\n\
         SetA == a = 0 /\\ a' = Big /\\ b' = b /\\ c' = c\n\
         SetB == b = 0 /\\ b' = Big /\\ a' = a /\\ c' = c\n\
         SetC == c = 0 /\\ c' = Big /\\ a' = a /\\ b' = b\n\
         Next == SetA \\/ SetB \\/ SetC\n\
         Bounded == a <= Big /\\ b <= Big /\\ c <= Big\n\
         ====\n",
        &["Bounded"],
        &[("a", "Int"), ("b", "Int"), ("c", "Int")],
        &[("Big", big)],
    )
}

#[test]
fn test_packed_state_just_below_cap_certifies_through_kernel() {
    // Retained-soundness-bound calibration (LOWER side). The mixed-radix packing
    // over `State := Nat` is injective onto `[0, ΠBᵢ)` only while the product
    // stays representable; `MAX_PACKED_STATE = 1<<32` is the conservative
    // fail-closed guard (the true injectivity ceiling is u64). Big=1600 gives a
    // packed product (1601³ = 4_103_684_801) that sits JUST BELOW the cap
    // (4_294_967_296), with only 8 reachable states. The finite product must
    // still certify end-to-end through the kernel — proving the bound is a
    // precisely-calibrated representation ceiling, not an early cutoff, and that
    // the kernel `rfl` leg evaluates packed literals up to ~4.1e9 faithfully.
    assert!(1601u128.pow(3) <= clean_tla::finite::MAX_PACKED_STATE);
    let (_env, report) = certify(&pack_cube_cert(1600), "TYPackCubeBelowCap");
    assert_eq!(
        report.reachable_states, 8,
        "the 8 corners of the {{0,Big}}³ cube"
    );
    // 3 scalar slots, each bound Big+1 = 1601.
    assert_eq!(report.manifest.len(), 3);
    assert!(
        report.manifest.iter().all(|(_, b)| *b == 1601),
        "each slot bound is Big+1: {:?}",
        report.manifest
    );
}

#[test]
fn test_packed_state_overflow_refused_with_named_reason() {
    // Retained-soundness-bound calibration (UPPER side / fail-closed pin). Big
    // bumped to 2000 makes the packed product 2001³ = 8_012_006_001, which
    // exceeds MAX_PACKED_STATE (1<<32). The enumeration is STILL only 8 states —
    // so this is NOT the state-space bound — yet the lane must REFUSE at encode
    // time with the named PackOverflow reason rather than emit a packing that
    // could exceed the u64 injectivity ceiling. Fail-closed: nothing registers.
    assert!(2001u128.pow(3) > clean_tla::finite::MAX_PACKED_STATE);
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYPackCubeOverflow", &pack_cube_cert(2000))
        .expect_err("oversize packed-state product must be refused");
    assert!(
        matches!(err, FiniteError::PackOverflow),
        "expected PackOverflow (packing bound), got {err}"
    );
    // Fail closed: NOTHING registered, no leg survives.
    for leg in [
        "TYPackCubeOverflow",
        "TYPackCubeOverflow_check",
        "TYPackCubeOverflow_check_eq_true",
        "TYPackCubeOverflow_sound",
    ] {
        assert!(
            env.get_const(&Name::from_string(leg)).is_none(),
            "{leg} must not survive a refused product"
        );
    }
}

#[test]
fn test_truncation_divergence_fails_closed() {
    // `x - 1 + 1 = x` at x=0: Int says 0=0 (true), Nat-truncating says 1=0
    // (false) — the encoding would not be faithful, so the lane refuses.
    let c = cert(
        "---- MODULE Trunc ----\n\
         VARIABLE x\n\
         Init == x = 0\n\
         Bump == x <= 0 /\\ x' = x\n\
         Next == Bump\n\
         Weird == x - 1 + 1 = x\n\
         ====\n",
        &["Weird"],
        &[("x", "Int")],
        &[],
    );
    let mut env = Environment::with_prelude();
    let err = register_ty_cert_safety_finite(&mut env, "TYTrunc", &c)
        .expect_err("truncation divergence must fail closed");
    assert!(
        matches!(err, FiniteError::TruncationDivergence { .. }),
        "got {err}"
    );
}

#[test]
fn test_finite_name_collision_errors() {
    let mut env = Environment::with_prelude();
    register_ty_cert_safety_finite(&mut env, "TYSquatTarget", &edgegate_cert(0))
        .expect("first registration");
    let err = register_ty_cert_safety_finite(&mut env, "TYSquatTarget", &edgegate_cert(0))
        .expect_err("second registration under the same name must error");
    assert!(matches!(err, FiniteError::NameCollision(_)), "got {err}");

    // Pre-squatting ANY of the four leg names also errors.
    let mut env2 = Environment::with_prelude();
    env2.add_decl(Declaration::Definition {
        name: Name::from_string("TYSquat2_check"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
        value: Expr::const_(Name::from_string("Bool.true"), vec![]),
        is_reducible: true,
    })
    .expect("squat the checker name");
    let err2 = register_ty_cert_safety_finite(&mut env2, "TYSquat2", &edgegate_cert(0))
        .expect_err("squatted leg name must be refused");
    assert!(matches!(err2, FiniteError::NameCollision(n) if n == "TYSquat2_check"));
}

// ── the α-gate: `_assumed` can NEVER look like the finite conclusion ───────

#[test]
fn test_assumed_product_never_passes_alpha_gate() {
    // Register the 1-variable `_assumed` product (three Pi-BOUND hypotheses)
    // and α-compare its type against the independently recomputed bare
    // conclusion — the exact check the Certified gate must run. They MUST
    // differ; ProofQuality does NOT discriminate (both are Constructive).
    let acc = TyCert {
        schema: "ty.cert/v1".into(),
        verdict: "inductive-safety-safe".into(),
        spec_src: "---- MODULE Accumulator ----\n\
                   EXTENDS Integers\n\
                   VARIABLE x\n\
                   Init == x = 0\n\
                   Next == x' = x + 1\n\
                   Safety == x >= 0\n\
                   ====\n"
            .into(),
        init: Some("Init".into()),
        next: Some("Next".into()),
        invariants: vec!["Safety".into()],
        invariant_j_tla: "x >= 0".into(),
        var_sorts: vec![("x".into(), "Int".into())],
        constants: vec![],
        ay_proof_obligations: vec![],
    };
    let enc = ty_cert::encode_cert(&acc).expect("encode");
    let conclusion = ty_cert::conclusion_ty(&enc.init, &enc.next, &enc.safety);

    let mut env = Environment::new();
    ty_cert::register_ty_cert_safety_assumed(&mut env, "TYAccAssumedGate", &enc)
        .expect("assumed registers");
    let assumed = env
        .get_const(&Name::from_string("TYAccAssumedGate"))
        .expect("assumed registered");
    assert_ne!(
        assumed.type_, conclusion,
        "the α-exact type comparison MUST reject the _assumed product \
         (its type carries three extra leading Pi-hypotheses)"
    );
    // …while ProofQuality alone would NOT reject it:
    assert_eq!(
        env.proof_quality(&Name::from_string("TYAccAssumedGate"))
            .expect("quality"),
        ProofQuality::Constructive,
        "Constructive does not discriminate _assumed — the TYPE does"
    );

    // The closed product DOES pass the same comparison.
    let mut env2 = Environment::with_prelude();
    ty_cert::register_ty_cert_safety_closed(&mut env2, "TYAccClosedGate", &enc)
        .expect("closed registers");
    let closed = env2
        .get_const(&Name::from_string("TYAccClosedGate"))
        .expect("closed registered");
    assert_eq!(closed.type_, conclusion, "closed product IS the conclusion");
}

// ── mutation battery: tampered reachable sets are caught BY THE KERNEL ─────

fn register_tampered(
    mutate: impl FnOnce(&mut Vec<Vec<i64>>),
    thm: &str,
) -> (Environment, Result<(), FiniteError>) {
    let m = FiniteMachine::from_cert(&edgegate_cert(0)).expect("machine");
    let mut x = m.explore().expect("explore");
    mutate(&mut x.reachable);
    let mut env = Environment::with_prelude();
    let r = encode_finite(&m, &x, thm)
        .and_then(|enc| clean_tla::finite::register_finite_encoded(&mut env, &enc).map(|_| ()));
    (env, r)
}

#[test]
fn test_mutation_dropped_successor_rejected_by_kernel() {
    // J = {init} only: the closure leaf `memB(step init)` evaluates FALSE, so
    // the rfl leg cannot kernel-check. Caught by the kernel, fail closed.
    let (env, r) = register_tampered(|reach| reach.truncate(1), "TYMutDrop");
    assert!(r.is_err(), "dropped successor must be rejected");
    assert!(env.get_const(&Name::from_string("TYMutDrop")).is_none());
    assert!(env
        .get_const(&Name::from_string("TYMutDrop_sound"))
        .is_none());
    // ATOMICITY: registration is staged; the earlier legs (the checker and the
    // rfl leg) must NOT survive a failed product in the caller's env.
    assert!(env
        .get_const(&Name::from_string("TYMutDrop_check"))
        .is_none());
    assert!(env
        .get_const(&Name::from_string("TYMutDrop_check_eq_true"))
        .is_none());
}

#[test]
fn test_mutation_injected_unsafe_state_rejected_by_kernel() {
    // Inject (granted=0, decision=1): closed under the actions but UNSAFE, so
    // the safety leaf evaluates FALSE and the rfl leg fails.
    let (env, r) = register_tampered(|reach| reach.push(vec![0, 1]), "TYMutUnsafe");
    assert!(r.is_err(), "unsafe member of J must be rejected");
    assert!(env.get_const(&Name::from_string("TYMutUnsafe")).is_none());
    assert!(
        env.get_const(&Name::from_string("TYMutUnsafe_check"))
            .is_none(),
        "atomic registration: no leg survives a failed product"
    );
}

#[test]
fn test_mutation_swapped_state_value_rejected_by_kernel() {
    // Replace (1,1) by (1,0): Grant's successor (1,1) is no longer in J, so
    // the closure leaf evaluates FALSE and the rfl leg fails.
    let (env, r) = register_tampered(
        |reach| {
            assert_eq!(reach[1], vec![1, 1]);
            reach[1] = vec![1, 0];
        },
        "TYMutSwap",
    );
    assert!(r.is_err(), "non-closed J must be rejected");
    assert!(env.get_const(&Name::from_string("TYMutSwap")).is_none());
    assert!(
        env.get_const(&Name::from_string("TYMutSwap_check"))
            .is_none(),
        "atomic registration: no leg survives a failed product"
    );
}

#[test]
fn test_mutation_safe_closed_superset_is_sound_and_accepted() {
    // Sanity inverse: ADDING a safe, closed extra state (granted=1,decision=0)
    // keeps every check true — J need not be exactly the reachable set, only
    // closed and safe. The kernel accepts; soundness is unaffected.
    let (env, r) = register_tampered(|reach| reach.push(vec![1, 0]), "TYMutSuperset");
    assert!(
        r.is_ok(),
        "a safe closed superset J is legitimately accepted: {r:?}"
    );
    assert!(env.get_const(&Name::from_string("TYMutSuperset")).is_some());
}

// ── blessed-vocabulary squats ──────────────────────────────────────────────

#[test]
fn test_tlafin_vocabulary_squat_refused() {
    let mut env = Environment::with_prelude();
    // A bogus TLAfin.cond (`λ c t e, t` — ignores the condition) with the
    // RIGHT type: building on it would change the meaning of every statement
    // mentioning it. Must be refused.
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
    let bogus = Expr::lam(
        BinderInfo::Default,
        bool_c.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_c.clone(),
            Expr::lam(BinderInfo::Default, nat_c.clone(), Expr::bvar(1)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TLAfin.cond"),
        level_params: vec![],
        type_: Expr::arrow(
            bool_c,
            Expr::arrow(nat_c.clone(), Expr::arrow(nat_c.clone(), nat_c)),
        ),
        value: bogus,
        is_reducible: true,
    })
    .expect("bogus TLAfin.cond registers as a plain definition");

    let err = register_ty_cert_safety_finite(&mut env, "TYVocabSquat", &edgegate_cert(0))
        .expect_err("squatted TLAfin vocabulary must be refused");
    assert!(
        matches!(&err, FiniteError::VocabularySquatted { name } if name == "TLAfin.cond"),
        "got {err}"
    );
    assert!(env.get_const(&Name::from_string("TYVocabSquat")).is_none());
}

#[test]
fn test_tlasem_keystone_squat_refused() {
    let mut env = Environment::with_prelude();
    // Squat the keystone NAME with a trivially-true theorem of a DIFFERENT
    // statement. The finite lane's integrity check must refuse to build on it.
    let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::nat_lit(0);
    let eq00 = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_c.clone(), zero.clone(), zero.clone()],
    );
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("TLAsem.InductiveInvariantSound"),
        level_params: vec![],
        type_: eq00,
        value: Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat_c, zero],
        ),
    })
    .expect("squatted keystone registers as a plain theorem");

    let err = register_ty_cert_safety_finite(&mut env, "TYKeystoneSquat", &edgegate_cert(0))
        .expect_err("squatted keystone must be refused");
    assert!(
        matches!(&err, FiniteError::VocabularySquatted { name } if name == "TLAsem.InductiveInvariantSound"),
        "got {err}"
    );
    assert!(env
        .get_const(&Name::from_string("TYKeystoneSquat"))
        .is_none());
}

// ── tractability: MaxSeq=6-class wall time is recorded and bounded ─────────

#[test]
fn test_kernel_evaluation_tractable_on_maxseq6_class() {
    let (_env, report) = certify(&ring_cert(6), "TYRingTiming");
    // Generous ceiling — the point is that exhaustive kernel evaluation of the
    // MaxSeq=6-class checker is tractable, and that we RECORD the real time.
    assert!(
        report.evidence.rfl_ms < 60_000.0,
        "rfl leg must stay tractable, took {:.1}ms",
        report.evidence.rfl_ms
    );
}
