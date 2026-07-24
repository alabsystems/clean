// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ALWAYS-ON MASQUERADE GATE for the Clean kernel corpus.
//!
//! The masquerade detector (`env::proof_quality::check_proof_nontrivial`) is
//! normally only run at registration time when `CLEAN_STRICT_PROOF_QUALITY=1` is
//! set (default OFF — see `decl_add.rs`). That means it has ZERO always-on
//! coverage: a newly-added masquerade (an `Eq.refl`-collapse / vacuous refl, an
//! argument-discarding carrier, or a hypothesis-wrapped `H -> H` tautology) could
//! silently reach a Constructive/PROVED count without any CI signal.
//!
//! This module closes that gap with an ALWAYS-ON test (`gate` below — NOT gated
//! by the env var, NOT `#[ignore]`d). It builds the full registered
//! prelude + NN-overlay corpus, runs `check_proof_nontrivial` over EVERY
//! `ConstantKind::Theorem`, and asserts that the set of flagged theorems is a
//! subset of the (now EMPTY) allowlist — i.e. that NOTHING is flagged. A
//! genuinely new masquerade produces a flag OUTSIDE the allowlist and FAILS the
//! gate immediately. (The detector's real soundness rules are M1 alias-collapse,
//! M2 hollow carrier, and M4 vacuous refl; the M3 unused-IH style heuristic is
//! non-gating — see `proof_quality.rs`.)
//!
//! ## Why a post-registration gate instead of registration-time rejection
//!
//! Enabling `CLEAN_STRICT_PROOF_QUALITY=1` globally would REJECT flagged
//! theorems at `add_decl`. So this gate runs the detector POST-registration over
//! the assembled corpus and turns NEW findings into a test failure without
//! disturbing init.
//!
//! ## Why the allowlist is EMPTY (the gate passes because the detector is precise)
//!
//! After the 2026-06 precision pass the masquerade rules are precise and the
//! corpus is clean, so the flagged set — and hence the allowlist — is EMPTY:
//!
//! * **M4 (`Eq.refl` root)** fires ONLY when the proved type, after peeling outer
//!   `Pi` binders, is a vacuous `Eq a a`/`HEq a a` (syntactically identical
//!   sides). Every sound definitional-equality lemma (`Nat.add_zero`,
//!   `Rat.inv_zero`, the C004 faithful refls, `Int.min_def`/`Rat.max_def`, …) has
//!   DISTINCT sides and is no longer flagged. The corpus has no vacuous `Eq a a`
//!   theorem → ZERO M4 findings.
//! * **M3 (unused induction hypothesis)** is NOT a masquerade rule and is no
//!   longer pushed by `check_proof_nontrivial` (see the SOUNDNESS note in
//!   `proof_quality.rs`). On a kernel-checked corpus "the step minor ignores its
//!   IH" has ZERO true positives: if the recursor application type-checks against
//!   the real goal, the per-case goal was provable directly — the sound
//!   "recursor as case-analysis" idiom (double-`Nat.rec` min/max lemmas, `Int`
//!   arithmetic, `Nat.divmodAux`/`Nat.ulpRound`, `Nat.pred_le`, …). An exhaustive
//!   audit of every former M3 flag found 100% genuine, axiom-free, Constructive
//!   proofs, so the rule was demoted to a non-gating structural diagnostic.
//! * **M1 (alias-collapse)** and **M2 (argument-discarding / hollow carrier)**
//!   remain fully active and yield ZERO findings on the current corpus.
//!
//! The gate therefore guards the genuine soundness signals (M1, M2, M4 + the
//! gamma-crown `H -> H` gate): a newly-introduced vacuous refl, alias-collapse,
//! or hollow carrier produces a flag that is — by construction — outside the
//! empty allowlist and FAILS the gate. Nothing is being "waved through".
//!
//! ## On the named gamma-crown H->H wrappers (C001/C004/C006/C009/C011/...)
//!
//! The known hypothesis-wrapped NN conjecture headline theorems
//! (`NNVerify.C011.softmax_width_monotone`, the C001/C009/C029/C030 `fun … h => h`
//! projections, etc.) are honestly classified `hypothesis_wrapped` /
//! `axiom-dependent` by the authoritative constructive-count gate
//! (`gamma_crown_verify::classify_headline_theorem`, which uses
//! `proof_is_bare_hypothesis_projection`) and are tracked in
//! `data/axiom_audit.json`. They are NOT flagged by M1-M4: a bare bound-variable
//! projection (`fun … h => h`) has no `Eq.refl` root, no recursor, and no
//! reducible carrier, so `check_proof_nontrivial` returns an EMPTY finding set
//! for them. They therefore (correctly) do not appear in the allowlist below —
//! their masquerade status is enforced by the gamma-crown gate's
//! `constructive_conjectures == 0` invariant, not by this M1-M4 gate. This gate
//! is the complementary always-on guard for the M1-M4 patterns specifically.

use super::types::ConstantKind;
use super::Environment;
use crate::name::Name;

/// Allowlist of theorems the masquerade detector flags on the full corpus.
///
/// **EMPTY — and that is the point.** After the 2026-06 precision pass the gate
/// passes because the detector is PRECISE, not because a baseline of genuine
/// proofs is being waved through:
///
/// * **M4 (`Eq.refl` root)** fires only on a vacuous `Eq a a`/`HEq a a`
///   (syntactically identical sides). Every sound definitional-equality lemma
///   (`Nat.add_zero`, `Rat.inv_zero`, the C004 faithful refls,
///   `Int.min_def`/`Rat.max_def`, …) has DISTINCT sides and is not flagged. The
///   corpus contains no vacuous `Eq a a` theorem, so M4 yields ZERO findings.
/// * **M3 (unused induction hypothesis)** is NOT a masquerade rule at all and is
///   no longer pushed by `check_proof_nontrivial` (see the SOUNDNESS note in
///   `proof_quality.rs`). On a kernel-checked corpus "the step minor ignores its
///   IH" has zero true positives: if the recursor application type-checks against
///   the real goal, the per-case goal was provable directly — the sound
///   "recursor as case-analysis" idiom. An exhaustive audit of all 54 former M3
///   flags confirmed 100% genuine, axiom-free, Constructive proofs.
/// * **M1 (alias-collapse)** and **M2 (argument-discarding / hollow carrier)**
///   remain fully active and yield ZERO findings on the current corpus.
///
/// So the real masquerade rules (M1, M2, M4 + the gamma-crown `H -> H` gate)
/// produce no findings, and the style heuristic (M3) no longer gates. The gate
/// therefore passes with an EMPTY allowlist. A genuinely new masquerade
/// (vacuous refl, alias-collapse, or hollow carrier) produces a flag whose name
/// is — by construction — NOT in this empty set and FAILS the gate immediately.
/// NEVER add a name here to silence a flag: an M1/M2/M4 flag is a real soundness
/// signal to be fixed at the proof, not allowlisted.
const ALLOWLIST: &[&str] = &[];

/// Build the representative full corpus: the Lean prelude plus every
/// gamma-crown NN-verify / Rat / Fin overlay init chain used elsewhere in the
/// test suite (mirrors `init_conjecture` in `gamma_crown_verify.rs` and
/// `init_full_environment` in `tests_proof_search_scan.rs`).
///
/// Each `init_*` is best-effort (`let _ = …`): an upstream init regression must
/// not turn this soundness gate into a false PASS by aborting early, and most of
/// the corpus loads independently. The gate inspects whatever was successfully
/// registered.
fn full_corpus_env() -> Environment {
    let mut env = Environment::with_prelude();
    let _ = env.init_nn_verify_c001();
    let _ = env.init_nn_verification_c002();
    let _ = env.init_nn_verify_eclipse_convergence();
    let _ = env.init_nn_verify_crown_layernorm();
    let _ = env.init_nn_verify_mccormick_attention();
    let _ = env.init_nn_verify_blockwise_crown();
    let _ = env.init_nn_verify_streaming_certs();
    let _ = env.init_nn_verify_ibp_tightness();
    let _ = env.init_nn_verification_c009();
    let _ = env.init_nn_verify_zonotope_crown();
    let _ = env.init_nn_verify_softmax_c011();
    let _ = env.init_nn_verify_relu_stability();
    let _ = env.init_nn_verify_nullstellensatz();
    let _ = env.init_nn_verify_pac_proof();
    let _ = env.init_nn_verify_orbit_crown();
    env
}

/// ALWAYS-ON gate: no theorem outside the audited allowlist may be flagged by
/// the M1-M4 masquerade detector. NOT gated by `CLEAN_STRICT_PROOF_QUALITY`,
/// NOT `#[ignore]`d — runs on every `cargo test -p clean-kernel --lib`.
#[test]
fn masquerade_gate_no_new_masquerade_reaches_corpus() {
    crate::test_utils::run_with_stack(crate::test_utils::LARGE_STACK, || {
        let env = full_corpus_env();

        let allowlist: std::collections::BTreeSet<&str> = ALLOWLIST.iter().copied().collect();

        // Iterate every registered Theorem-kind constant and collect the names
        // that `check_proof_nontrivial` flags with a non-empty finding set.
        let mut flagged: Vec<(String, String)> = Vec::new();
        let theorem_names: Vec<Name> = env
            .constants()
            .filter(|c| c.kind == ConstantKind::Theorem)
            .map(|c| c.name.clone())
            .collect();
        let total_theorems = theorem_names.len();

        for name in &theorem_names {
            if let Some(findings) = env.check_proof_nontrivial(name) {
                if !findings.is_empty() {
                    flagged.push((name.to_string(), format!("{findings:?}")));
                }
            }
        }
        flagged.sort();

        // Sanity: the gate is meaningless on an empty corpus. The prelude alone
        // registers well over a hundred theorems, so this must be non-trivial.
        assert!(
            total_theorems > 50,
            "masquerade gate ran on a near-empty corpus ({total_theorems} theorems); \
             full_corpus_env() failed to populate — the gate would silently pass"
        );

        // The actionable failures: theorems flagged by the detector that are NOT
        // on the audited baseline allowlist. Any such name is a genuinely NEW
        // M1-M4 masquerade (or a regression that turned a faithful carrier
        // hollow) and must be investigated, not silently absorbed.
        let unexpected: Vec<&(String, String)> = flagged
            .iter()
            .filter(|(name, _)| !allowlist.contains(name.as_str()))
            .collect();

        assert!(
            unexpected.is_empty(),
            "MASQUERADE GATE FAILED: {} theorem(s) flagged by check_proof_nontrivial \
             (M1-M4) are NOT on the audited allowlist. A new masquerade may have \
             reached the corpus. Either fix the proof or, after auditing the \
             registration site and confirming it is a GENUINE proof the heuristic \
             over-fires on, add the exact name to ALLOWLIST in \
             tests_masquerade_gate.rs with a justification. NEVER allowlist a \
             hypothesis-wrapped H->H projection or a collapsed/placeholder carrier.\n\
             Non-allowlisted flagged theorems:\n{}",
            unexpected.len(),
            unexpected
                .iter()
                .map(|(name, findings)| format!("  - {name} :: {findings}"))
                .collect::<Vec<_>>()
                .join("\n"),
        );

        // Tightness guard: if an allowlisted name is no longer flagged (e.g. its
        // proof was hardened or the detector refined), prune it so the allowlist
        // stays exact and can never mask a future regression at that name.
        let flagged_set: std::collections::BTreeSet<&str> =
            flagged.iter().map(|(n, _)| n.as_str()).collect();
        let stale: Vec<&&str> = ALLOWLIST
            .iter()
            .filter(|n| !flagged_set.contains(*n))
            .collect();
        assert!(
            stale.is_empty(),
            "STALE ALLOWLIST ENTRIES: {} name(s) on the masquerade-gate allowlist are \
             no longer flagged by check_proof_nontrivial. Remove them from ALLOWLIST \
             so the allowlist stays TIGHT (an exact match of reality):\n{}",
            stale.len(),
            stale
                .iter()
                .map(|n| format!("  - {n}"))
                .collect::<Vec<_>>()
                .join("\n"),
        );
    });
}
