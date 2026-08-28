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
//! ## What "always-on" did and did not mean before 2026-08-25
//!
//! Two things were measured on 2026-08-25 (lane MASQ) and both are now fixed
//! here; the registry row `gate::masquerade` carries the full record.
//!
//! 1. **Nothing scheduled it.** "Always-on" meant "not `#[ignore]`d". No runner
//!    in the tree ran it: not `scripts/local_gate.sh`, not the pre-push hook,
//!    not `scripts/verify_runner.py` — whose 51 rows do not include
//!    `clean-kernel::lib`. It moved only when somebody typed `cargo test -p
//!    clean-kernel --lib` or ran a whole-workspace sweep. It is now
//!    `gate::masquerade`, a suite row in `scripts/verify_runner.py`.
//! 2. **The corpus was a third of what this doc claimed.** `full_corpus_env()`
//!    was fifteen hand-written `let _ = env.init_…()` lines that reached
//!    ELEVEN of the kernel's FIFTY-TWO `init_nn_verif*` roots transitively.
//!    Measured: prelude alone **336** theorems, the fifteen-seed corpus
//!    **565**, all fifty-two roots **619**. Among the forty-one missing roots
//!    was `init_nn_verify_blockwise_crown_ext` — the one that registers
//!    `NNVerify.Block.blockwise_complexity`, the single name this repo has ever
//!    had to strike from a ratchet BY HAND as a masquerade (#3648 Branch A).
//!    See `full_corpus_env` for the fix and the fail-open it also closed.
//!
//! It is also the recorded successor of `scripts/masquerade_gate/`, a Python
//! source-scanning fragment retired the same day (it could never run: its
//! `__main__.py` imports a `cli` module that has never existed in this repo).
//! `masquerade_gate_corpus_contains_the_retired_gates_findings` keeps that
//! succession honest by name.
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

use super::types::{ConstantKind, EnvError};
use super::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
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

/// How many `init_nn_verif*` roots the kernel exposed when `NN_VERIFY_INITS`
/// was minted (2026-08-25). Bump it in the same commit that adds a root.
const EXPECTED_INIT_ROOTS: usize = 52;

/// Floor on the number of Theorem-kind constants the full corpus must carry.
///
/// MEASURED 2026-08-25 at 0b3b94e5b, printed by the gate itself: prelude alone
/// **336**, the legacy fifteen-seed corpus **565**, the full fifty-two-root
/// corpus **619**. The old floor was `total_theorems > 50` — satisfied by the
/// prelude with 286 to spare, so it could not tell a full corpus from one where
/// every single NN-verify init had failed.
const THEOREM_FLOOR: usize = 619;

/// Ceiling on `init_nn_verif*` roots that may fail to register. MEASURED at the
/// same run: **0 of 52 failed**. A root that starts failing takes its theorems
/// out of this gate's reach, so it is a COVERAGE regression and is refused here
/// rather than silently absorbed by a `let _ = …`.
const FAILED_INIT_CEILING: usize = 0;

/// The shape of every `init_nn_verif*` entry point on [`Environment`].
type InitFn = fn(&mut Environment) -> Result<(), EnvError>;

/// EVERY `init_nn_verif*` entry point the kernel exposes. Re-derive with:
///
/// ```text
/// grep -rhoE "pub fn init_nn_verif[a-z_0-9]+" crates/clean-kernel/src/env/*.rs \
///   | sed 's/pub fn //' | sort -u
/// ```
///
/// `masquerade_gate_table_covers_every_init_root` re-checks the count, so a
/// table that drifts from the source is a red test and not a quiet hole.
const NN_VERIFY_INITS: &[(&str, InitFn)] = &[
    ("init_nn_verification", Environment::init_nn_verification),
    (
        "init_nn_verification_c002",
        Environment::init_nn_verification_c002,
    ),
    (
        "init_nn_verification_c009",
        Environment::init_nn_verification_c009,
    ),
    (
        "init_nn_verify_blockwise_crown",
        Environment::init_nn_verify_blockwise_crown,
    ),
    (
        "init_nn_verify_blockwise_crown_ext",
        Environment::init_nn_verify_blockwise_crown_ext,
    ),
    (
        "init_nn_verify_cert_proofs",
        Environment::init_nn_verify_cert_proofs,
    ),
    (
        "init_nn_verify_farkas_constructive",
        Environment::init_nn_verify_farkas_constructive,
    ),
    (
        "init_nn_verify_farkas_list",
        Environment::init_nn_verify_farkas_list,
    ),
    (
        "init_nn_verify_farkas_to_interval_constructive",
        Environment::init_nn_verify_farkas_to_interval_constructive,
    ),
    (
        "init_nn_verify_float_rational",
        Environment::init_nn_verify_float_rational,
    ),
    (
        "init_nn_verify_foundation_theorems",
        Environment::init_nn_verify_foundation_theorems,
    ),
    (
        "init_nn_verify_ibp_composition",
        Environment::init_nn_verify_ibp_composition,
    ),
    (
        "init_nn_verify_ibp_linear",
        Environment::init_nn_verify_ibp_linear,
    ),
    (
        "init_nn_verify_ibp_tightness",
        Environment::init_nn_verify_ibp_tightness,
    ),
    (
        "init_nn_verify_ibp_width_zero",
        Environment::init_nn_verify_ibp_width_zero,
    ),
    (
        "init_nn_verify_interval_arith_proofs",
        Environment::init_nn_verify_interval_arith_proofs,
    ),
    (
        "init_nn_verify_interval_containment_proofs",
        Environment::init_nn_verify_interval_containment_proofs,
    ),
    (
        "init_nn_verify_interval_primitives",
        Environment::init_nn_verify_interval_primitives,
    ),
    (
        "init_nn_verify_mccormick",
        Environment::init_nn_verify_mccormick,
    ),
    (
        "init_nn_verify_network_proof",
        Environment::init_nn_verify_network_proof,
    ),
    (
        "init_nn_verify_proof_complexity",
        Environment::init_nn_verify_proof_complexity,
    ),
    ("init_nn_verify_proofs", Environment::init_nn_verify_proofs),
    (
        "init_nn_verify_rat_interval",
        Environment::init_nn_verify_rat_interval,
    ),
    (
        "init_nn_verify_rat_interval_proofs",
        Environment::init_nn_verify_rat_interval_proofs,
    ),
    (
        "init_nn_verify_rat_ordering",
        Environment::init_nn_verify_rat_ordering,
    ),
    ("init_nn_verify_relu", Environment::init_nn_verify_relu),
    (
        "init_nn_verify_softmax_c011",
        Environment::init_nn_verify_softmax_c011,
    ),
    (
        "init_nn_verify_tier_a_nat_ordering",
        Environment::init_nn_verify_tier_a_nat_ordering,
    ),
    (
        "init_nn_verify_tier_a_rat_add_left_neg_zero",
        Environment::init_nn_verify_tier_a_rat_add_left_neg_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_add_neg_self_zero",
        Environment::init_nn_verify_tier_a_rat_add_neg_self_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_le_refl_max_zero_zero",
        Environment::init_nn_verify_tier_a_rat_le_refl_max_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_le_refl_min_zero_zero",
        Environment::init_nn_verify_tier_a_rat_le_refl_min_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_le_refl_zero",
        Environment::init_nn_verify_tier_a_rat_le_refl_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_max_eq_min",
        Environment::init_nn_verify_tier_a_rat_max_eq_min,
    ),
    (
        "init_nn_verify_tier_a_rat_max_le_min_zero_zero",
        Environment::init_nn_verify_tier_a_rat_max_le_min_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_max_max_zero_zero",
        Environment::init_nn_verify_tier_a_rat_max_max_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_max_min_zero_zero",
        Environment::init_nn_verify_tier_a_rat_max_min_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_max_zero_zero_alt",
        Environment::init_nn_verify_tier_a_rat_max_zero_zero_alt,
    ),
    (
        "init_nn_verify_tier_a_rat_min_eq_max",
        Environment::init_nn_verify_tier_a_rat_min_eq_max,
    ),
    (
        "init_nn_verify_tier_a_rat_min_le_max_zero_zero",
        Environment::init_nn_verify_tier_a_rat_min_le_max_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_min_min_zero_zero",
        Environment::init_nn_verify_tier_a_rat_min_min_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_min_zero",
        Environment::init_nn_verify_tier_a_rat_min_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_min_zero_zero_alt",
        Environment::init_nn_verify_tier_a_rat_min_zero_zero_alt,
    ),
    (
        "init_nn_verify_tier_a_rat_mul_neg_zero_zero",
        Environment::init_nn_verify_tier_a_rat_mul_neg_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_mul_one_zero",
        Environment::init_nn_verify_tier_a_rat_mul_one_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_mul_zero_one",
        Environment::init_nn_verify_tier_a_rat_mul_zero_one,
    ),
    (
        "init_nn_verify_tier_a_rat_mul_zero_zero",
        Environment::init_nn_verify_tier_a_rat_mul_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_neg_zero_zero",
        Environment::init_nn_verify_tier_a_rat_neg_zero_zero,
    ),
    (
        "init_nn_verify_tier_a_rat_zero_eq_max",
        Environment::init_nn_verify_tier_a_rat_zero_eq_max,
    ),
    (
        "init_nn_verify_tier_a_rat_zero_eq_min",
        Environment::init_nn_verify_tier_a_rat_zero_eq_min,
    ),
    ("init_nn_verify_types", Environment::init_nn_verify_types),
    (
        "init_nn_verify_zonotope_proofs",
        Environment::init_nn_verify_zonotope_proofs,
    ),
];

/// Build the FULL NN-verify corpus: the Lean prelude plus every
/// `init_nn_verif*` entry point the kernel exposes.
///
/// ## Why this is a table, and why that is a soundness fix (measured 2026-08-25)
///
/// This used to be FIFTEEN hand-written `let _ = env.init_…()` lines under a
/// doc comment calling the result "the representative full corpus". The kernel
/// exposes FIFTY-TWO `init_nn_verif*` entry points, and those fifteen seeds
/// reached ELEVEN of them transitively — so FORTY-ONE roots, and every theorem
/// only they register, sat OUTSIDE the corpus this always-on gate scans.
///
/// The hole was not hypothetical. `init_nn_verify_blockwise_crown_ext` was one
/// of the forty-one, and it is the root that registers
/// `NNVerify.Block.blockwise_complexity` — the one name this repo has already
/// had to strike from a ratchet BY HAND as a masquerade (#3648 Branch A, where
/// argument-discarding carriers made it a vacuous `0 <= 0*0`) — together with
/// the whole T22 `NNVerify.LayerNorm.*` family. A gate that cannot see the only
/// masquerade the repo has ever caught is not covering the vector, however
/// always-on it is.
///
/// One precision, because the point is the ROOT and not that one name:
/// `blockwise_complexity` itself has been a `Declaration::Axiom` since the
/// #3648 demotion, so the Theorem sweep would not examine it even now. What was
/// missing is the root — and with it the fifty-four theorems the fifty-two-root
/// corpus carries over the fifteen-seed one (565 -> 619), including the two T22
/// `NNVerify.LayerNorm.*` registrations that the retired
/// `scripts/masquerade_gate/` fragment flagged on the live tree.
///
/// ## Why it returns the failures instead of swallowing them
///
/// "Best-effort" used to be spelled `let _ = …`, which is fail-OPEN: an init
/// regression could empty most of the corpus and this gate would still pass,
/// silently, because `total_theorems > 50` is satisfied by the prelude alone.
/// The failures come back so the caller can ratchet them.
fn full_corpus_env() -> (Environment, Vec<(&'static str, String)>) {
    let mut env = Environment::with_prelude();
    let mut failed: Vec<(&'static str, String)> = Vec::new();
    for (name, init) in NN_VERIFY_INITS {
        if let Err(e) = init(&mut env) {
            failed.push((*name, format!("{e:?}")));
        }
    }
    (env, failed)
}

/// The table above must name EVERY `init_nn_verif*` root, not a curated subset.
/// This is what turns "somebody added an init and forgot the gate" into a red
/// test instead of another forty-one-root hole.
#[test]
fn masquerade_gate_table_covers_every_init_root() {
    assert_eq!(
        NN_VERIFY_INITS.len(),
        EXPECTED_INIT_ROOTS,
        "NN_VERIFY_INITS has {} rows but {} `init_nn_verif*` roots were counted when \
         this table was minted. Re-derive it with the grep in the table's doc comment \
         and add the missing root(s): a root outside this table is a corpus the \
         masquerade gate never scans.",
        NN_VERIFY_INITS.len(),
        EXPECTED_INIT_ROOTS,
    );
    let mut names: Vec<&str> = NN_VERIFY_INITS.iter().map(|(n, _)| *n).collect();
    names.sort_unstable();
    let before = names.len();
    names.dedup();
    assert_eq!(
        names.len(),
        before,
        "NN_VERIFY_INITS contains duplicate roots"
    );
}

/// ALWAYS-ON gate: no theorem outside the audited allowlist may be flagged by
/// the M1-M4 masquerade detector. NOT gated by `CLEAN_STRICT_PROOF_QUALITY`,
/// NOT `#[ignore]`d — runs on every `cargo test -p clean-kernel --lib`.
#[test]
fn masquerade_gate_no_new_masquerade_reaches_corpus() {
    crate::test_utils::run_with_stack(crate::test_utils::LARGE_STACK, || {
        let (env, failed_inits) = full_corpus_env();

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

        println!(
            "[masquerade-gate] corpus: {} init roots, {} failed, {} theorems scanned, {} flagged",
            NN_VERIFY_INITS.len(),
            failed_inits.len(),
            total_theorems,
            flagged.len(),
        );

        // COVERAGE FIRST: a gate that scanned a shrunken corpus is not a gate
        // that passed. Both floors below are MEASURED, never guessed.
        //
        // Spelled as a saturating subtraction rather than `len() <=
        // FAILED_INIT_CEILING` because the ceiling is 0 today, and
        // `usize <= 0` is `clippy::absurd_extreme_comparisons` — a real
        // finding, since that comparison is `== 0` in disguise. This form says
        // the same thing, keeps the ratchet semantics if the ceiling is ever
        // raised, and reports HOW FAR over it is.
        let over_ceiling = failed_inits.len().saturating_sub(FAILED_INIT_CEILING);
        assert!(
            over_ceiling == 0,
            "MASQUERADE GATE COVERAGE REGRESSION: {} of {} `init_nn_verif*` roots failed \
             to register (ceiling {}). Every theorem those roots register is now OUTSIDE \
             this gate. Fix the init, or -- if the failure is legitimate -- raise \
             FAILED_INIT_CEILING in the same commit and say why.\n{}",
            failed_inits.len(),
            NN_VERIFY_INITS.len(),
            FAILED_INIT_CEILING,
            failed_inits
                .iter()
                .map(|(n, e)| format!("  - {n} :: {e}"))
                .collect::<Vec<_>>()
                .join("\n"),
        );
        assert!(
            total_theorems >= THEOREM_FLOOR,
            "masquerade gate ran on a SHRUNKEN corpus ({total_theorems} theorems, floor \
             {THEOREM_FLOOR}); full_corpus_env() failed to populate -- the gate would \
             silently pass on whatever survived"
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

/// The two theorems the RETIRED `scripts/masquerade_gate/` Python fragment
/// flagged on the live tree must be INSIDE the corpus this gate scans.
///
/// This is the R8 link made mechanical rather than asserted in prose. That
/// fragment (deleted 2026-08-25, see `retired` in `data/gate_registry.json`)
/// was retired onto THIS gate, and a retirement is only honest if the
/// successor can actually see what the retired artifact saw. Both names are
/// registered by `init_nn_verify_blockwise_crown_ext`, which was one of the
/// forty-one roots the old fifteen-seed corpus never called: measured
/// 2026-08-25, `NNVerify.LayerNorm.zonotope_generators_reset` was ABSENT from
/// the legacy corpus (565 theorems) and is PRESENT in this one (619).
///
/// If someone shrinks the corpus again, this test names the casualty instead
/// of leaving a green that means less than it used to.
#[test]
fn masquerade_gate_corpus_contains_the_retired_gates_findings() {
    crate::test_utils::run_with_stack(crate::test_utils::LARGE_STACK, || {
        let (env, _failed) = full_corpus_env();
        for name in [
            "NNVerify.LayerNorm.zonotope_generators_reset",
            "NNVerify.LayerNorm.zonotope_generators_offdiagonal",
            "NNVerify.Block.blockwise_crown_equiv_faithful",
        ] {
            let n = Name::from_string(name);
            let info = env.get_const(&n).unwrap_or_else(|| {
                panic!(
                    "{name} is NOT in the masquerade gate's corpus. It is one of the \
                     registrations the retired scripts/masquerade_gate/ fragment \
                     flagged, and this gate is its recorded successor -- a successor \
                     that cannot see them is the R8 trap, not a replacement."
                )
            });
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} is registered as {:?}, not a Theorem; the gate only scans \
                 Theorem-kind constants, so it would not be examined",
                info.kind,
            );
            assert!(
                env.check_proof_nontrivial(&n).is_some(),
                "the detector returned None for {name} -- it was not examined at all"
            );
        }
    });
}

/// FALSIFIABILITY ARM: the gate must be able to say NO.
///
/// A soundness gate that has never been seen to fail is the worst artifact in
/// the repo. This plants a textbook MASQUERADE into the REAL corpus -- a
/// reducible, argument-discarding carrier (`fun _ => Nat.zero`, M2) under a
/// vacuous `Eq a a` closed by `Eq.refl` (M4), the exact compound shape
/// `NNVerify.Block.blockwise_complexity` had when #3648 Branch A demoted it --
/// and asserts the detector flags it AND that the gate's own subset predicate
/// would reject it against the empty allowlist.
///
/// Both halves matter. Flagging alone would not prove the GATE fails, only
/// that the detector fired; the second assertion replays the comparison the
/// gate above actually makes.
#[test]
fn masquerade_gate_says_no_to_a_planted_hollow_carrier() {
    crate::test_utils::run_with_stack(crate::test_utils::LARGE_STACK, || {
        let (mut env, _failed) = full_corpus_env();

        let one = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let carrier = Name::from_string("MasqueradeGateProbe.hollowCarrier");
        let thm = Name::from_string("MasqueradeGateProbe.vacuousRefl");

        // M2: a REDUCIBLE Definition `Nat -> Nat` whose body ignores its
        // argument. `classify_discarding_body` calls this "constant body".
        env.add_decl(Declaration::Definition {
            name: carrier.clone(),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), nat.clone()),
            value: Expr::lam(BinderInfo::Default, nat.clone(), zero.clone()),
            is_reducible: true,
        })
        .expect("the planted carrier must type-check; it is a total Nat -> Nat");

        // M4: `Eq Nat (carrier 0) (carrier 0)` -- syntactically identical
        // sides -- closed by `@Eq.refl.{1} Nat (carrier 0)`.
        let applied = Expr::app(Expr::const_(carrier.clone(), vec![]), zero.clone());
        env.add_decl(Declaration::Theorem {
            name: thm.clone(),
            level_params: vec![],
            type_: Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [nat.clone(), applied.clone(), applied.clone()],
            ),
            value: Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
                [nat.clone(), applied.clone()],
            ),
        })
        .expect(
            "the planted masquerade must type-check -- that is the point: a \
                 masquerade is a TRUE statement whose content is vacuous, so the \
                 kernel accepts it and only the detector can object",
        );

        let findings = env
            .check_proof_nontrivial(&thm)
            .expect("the detector must examine a registered Theorem");
        assert!(
            !findings.is_empty(),
            "MASQUERADE DETECTOR IS BLIND: a reducible argument-discarding carrier \
             under a vacuous `Eq a a` closed by Eq.refl produced ZERO findings. That \
             is the #3648 Branch A shape; if it does not fire, the gate above passes \
             on an empty predicate and proves nothing."
        );

        // Replay the gate's OWN per-name predicate, byte for byte: a theorem
        // is `unexpected` iff the detector flagged it AND its name is not on
        // the allowlist. Asserting only "not allowlisted" would be vacuous
        // against an empty ALLOWLIST and would prove nothing about the gate.
        let allowlist: std::collections::BTreeSet<&str> = ALLOWLIST.iter().copied().collect();
        let planted = thm.to_string();
        let would_fail_the_gate = !findings.is_empty() && !allowlist.contains(planted.as_str());
        assert!(
            would_fail_the_gate,
            "the gate would NOT have failed on a planted masquerade: flagged={}, \
             allowlisted={}. Findings were {findings:?}",
            !findings.is_empty(),
            allowlist.contains(planted.as_str()),
        );
    });
}
