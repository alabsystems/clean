// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for C006 block-wise CROWN equivalence formalization.
//!
//! Tests the typed formalization in `nn_verify_blockwise_crown.rs` and
//! `nn_verify_blockwise_crown_ext.rs`:
//! - All definitions, opaques, and theorems are correctly registered
//! - The C006 main theorem `NNVerify.C006.blockwise_equals_monolithic`
//!   is a Phase-2 hypothesis-wrapped `Declaration::Theorem`; `blockwise_base`
//!   is a Phase-3 zero-input hypothesis-wrapped theorem;
//!   `NNVerify.C006.blockwise_step` and
//!   `NNVerify.C006.blockwise_nat_induction` are local-evidence theorems;
//!   `NNVerify.Block.blockwise_complexity` (T61, #3648 Branch B) and the T22
//!   pair (`zonotope_generators_reset` + `zonotope_generators_offdiagonal`,
//!   #3590 Branch B) are faithful constructive `Declaration::Theorem`s over
//!   k-consuming carriers. T20/T21/T60 remain honest `Declaration::Axiom`s
//!   after Branch A MASQUERADE demotions (#3489-#3494, #3507, #3509); their
//!   Branch B faithful carriers remain future work.
//! - Transitive axiom-dependency audit shows ZERO C006-specific domain axioms.
//! - Idempotency of initialization.
//!
//! Mirrors the C008 integration-test suite in `nn_verification_c008_tightness.rs`
//! (see #3374) so each published conjecture has its own audit-level test
//! verifying zero domain axioms at the publication-quality gate.
//!
//! Part of #3375, #3381.

use clean_kernel::{ConstantKind, Environment, Expr, ExprKind, Name, TypeChecker};

/// Create an environment with C006 block-wise CROWN + extended declarations
/// initialized. The `ext` init pulls in the base init as a dependency.
fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext should succeed");
    env
}

/// Assert that a constant is registered.
fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "Expected constant '{name}' to be registered"
    );
}

/// Assert that a constant has a specific kind.
fn assert_is_kind(env: &Environment, name: &str, expected: ConstantKind) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("'{name}' should be registered"));
    assert_eq!(
        info.kind, expected,
        "'{name}' should be {expected:?}, got {:?}",
        info.kind
    );
}

// =============================================================================
// Initialization tests
// =============================================================================

#[test]
fn test_c006_init_succeeds() {
    make_env();
}

#[test]
fn test_c006_init_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("first init should succeed");
    let count_after_first = env.num_constants();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("second init should succeed (idempotent)");
    assert_eq!(
        env.num_constants(),
        count_after_first,
        "Idempotent init should not add more constants"
    );
}

// =============================================================================
// Theorem registration tests (main + extension theorems)
// =============================================================================

#[test]
fn test_c006_blockwise_base_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.C006.blockwise_base");
}

#[test]
fn test_c006_blockwise_step_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.C006.blockwise_step");
}

#[test]
fn test_c006_nat_induction_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.C006.blockwise_nat_induction");
}

#[test]
fn test_c006_main_theorem_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.C006.blockwise_equals_monolithic");
}

#[test]
fn test_c006_t60_blockwise_crown_sound_registered() {
    // 2026-06-17: T60 retired — the false `blockwise_crown_equiv` axiom is gone;
    // its replacement is the faithful soundness theorem `blockwise_crown_sound`.
    let env = make_env();
    assert_registered(&env, "NNVerify.Block.blockwise_crown_sound");
}

#[test]
fn test_c006_t61_blockwise_complexity_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.Block.blockwise_complexity");
}

#[test]
fn test_c006_t22_generators_reset_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.LayerNorm.zonotope_generators_reset");
}

// =============================================================================
// Kind verification (theorems are Theorems, not Axioms; helpers are Opaques)
// =============================================================================

#[test]
fn test_c006_blockwise_base_is_hypothesis_wrapped_theorem() {
    // 2026-04-26 Phase 3: `blockwise_base` is re-promoted only after adding
    // the missing zero-input hypothesis `B = zero_ib`. At k=0 the Phase-1
    // indexed carriers reduce to the input `B`, so the proof reuses that
    // hypothesis for both conjuncts via `And.intro`.
    let env = make_env();
    assert_is_kind(&env, "NNVerify.C006.blockwise_base", ConstantKind::Theorem);
    let info = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_base"))
        .expect("base theorem should be registered");
    assert!(
        info.value.is_some(),
        "Phase-3 base theorem should carry a proof value",
    );
}

// 2026-04-19 MASQUERADE demotion (#3489-#3494): blockwise_step and
// Block.blockwise_crown_equiv (T60) were demoted from Declaration::Theorem
// to Declaration::Axiom. The core C006 names are now hypothesis-wrapped
// theorems that expose the missing local evidence explicitly.

#[test]
fn test_c006_blockwise_step_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_step"))
        .expect("blockwise_step should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "blockwise_step should be a hypothesis-wrapped theorem"
    );
    assert!(
        info.value.is_some(),
        "blockwise_step theorem should carry a proof value"
    );
}

#[test]
fn test_c006_main_theorem_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("main theorem should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Phase-2 headline should be a hypothesis-wrapped theorem"
    );
    assert!(
        info.value.is_some(),
        "Phase-2 headline theorem should carry a proof value"
    );
}

#[test]
fn test_c006_t60_is_faithful_soundness_theorem() {
    // 2026-06-17: the false unconditional `=` axiom blockwise_crown_equiv was
    // RETIRED and restated as the hypothesis-carrying soundness theorem
    // blockwise_crown_sound (monolithic ⊆ compose, proved by Nat.rec).
    let env = make_env();
    assert_is_kind(
        &env,
        "NNVerify.Block.blockwise_crown_sound",
        ConstantKind::Theorem,
    );
}

#[test]
fn test_c006_t61_is_faithful_theorem_branch_b() {
    // #3648 Branch B (2026-06-11): T61 blockwise_complexity is a faithful
    // constructive Declaration::Theorem (`Σ bd² ≤ (Σ bd)²` by Nat.rec
    // induction over the FAITHFUL reducible crown_cost / total_dim carriers
    // that consume k, bd, and the IH). The earlier Branch A Axiom (and the
    // even-earlier `Nat.le_refl Nat.zero` masquerade) are retired.
    //
    // PRE-EXISTING DRIFT ALIGNMENT: the lib test
    // `test_t61_is_faithful_theorem_with_proof_value` already pins this state;
    // this integration test had not been updated alongside #3648 Branch B and
    // was already red on main. Aligned here (test-only; no T61 kernel change).
    let env = make_env();
    assert_is_kind(
        &env,
        "NNVerify.Block.blockwise_complexity",
        ConstantKind::Theorem,
    );
    let ci = env
        .get_const(&Name::from_string("NNVerify.Block.blockwise_complexity"))
        .expect("T61 should be registered");
    assert!(
        ci.value.is_some(),
        "#3648 Branch B: T61 Theorem must carry its Nat.rec induction proof value",
    );
}

#[test]
fn test_c006_t22_is_faithful_theorem_branch_b() {
    // #3590 Branch B (FAITHFUL MATRIX RESTATEMENT): the body-less Branch A
    // axiom is RETIRED. `generators_after_ln` is now the reducible diagonal
    // radius matrix `(n k) z -> NNMat n n` (consuming all k input columns via
    // `Fin.sum k Rat.abs`), and T22 `zonotope_generators_reset` is a
    // kernel-checked Declaration::Theorem stating the diagonal-entry equation
    // `generators_after_ln n k z i i = Σ_j |G_ij|`. See
    // tests_nn_verify_blockwise_crown_ext_t22_demasquerade_3590.rs.
    let env = make_env();
    assert_is_kind(
        &env,
        "NNVerify.LayerNorm.zonotope_generators_reset",
        ConstantKind::Theorem,
    );
    assert_is_kind(
        &env,
        "NNVerify.LayerNorm.zonotope_generators_offdiagonal",
        ConstantKind::Theorem,
    );
    assert_is_kind(
        &env,
        "NNVerify.LayerNorm.generators_after_ln",
        ConstantKind::Definition,
    );
}

/// T20/T21 were upgraded from Axiom -> Opaque (#3375) -> Theorem (#3435) ->
/// demoted back to Axiom in the 2026-04-19 MASQUERADE audit (#3509).
/// The #3435 `Eq.refl` / `Rat.le_refl` proofs closed only because the
/// reducible carrier `zonotope_output` collapsed to `to_ibp n k z` on both
/// sides, discarding γ, β, ε, and z. Per
/// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Branch A, T20/T21 are
/// now honest `Declaration::Axiom`s pending the faithful Zonotope carrier
/// refactor (Branch B Phase 3, deferred).
#[test]
fn test_c006_t20_is_faithful_theorem_after_2026_06_17_restatement() {
    // 2026-06-17: T20 zonotope_reset RETIRED — the false `= to_ibp z` masquerade
    // was restated as a faithful Theorem over the γ/β-consuming layernorm_zono
    // carrier (bounds = (γc+β) ∓ Σ|γG|). It is now a Theorem, not an Axiom.
    let env = make_env();
    assert_is_kind(
        &env,
        "NNVerify.LayerNorm.zonotope_reset",
        ConstantKind::Theorem,
    );
}

/// 2026-06-17: T21 `zonotope_width_preserved` RETIRED. The UNCONDITIONAL
/// axiom was FALSE over the faithful LayerNorm carrier — `width(out)_i =
/// |γ_i|·width(in)_i`, so any `|γ_i| > 1` makes the output width EXCEED the
/// input width. It was restated as a kernel-checked GAIN-BOUND Theorem
/// conditional on `∀ i, |γ_i| ≤ 1` (admitted TCB 5 → 4), exactly as T20 was
/// restated directly above.
#[test]
fn test_c006_t21_is_faithful_theorem_after_gain_bound_restatement() {
    let env = make_env();
    assert_is_kind(
        &env,
        "NNVerify.LayerNorm.zonotope_width_preserved",
        ConstantKind::Theorem,
    );
}

// =============================================================================
// Proof-term existence tests
// =============================================================================

#[test]
fn test_c006_main_theorem_has_proof_value_after_phase2_promotion() {
    // 2026-04-26 Phase 2: the headline name is promoted back to Theorem
    // by strengthening the statement with the missing pointwise
    // `crown_block = mono_step` hypothesis. The proof is Nat.rec over k
    // and does not delegate to the demoted C006 axioms.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.C006.blockwise_equals_monolithic",
        ))
        .expect("main theorem should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Phase-2 main theorem must be Declaration::Theorem"
    );
    assert!(
        info.value.is_some(),
        "Phase-2 main theorem must carry a proof value"
    );
}

#[test]
fn test_c006_nat_induction_has_proof_term_after_hypothesis_wrapping() {
    // 2026-04-27: the old hypothesis-free Nat.rec proof is not restored.
    // The theorem now takes explicit local induction evidence and returns
    // the requested instance.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("nat induction theorem should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "nat induction must be a hypothesis-wrapped Theorem"
    );
    assert!(
        info.value.is_some(),
        "hypothesis-wrapped nat induction theorem must carry a proof value"
    );
}

#[test]
fn test_c006_main_theorem_type_is_pi() {
    let env = make_env();
    let tc = TypeChecker::new(&env);
    let e = Expr::const_(
        Name::from_string("NNVerify.C006.blockwise_equals_monolithic"),
        vec![],
    );
    let ty = tc.infer_type(&e).expect("main theorem should type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Pi { .. }),
        "main theorem type should be Pi, got {:?}",
        ty.kind()
    );
}

// =============================================================================
// Axiom-absence checks (kind-level)
// =============================================================================

/// After the 2026-04-19 MASQUERADE audit (#3489-#3495, #3509) the former
/// #3375 "zero domain axioms" milestone was repudiated. The following
/// C006 names were demoted back to `Declaration::Axiom` because their
/// proof terms closed only over reducible placeholder carriers:
///
/// - Core C006 cluster (#3489-#3493): `blockwise_step` and
///   `blockwise_nat_induction` were demoted, then retired as local-evidence
///   theorems.
/// - Phase-2/3 core promotions (2026-04-26): `blockwise_equals_monolithic`
///   and `blockwise_base` are now hypothesis-wrapped Theorems and are no
///   longer in this set.
/// - T60 (#3494): `Block.blockwise_crown_equiv`.
/// - T22 (#3495): `LayerNorm.zonotope_generators_reset`.
/// - T20/T21 (#3509): `LayerNorm.zonotope_reset`,
///   `LayerNorm.zonotope_width_preserved`.
///
/// This test pins the honest set of demoted C006 axioms so any future
/// regression (e.g., silently re-promoting one to a masquerading
/// Theorem) is caught. A fresh Axiom outside this list would also
/// surface here. Once a faithful carrier lands (Branch B of
/// `designs/2026-04-19-demasquerade-cxxx-pattern.md`) the corresponding
/// entry should be removed from this set in the same commit that
/// introduces the real proof.
#[test]
fn test_c006_masquerade_demoted_axioms() {
    let env = make_env();
    // All C006-universe names that have ever been Axiom / Theorem.
    let c006_names = [
        "NNVerify.Block.ibp_transfer",
        "NNVerify.Block.compose",
        "NNVerify.Block.monolithic_crown",
        "NNVerify.C006.follows_from_c004",
        "NNVerify.LayerNorm.generators_after_ln",
        "NNVerify.LayerNorm.layernorm_zonotope_output",
        "NNVerify.Block.crown_cost",
        "NNVerify.Block.total_dim",
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
        "NNVerify.Block.blockwise_crown_sound",
        "NNVerify.Block.blockwise_complexity",
        "NNVerify.LayerNorm.zonotope_reset",
        "NNVerify.LayerNorm.zonotope_width_preserved",
        "NNVerify.LayerNorm.zonotope_generators_reset",
    ];
    // The honest MASQUERADE-demoted axiom set pinned by the audits.
    // After #3507 (blockwise_base/blockwise_nat_induction -> Axiom), #3590
    // (T22 zonotope_generators_reset → Axiom), and #3648 (T61
    // blockwise_complexity → Axiom per #3646 triage Site 4), most of the
    // C006 theorem cluster is now honest axioms. Phase 2 (2026-04-26)
    // removes the headline theorem from this set by adding a pointwise
    // mono-step hypothesis and a real Nat.rec proof. Phase 3 removes
    // blockwise_base by adding the zero-input hypothesis. The 2026-04-27
    // follow-up removes blockwise_nat_induction by requiring explicit local
    // induction evidence. This slot removes blockwise_step by adding the
    // pointwise mono-step hypothesis to the step theorem itself.
    // #3590 Branch B retired the T22 zonotope_generators_reset axiom: it is
    // now a faithful Declaration::Theorem (diagonal-entry equation over the
    // k-consuming diagonal radius-box carrier), so it is no longer in this
    // demoted-axiom set (admitted 8 -> 7).
    //
    // PRE-EXISTING DRIFT ALIGNMENT (T61): `blockwise_complexity` was promoted
    // back to a faithful constructive Theorem by #3648 Branch B (see the lib
    // test `test_t61_is_faithful_theorem_with_proof_value`), but this
    // integration set still listed it — a stale assertion that was already
    // red on main. Dropped here so this set reflects the live kind-partition;
    // no T61 kernel code is touched.
    // 2026-06-17: T60 (blockwise_crown_equiv) RETIRED → blockwise_crown_sound
    // Theorem; T20 (zonotope_reset) RETIRED → faithful Theorem pair. Only T21
    // (zonotope_width_preserved) remains an admitted Axiom (Tranche B γ-bound,
    // parked on the user). admitted 7 → 5 across these two retirements.
    // DRIFT ALIGNMENT (T21), same class as the T61 alignment noted above.
    // 2026-06-17 `b4cb27e8b` retired T21 to a faithful gain-bound Theorem
    // (admitted 5 -> 4), and `ea7dc64ae` aligned this file for the T20+T60
    // retirements the SAME DAY but missed the T21 case — leaving these
    // assertions red on main. The set is now empty: every C006 name above is a
    // Theorem. No kernel code is touched; this reflects the live
    // kind-partition, and the assertion still fails loudly if any name is ever
    // demoted back to an Axiom.
    let expected_axioms: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();

    let actual_axioms: std::collections::BTreeSet<&str> = c006_names
        .iter()
        .copied()
        .filter(|name| {
            env.get_const(&Name::from_string(name))
                .map(|info| info.kind == ConstantKind::Axiom)
                .unwrap_or(false)
        })
        .collect();

    assert_eq!(
        actual_axioms, expected_axioms,
        "#3509: C006 MASQUERADE-demoted Axiom set drifted. \
         The expected set is pinned by the 2026-04-19 audit \
         (reports/audit/2026-04-19-clean-native-shard-audit.md). \
         Promoting one of these back to Theorem requires a faithful \
         carrier per designs/2026-04-19-demasquerade-cxxx-pattern.md \
         Branch B, not a masquerading Eq.refl / Rat.le_refl body."
    );
}

// =============================================================================
// Transitive-dependency axiom audit (#3375)
//
// Tests in this section use the kernel's axiom_audit API (axiom_deps,
// proof_quality, soundness_report) to walk the TRANSITIVE constant-reference
// graph of C006 theorems and verify that ZERO C006-specific domain axioms
// appear in the dep tree. Strictly stronger than the kind-only check above.
//
// Pattern mirrors C008's nn_verification_c008_tightness.rs (#3374).
// =============================================================================

/// C006-specific names that, if they appear as `Declaration::Axiom` in any
/// theorem's transitive dep tree, indicate a regression in the #3375 work.
///
/// Remaining honest `Declaration::Axiom` names from the 2026-04-19/20
/// MASQUERADE demotions are intentionally omitted here — flagging them in
/// transitive-dep tests would falsely re-raise a closed Branch-A finding.
/// Retired names such as the Phase-3 `blockwise_base` theorem do belong here:
///
/// - `NNVerify.C006.blockwise_step` (#3491, retired as local-evidence theorem)
/// - `NNVerify.C006.blockwise_nat_induction` (#3492, finalized #3507)
/// - `NNVerify.Block.blockwise_crown_equiv` (#3494, T60)
/// - `NNVerify.Block.blockwise_complexity` (#3648, T61)
/// - `NNVerify.LayerNorm.zonotope_reset` (#3509, T20)
/// - `NNVerify.LayerNorm.zonotope_width_preserved` (#3509, T21)
/// - `NNVerify.LayerNorm.zonotope_generators_reset` (#3590, T22)
///
/// Dedicated gates pin their honest-axiom state
/// (`test_c006_*_is_axiom_honest_demotion` /
/// `test_c006_t20_is_axiom_no_proof_value` / etc.).
const C006_ELIMINATED_AXIOMS: &[&str] = &[
    // Category A: definition-function axioms (now Opaques or reducible Defs)
    "NNVerify.Block.ibp_transfer",
    "NNVerify.Block.compose",
    "NNVerify.Block.monolithic_crown",
    "NNVerify.Block.crown_cost",
    "NNVerify.Block.total_dim",
    "NNVerify.LayerNorm.generators_after_ln",
    "NNVerify.LayerNorm.layernorm_zonotope_output",
    // Category B: C004 -> C006 implication (now Opaque returning True)
    "NNVerify.C006.follows_from_c004",
    // Category C: hypothesis-wrapped C006 theorem names retired from the
    // domain-axiom set.
    "NNVerify.C006.blockwise_base",
    "NNVerify.C006.blockwise_step",
    "NNVerify.C006.blockwise_nat_induction",
    "NNVerify.C006.blockwise_equals_monolithic",
    // Category C (#3648): T61 blockwise_complexity demoted to honest Axiom;
    // removed from this list because it is now an expected domain axiom
    // (see `expected_axioms` in `test_c006_masquerade_demoted_axioms`).
];

/// The C006 main theorem (`blockwise_equals_monolithic`) must have zero
/// C006-specific domain axioms in its transitive dep tree.
///
/// Infrastructure axioms (propext, Quot.sound, Classical.choice, sorryAx,
/// Rat.le_refl, etc.) are permitted because they encode standard ordered-field
/// or Prop-level properties and are not C006-specific claims.
#[test]
fn test_c006_main_theorem_no_c006_specific_axioms() {
    let env = make_env();
    let name = Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for blockwise_equals_monolithic");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for eliminated in C006_ELIMINATED_AXIOMS {
        assert!(
            !dep_strs.contains(&eliminated.to_string()),
            "#3375: C006 eliminated axiom {} still appears in transitive deps of \
             blockwise_equals_monolithic. All deps: {:?}",
            eliminated,
            dep_strs,
        );
    }
    for forbidden in [
        "NNVerify.C006.blockwise_base",
        "NNVerify.C006.blockwise_step",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.C006.blockwise_equals_monolithic",
    ] {
        assert!(
            !dep_strs.contains(&forbidden.to_string()),
            "Phase-2 main theorem must not depend on C006 axiom {forbidden}; deps: {dep_strs:?}",
        );
    }
}

/// T60 (`blockwise_crown_equiv`) must also be free of C006-specific axioms.
#[test]
fn test_c006_t60_no_c006_specific_axioms() {
    let env = make_env();
    let name = Name::from_string("NNVerify.Block.blockwise_crown_sound");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for blockwise_crown_sound");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for eliminated in C006_ELIMINATED_AXIOMS {
        assert!(
            !dep_strs.contains(&eliminated.to_string()),
            "#3375: C006 eliminated axiom {} still appears in transitive deps of \
             blockwise_crown_sound. All deps: {:?}",
            eliminated,
            dep_strs,
        );
    }
}

/// T61 (`blockwise_complexity`) must also be free of C006-specific axioms.
#[test]
fn test_c006_t61_no_c006_specific_axioms() {
    let env = make_env();
    let name = Name::from_string("NNVerify.Block.blockwise_complexity");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for blockwise_complexity");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for eliminated in C006_ELIMINATED_AXIOMS {
        assert!(
            !dep_strs.contains(&eliminated.to_string()),
            "#3375: C006 eliminated axiom {} still appears in transitive deps of \
             blockwise_complexity. All deps: {:?}",
            eliminated,
            dep_strs,
        );
    }
}

/// T22 (`generators_reset`) is now a faithful Branch B Theorem (the diagonal
/// radius-box equation, proved by a `Decidable.rec` split over the k-consuming
/// carrier). Its transitive deps must contain no C006-specific axioms — the
/// reducible `generators_after_ln` matrix carrier is a Definition, not an
/// axiom, so it never appears in the `axiom_deps` closure.
#[test]
fn test_c006_t22_no_c006_specific_axioms() {
    let env = make_env();
    let name = Name::from_string("NNVerify.LayerNorm.zonotope_generators_reset");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for zonotope_generators_reset");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for eliminated in C006_ELIMINATED_AXIOMS {
        assert!(
            !dep_strs.contains(&eliminated.to_string()),
            "#3375: C006 eliminated axiom {} still appears in transitive deps of \
             zonotope_generators_reset. All deps: {:?}",
            eliminated,
            dep_strs,
        );
    }
}

/// Soundness-report-based check: no constant whose name matches a C006
/// "eliminated" axiom should appear in the environment-wide `domain_axioms`
/// list. Stronger than the per-theorem checks because it inspects every
/// registered declaration.
#[test]
fn test_c006_no_c006_domain_axioms_in_soundness_report() {
    let env = make_env();
    let report = env.soundness_report();
    let c006_axiom_names: Vec<String> = report
        .domain_axioms
        .iter()
        .map(|n| n.to_string())
        .filter(|s| C006_ELIMINATED_AXIOMS.contains(&s.as_str()))
        .collect();
    assert!(
        c006_axiom_names.is_empty(),
        "#3375: soundness_report must not list any C006 eliminated axiom as a \
         domain axiom, found: {:?}",
        c006_axiom_names,
    );
}

/// Phase 2 (2026-04-26) promotes the C006 headline to a hypothesis-wrapped
/// theorem with a `Nat.rec` + pointwise-hypothesis proof. Its only
/// non-foundational dependency was the admitted `Rat.le_refl` ordered-field
/// axiom.
///
/// #3470 Lane #2/#3 (2026-06): `Rat.le_refl` — the sole remaining admitted-axiom
/// dependency — has been GENUINELY ELIMINATED to a kernel-checked constructive
/// `Declaration::Theorem` (`λ a => @Int.le_refl (cross a a)`). With it removed,
/// `blockwise_equals_monolithic` now has an EMPTY domain-axiom closure and
/// honestly classifies `ProofQuality::Constructive` — a genuine increase in
/// verified depth (the kernel accepts every step; no `sorry`, no domain axiom).
#[test]
fn test_c006_main_theorem_proof_quality() {
    use clean_kernel::ProofQuality;
    let env = make_env();
    let name = Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
    let quality = env
        .proof_quality(&name)
        .expect("proof_quality should work for blockwise_equals_monolithic");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "blockwise_equals_monolithic should now classify as Constructive after \
         the Rat.le_refl elimination (#3470 Lane #2/#3); got {quality:?}",
    );
    // Belt-and-suspenders: the transitive domain-axiom closure is empty.
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for blockwise_equals_monolithic");
    assert!(
        deps.is_empty(),
        "blockwise_equals_monolithic domain-axiom closure must be empty; got {:?}",
        deps.iter().map(|d| d.to_string()).collect::<Vec<_>>(),
    );
}

/// Diagnostic: emit the full transitive domain-axiom dep set of the C006
/// infrastructure axioms survive. Runs quietly; use `-- --nocapture` to view.
///
/// This test PASSES regardless of content; it is a reporting aid, not a
/// correctness gate. The correctness gates are the `no_c006_specific_axioms`
/// tests above.
#[test]
fn test_c006_report_domain_axiom_deps() {
    let env = make_env();
    for target in &[
        "NNVerify.C006.blockwise_equals_monolithic",
        "NNVerify.C006.blockwise_nat_induction",
        "NNVerify.Block.blockwise_crown_sound",
        "NNVerify.Block.blockwise_complexity",
        "NNVerify.LayerNorm.zonotope_generators_reset",
    ] {
        let name = Name::from_string(target);
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("axiom_deps should work for {}", target));
        let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        dep_strs.sort();
        eprintln!(
            "[C006 audit] {} -> {} domain axioms: {:?}",
            target,
            dep_strs.len(),
            dep_strs
        );
    }
}

// =============================================================================
// T20/T21 honest-Axiom gates (#3509, 2026-04-19 MASQUERADE demotion)
//
// These tests enforce the Branch A remediation contract from
// `designs/2026-04-19-demasquerade-cxxx-pattern.md`: T20 `zonotope_reset`
// and T21 `zonotope_width_preserved` are honest `Declaration::Axiom`s with
// NO proof term, NO `Eq.refl` / `Rat.le_refl` masquerading body, and NO
// sorry-inhabitation. Both former proofs were rejected because they closed
// by reflexivity over the reducible argument-discarding carrier
// `NNVerify.LayerNorm.zonotope_output` → `NNVerify.Zonotope.to_ibp`.
//
// Failure modes these tests catch:
// - Regressing T20/T21 back to a masquerading Theorem with a vacuous
//   `Eq.refl` / `Rat.le_refl` proof (`test_c006_t20_is_axiom_no_proof_value`,
//   `test_c006_t21_is_axiom_no_proof_value`).
// - Shipping `sorry` / `sorryAx` in the axiom type itself
//   (`test_c006_t20_t21_no_sorry`).
// =============================================================================

/// C006 T20 (`NNVerify.LayerNorm.zonotope_reset`) must be a
/// `Declaration::Axiom` with no proof value after the 2026-04-19 MASQUERADE
/// demotion (#3509). This gate prevents silent regression to a
/// `Declaration::Theorem` with an `Eq.refl` body that only type-checks
/// because `zonotope_output` reduces to `to_ibp n k z` via its reducible
/// placeholder Definition.
#[test]
fn test_c006_t20_is_faithful_theorem_with_proof_value() {
    // 2026-06-17: T20 is a faithful Declaration::Theorem carrying a real proof
    // value (the γ/β-consuming layernorm_zono restatement), NOT a re-attached
    // Eq.refl over the old argument-discarding placeholder.
    let env = make_env();
    let name = Name::from_string("NNVerify.LayerNorm.zonotope_reset");

    let info = env
        .get_const(&name)
        .expect("T20 `zonotope_reset` should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "2026-06-17: T20 is a faithful Theorem after restatement; got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "T20 faithful theorem must carry its kernel-checked proof value",
    );
}

/// C006 T21 (`NNVerify.LayerNorm.zonotope_width_preserved`) must be a
/// `Declaration::Theorem` CARRYING its kernel-checked proof value.
///
/// History: #3509 demoted it to a body-less Axiom because the original
/// `Rat.le_refl` proof was a masquerade — it closed only because both sides of
/// `LE.le` collapsed to `l1_norm n (width n (to_ibp n k z))`. 2026-06-17
/// retired that Axiom in turn, replacing it with the GAIN-BOUND statement
/// (conditional on `∀ i, |γ_i| ≤ 1`), which the kernel checks at `add_decl`.
///
/// This is STRICTLY STRONGER than the assertion it replaces: a body-less Axiom
/// is now a rejection, and so is a Theorem without a proof value.
#[test]
fn test_c006_t21_is_theorem_with_proof_value() {
    let env = make_env();
    let name = Name::from_string("NNVerify.LayerNorm.zonotope_width_preserved");

    let info = env
        .get_const(&name)
        .expect("T21 `zonotope_width_preserved` should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "2026-06-17: T21 is a faithful gain-bound Theorem after restatement; got {:?}",
        info.kind,
    );

    assert!(
        info.value.is_some(),
        "T21 faithful theorem must carry its kernel-checked proof value — a \
         body-less T21 would mean the gain-bound restatement had regressed \
         back to an admitted axiom",
    );
}

/// T20 and T21 must be sorry-free in both their TYPE and their proof VALUE.
///
/// Since the 2026-06-17 retirements both carry kernel-checked proofs, so this
/// covers the proof terms as well as the statements — a `sorry` reachable from
/// either would make the retirement hollow.
#[test]
fn test_c006_t20_t21_no_sorry() {
    fn contains_sorry(expr: &Expr) -> bool {
        let mut stack: Vec<&Expr> = vec![expr];
        while let Some(e) = stack.pop() {
            match e.kind() {
                ExprKind::Const(name, _) => {
                    let s = name.to_string();
                    if s == "sorry" || s == "sorryAx" || s.ends_with(".sorry") {
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
                ExprKind::MData(_, inner)
                | ExprKind::Proj(_, _, inner)
                | ExprKind::Squash(inner) => {
                    stack.push(inner);
                }
                _ => {}
            }
        }
        false
    }

    let env = make_env();
    // Both T20 and T21 must be sorry-free in their TYPE. Since 2026-06-17 T20 is
    // a faithful Theorem (its proof VALUE must also be sorry-free); T21 remains
    // an honest Axiom with no value.
    for target in &[
        "NNVerify.LayerNorm.zonotope_reset",
        "NNVerify.LayerNorm.zonotope_width_preserved",
    ] {
        let name = Name::from_string(target);
        let info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{} should be registered", target));
        assert!(
            !contains_sorry(&info.type_),
            "#3509: {} type must not reference `sorry` / `sorryAx`",
            target,
        );
        if let Some(value) = &info.value {
            assert!(
                !contains_sorry(value),
                "{} proof value must not reference `sorry` / `sorryAx`",
                target,
            );
        }
    }
    // Since the 2026-06-17 retirements BOTH are faithful Theorems carrying
    // kernel-checked proof values — pin that so neither silently flips back to
    // an admitted axiom. The sorry-free check above already covers their proof
    // values now that both have one.
    for target in &[
        "NNVerify.LayerNorm.zonotope_reset",
        "NNVerify.LayerNorm.zonotope_width_preserved",
    ] {
        let info = env
            .get_const(&Name::from_string(target))
            .unwrap_or_else(|| panic!("{target} registered"));
        assert!(
            info.value.is_some() && info.kind == ConstantKind::Theorem,
            "{target} must be a faithful Theorem with a proof value; got {:?}",
            info.kind,
        );
    }
}
