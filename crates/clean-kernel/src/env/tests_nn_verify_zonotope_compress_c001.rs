// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C001: Zonotope Compression Soundness.
//!
//! Verifies that the novel kernel theorems C001a (soundness) and C001b
//! (tightness) are correctly registered, type-check through the kernel
//! TypeChecker, and have the expected Declaration kinds.
//!
//! Part of #3150.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_c001()
        .expect("init_nn_verify_c001 should succeed");
    env
}

fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered"
    );
}

fn assert_type_checks_as_pi(env: &Environment, name: &str) {
    let e = Expr::const_(Name::from_string(name), vec![]);
    let tc = TypeChecker::with_mode(env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{name} should type-check, got: {err:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "{name} type should be Pi, got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// Registration tests
// ---------------------------------------------------------------

#[test]
fn test_c001a_compress_soundness_registered() {
    assert_registered(&make_env(), "NNVerify.C001.compress_soundness");
}

#[test]
fn test_c001b_compress_tightness_registered() {
    assert_registered(&make_env(), "NNVerify.C001.compress_tightness");
}

#[test]
fn test_helper_abs_weighted_sum_le_registered() {
    assert_registered(&make_env(), "NNVerify.C001.abs_weighted_sum_le");
}

#[test]
fn test_helper_tail_norm_sum_registered() {
    assert_registered(&make_env(), "NNVerify.C001.tail_norm_sum");
}

#[test]
fn test_helper_tightness_helper_registered() {
    assert_registered(&make_env(), "NNVerify.C001.compress_tightness_helper");
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_c001a_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C001.compress_soundness");
}

#[test]
fn test_c001b_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C001.compress_tightness");
}

#[test]
fn test_abs_weighted_sum_le_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C001.abs_weighted_sum_le");
}

#[test]
fn test_tail_norm_sum_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C001.tail_norm_sum");
}

#[test]
fn test_tightness_helper_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C001.compress_tightness_helper");
}

// ---------------------------------------------------------------
// Declaration kind tests — C001a and C001b are Theorems, not Axioms
// ---------------------------------------------------------------

#[test]
fn test_c001a_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.compress_soundness"))
        .expect("C001a should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "C001a should be Theorem (machine-checked proof), got {:?}",
        info.kind
    );
}

#[test]
fn test_c001b_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.compress_tightness"))
        .expect("C001b should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "C001b should be Theorem (machine-checked proof), got {:?}",
        info.kind
    );
}

#[test]
fn test_abs_weighted_sum_le_is_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.abs_weighted_sum_le"))
        .expect("abs_weighted_sum_le should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "abs_weighted_sum_le should be Definition (predicate body), got {:?}",
        info.kind
    );
}

// #3586 demoted the prior masqueraded helper to an honest Axiom. The current
// hypothesis-wrapper pass retires that C001 axiom by strengthening the helper
// and headline tightness theorem with an explicit local tightness premise.

// ---------------------------------------------------------------
// Dependency tests — base infrastructure is present
// ---------------------------------------------------------------

#[test]
fn test_base_zonotope_deps_present() {
    let env = make_env();
    // T10-T12 from zonotope_compress
    assert_registered(&env, "NNVerify.Zonotope.center_contained");
    assert_registered(&env, "NNVerify.Zonotope.compress_sound");
    assert_registered(&env, "NNVerify.Zonotope.to_ibp_sound");
    // l1_norm and width are now proper Definitions from foundation_types
    assert_registered(&env, "NNVerify.NNVec.l1_norm");
    assert_registered(&env, "NNVerify.IntervalBounds.width");
    // Rat.two is now a Definition (Rat.add Rat.one Rat.one)
    assert_registered(&env, "Rat.two");
    // Rat.mul is a Definition from init_rat_arith (no longer re-registered)
    assert_registered(&env, "Rat.mul");
}

// ---------------------------------------------------------------
// Axiom-to-Definition upgrade tests — verify reduced axiom budget
// ---------------------------------------------------------------

#[test]
fn test_l1_norm_is_definition_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.NNVec.l1_norm"))
        .expect("l1_norm should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "l1_norm should be Definition (from foundation_types), got {:?}",
        info.kind
    );
}

#[test]
fn test_width_is_definition_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.IntervalBounds.width"))
        .expect("width should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "width should be Definition (from foundation_types), got {:?}",
        info.kind
    );
}

#[test]
fn test_rat_two_is_definition_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.two"))
        .expect("Rat.two should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "Rat.two should be Definition (Rat.add Rat.one Rat.one), got {:?}",
        info.kind
    );
}

#[test]
fn test_rat_mul_is_definition_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.mul"))
        .expect("Rat.mul should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "Rat.mul should be Definition (from init_rat_arith), got {:?}",
        info.kind
    );
}

// ---------------------------------------------------------------
// Naming convention test
// ---------------------------------------------------------------

#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.C001.compress_soundness",
        "NNVerify.C001.compress_tightness",
        "NNVerify.C001.abs_weighted_sum_le",
        "NNVerify.C001.tail_norm_sum",
        "NNVerify.C001.compress_tightness_helper",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
        assert!(
            name.starts_with("NNVerify.C001."),
            "{name} must use NNVerify.C001. prefix"
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_c001().expect("first init");
    env.init_nn_verify_c001().expect("second init (idempotent)");
}

// ---------------------------------------------------------------
// Rat.two registration test
// ---------------------------------------------------------------

#[test]
fn test_rat_two_registered() {
    assert_registered(&make_env(), "Rat.two");
}

// ---------------------------------------------------------------
// Axiom count reduction tests (#3371)
// ---------------------------------------------------------------

#[test]
fn test_c001_domain_axiom_count_after_3586() {
    use crate::env::axiom_audit::ProofQuality;

    let env = make_env();

    // The tightness theorem is hypothesis-wrapped and should not depend on
    // any C001-prefix axiom. `abs_weighted_sum_le` stays a Definition and
    // `tail_norm_sum` stays an Opaque, so neither appears as an axiom.
    let quality = env
        .proof_quality(&Name::from_string("NNVerify.C001.compress_tightness"))
        .expect("C001b should exist");
    match &quality {
        ProofQuality::Constructive => {}
        ProofQuality::AxiomDependent { axioms, .. } => {
            let axiom_names: Vec<String> = axioms.iter().map(|a| a.to_string()).collect();
            assert!(
                !axiom_names.contains(&"NNVerify.C001.abs_weighted_sum_le".to_string()),
                "abs_weighted_sum_le should not be in axiom deps (Definition)"
            );
            assert!(
                !axiom_names.contains(&"NNVerify.C001.tail_norm_sum".to_string()),
                "tail_norm_sum should not be in axiom deps (Opaque post-#3586)"
            );
            assert!(
                !axiom_names.iter().any(|a| a.starts_with("NNVerify.C001.")),
                "C001b must not depend on C001-prefix axioms after hypothesis \
                 wrapping; got {axiom_names:?}"
            );
        }
        other => {
            panic!(
                "C001b should be Constructive or depend only on non-C001 axioms, got: {:?}",
                other
            );
        }
    }
}

#[test]
fn test_c001_domain_axioms_after_3586() {
    let env = make_env();

    // The C001 helper axiom has been retired; abs_weighted_sum_le (Def) and
    // tail_norm_sum (Opaque) are NOT axioms.
    let c001_axioms: Vec<String> = env
        .constants()
        .filter(|c| {
            c.name.to_string().starts_with("NNVerify.C001.") && c.kind == ConstantKind::Axiom
        })
        .map(|c| c.name.to_string())
        .collect();

    assert_eq!(
        c001_axioms,
        Vec::<String>::new(),
        "Expected no C001-namespace axioms after hypothesis wrapping; got {c001_axioms:?}"
    );
}

// ---------------------------------------------------------------
// Proof quality classification tests (#3371)
// ---------------------------------------------------------------

#[test]
fn test_c001a_proof_quality_is_constructive_after_compress_retirement() {
    use crate::env::axiom_audit::ProofQuality;

    let env = make_env();
    let quality = env
        .proof_quality(&Name::from_string("NNVerify.C001.compress_soundness"))
        .expect("C001a should exist");

    // COMPRESS RETIREMENT: `NNVerify.Zonotope.compress` was a body-less
    // `Declaration::Axiom`; it is now a faithful reducible `Declaration::Definition`
    // (box-cover body over `Fin.sum` + `Rat.abs` + a `Decidable.rec` index split,
    // with constructive Nat bound bricks). `compress` therefore no longer appears
    // as an admitted axiom in any closure, and the body's own closure is empty
    // (the Nat/Fin/Rat bricks it uses are all constructive kernel theorems). The
    // delegated T11 `compress_sound` is itself a hypothesis-wrapped Theorem (not
    // an axiom). So C001a's transitive axiom closure is now EMPTY and it
    // classifies as `ProofQuality::Constructive` — strictly stronger than the
    // prior `AxiomDependent`-on-`compress` state. Pinned here so a regression that
    // re-admits `compress` (or any domain axiom into C001a) turns this RED.
    match quality {
        ProofQuality::Constructive => {}
        ProofQuality::AxiomDependent { axioms, .. } => {
            let axiom_names: Vec<String> = axioms.iter().map(|a| a.to_string()).collect();
            assert!(
                !axiom_names
                    .iter()
                    .any(|n| n == "NNVerify.Zonotope.compress"),
                "compress is now a faithful Definition and must NOT reappear as an \
                 admitted axiom in C001a's closure, got {axiom_names:?}"
            );
            assert!(
                !axiom_names
                    .iter()
                    .any(|n| n == "NNVerify.Zonotope.compress_sound"),
                "compress_sound is a hypothesis-wrapped Theorem and must not appear \
                 as an admitted axiom in C001a's closure, got {axiom_names:?}"
            );
            panic!(
                "C001a should now be Constructive (compress retired to a Definition, \
                 empty closure), got AxiomDependent on {axiom_names:?}"
            );
        }
        other => {
            panic!("C001a should be Constructive, got: {other:?}");
        }
    }
}

#[test]
fn test_c001b_proof_quality_after_3586() {
    use crate::env::axiom_audit::ProofQuality;

    let env = make_env();
    let quality = env
        .proof_quality(&Name::from_string("NNVerify.C001.compress_tightness"))
        .expect("C001b should exist");

    // The tightness theorem is now hypothesis-wrapped, so the missing bound
    // is an explicit local premise rather than a transitive global axiom: no
    // C001-namespace axiom remains. #integrity-audit (2026-06): the Rat
    // ordering/ring facts the proof DOES reach (e.g. Rat.mul_zero, Rat.le_refl,
    // Rat.le_add_of_nonneg_right) are admitted DOMAIN axioms, NOT foundational,
    // so C001b is honestly AxiomDependent on admitted domain assumptions. We
    // assert every reached axiom is in ADMITTED_DOMAIN_AXIOMS (no rogue/unproved
    // axiom and no sorry leaks in) rather than pretending the closure is empty.
    use crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS;
    match quality {
        ProofQuality::Constructive => {}
        ProofQuality::AxiomDependent { axioms, .. } => {
            let axiom_names: Vec<String> = axioms.iter().map(|a| a.to_string()).collect();
            let c001_axioms: Vec<_> = axiom_names
                .iter()
                .filter(|a| a.starts_with("NNVerify.C001."))
                .collect();
            assert_eq!(
                c001_axioms.len(),
                0,
                "Expected no C001-namespace axioms after hypothesis wrapping, got: {:?}",
                c001_axioms
            );
            // The closure is honestly non-empty but contains only KNOWN domain
            // assumptions: an admitted Rat/Fin/Nat-bitwise DOMAIN axiom, or the
            // `NNVerify.Zonotope.compress` scaffolding primitive this conjecture
            // is explicitly built on. No `sorry`/`sorryAx` and no rogue/unproved
            // axiom may leak in. (#integrity-audit 2026-06.)
            for ax in &axiom_names {
                assert!(
                    !ax.contains("sorry"),
                    "sorry/sorryAx leaked into C001b closure: {ax}"
                );
                assert!(
                    ADMITTED_DOMAIN_AXIOMS.contains(&ax.as_str())
                        || ax == "NNVerify.Zonotope.compress",
                    "unexpected axiom in C001b closure: {ax} (expected only \
                     admitted domain axioms or the NNVerify.Zonotope.compress \
                     scaffolding primitive)"
                );
            }
        }
        other => {
            panic!(
                "C001b should be Constructive or depend only on non-C001 axioms, got: {:?}",
                other
            );
        }
    }
}

#[test]
fn test_c001_abs_weighted_sum_le_is_constructive() {
    use crate::env::axiom_audit::ProofQuality;

    let env = make_env();
    let quality = env
        .proof_quality(&Name::from_string("NNVerify.C001.abs_weighted_sum_le"))
        .expect("abs_weighted_sum_le should exist");

    // abs_weighted_sum_le is now a Definition, so proof_quality returns NotATheorem
    assert_eq!(
        quality,
        ProofQuality::NotATheorem,
        "abs_weighted_sum_le (Definition) should be NotATheorem, got: {:?}",
        quality
    );
}

#[test]
fn test_c001_tail_norm_sum_is_not_a_theorem() {
    use crate::env::axiom_audit::ProofQuality;

    let env = make_env();
    let quality = env
        .proof_quality(&Name::from_string("NNVerify.C001.tail_norm_sum"))
        .expect("tail_norm_sum should exist");

    // tail_norm_sum is Opaque, so proof_quality returns NotATheorem
    assert_eq!(
        quality,
        ProofQuality::NotATheorem,
        "tail_norm_sum (Opaque) should be NotATheorem, got: {:?}",
        quality
    );
}

// ---------------------------------------------------------------
// Rat ordered field axioms are admitted domain axioms, NOT foundational
// (#3371; reclassified by #integrity-audit 2026-06)
// ---------------------------------------------------------------

#[test]
fn test_rat_ordering_axioms_are_admitted_domain_not_foundational() {
    use crate::env::axiom_audit::{is_foundational_axiom, ADMITTED_DOMAIN_AXIOMS};

    // #integrity-audit (2026-06): The Rat ordering axioms used in C001 were
    // dishonestly whitelisted as "foundational" so theorems resting on them were
    // reported Constructive / "0 domain axioms". That overstated the proof
    // status. They are now in ADMITTED_DOMAIN_AXIOMS and EXCLUDED from
    // is_foundational_axiom: a theorem reaching one is honestly AxiomDependent.
    // This test pins that honest reclassification (it previously pinned the
    // dishonest "are foundational" policy).
    //
    // NOTE (#3470 Lane #2/#3): `Rat.le_refl` and `Rat.le_total` were ELIMINATED
    // to constructive Theorems; `Rat.le_trans` likewise (soundness fix 7971c3f5).
    // WS-A ATOMIC LIVE SWITCH: `Rat.le_antisymm` (FALSE on the free carrier) has
    // ALSO been ELIMINATED — the live `Rat` is now the quotient carrier
    // `Rat := Quot Rat.Raw.Equiv`, over which `Rat.le_antisymm` is a genuine
    // `Constructive` Theorem.
    //
    // WS-B: `Rat.max` / `Rat.min` (the last admitted Rat ordering/lattice
    // axioms) were ELIMINATED to constructive quotient `Declaration::Definition`s
    // (`algebra_rat_minmax_proof.rs`), so the admitted-domain Rat roster is now
    // empty — they join the eliminated set below.

    // The eliminated lemmas/operations must now be neither foundational nor
    // admitted — they are constructive Theorems (or, for `Rat.min`/`Rat.max`,
    // reducible Definitions; for `le_trans`, the soundness-fix Theorem).
    for name in &[
        "Rat.le_refl",
        "Rat.le_total",
        "Rat.le_trans",
        "Rat.le_antisymm",
        "Rat.max",
        "Rat.min",
    ] {
        let n = Name::from_string(name);
        assert!(
            !is_foundational_axiom(&n),
            "{name} is a constructive Theorem and must not be foundational",
        );
        assert!(
            !ADMITTED_DOMAIN_AXIOMS.contains(name),
            "{name} has been eliminated to a Theorem and must NOT be in \
             ADMITTED_DOMAIN_AXIOMS",
        );
    }
}

// ---------------------------------------------------------------
// Soundness report test (#3371)
// ---------------------------------------------------------------

#[test]
fn test_c001_soundness_report_after_3586() {
    let env = make_env();
    let report = env.soundness_report();

    // At least 2 theorems (C001a, C001b)
    assert!(
        report.theorems >= 2,
        "C001 should have at least 2 theorems, got {}",
        report.theorems
    );

    // The C001 helper axiom has been retired. `abs_weighted_sum_le` is a
    // Definition and `tail_norm_sum` is an Opaque; neither is an axiom.
    let c001_domain_axioms: Vec<String> = report
        .domain_axioms
        .iter()
        .filter(|a| a.to_string().starts_with("NNVerify.C001."))
        .map(|a| a.to_string())
        .collect();
    assert_eq!(
        c001_domain_axioms,
        Vec::<String>::new(),
        "Expected no C001-namespace domain axioms after hypothesis wrapping, got {c001_domain_axioms:?}"
    );
}

// ---------------------------------------------------------------
// Ordered field infrastructure available for C001 proof (#3371)
// ---------------------------------------------------------------

#[test]
fn test_rat_le_add_of_nonneg_right_available() {
    let mut env = Environment::new();
    env.init_rat_ordered_field_axioms()
        .expect("init_rat_ordered_field_axioms should succeed");

    let info = env
        .get_const(&Name::from_string("Rat.le_add_of_nonneg_right"))
        .expect("Rat.le_add_of_nonneg_right should be registered");

    // WS-A ATOMIC LIVE SWITCH: `Rat.le_add_of_nonneg_right` (FALSE on the free
    // carrier) is now a genuine `Constructive` quotient `Declaration::Theorem`.
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.le_add_of_nonneg_right should now be a Theorem (quotient payoff)"
    );

    // Type-check the axiom
    let e = Expr::const_(Name::from_string("Rat.le_add_of_nonneg_right"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("Rat.le_add_of_nonneg_right should type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Rat.le_add_of_nonneg_right type should be Pi"
    );
}

#[test]
fn test_rat_mul_nonneg_available() {
    let mut env = Environment::new();
    env.init_rat_ordered_field_axioms()
        .expect("init_rat_ordered_field_axioms should succeed");

    let info = env
        .get_const(&Name::from_string("Rat.mul_nonneg"))
        .expect("Rat.mul_nonneg should be registered");

    // Rat.mul_nonneg ELIMINATED: it is now a GENUINE kernel-checked
    // `Declaration::Theorem` (`algebra_rat_order_proofs.rs::
    // register_rat_mul_nonneg`), the `Rat.le` analog of the proven
    // `Rat.mul_pos`. `init_rat_ordered_field_axioms` registers it via
    // `register_rat_order_proofs` before the (now-removed) axiom block. It is no
    // longer an admitted DOMAIN axiom — theorems reaching it stay `Constructive`.
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.mul_nonneg should be a kernel-checked Theorem (genuinely proven, not admitted)"
    );
    assert!(
        info.value.is_some(),
        "Rat.mul_nonneg Theorem must retain its proof value"
    );

    // The proof term kernel-type-checks at its canonical type.
    let e = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("Rat.mul_nonneg should type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Rat.mul_nonneg type should be Pi"
    );

    // Genuinely Constructive — empty domain-axiom closure (no Rat-level axiom).
    use crate::env::axiom_audit::ProofQuality;
    let q = env
        .proof_quality(&Name::from_string("Rat.mul_nonneg"))
        .expect("proof_quality");
    assert!(
        matches!(q, ProofQuality::Constructive),
        "Rat.mul_nonneg must be Constructive after elimination, got {q:?}"
    );
}
