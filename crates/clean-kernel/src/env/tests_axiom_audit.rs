// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for axiom dependency analysis and proof quality classification.

use super::*;
use crate::expr::Expr;
use crate::name::Name;

/// Helper: build a minimal empty environment.
///
/// Uses `Environment::default()` instead of `Environment::new()` to avoid
/// pre-populated sorry/trustedArith/trustedAy axioms that would make
/// assertion counts unpredictable.
fn base_env() -> Environment {
    Environment::default()
}

/// Build an environment containing the Rat field/order declarations relevant
/// to the #3656/#3657 bridge-fallout closure guards.
fn rat_bridge_fallout_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_rat_ordering()
        .expect("init_nn_verify_rat_ordering should succeed");
    env
}

fn try_rat_bridge_fallout_env() -> Option<Environment> {
    let mut env = Environment::new();
    env.init_nn_verify_rat_ordering().ok()?;
    Some(env)
}

/// Helper: exact `axiom_deps` closure as a sorted string set for stable pins.
fn axiom_dep_names(env: &Environment, name: &str) -> std::collections::BTreeSet<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("axiom_deps should work for {name}"))
        .into_iter()
        .map(|dep| dep.to_string())
        .collect()
}

// ════════════════════════════════════════════════════════════════════════════
// axiom_deps tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_axiom_deps_constructive_theorem_returns_empty() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Add a simple axiom-free theorem: True
    // type: Prop, value: Prop (self-referencing for simplicity)
    let thm = Declaration::Theorem {
        name: Name::from_string("my_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: prop.clone(),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("my_thm"))
        .expect("should find declaration");
    assert!(
        deps.is_empty(),
        "constructive theorem should have no axiom deps"
    );
}

#[test]
fn test_axiom_deps_theorem_wrapping_axiom_returns_that_axiom() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Add a domain-specific axiom
    let axiom = Declaration::Axiom {
        name: Name::from_string("my_axiom"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom).expect("add axiom");

    // Add a theorem whose proof references the axiom
    let axiom_ref = Expr::const_str("my_axiom");
    let thm = Declaration::Theorem {
        name: Name::from_string("fake_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: axiom_ref,
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("fake_thm"))
        .expect("should find declaration");
    assert_eq!(deps.len(), 1);
    assert!(
        deps.contains(&Name::from_string("my_axiom")),
        "should contain the domain axiom"
    );
}

#[test]
fn test_axiom_deps_transitive_chain() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Axiom C: Prop (domain-specific, leaf)
    let axiom_c = Declaration::Axiom {
        name: Name::from_string("axiom_C"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom_c).expect("add axiom_C");

    // Axiom B: type references axiom_C
    let axiom_b_type = Expr::arrow(Expr::const_str("axiom_C"), prop.clone());
    let axiom_b = Declaration::Axiom {
        name: Name::from_string("axiom_B"),
        level_params: vec![],
        type_: axiom_b_type,
    };
    env.add_decl_structural(axiom_b).expect("add axiom_B");

    // Theorem A: proof references axiom_B
    let thm = Declaration::Theorem {
        name: Name::from_string("thm_A"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("axiom_B"),
    };
    env.add_decl_structural(thm).expect("add thm_A");

    let deps = env
        .axiom_deps(&Name::from_string("thm_A"))
        .expect("should find declaration");
    assert_eq!(deps.len(), 2, "should find both axiom_B and axiom_C");
    assert!(deps.contains(&Name::from_string("axiom_B")));
    assert!(deps.contains(&Name::from_string("axiom_C")));
}

#[test]
fn test_axiom_deps_foundational_axiom_excluded() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Register propext as a foundational axiom
    let propext = Declaration::Axiom {
        name: Name::from_string("propext"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(propext).expect("add propext");

    // Theorem that references propext
    let thm = Declaration::Theorem {
        name: Name::from_string("uses_propext"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("propext"),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("uses_propext"))
        .expect("should find declaration");
    assert!(
        deps.is_empty(),
        "propext is foundational and should not appear in deps"
    );
}

#[test]
fn test_axiom_deps_nonexistent_returns_none() {
    let env = base_env();
    assert!(
        env.axiom_deps(&Name::from_string("nonexistent")).is_none(),
        "missing declaration should return None"
    );
}

#[test]
fn test_axiom_deps_definition_with_axiom_in_value() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Domain axiom
    let axiom = Declaration::Axiom {
        name: Name::from_string("dom_ax"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom).expect("add axiom");

    // Definition whose value references the axiom
    let def = Declaration::Definition {
        name: Name::from_string("my_def"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("dom_ax"),
        is_reducible: false,
    };
    env.add_decl_structural(def).expect("add definition");

    let deps = env
        .axiom_deps(&Name::from_string("my_def"))
        .expect("should find declaration");
    assert_eq!(deps.len(), 1);
    assert!(deps.contains(&Name::from_string("dom_ax")));
}

// ════════════════════════════════════════════════════════════════════════════
// proof_quality tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_proof_quality_constructive() {
    let mut env = base_env();
    let prop = Expr::prop();

    let thm = Declaration::Theorem {
        name: Name::from_string("good_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: prop.clone(),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let quality = env
        .proof_quality(&Name::from_string("good_thm"))
        .expect("should find");
    assert_eq!(quality, ProofQuality::Constructive);
}

#[test]
fn test_proof_quality_axiom_dependent() {
    let mut env = base_env();
    let prop = Expr::prop();

    let axiom = Declaration::Axiom {
        name: Name::from_string("sneaky_axiom"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom).expect("add axiom");

    let thm = Declaration::Theorem {
        name: Name::from_string("bad_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("sneaky_axiom"),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let quality = env
        .proof_quality(&Name::from_string("bad_thm"))
        .expect("should find");
    match quality {
        ProofQuality::AxiomDependent {
            axiom_count,
            axioms,
        } => {
            assert_eq!(axiom_count, 1);
            assert_eq!(axioms[0], Name::from_string("sneaky_axiom"));
        }
        other => panic!("expected AxiomDependent, got {:?}", other),
    }
}

#[test]
fn test_proof_quality_not_a_theorem() {
    let mut env = base_env();
    let prop = Expr::prop();

    let axiom = Declaration::Axiom {
        name: Name::from_string("just_an_axiom"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom).expect("add axiom");

    let quality = env
        .proof_quality(&Name::from_string("just_an_axiom"))
        .expect("should find");
    assert_eq!(quality, ProofQuality::NotATheorem);
}

#[test]
fn test_proof_quality_definition_is_not_a_theorem() {
    let mut env = base_env();
    let prop = Expr::prop();

    let def = Declaration::Definition {
        name: Name::from_string("my_def"),
        level_params: vec![],
        type_: prop.clone(),
        value: prop.clone(),
        is_reducible: false,
    };
    env.add_decl_structural(def).expect("add def");

    let quality = env
        .proof_quality(&Name::from_string("my_def"))
        .expect("should find");
    assert_eq!(quality, ProofQuality::NotATheorem);
}

#[test]
fn test_proof_quality_nonexistent_returns_none() {
    let env = base_env();
    assert!(env.proof_quality(&Name::from_string("nope")).is_none());
}

// ════════════════════════════════════════════════════════════════════════════
// soundness_report tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_soundness_report_empty_env() {
    let env = base_env();
    let report = env.soundness_report();
    assert_eq!(report.total_declarations, 0);
    assert_eq!(report.theorems, 0);
    assert_eq!(report.axioms, 0);
    assert_eq!(report.definitions, 0);
    assert_eq!(report.constructive_theorems, 0);
    assert_eq!(report.axiom_dependent_theorems, 0);
    assert_eq!(report.total_domain_axioms, 0);
}

#[test]
fn test_soundness_report_mixed_env() {
    let mut env = base_env();
    let prop = Expr::prop();

    // 1. Foundational axiom (should not count as domain axiom)
    let propext = Declaration::Axiom {
        name: Name::from_string("propext"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(propext).expect("add propext");

    // 2. Domain axiom
    let domain_ax = Declaration::Axiom {
        name: Name::from_string("domain_axiom"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(domain_ax)
        .expect("add domain_axiom");

    // 3. Constructive theorem
    let good = Declaration::Theorem {
        name: Name::from_string("good_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: prop.clone(),
    };
    env.add_decl_structural(good).expect("add good_thm");

    // 4. Fake theorem wrapping the domain axiom
    let fake = Declaration::Theorem {
        name: Name::from_string("fake_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("domain_axiom"),
    };
    env.add_decl_structural(fake).expect("add fake_thm");

    // 5. Definition
    let def = Declaration::Definition {
        name: Name::from_string("my_def"),
        level_params: vec![],
        type_: prop.clone(),
        value: prop.clone(),
        is_reducible: false,
    };
    env.add_decl_structural(def).expect("add my_def");

    let report = env.soundness_report();
    assert_eq!(report.total_declarations, 5);
    assert_eq!(report.theorems, 2);
    assert_eq!(report.axioms, 2); // propext + domain_axiom
    assert_eq!(report.definitions, 1);
    assert_eq!(report.constructive_theorems, 1);
    assert_eq!(report.axiom_dependent_theorems, 1);
    assert_eq!(report.total_domain_axioms, 1); // only domain_axiom
    assert_eq!(
        report.domain_axioms,
        vec![Name::from_string("domain_axiom")]
    );
}

// ════════════════════════════════════════════════════════════════════════════
// nn_verify-style scenario: multiple fake proofs wrapping axioms
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_soundness_report_nn_verify_fake_proof_pattern() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Register 5 domain-specific "neural net verification" axioms
    for i in 0..5 {
        let name = Name::from_string(&format!("nn_verify_axiom_{i}"));
        let axiom = Declaration::Axiom {
            name,
            level_params: vec![],
            type_: prop.clone(),
        };
        env.add_decl_structural(axiom).expect("add nn_verify axiom");
    }

    // "Prove" 10 theorems, each wrapping one of the 5 axioms
    for i in 0..10 {
        let axiom_idx = i % 5;
        let axiom_name = format!("nn_verify_axiom_{axiom_idx}");
        let thm = Declaration::Theorem {
            name: Name::from_string(&format!("nn_thm_{i}")),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str(&axiom_name),
        };
        env.add_decl_structural(thm).expect("add nn theorem");
    }

    // Add 3 genuinely constructive theorems
    for i in 0..3 {
        let thm = Declaration::Theorem {
            name: Name::from_string(&format!("real_thm_{i}")),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
        };
        env.add_decl_structural(thm).expect("add real theorem");
    }

    let report = env.soundness_report();
    assert_eq!(report.total_declarations, 18); // 5 axioms + 10 fake + 3 real
    assert_eq!(report.theorems, 13); // 10 fake + 3 real
    assert_eq!(report.axioms, 5);
    assert_eq!(report.constructive_theorems, 3);
    assert_eq!(report.axiom_dependent_theorems, 10);
    assert_eq!(report.total_domain_axioms, 5);

    // Verify each fake theorem is AxiomDependent
    for i in 0..10 {
        let name = Name::from_string(&format!("nn_thm_{i}"));
        let quality = env.proof_quality(&name).expect("should find");
        match quality {
            ProofQuality::AxiomDependent { axiom_count, .. } => {
                assert_eq!(axiom_count, 1, "each fake thm wraps exactly 1 axiom");
            }
            other => panic!("nn_thm_{i} should be AxiomDependent, got {:?}", other),
        }
    }

    // Verify each real theorem is Constructive
    for i in 0..3 {
        let name = Name::from_string(&format!("real_thm_{i}"));
        let quality = env.proof_quality(&name).expect("should find");
        assert_eq!(quality, ProofQuality::Constructive);
    }
}

#[test]
fn test_axiom_deps_app_expr_traversal() {
    // Test that axiom_deps correctly walks App(f, arg) expressions
    let mut env = base_env();
    let prop = Expr::prop();

    let axiom = Declaration::Axiom {
        name: Name::from_string("hidden_ax"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom).expect("add axiom");

    // Build App(hidden_ax, Prop) as the proof term
    let proof = Expr::app(Expr::const_str("hidden_ax"), prop.clone());
    let thm = Declaration::Theorem {
        name: Name::from_string("app_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: proof,
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("app_thm"))
        .expect("should find");
    assert_eq!(deps.len(), 1);
    assert!(deps.contains(&Name::from_string("hidden_ax")));
}

#[test]
fn test_axiom_deps_pi_type_traversal() {
    // Test that axiom_deps walks Pi types in declarations
    let mut env = base_env();
    let prop = Expr::prop();

    let axiom = Declaration::Axiom {
        name: Name::from_string("type_axiom"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom).expect("add axiom");

    // Theorem whose TYPE references the axiom (via arrow/Pi)
    let thm_type = Expr::arrow(Expr::const_str("type_axiom"), prop.clone());
    let thm = Declaration::Theorem {
        name: Name::from_string("pi_thm"),
        level_params: vec![],
        type_: thm_type,
        value: prop.clone(),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("pi_thm"))
        .expect("should find");
    assert_eq!(deps.len(), 1);
    assert!(deps.contains(&Name::from_string("type_axiom")));
}

#[test]
fn test_axiom_deps_multiple_foundational_axioms() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Register several foundational axioms.
    // NOTE: `funext` is no longer foundational (it is now a kernel-checked
    // Theorem derived from Quot.sound), so this synthetic test uses
    // `proofIrrel` as the fourth still-foundational axiom instead.
    for name in &["propext", "Classical.choice", "Quot.sound", "proofIrrel"] {
        let axiom = Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        };
        env.add_decl_structural(axiom)
            .expect("add foundational axiom");
    }

    // Theorem referencing all of them through nested App
    let proof = Expr::app(
        Expr::app(
            Expr::const_str("propext"),
            Expr::const_str("Classical.choice"),
        ),
        Expr::app(Expr::const_str("Quot.sound"), Expr::const_str("proofIrrel")),
    );

    let thm = Declaration::Theorem {
        name: Name::from_string("uses_all_foundational"),
        level_params: vec![],
        type_: prop.clone(),
        value: proof,
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("uses_all_foundational"))
        .expect("should find");
    assert!(
        deps.is_empty(),
        "all referenced axioms are foundational, deps should be empty"
    );

    let quality = env
        .proof_quality(&Name::from_string("uses_all_foundational"))
        .expect("should find");
    assert_eq!(quality, ProofQuality::Constructive);
}

#[test]
fn test_axiom_deps_mixed_foundational_and_domain() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Foundational
    let propext = Declaration::Axiom {
        name: Name::from_string("propext"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(propext).expect("add propext");

    // Domain-specific
    let domain = Declaration::Axiom {
        name: Name::from_string("my_unproved_lemma"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(domain).expect("add domain axiom");

    // Theorem referencing both
    let proof = Expr::app(
        Expr::const_str("propext"),
        Expr::const_str("my_unproved_lemma"),
    );
    let thm = Declaration::Theorem {
        name: Name::from_string("mixed_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: proof,
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("mixed_thm"))
        .expect("should find");
    assert_eq!(deps.len(), 1, "only the domain axiom should appear");
    assert!(deps.contains(&Name::from_string("my_unproved_lemma")));
}

// Trust-marker soundness tests (#3554)
//
// Before #3554, `sorryAx` was listed inside `FOUNDATIONAL_AXIOMS` and
// therefore filtered out of `axiom_deps()`. Any theorem whose proof
// transitively reached `sorryAx` was reported as
// `ProofQuality::Constructive` — a soundness classifier bug.
// These tests pin the post-fix behaviour: reaching `sorryAx`, `sorry`,
// `trustedArith`, or `trustedAy` MUST NOT yield `Constructive`.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_is_trust_marker_recognizes_all_four() {
    assert!(is_trust_marker(&Name::from_string("sorry")));
    assert!(is_trust_marker(&Name::from_string("sorryAx")));
    assert!(is_trust_marker(&Name::from_string("trustedArith")));
    assert!(is_trust_marker(&Name::from_string("trustedAy")));
}

#[test]
fn test_is_trust_marker_rejects_foundational_and_domain() {
    // Foundational axioms are NOT trust markers.
    assert!(!is_trust_marker(&Name::from_string("propext")));
    assert!(!is_trust_marker(&Name::from_string("Quot.sound")));
    assert!(!is_trust_marker(&Name::from_string("Classical.choice")));
    assert!(!is_trust_marker(&Name::from_string("Eq.refl")));
    // Arbitrary domain axioms are NOT trust markers.
    assert!(!is_trust_marker(&Name::from_string("my_domain_axiom")));
    assert!(!is_trust_marker(&Name::from_string("NNVerify.some_axiom")));
}

#[test]
fn test_sorry_ax_is_not_foundational() {
    // The bug being fixed: `sorryAx` must NOT be classified as foundational.
    // Before #3554 this returned `true`, causing
    // `Environment::axiom_deps()` to drop `sorryAx` from the returned set
    // and `proof_quality` to report `Constructive` for theorems reaching
    // `sorry`.
    assert!(
        !is_foundational_axiom(&Name::from_string("sorryAx")),
        "sorryAx must not be in FOUNDATIONAL_AXIOMS (see #3554)"
    );
    assert!(
        !is_foundational_axiom(&Name::from_string("sorry")),
        "sorry must not be in FOUNDATIONAL_AXIOMS (see #3554)"
    );
    assert!(
        !is_foundational_axiom(&Name::from_string("trustedArith")),
        "trustedArith must not be in FOUNDATIONAL_AXIOMS (see #3554)"
    );
    assert!(
        !is_foundational_axiom(&Name::from_string("trustedAy")),
        "trustedAy must not be in FOUNDATIONAL_AXIOMS (see #3554)"
    );
}

#[test]
fn test_trust_markers_are_disjoint_from_foundational() {
    // No trust marker may also be foundational. This property prevents
    // re-introduction of the #3554 classifier bug: if someone adds
    // `sorryAx` back to `FOUNDATIONAL_AXIOMS`, this test fires.
    for name in &["sorry", "sorryAx", "trustedArith", "trustedAy"] {
        let n = Name::from_string(name);
        assert!(is_trust_marker(&n), "{name} should be a trust marker",);
        assert!(
            !is_foundational_axiom(&n),
            "{name} must not also be foundational (see #3554)",
        );
    }
}

/// Belt-and-suspenders: `is_foundational_axiom` MUST return `false` for
/// every trust-marker name regardless of the `FOUNDATIONAL_AXIOMS` slice
/// contents. This pins the defensive guard added in #3554 that short-
/// circuits on `is_trust_marker(name)` before scanning the slice.
///
/// If a future refactor weakens `is_foundational_axiom` (e.g. drops the
/// `is_trust_marker` short-circuit and relies solely on the slice being
/// clean), this test still fires the moment someone then re-adds a trust
/// marker to the slice — closing the classifier-bug re-introduction path
/// twice over.
#[test]
fn test_is_foundational_axiom_rejects_every_trust_marker_3554() {
    for name in &["sorry", "sorryAx", "trustedArith", "trustedAy"] {
        let n = Name::from_string(name);
        assert!(
            !is_foundational_axiom(&n),
            "is_foundational_axiom must return false for trust marker {name} \
             (belt-and-suspenders guard; see #3554)",
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Rat field axiom tranche (#3555): whitelist pins for the multiplicative
// field axioms promoted in the classification decision. Each name below is
// registered as a plain `Declaration::Axiom` in
// `crates/clean-kernel/src/env/algebra_field_inst.rs` with its canonical
// Mathlib type signature. The whitelist entries themselves carry no domain
// content; they are a promissory note that the constructive proof via the
// quotient carrier `Rat := Int × Nat* / ≈` is expected to land (tracker:
// epic #3470). These tests fix the classification so future edits that
// accidentally demote one of these axioms back into the "domain-specific"
// bucket are caught by the unit suite instead of by a downstream proof
// regression.
// ════════════════════════════════════════════════════════════════════════════

/// #integrity-audit (2026-06): the Rat multiplicative-field axioms that #3555
/// had whitelisted as "foundational" are admitted DOMAIN axioms — mathematically
/// true but carrying NO Clean-kernel proof term. Whitelisting them as
/// foundational dishonestly reported theorems resting on them as
/// `ProofQuality::Constructive` ("0 domain axioms"). They are now listed in
/// `ADMITTED_DOMAIN_AXIOMS` and EXCLUDED from `is_foundational_axiom`. This test
/// (formerly `test_rat_field_axioms_are_foundational_3555`, which PINNED the
/// dishonest policy) is flipped to pin the honest state: each name is NOT
/// foundational and IS an admitted domain axiom.
#[test]
fn test_rat_field_axioms_are_admitted_domain_not_foundational_3555() {
    use super::axiom_audit::{is_foundational_axiom, ADMITTED_DOMAIN_AXIOMS};

    // History: this pin tracked the admitted Rat field/lattice axioms. Tranche
    // B/C/D.1 + the WS-A quotient switch eliminated the ring/field axioms to
    // constructive `Declaration::Theorem`s. WS-B eliminated the LAST entries —
    // `Rat.max` / `Rat.min` — to constructive quotient `Declaration::Definition`s
    // (`algebra_rat_minmax_proof.rs`). The pin now verifies the ELIMINATED state:
    // each is NOT in `ADMITTED_DOMAIN_AXIOMS`, is NOT foundational, and is a
    // reducible `Definition` (not an axiom) in the init'd environment.
    let mut env = base_env();
    env.init_rat_minmax().expect("init_rat_minmax");
    for name in &["Rat.max", "Rat.min"] {
        assert!(
            !ADMITTED_DOMAIN_AXIOMS.contains(name),
            "WS-B: {name} was ELIMINATED to a constructive quotient Definition; \
             it must NOT remain in ADMITTED_DOMAIN_AXIOMS",
        );
        assert!(
            !is_foundational_axiom(&Name::from_string(name)),
            "WS-B: {name} is a constructive Definition, not a foundational axiom",
        );
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "WS-B: {name} must be a reducible Definition (eliminated), got {:?}",
            info.kind,
        );
    }
}

/// #integrity-audit (2026-06): the pre-#3555 additive / cancellation /
/// sign batch (`Rat.add_left_neg`, `Rat.add_neg_self`, `Rat.add_right_cancel`)
/// was also dishonestly whitelisted as "foundational". They are admitted
/// DOMAIN axioms with no Clean-kernel proof term, now in
/// `ADMITTED_DOMAIN_AXIOMS` and excluded from `is_foundational_axiom`. This
/// test (formerly `test_rat_additive_and_cancellation_axioms_remain_foundational`,
/// which PINNED the dishonest policy) is flipped to pin the honest state: each
/// name is NOT foundational and IS an admitted domain axiom.
///
/// NOTE (#3470 Lane #2/#3): `Rat.mul_neg` was previously in this batch as an
/// admitted domain axiom. It has since been GENUINELY ELIMINATED to a
/// kernel-checked `Declaration::Theorem` (`congrArg` over `Int.neg_mul_right`)
/// and removed from `ADMITTED_DOMAIN_AXIOMS`, so it is dropped from this pin.
#[test]
fn test_rat_additive_and_cancellation_axioms_are_admitted_domain_not_foundational() {
    use super::axiom_audit::{is_foundational_axiom, ADMITTED_DOMAIN_AXIOMS};

    // History: this pin tracked the admitted Rat additive / cancellation / sign
    // axioms. They were progressively eliminated to constructive
    // `Declaration::Theorem`s — `Rat.add_assoc` (#3572), `Rat.add_comm` (#3572),
    // `Rat.zero_add` / `Rat.add_zero` (#3581), and `Rat.add_left_neg` /
    // `Rat.add_neg_self` / `Rat.add_right_cancel` (WS-A quotient switch), all
    // removed from `ADMITTED_DOMAIN_AXIOMS` per the #3559 disjointness rule.
    //
    // WS-B: the last admitted entries in this pin (`Rat.min_le_left` /
    // `Rat.le_max_left`) were ELIMINATED to constructive quotient
    // `Declaration::Theorem`s (`algebra_rat_minmax_proof.rs`). The pin now
    // verifies the ELIMINATED state: NOT in `ADMITTED_DOMAIN_AXIOMS`, NOT
    // foundational, and registered as a `Declaration::Theorem`.
    let mut env = base_env();
    // `register_rat_min_max_lemmas` (pulled by the interval-arith init) registers
    // the lattice lemmas as constructive Theorems via `register_rat_minmax_proofs`.
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");
    for name in &["Rat.min_le_left", "Rat.le_max_left"] {
        assert!(
            !ADMITTED_DOMAIN_AXIOMS.contains(name),
            "WS-B: {name} was ELIMINATED to a constructive quotient Theorem; \
             it must NOT remain in ADMITTED_DOMAIN_AXIOMS",
        );
        assert!(
            !is_foundational_axiom(&Name::from_string(name)),
            "WS-B: {name} is a constructive Theorem, not a foundational axiom",
        );
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "WS-B: {name} must be a constructive Theorem (eliminated), got {:?}",
            info.kind,
        );
    }
}

/// #integrity-audit (2026-06): a fake theorem wrapping an admitted DOMAIN axiom
/// must classify as `AxiomDependent`, NOT `Constructive`. The example axiom is
/// `Rat.le_antisymm` — a Rat ordered-field ordering axiom with no Clean-kernel
/// proof term, excluded from `is_foundational_axiom`. Reaching such an axiom in
/// the transitive closure is a genuine (admitted) domain-axiom dependency, so
/// the honest classification is `AxiomDependent` on exactly that one axiom.
///
/// NOTE (#3470 Lane #2/#3): this test formerly used `Rat.le_refl`, repointed to
/// `Rat.le_trans`, then `Rat.le_antisymm`, then `Nat.shiftRight` as those each
/// became Theorems/Definitions. NOTE (TCB-shrink Tier-0): `Nat.shiftRight` has
/// now ALSO been ELIMINATED to a Definition (`fun m n => Nat.iterDiv2 n m`), so
/// the curated `ADMITTED_DOMAIN_AXIOMS` list is empty. The classifier behavior
/// under test — "a theorem reaching a non-foundational admitted domain axiom is
/// `AxiomDependent`" — is driven by `is_foundational_axiom` (the single source
/// of truth), not by curated-list membership: line 629 of `axiom_audit.rs`
/// classifies any `Axiom`-kind dep with `!is_foundational_axiom` as a domain
/// dependency. We therefore install a SYNTHETIC admitted domain axiom
/// (`Domain.synthetic_admitted`, not a foundational name) and assert the wrapper
/// classifies as `AxiomDependent` on exactly it.
#[test]
fn test_proof_quality_rat_admitted_wrapper_is_axiom_dependent_3555() {
    use super::axiom_audit::is_foundational_axiom;

    let mut env = base_env();
    let prop = Expr::prop();

    // A synthetic non-foundational admitted domain axiom (stands in for the now
    // fully-discharged Rat/Nat domain axioms). It is NOT a foundational name, so
    // `is_foundational_axiom` returns false and the classifier must treat a
    // theorem reaching it as `AxiomDependent`.
    let domain_axiom_name = Name::from_string("Domain.synthetic_admitted");
    assert!(
        !is_foundational_axiom(&domain_axiom_name),
        "the synthetic domain axiom must be non-foundational"
    );
    let axiom = Declaration::Axiom {
        name: domain_axiom_name.clone(),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(axiom)
        .expect("add Domain.synthetic_admitted");

    let thm = Declaration::Theorem {
        name: Name::from_string("wraps_domain_axiom"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("Domain.synthetic_admitted"),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let quality = env
        .proof_quality(&Name::from_string("wraps_domain_axiom"))
        .expect("should find");
    match quality {
        ProofQuality::AxiomDependent {
            axiom_count,
            axioms,
        } => {
            assert_eq!(
                axiom_count, 1,
                "the only axiom dep is the admitted domain axiom",
            );
            assert_eq!(axioms, vec![domain_axiom_name.clone()]);
            assert!(
                axioms.iter().all(|a| !is_foundational_axiom(a)),
                "every listed axiom must be a non-foundational (admitted) domain \
                 axiom; got {axioms:?}",
            );
        }
        other => panic!(
            "a theorem whose only axiom dep is a non-foundational admitted domain \
             axiom must classify as AxiomDependent, got {other:?}",
        ),
    }
}

/// Cross-check: trust markers (`sorry`, `sorryAx`, `trustedArith`,
/// `trustedAy`) remain NON-foundational after #3554. #3555 must not
/// accidentally relax this. Regression guard against misfiling a trust
/// marker under the new Rat whitelist block.
#[test]
fn test_trust_markers_not_foundational_after_3555() {
    use super::axiom_audit::{is_foundational_axiom, is_trust_marker};

    for name in &["sorry", "sorryAx", "trustedArith", "trustedAy"] {
        let n = Name::from_string(name);
        assert!(
            !is_foundational_axiom(&n),
            "{name} must NOT be foundational (trust marker)",
        );
        assert!(is_trust_marker(&n), "{name} must be a trust marker",);
    }
}

/// Disjointness sanity check: no Rat field axiom promoted by #3555 can
/// also be a trust marker. If someone pastes a name into the wrong
/// bucket, this test fires.
#[test]
fn test_rat_field_axioms_are_not_trust_markers_3555() {
    use super::axiom_audit::is_trust_marker;

    // NOTE (#3581 Phase 2): `Rat.one_mul`, `Rat.mul_one`, and `Rat.inv_zero`
    // have been promoted from Declaration::Axiom to Declaration::Theorem with
    // constructive kernel-checked proof terms (see
    // `algebra_rat_tranche_b_proofs.rs`). They are no longer foundational
    // axioms, so the "must not be a trust marker (it is a foundational
    // axiom)" semantic does not apply. Their former positions remain covered
    // by `test_tranche_b_*_is_theorem_not_axiom` in the tranche B proof
    // module.
    //
    // NOTE (Part of #3582, Tranche C Phase 3): `Rat.mul_assoc` has been
    // promoted from Declaration::Axiom to Declaration::Theorem with a
    // constructive proof over `Int.mul_assoc + Nat.mul_assoc` (see
    // `algebra_rat_mul_assoc_proof.rs`). Removed from this pin per the
    // #3559 disjointness rule; theorem kind pinned by
    // `test_rat_mul_assoc_is_theorem_not_axiom` in
    // `tests_algebra_rat_mul_assoc.rs`.
    //
    // NOTE (#3642 Tranche D.1, Part of #3652): `Rat.zero_mul` and
    // `Rat.mul_zero` have been promoted from Declaration::Axiom to
    // Declaration::Theorem with constructive proofs (see
    // `algebra_rat_tranche_d1_proofs/`). Removed here per the #3559
    // disjointness rule; theorem kind pinned by
    // `test_rat_zero_mul_is_theorem_not_axiom` /
    // `test_rat_mul_zero_is_theorem_not_axiom` in the Tranche D.1 proof
    // module.
    //
    // NOTE (#integrity-audit 2026-06): the remaining names here
    // (`Rat.right_distrib`, `Rat.mul_inv_cancel`) are NOT foundational axioms —
    // they are admitted DOMAIN axioms (now in `ADMITTED_DOMAIN_AXIOMS`,
    // excluded from `is_foundational_axiom`). The disjointness intent of this
    // test still holds: an admitted domain axiom must never also be a trust
    // marker, so a name pasted into the wrong bucket still fires here.
    for name in &["Rat.right_distrib", "Rat.mul_inv_cancel"] {
        assert!(
            !is_trust_marker(&Name::from_string(name)),
            "{name} must not be a trust marker (it is an admitted domain axiom)",
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Rat bridge fallout closure guards (#3657)
// ════════════════════════════════════════════════════════════════════════════

/// #3656 rollback guard: once the unsound `Rat.mk_eq_mk_of_cross_eq` bridge
/// path is removed from these declarations, their own `axiom_deps` closures
/// must collapse to empty sets. As axioms, they have no proof body for the
/// BFS to walk; only their types remain, and those types contain no
/// non-foundational axiom references.
#[test]
fn test_rat_bridge_rollbacks_have_empty_self_closures_3657() {
    let env = rat_bridge_fallout_env();

    for name in ["Rat.zero_mul", "Rat.mul_zero", "Rat.left_distrib"] {
        let deps = axiom_dep_names(&env, name);
        assert!(
            deps.is_empty(),
            "{name} should have empty axiom_deps after the #3656 rollback; got {deps:?}",
        );
    }
}

/// #3654 regression guard: the live Rat initializer must not register the
/// unsound bridge axiom at all. The rollback leaves the helper available as
/// historical code only; it must stay unhooked from `init_nn_verify_rat_ordering`.
#[test]
fn test_rat_mk_eq_mk_of_cross_eq_is_not_registered_in_live_rat_env_3654() {
    let env = rat_bridge_fallout_env();
    assert!(
        env.get_const(&Name::from_string("Rat.mk_eq_mk_of_cross_eq"))
            .is_none(),
        "Rat.mk_eq_mk_of_cross_eq must not be registered by the live Rat environment after #3654",
    );
}

/// #3657 + #integrity-audit (2026-06): after `Rat.left_distrib` rolls back to
/// `Declaration::Axiom`, `Rat.mul_sub` must expose its trust gaps directly. The
/// old bridge fanout (`Rat.mk_eq_mk_of_cross_eq`, `Int.left_distrib`, ...) must
/// still be gone.
///
/// NOTE (#3470 Lane #2/#3): the honest closure is now EXACTLY `{Rat.left_distrib}`.
/// `Rat.mul_neg` — which `build_mul_sub_proof` uses directly — has been
/// GENUINELY ELIMINATED to a constructive `Declaration::Theorem` (`congrArg` over
/// `Int.neg_mul_right`). Because `axiom_deps` short-circuits only on
/// `kind == Axiom`, the BFS now walks into `Rat.mul_neg`'s constructive proof
/// (which reaches no domain axiom) instead of stopping at it, so it no longer
/// appears in the closure. The single remaining non-foundational dep is the
/// deliberately non-foundational, non-admitted `Rat.left_distrib` axiom.
#[test]
fn test_rat_mul_sub_closure_surfaces_left_distrib_only_3657() {
    let env = rat_bridge_fallout_env();
    let deps = axiom_dep_names(&env, "Rat.mul_sub");

    // WS-A ATOMIC LIVE SWITCH: `Rat.left_distrib` (the last non-foundational dep
    // of `Rat.mul_sub`) is now a `Constructive` quotient Theorem, and
    // `Rat.mul_neg` was already eliminated. So `Rat.mul_sub`'s non-foundational
    // axiom closure is now EMPTY.
    assert!(
        deps.is_empty(),
        "Rat.mul_sub closure must now be EMPTY (Rat.left_distrib + Rat.mul_neg \
         are quotient Theorems); got {deps:?}",
    );
}

/// #3657 + #integrity-audit (2026-06) regression guard: `Rat.left_distrib`
/// must stay outside `FOUNDATIONAL_AXIOMS` and outside `ADMITTED_DOMAIN_AXIOMS`
/// (it is a deliberately exposed non-foundational, non-admitted trust gap), and
/// `Rat.mul_sub` must remain `AxiomDependent` on it. After the integrity audit
/// the closure also honestly surfaces the admitted domain axiom `Rat.mul_neg`
/// that the proof term uses (previously masked by the dishonest whitelist), so
/// the closure is no longer a single axiom — but every member is either
/// `Rat.left_distrib` or an admitted domain axiom.
#[test]
fn test_rat_left_distrib_stays_nonfoundational_and_mul_sub_stays_bridge_scoped_3657() {
    use super::axiom_audit::{is_foundational_axiom, ADMITTED_DOMAIN_AXIOMS};

    let left_distrib = Name::from_string("Rat.left_distrib");
    assert!(
        !is_foundational_axiom(&left_distrib),
        "Rat.left_distrib must stay outside FOUNDATIONAL_AXIOMS after #3656/#3657",
    );
    assert!(
        !ADMITTED_DOMAIN_AXIOMS.contains(&"Rat.left_distrib"),
        "Rat.left_distrib is a deliberately exposed non-foundational, \
         non-admitted trust gap; it must NOT be in ADMITTED_DOMAIN_AXIOMS",
    );

    // WS-A ATOMIC LIVE SWITCH: `Rat.left_distrib` is now a `Constructive`
    // quotient Theorem (no longer an exposed bridge-scoped axiom), so
    // `Rat.mul_sub`, which formerly rested only on it, is now `Constructive`.
    let env = rat_bridge_fallout_env();
    let quality = env
        .proof_quality(&Name::from_string("Rat.mul_sub"))
        .expect("Rat.mul_sub should have a proof quality");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "Rat.mul_sub must now be Constructive (its former dep Rat.left_distrib \
         is a quotient Theorem), got {quality:?}",
    );
}

/// Adversarial control: `Rat.mul_assoc` never needed the temporary bridge, so
/// the rollback fallout MUST NOT contaminate its closure.
#[test]
fn test_rat_mul_assoc_stays_bridge_free_3657() {
    let Some(env) = try_rat_bridge_fallout_env() else {
        eprintln!("SKIP: init_nn_verify_rat_ordering failed upstream");
        return;
    };
    let deps = axiom_dep_names(&env, "Rat.mul_assoc");

    // #3604: both `Nat.mul_assoc` and `Int.mul_assoc` were demoted from
    // `Declaration::Axiom` to constructive `Declaration::Theorem`s (empty
    // closures), so neither surfaces in `Rat.mul_assoc`'s closure. With the
    // last associativity axiom gone, `Rat.mul_assoc` is bridge-free AND
    // domain-axiom-free.
    for forbidden in [
        "Nat.mul_assoc",
        "Int.mul_assoc",
        "Rat.mk_eq_mk_of_cross_eq",
        "Rat.left_distrib",
        "Int.left_distrib",
    ] {
        assert!(
            !deps.contains(forbidden),
            "Rat.mul_assoc must stay bridge-free; unexpected closure member \
             {forbidden} in {deps:?}",
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════
// axiom_deps / trust_marker_deps behavioural tests (#3554)
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_axiom_deps_theorem_reaching_sorry_ax_includes_it() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Register `sorryAx` as an axiom (mirror of how `init_sorry_ax` does it
    // in core/trust.rs).
    let sorry_ax = Declaration::Axiom {
        name: Name::from_string("sorryAx"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(sorry_ax).expect("add sorryAx");

    // A theorem whose proof term is literally `sorryAx`.
    let thm = Declaration::Theorem {
        name: Name::from_string("fake_constructive"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("sorryAx"),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("fake_constructive"))
        .expect("should find declaration");
    assert!(
        deps.contains(&Name::from_string("sorryAx")),
        "axiom_deps MUST include sorryAx (see #3554); got {:?}",
        deps,
    );
}

#[test]
fn test_proof_quality_theorem_reaching_sorry_ax_is_axiom_dependent() {
    // This is the core soundness regression test. Before #3554, a theorem
    // whose proof term referenced `sorryAx` was reported as
    // `ProofQuality::Constructive`. After #3554, it MUST be reported as
    // `ProofQuality::AxiomDependent`.
    let mut env = base_env();
    let prop = Expr::prop();

    let sorry_ax = Declaration::Axiom {
        name: Name::from_string("sorryAx"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(sorry_ax).expect("add sorryAx");

    let thm = Declaration::Theorem {
        name: Name::from_string("fake_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("sorryAx"),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let quality = env
        .proof_quality(&Name::from_string("fake_thm"))
        .expect("should find");
    match quality {
        ProofQuality::AxiomDependent {
            axiom_count,
            axioms,
        } => {
            assert_eq!(axiom_count, 1);
            assert_eq!(axioms[0], Name::from_string("sorryAx"));
        }
        other => panic!(
            "theorem reaching sorryAx must be AxiomDependent, got {:?} (see #3554)",
            other
        ),
    }
}

#[test]
fn test_proof_quality_theorem_reaching_trust_markers_is_axiom_dependent() {
    // All four trust markers should disqualify `Constructive`.
    for marker in &["sorry", "sorryAx", "trustedArith", "trustedAy"] {
        let mut env = base_env();
        let prop = Expr::prop();

        let marker_ax = Declaration::Axiom {
            name: Name::from_string(marker),
            level_params: vec![],
            type_: prop.clone(),
        };
        env.add_decl_structural(marker_ax)
            .expect("add marker axiom");

        let thm_name = format!("thm_via_{marker}");
        let thm = Declaration::Theorem {
            name: Name::from_string(&thm_name),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str(marker),
        };
        env.add_decl_structural(thm).expect("add theorem");

        let quality = env
            .proof_quality(&Name::from_string(&thm_name))
            .expect("should find");
        match quality {
            ProofQuality::AxiomDependent { axioms, .. } => {
                assert!(
                    axioms.iter().any(|a| a == &Name::from_string(marker)),
                    "theorem reaching {marker} must list it as an axiom dep; got {:?}",
                    axioms,
                );
            }
            other => panic!(
                "theorem reaching trust marker {marker} must be AxiomDependent, got {:?} (see #3554)",
                other
            ),
        }
    }
}

#[test]
fn test_trust_marker_deps_returns_only_trust_markers() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Register one trust marker and one regular domain axiom.
    let sorry_ax = Declaration::Axiom {
        name: Name::from_string("sorryAx"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(sorry_ax).expect("add sorryAx");

    let domain_ax = Declaration::Axiom {
        name: Name::from_string("some_domain_axiom"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(domain_ax)
        .expect("add domain axiom");

    // Theorem references both.
    let proof = Expr::app(
        Expr::const_str("sorryAx"),
        Expr::const_str("some_domain_axiom"),
    );
    let thm = Declaration::Theorem {
        name: Name::from_string("both_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: proof,
    };
    env.add_decl_structural(thm).expect("add theorem");

    let all = env
        .axiom_deps(&Name::from_string("both_thm"))
        .expect("should find");
    let trust = env
        .trust_marker_deps(&Name::from_string("both_thm"))
        .expect("should find");

    assert_eq!(all.len(), 2);
    assert!(all.contains(&Name::from_string("sorryAx")));
    assert!(all.contains(&Name::from_string("some_domain_axiom")));

    assert_eq!(trust.len(), 1);
    assert!(trust.contains(&Name::from_string("sorryAx")));
    assert!(!trust.contains(&Name::from_string("some_domain_axiom")));
}

#[test]
fn test_trust_marker_deps_empty_when_no_markers_reached() {
    let mut env = base_env();
    let prop = Expr::prop();

    // Only a plain domain axiom, no trust markers.
    let domain_ax = Declaration::Axiom {
        name: Name::from_string("plain_domain_ax"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(domain_ax).expect("add axiom");

    let thm = Declaration::Theorem {
        name: Name::from_string("plain_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("plain_domain_ax"),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let trust = env
        .trust_marker_deps(&Name::from_string("plain_thm"))
        .expect("should find");
    assert!(
        trust.is_empty(),
        "no trust markers reached; trust_marker_deps should be empty, got {:?}",
        trust,
    );
}

#[test]
fn test_trust_marker_deps_nonexistent_returns_none() {
    let env = base_env();
    assert!(
        env.trust_marker_deps(&Name::from_string("nope")).is_none(),
        "missing declaration should return None"
    );
}

#[test]
fn test_axiom_deps_theorem_reaching_sorry_ax_through_wrapper_includes_it() {
    // Transitive case: theorem -> helper_axiom (type references sorryAx).
    let mut env = base_env();
    let prop = Expr::prop();

    // sorryAx itself.
    let sorry_ax = Declaration::Axiom {
        name: Name::from_string("sorryAx"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(sorry_ax).expect("add sorryAx");

    // helper_axiom whose type mentions sorryAx.
    let helper_type = Expr::arrow(Expr::const_str("sorryAx"), prop.clone());
    let helper = Declaration::Axiom {
        name: Name::from_string("helper_axiom"),
        level_params: vec![],
        type_: helper_type,
    };
    env.add_decl_structural(helper).expect("add helper");

    // Theorem referencing helper_axiom.
    let thm = Declaration::Theorem {
        name: Name::from_string("transitive_thm"),
        level_params: vec![],
        type_: prop.clone(),
        value: Expr::const_str("helper_axiom"),
    };
    env.add_decl_structural(thm).expect("add theorem");

    let deps = env
        .axiom_deps(&Name::from_string("transitive_thm"))
        .expect("should find");
    // Both `helper_axiom` (domain) and `sorryAx` (trust marker) must
    // appear in the transitive closure.
    assert!(deps.contains(&Name::from_string("helper_axiom")));
    assert!(
        deps.contains(&Name::from_string("sorryAx")),
        "transitive reach of sorryAx must appear in axiom_deps (see #3554)"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// FOUNDATIONAL_AXIOMS / Declaration::Theorem disjointness (#3559)
//
// Any name that is registered as `Declaration::Theorem` with a genuine proof
// term MUST NOT also appear in `FOUNDATIONAL_AXIOMS`. The whitelist is only
// consulted by `axiom_deps`' BFS when `kind == ConstantKind::Axiom`, so a
// whitelist entry for a Theorem is dead code — but it also creates a silent
// "safety net" that would mask a demotion regression (Theorem -> Axiom). This
// test pins the disjointness invariant.
// ════════════════════════════════════════════════════════════════════════════

/// Regression test for #3559: every name in `FOUNDATIONAL_AXIOMS` MUST NOT be
/// registered as `Declaration::Theorem` in an environment initialized to
/// populate the full Rat ordered-field / Nat / Fin whitelist population.
///
/// This guards against the scenario where a name is promoted from
/// `Declaration::Axiom` to `Declaration::Theorem` (e.g. #3537, #3538) but its
/// stale whitelist entry is left behind. Such an entry is dead today (BFS
/// short-circuits on `kind == Axiom`), but it would silently accept the
/// regression if someone demoted the Theorem back to an Axiom in the future.
#[test]
fn test_foundational_axioms_disjoint_from_theorems() {
    use super::axiom_audit::FOUNDATIONAL_AXIOMS;

    // Initialize an environment populated with the init chains that register
    // every name currently in FOUNDATIONAL_AXIOMS. `init_nn_verify_interval_arith_proofs`
    // transitively pulls in init_rat_linear_order (#3470 Lane #2/#3: Rat.le_refl,
    // Rat.le_total, Rat.lt_iff_le_not_le are now Theorems via
    // register_rat_order_proofs; Rat.le_trans is now ALSO a Theorem (soundness
    // fix — it was a FALSE axiom — via register_rat_le_trans_proof over the
    // effective-denominator Rat.le); Rat.le_antisymm remains an axiom),
    // init_rat_ordered_field_axioms (Rat.add_le_add_left,
    // Rat.le_add_of_nonneg_right; Rat.mul_pos, Rat.zero_lt_one, and
    // Rat.mul_nonneg are now Theorems via register_rat_order_proofs —
    // Rat.mul_nonneg eliminated as the Rat.le analog of Rat.mul_pos),
    // init_rat_field_inst (Rat.add_assoc/add_comm/..., Rat.mul_assoc/..., etc.),
    // init_rat_minmax (Rat.max/min/max_def/...), init_nn_verify_rat_ordering
    // (Rat.add_neg_self, Rat.mul_neg), and register_rat_add_le_add /
    // register_rat_neg_le_neg / register_rat_sub_le_sub (the three now-Theorem names).
    // We additionally call init_nat_preorder (Nat.le_refl) and init_fin_sum
    // (Fin.castSucc, Fin.last) to cover the non-Rat whitelist entries.
    let mut env = Environment::new();
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");
    env.init_nat_preorder().expect("init_nat_preorder");
    env.init_fin_sum().expect("init_fin_sum");

    let mut violations: Vec<String> = Vec::new();
    for &foundational_name in FOUNDATIONAL_AXIOMS {
        // Skip names not (yet) registered in this init chain. The invariant
        // only applies to names that actually appear in the environment.
        let Some(info) = env.get_const(&Name::from_string(foundational_name)) else {
            continue;
        };
        if info.kind == ConstantKind::Theorem {
            violations.push(foundational_name.to_string());
        }
    }

    assert!(
        violations.is_empty(),
        "FOUNDATIONAL_AXIOMS contains names registered as Declaration::Theorem: \
         {violations:?}. Whitelist entries for Theorems are dead code (the \
         axiom_deps BFS short-circuits on kind == Axiom) and would silently \
         mask a demotion regression. Remove these entries from \
         FOUNDATIONAL_AXIOMS in crates/clean-kernel/src/env/axiom_audit.rs. \
         See #3559."
    );
}

/// #3559: the three promoted names (`Rat.add_le_add` #3537, `Rat.neg_le_neg`
/// #3538, `Rat.sub_le_sub` #3539) must be registered as `Declaration::Theorem`
/// in the init'd environment. This is the positive half of the disjointness
/// invariant: if any of these is ever silently demoted back to
/// `Declaration::Axiom`, the `is_foundational_axiom` whitelist could mask
/// the regression. Pinning the Theorem kind here catches the demotion before
/// the classifier accepts it.
#[test]
fn test_promoted_theorems_are_not_foundational_and_are_theorems() {
    use super::axiom_audit::is_foundational_axiom;

    let mut env = Environment::new();
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");

    // NOTE (#3581 Phase 2): Extended the promoted-theorem roster with the
    // four Tranche B identities registered by
    // `algebra_rat_tranche_b_proofs.rs` (plus the Phase 1 `Rat.inv_zero`).
    // These must all be Declaration::Theorem AND absent from
    // FOUNDATIONAL_AXIOMS per the #3559 disjointness rule.
    for name in &[
        "Rat.add_le_add",
        "Rat.neg_le_neg",
        "Rat.sub_le_sub",
        "Rat.inv_zero",
        "Rat.zero_add",
        "Rat.add_zero",
        "Rat.one_mul",
        "Rat.mul_one",
        // #3470 Lane #2/#3: the genuinely-eliminated Rat ordering lemmas
        // (`Rat.mul_pos` and `Rat.mul_neg` are also now Theorems).
        "Rat.le_refl",
        "Rat.le_total",
        "Rat.zero_lt_one",
        "Rat.lt_iff_le_not_le",
        "Rat.mul_pos",
        "Rat.mul_neg",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be Declaration::Theorem (promoted by #3537/#3538/#3539/#3572/#3581), got {:?}",
            info.kind
        );
        assert!(
            !is_foundational_axiom(&n),
            "{name} was promoted to Declaration::Theorem and must NOT appear \
             in FOUNDATIONAL_AXIOMS (see #3559)"
        );
    }
}

/// `funext` is now a kernel-checked `Declaration::Theorem` derived from
/// `Quot.sound` (Lean 4 core construction — see `Environment::init_funext`).
/// This is the positive half of the #3559 disjointness invariant for funext:
///   1. funext is registered with `kind == Theorem` (not Axiom).
///   2. funext is NOT in `FOUNDATIONAL_AXIOMS` (would be dead-code masking).
///   3. funext's transitive axiom closure reaches `Quot.sound` (still
///      foundational), so `proof_quality(funext) == Constructive`.
///
/// If a future change ever silently demotes funext back to an Axiom or breaks
/// the proof, this pin fails before the classifier can misreport it.
#[test]
fn test_funext_is_proved_from_quot_sound_not_foundational() {
    use super::axiom_audit::is_foundational_axiom;

    let mut env = Environment::new();
    env.init_funext().expect("init_funext should succeed");

    let n = Name::from_string("funext");
    let info = env.get_const(&n).expect("funext should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "funext must be a Declaration::Theorem derived from Quot.sound, got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "funext must carry a kernel-checked proof value"
    );
    assert!(
        !is_foundational_axiom(&n),
        "funext is now a Theorem and must NOT appear in FOUNDATIONAL_AXIOMS (#3559)"
    );

    // Its transitive axiom closure should be ⊆ FOUNDATIONAL_AXIOMS (it reaches
    // Quot.sound, which is foundational), so it is Constructive — the
    // `axiom_deps` BFS filters foundational names, leaving an empty domain set.
    let deps = env.axiom_deps(&n).expect("funext should have a closure");
    assert!(
        deps.is_empty(),
        "funext's domain-axiom closure should be empty (only Quot.sound, \
         which is foundational), got: {deps:?}"
    );
    let quality = env
        .proof_quality(&n)
        .expect("funext proof_quality should resolve");
    assert_eq!(
        quality,
        ProofQuality::Constructive,
        "funext is proved from foundational Quot.sound, so it is Constructive"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// #3554 task-brief pinning tests (follow-up)
//
// These mirror the exact wording of the #3554 task brief: "a theorem
// transitively using `sorryAx` is NOT classified as `Constructive`, and
// `is_trust_marker("sorryAx") == true`". The behaviour is already covered by
// `test_is_trust_marker_recognizes_all_four` and
// `test_proof_quality_theorem_reaching_sorry_ax_is_axiom_dependent`, but the
// task brief asks for assertions phrased in a 1:1 way so future auditors can
// grep for them under the #3554 anchor. Keeping both the broad-coverage and
// the explicit-phrasing variants preserves the regression guard in two
// independent places (belt-and-suspenders — same pattern as
// `test_is_foundational_axiom_rejects_every_trust_marker_3554` vs
// `test_sorry_ax_is_not_foundational`).
// ════════════════════════════════════════════════════════════════════════════

/// Task-brief pin: `is_trust_marker("sorryAx") == true`.
///
/// Direct 1:1 transcription of the task-brief assertion. Catches a future
/// refactor that accidentally renames `sorryAx` inside `TRUST_MARKERS` or
/// changes the `is_trust_marker` string-matching logic.
#[test]
fn test_is_trust_marker_sorry_ax_is_true_3554() {
    assert!(
        is_trust_marker(&Name::from_string("sorryAx")),
        "is_trust_marker(\"sorryAx\") must return true (#3554 task brief)",
    );
}

/// Helper: build a 2-hop transitive chain `thm -> helper_B -> helper_A -> sorryAx`.
///
/// Chain layout:
/// ```text
///   thm_name   -->  helper_B_3554  (Axiom whose TYPE mentions helper_A)
///   helper_B   -->  helper_A_3554  (Axiom whose TYPE mentions sorryAx)
///   helper_A   -->  sorryAx        (TRUST_MARKERS)
/// ```
///
/// Returns the populated environment plus the theorem name. Shared between the
/// three #3554 task-brief sub-tests below to keep each one under the 80-line
/// function-size hook limit.
fn build_sorry_ax_transitive_env(thm_name: &str) -> (Environment, Name) {
    let mut env = base_env();
    let prop = Expr::prop();

    let sorry_ax = Declaration::Axiom {
        name: Name::from_string("sorryAx"),
        level_params: vec![],
        type_: prop.clone(),
    };
    env.add_decl_structural(sorry_ax).expect("add sorryAx");

    let helper_a = Declaration::Axiom {
        name: Name::from_string("helper_A_3554"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_str("sorryAx"), prop.clone()),
    };
    env.add_decl_structural(helper_a).expect("add helper_A");

    let helper_b = Declaration::Axiom {
        name: Name::from_string("helper_B_3554"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_str("helper_A_3554"), prop.clone()),
    };
    env.add_decl_structural(helper_b).expect("add helper_B");

    let name = Name::from_string(thm_name);
    let thm = Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: prop,
        value: Expr::const_str("helper_B_3554"),
    };
    env.add_decl_structural(thm).expect("add transitive_thm");

    (env, name)
}

/// Task-brief pin (step 1): `axiom_deps` must surface `sorryAx` through the
/// 2-hop helper chain. Pre-#3554 this returned a set without `sorryAx` because
/// `sorryAx` was whitelisted as foundational.
#[test]
fn test_transitive_axiom_deps_contains_sorry_ax_3554() {
    let (env, name) = build_sorry_ax_transitive_env("transitive_thm_3554_step1");
    let deps = env.axiom_deps(&name).expect("should find declaration");
    assert!(
        deps.contains(&Name::from_string("sorryAx")),
        "2-hop transitive reach of sorryAx must appear in axiom_deps (#3554); got {:?}",
        deps,
    );
}

/// Task-brief pin (step 2): `proof_quality` for a theorem transitively using
/// `sorryAx` must be `AxiomDependent` (NOT `Constructive`). This is the core
/// soundness guarantee of #3554.
#[test]
fn test_transitive_sorry_ax_theorem_is_not_constructive_3554() {
    let (env, name) = build_sorry_ax_transitive_env("transitive_thm_3554_step2");
    let quality = env.proof_quality(&name).expect("should find");
    assert_ne!(
        quality,
        ProofQuality::Constructive,
        "theorem transitively using sorryAx must NOT be Constructive (#3554 task brief)",
    );
    match quality {
        ProofQuality::AxiomDependent { axioms, .. } => {
            assert!(
                axioms.iter().any(|a| a == &Name::from_string("sorryAx")),
                "AxiomDependent.axioms must list sorryAx (#3554); got {:?}",
                axioms,
            );
        }
        other => panic!(
            "expected AxiomDependent with sorryAx in the axiom list, got {:?} (#3554)",
            other
        ),
    }
}

/// Task-brief pin (step 3): `trust_marker_deps` must isolate `sorryAx` from
/// `helper_A` / `helper_B`. Ensures the trust-marker filter is narrower than
/// the full domain-axiom set.
#[test]
fn test_transitive_trust_marker_deps_isolates_sorry_ax_3554() {
    let (env, name) = build_sorry_ax_transitive_env("transitive_thm_3554_step3");
    let trust = env.trust_marker_deps(&name).expect("should find");
    assert_eq!(
        trust.len(),
        1,
        "only sorryAx should appear in trust_marker_deps; got {:?}",
        trust,
    );
    assert!(
        trust.contains(&Name::from_string("sorryAx")),
        "trust_marker_deps must contain sorryAx (#3554)",
    );
}
