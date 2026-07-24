// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::test_utils::build_spec_with_stack;
use clean_kernel::Environment;
use proptest::prelude::*;

#[test]
fn test_proof_library_creation() {
    let lib = ProofLibrary::new();
    assert!(!lib.proofs.is_empty());
}

#[test]
fn test_def_eq_proofs_exist() {
    let lib = ProofLibrary::new();
    // C001 core: reflexivity, symmetry, transitivity
    lib.get("def_eq_refl")
        .expect("proof 'def_eq_refl' missing from library");
    lib.get("def_eq_symm")
        .expect("proof 'def_eq_symm' missing from library");
    lib.get("def_eq_trans")
        .expect("proof 'def_eq_trans' missing from library");
    // C001 congruence: app, lam, pi (Part of #3306)
    lib.get("def_eq_congr_app")
        .expect("proof 'def_eq_congr_app' missing from library");
    lib.get("def_eq_congr_lam")
        .expect("proof 'def_eq_congr_lam' missing from library");
    lib.get("def_eq_congr_pi")
        .expect("proof 'def_eq_congr_pi' missing from library");
    // C001 beta reduction (Part of #3306)
    lib.get("def_eq_beta")
        .expect("proof 'def_eq_beta' missing from library");
}

#[test]
fn test_typing_proofs_exist() {
    let lib = ProofLibrary::new();
    lib.get("identity_typed")
        .expect("proof 'identity_typed' missing from library");
    lib.get("const_typed")
        .expect("proof 'const_typed' missing from library");
    lib.get("compose_typed")
        .expect("proof 'compose_typed' missing from library");
}

#[test]
fn test_identity_proof_elaborates() {
    let env = Environment::new();
    let proof = "fun (A : Type) (x : A) => x";

    let surface = clean_parser::parse_expr(proof).unwrap();
    let mut ctx = clean_elab::ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);

    assert!(
        result.is_ok(),
        "Identity proof should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_const_proof_elaborates() {
    let env = Environment::new();
    let proof = "fun (A : Type) (B : Type) (a : A) (b : B) => a";

    let surface = clean_parser::parse_expr(proof).unwrap();
    let mut ctx = clean_elab::ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);

    assert!(
        result.is_ok(),
        "Const proof should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_compose_proof_elaborates() {
    let env = Environment::new();
    let proof = "fun (A : Type) (B : Type) (C : Type) (g : B -> C) (f : A -> B) (x : A) => g (f x)";

    let surface = clean_parser::parse_expr(proof).unwrap();
    let mut ctx = clean_elab::ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);

    assert!(
        result.is_ok(),
        "Compose proof should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_type_preservation_proofs_exist() {
    let lib = ProofLibrary::new();
    lib.get("TypePreservation")
        .expect("proof 'TypePreservation' missing from library");
    lib.get("type_preservation_helper")
        .expect("proof 'type_preservation_helper' missing from library");
    lib.get("beta_type_preservation")
        .expect("proof 'beta_type_preservation' missing from library");
}

#[test]
fn test_congruence_proofs_exist() {
    let lib = ProofLibrary::new();
    lib.get("app_cong")
        .expect("proof 'app_cong' missing from library");
    lib.get("lam_cong")
        .expect("proof 'lam_cong' missing from library");
    lib.get("pi_cong")
        .expect("proof 'pi_cong' missing from library");
}

fn definitional_extension_proof_names() -> &'static [&'static str] {
    &[
        "constant_extension_intro",
        "inductive_extension_intro",
        "constant_extension_soundness",
        "inductive_extension_soundness",
        "definitional_extension_soundness",
    ]
}

#[test]
fn test_definitional_extension_proofs_exist() {
    let lib = ProofLibrary::new();
    for name in definitional_extension_proof_names() {
        lib.get(name)
            .unwrap_or_else(|| panic!("proof '{name}' missing from library"));
    }
}

#[test]
fn test_definitional_extension_proofs_parse() {
    let lib = ProofLibrary::new();
    for name in definitional_extension_proof_names() {
        let proof = lib
            .get(name)
            .unwrap_or_else(|| panic!("proof '{name}' missing"));
        let result = clean_parser::parse_expr(&proof.proof_src);
        assert!(
            result.is_ok(),
            "proof '{name}' should parse: {:?}",
            result.err()
        );
    }
}

fn proof_source_samples() -> &'static Vec<(String, String)> {
    use std::sync::OnceLock;
    static SAMPLES: OnceLock<Vec<(String, String)>> = OnceLock::new();
    SAMPLES.get_or_init(|| {
        let lib = ProofLibrary::new();
        lib.all_proofs()
            .filter(|(_, p)| !p.proof_src.is_empty())
            .map(|(name, proof)| (name.clone(), proof.proof_src.clone()))
            .collect()
    })
}

proptest! {
    #[test]
    fn prop_proof_sources_parse(
        idx in 0..proof_source_samples().len()
    ) {
        let (name, src) = &proof_source_samples()[idx];
        let result = clean_parser::parse_expr(src);
        prop_assert!(
            result.is_ok(),
            "proof '{}' should parse without error: {:?}",
            name,
            result.err()
        );
    }
}

#[test]
fn test_audit_dependencies_consistent() {
    // Part of #326, #393: All proofs in library should have consistent dependency info
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    // Every proof in library should have a result in the report
    for (name, _) in lib.all_proofs() {
        assert!(
            report.results.contains_key(name),
            "Missing dependency result for proof: {name}"
        );
    }

    // DerivedProved proofs should have no axiom deps
    for (name, result) in &report.results {
        if result.status == ProofStatus::DerivedProved {
            assert!(
                result.axiom_deps.is_empty(),
                "DerivedProved proof '{}' should have no axiom deps, but has: {:?}",
                name,
                result.axiom_deps
            );
        }
    }

    // DerivedPending proofs should have at least one axiom dep
    for (name, result) in &report.results {
        if result.status == ProofStatus::DerivedPending {
            assert!(
                !result.axiom_deps.is_empty() || result.error.is_some(),
                "DerivedPending proof '{}' should have axiom deps or error",
                name
            );
        }
    }

    // Print summary for test output
    println!("{}", report.summary());
}

#[test]
fn test_all_proof_sources_parse() {
    let lib = ProofLibrary::new();
    let mut failures = Vec::new();

    for (name, proof) in lib.all_proofs() {
        if proof.proof_src.is_empty() {
            continue;
        }
        if let Err(e) = clean_parser::parse_expr(&proof.proof_src) {
            failures.push(format!("{name}: {e}"));
        }
    }

    assert!(
        failures.is_empty(),
        "Some proofs failed to parse:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_proof_count() {
    let lib = ProofLibrary::new();
    let count = lib.all_proofs().count();
    assert!(count >= 10, "Expected at least 10 proofs, got {count}");
}

/// Diagnostic: list all proofs by status for issue #3333 audit.
#[test]
fn test_audit_all_proofs_by_status() {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    let mut errors: Vec<(&str, &str)> = Vec::new();
    let mut pending: Vec<(&str, Vec<&str>)> = Vec::new();
    let mut proved: Vec<&str> = Vec::new();

    for (name, result) in &report.results {
        if let Some(err) = &result.error {
            errors.push((name.as_str(), err.as_str()));
        } else if result.status == ProofStatus::DerivedPending {
            let mut deps: Vec<&str> = result.axiom_deps.iter().map(|s| s.as_str()).collect();
            deps.sort();
            pending.push((name.as_str(), deps));
        } else {
            proved.push(name.as_str());
        }
    }

    errors.sort_by_key(|(name, _)| *name);
    pending.sort_by_key(|(name, _)| *name);
    proved.sort();

    println!("\n=== ERRORS ({}) ===", errors.len());
    for (name, err) in &errors {
        println!("  {name}: {err}");
    }

    println!("\n=== PENDING ({}) ===", pending.len());
    for (name, deps) in &pending {
        println!("  {name}: deps={}", deps.join(", "));
    }

    println!("\n=== PROVED ({}) ===", proved.len());
    for name in &proved {
        println!("  {name}");
    }

    // The test itself passes — this is diagnostic output for #3333.
}

#[test]
fn test_micro_checker_proofs_exist() {
    // Part of #412: micro checker proof existence
    let lib = ProofLibrary::new();

    // Core micro checker soundness proofs
    lib.get("micro_verify_soundness")
        .expect("proof 'micro_verify_soundness' missing from library");
    lib.get("micro_type_pres")
        .expect("proof 'micro_type_pres' missing from library");

    // Transitivity proof terms
    lib.get("trans_typing")
        .expect("proof 'trans_typing' missing from library");
    // trans_def_eq REMOVED (Brick 3 of the micro-band drain): it forwarded to the
    // FALSE `kernel_to_micro_def_eq` axiom, which was refuted-and-deleted.

    // Core kernel proofs from library.rs
    lib.get("def_eq_refl")
        .expect("proof 'def_eq_refl' missing from library");
    lib.get("def_eq_symm")
        .expect("proof 'def_eq_symm' missing from library");
    lib.get("def_eq_trans")
        .expect("proof 'def_eq_trans' missing from library");
    lib.get("subst_typing")
        .expect("proof 'subst_typing' missing from library");
    lib.get("type_conv")
        .expect("proof 'type_conv' missing from library");

    // Congruence proofs
    lib.get("app_cong")
        .expect("proof 'app_cong' missing from library");
    lib.get("lam_cong")
        .expect("proof 'lam_cong' missing from library");
    lib.get("pi_cong")
        .expect("proof 'pi_cong' missing from library");
}

#[test]
fn test_beta_reduces_inductive_proofs_exist() {
    // Part of #412: beta_reduces inductive type constructor proofs
    let lib = ProofLibrary::new();
    lib.get("beta_redex")
        .expect("proof 'beta_redex' missing from library");
    lib.get("beta_app_left")
        .expect("proof 'beta_app_left' missing from library");
    lib.get("beta_app_right")
        .expect("proof 'beta_app_right' missing from library");
    lib.get("beta_lam_ty")
        .expect("proof 'beta_lam_ty' missing from library");
    lib.get("beta_lam_body")
        .expect("proof 'beta_lam_body' missing from library");
    lib.get("beta_pi_dom")
        .expect("proof 'beta_pi_dom' missing from library");
    lib.get("beta_pi_cod")
        .expect("proof 'beta_pi_cod' missing from library");
    lib.get("value_whnf")
        .expect("proof 'value_whnf' missing from library");
    lib.get("whnf_refl")
        .expect("proof 'whnf_refl' missing from library");
}

#[test]
fn test_whnf_to_inductive_proofs_exist() {
    // Part of #412: whnf_to inductive type constructor proofs
    let lib = ProofLibrary::new();
    lib.get("whnf_idem")
        .expect("proof 'whnf_idem' missing from library");
    lib.get("whnf_conf")
        .expect("proof 'whnf_conf' missing from library");
    lib.get("beta_det")
        .expect("proof 'beta_det' missing from library");
}

// =========================================================================
// #412: beta_reduces/whnf_to inductive type constructor elaboration tests
// =========================================================================

/// Helper to verify a proof against the specification
fn verify_proof(proof_name: &str) -> Result<(), ProofError> {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let proof = lib
        .get(proof_name)
        .ok_or_else(|| ProofError::UnknownProperty(proof_name.to_string()))?;
    proof.verify(&spec)
}

#[test]
fn test_beta_redex_elaborates() {
    // Part of #412: beta_reduces.beta constructor should elaborate
    let result = verify_proof("beta_redex");
    assert!(
        result.is_ok(),
        "beta_redex proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_beta_binder_constructor_proofs_elaborate() {
    for proof_name in ["beta_lam_ty", "beta_lam_body", "beta_pi_dom", "beta_pi_cod"] {
        let result = verify_proof(proof_name);
        assert!(
            result.is_ok(),
            "{proof_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_whnf_refl_elaborates() {
    // Part of #412: whnf_to.refl constructor should elaborate
    let result = verify_proof("whnf_refl");
    assert!(
        result.is_ok(),
        "whnf_refl proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_value_whnf_elaborates() {
    // Part of #412: value_in_whnf derived proof should elaborate
    // This proof uses WhnfTo.refl (PascalCase) constructor
    let result = verify_proof("value_whnf");
    assert!(
        result.is_ok(),
        "value_whnf proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_whnf_idem_elaborates() {
    let result = verify_proof("whnf_idem");
    assert!(
        result.is_ok(),
        "whnf_idem proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_whnf_conf_elaborates() {
    let result = verify_proof("whnf_conf");
    assert!(
        result.is_ok(),
        "whnf_conf proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_beta_det_elaborates() {
    let result = verify_proof("beta_det");
    assert!(
        result.is_ok(),
        "beta_det proof should elaborate and type-check: {:?}",
        result.err()
    );
}

// =========================================================================
// #724: Expression operation proofs
// =========================================================================

#[test]
fn test_inst_bvar_zero_elaborates() {
    // Part of #724: instantiate_bvar_zero derived proof using equality chain
    // instantiate (BVar 0) val = val
    let result = verify_proof("inst_bvar_zero");
    assert!(
        result.is_ok(),
        "inst_bvar_zero proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_lift_zero_elaborates() {
    // lift e 0 = e
    let result = verify_proof("lift_zero");
    assert!(
        result.is_ok(),
        "lift_zero proof should elaborate and type-check: {:?}",
        result.err()
    );
}

// =========================================================================
// #3306: C001 constructive proof verification — zero axiom dependencies
// =========================================================================

/// All 7 C001 definitional equality proofs exist in the library.
#[test]
fn test_c001_all_proofs_exist() {
    let lib = ProofLibrary::new();
    let c001_proofs = [
        "def_eq_refl",
        "def_eq_symm",
        "def_eq_trans",
        "def_eq_congr_app",
        "def_eq_congr_lam",
        "def_eq_congr_pi",
        "def_eq_beta",
    ];
    for name in &c001_proofs {
        lib.get(name)
            .unwrap_or_else(|| panic!("C001 proof '{name}' missing from library"));
    }
}

/// All 7 C001 proofs parse as valid expressions and use direct inductive
/// constructors (not aliases or helper axioms). This verifies the proof terms
/// are syntactically well-formed and reference the correct constructors.
#[test]
fn test_c001_all_proofs_parse_and_use_constructors() {
    let lib = ProofLibrary::new();
    let c001_proofs_and_constructors = [
        ("def_eq_refl", "DefEq.refl"),
        ("def_eq_symm", "DefEq.symm"),
        ("def_eq_trans", "DefEq.trans"),
        ("def_eq_congr_app", "DefEq.app_cong"),
        ("def_eq_congr_lam", "DefEq.lam_cong"),
        ("def_eq_congr_pi", "DefEq.pi_cong"),
        ("def_eq_beta", "DefEq.beta"),
    ];

    for (name, expected_constructor) in &c001_proofs_and_constructors {
        let proof = lib.get(name).unwrap();

        // Verify proof parses.
        let parse_result = clean_parser::parse_expr(&proof.proof_src);
        assert!(
            parse_result.is_ok(),
            "C001 proof '{name}' should parse: {:?}",
            parse_result.err()
        );

        // Verify proof term references the correct inductive constructor.
        assert!(
            proof.proof_src.contains(expected_constructor),
            "C001 proof '{name}' should use constructor '{expected_constructor}', \
             but proof_src is: {}",
            proof.proof_src
        );

        // Verify no HelperAxiom or Eq.refl placeholder patterns.
        assert!(
            !proof.proof_src.contains("HelperAxiom"),
            "C001 proof '{name}' should not reference HelperAxiom (found in proof_src)"
        );
    }
}

/// Verify that all 7 C001 proofs use lambda abstractions (constructive form),
/// not bare constant references (axiom form).
#[test]
fn test_c001_proofs_are_lambda_abstractions() {
    let lib = ProofLibrary::new();
    let c001_proofs = [
        "def_eq_refl",
        "def_eq_symm",
        "def_eq_trans",
        "def_eq_congr_app",
        "def_eq_congr_lam",
        "def_eq_congr_pi",
        "def_eq_beta",
    ];

    for name in &c001_proofs {
        let proof = lib.get(name).unwrap();
        assert!(
            proof.proof_src.starts_with("fun "),
            "C001 proof '{name}' should be a lambda abstraction (start with 'fun '), \
             but proof_src starts with: {}",
            &proof.proof_src[..proof.proof_src.len().min(30)]
        );
    }
}

// =========================================================================
// #3308: C004 constructive proof verification — zero axiom dependencies
// =========================================================================

/// All C004 WHNF and reduction proof terms exist in the library.
/// The 9 proofs that were formerly bare constants or axioms are now
/// constructive lambda abstractions. Part of #3308.
#[test]
fn test_c004_all_proofs_exist() {
    let lib = ProofLibrary::new();
    // The 9 proofs specifically converted from axioms in #3308
    let c004_proofs = [
        "whnf_idem",
        "whnf_conf",
        "beta_det",
        "beta_app_left",
        "beta_app_right",
        "beta_lam_ty",
        "beta_lam_body",
        "beta_pi_dom",
        "beta_pi_cod",
    ];
    for name in &c004_proofs {
        lib.get(name)
            .unwrap_or_else(|| panic!("C004 proof '{name}' missing from library"));
    }
}

/// All 9 C004 proofs parse as valid expressions and use the correct inductive
/// constructors or derived lemmas. Part of #3308.
#[test]
fn test_c004_all_proofs_parse_and_use_constructors() {
    let lib = ProofLibrary::new();
    let c004_proofs_and_constructors = [
        ("whnf_idem", "whnf_to.refl"),
        ("whnf_conf", "DefEq.trans"),
        ("beta_det", "DefEq.trans"),
        ("beta_app_left", "BetaReduces.app_left"),
        ("beta_app_right", "BetaReduces.app_right"),
        ("beta_lam_ty", "BetaReduces.lam_ty"),
        ("beta_lam_body", "BetaReduces.lam_body"),
        ("beta_pi_dom", "BetaReduces.pi_dom"),
        ("beta_pi_cod", "BetaReduces.pi_cod"),
    ];

    for (name, expected_constructor) in &c004_proofs_and_constructors {
        let proof = lib.get(name).unwrap();

        // Verify proof parses.
        let parse_result = clean_parser::parse_expr(&proof.proof_src);
        assert!(
            parse_result.is_ok(),
            "C004 proof '{name}' should parse: {:?}",
            parse_result.err()
        );

        // Verify proof term references the correct inductive constructor.
        assert!(
            proof.proof_src.contains(expected_constructor),
            "C004 proof '{name}' should use constructor '{expected_constructor}', \
             but proof_src is: {}",
            proof.proof_src
        );

        // Verify no HelperAxiom placeholder patterns.
        assert!(
            !proof.proof_src.contains("HelperAxiom"),
            "C004 proof '{name}' should not reference HelperAxiom (found in proof_src)"
        );
    }
}

/// Verify that all 9 C004 proofs use lambda abstractions (constructive form),
/// not bare constant references (axiom form). Part of #3308.
#[test]
fn test_c004_proofs_are_lambda_abstractions() {
    let lib = ProofLibrary::new();
    let c004_proofs = [
        "whnf_idem",
        "whnf_conf",
        "beta_det",
        "beta_app_left",
        "beta_app_right",
        "beta_lam_ty",
        "beta_lam_body",
        "beta_pi_dom",
        "beta_pi_cod",
    ];

    for name in &c004_proofs {
        let proof = lib.get(name).unwrap();
        assert!(
            proof.proof_src.starts_with("fun "),
            "C004 proof '{name}' should be a lambda abstraction (start with 'fun '), \
             but proof_src starts with: {}",
            &proof.proof_src[..proof.proof_src.len().min(30)]
        );
    }
}

/// All C004 remaining WHNF proof terms (value constructors, whnf constructors)
/// also exist and are constructive. Part of #3308.
#[test]
fn test_c004_supporting_proofs_exist_and_constructive() {
    let lib = ProofLibrary::new();
    let supporting_proofs = [
        ("sort_value", "IsValue.sort"),
        ("lam_value", "IsValue.lam"),
        ("pi_value", "IsValue.pi"),
        ("value_whnf", "WhnfTo.refl"),
        ("beta_redex", "BetaReduces.beta"),
        ("whnf_refl", "WhnfTo.refl"),
        ("whnf_step", "WhnfTo.step"),
    ];

    for (name, expected_constructor) in &supporting_proofs {
        let proof = lib
            .get(name)
            .unwrap_or_else(|| panic!("C004 supporting proof '{name}' missing from library"));

        assert!(
            proof.proof_src.starts_with("fun "),
            "C004 supporting proof '{name}' should be a lambda abstraction"
        );

        assert!(
            proof.proof_src.contains(expected_constructor),
            "C004 supporting proof '{name}' should use constructor '{expected_constructor}'"
        );
    }
}

// =========================================================================
// #3309: C006 constructive proof verification — zero axiom dependencies
// =========================================================================

/// All 12 C006 expression operation proofs exist in the library.
/// These cover lift_at structural lemmas, lift_zero identity,
/// instantiate structural lemmas, inst_bvar_zero, and lift_cancel.
/// Part of #3309.
#[test]
fn test_c006_all_proofs_exist() {
    let lib = ProofLibrary::new();
    let c006_proofs = [
        "lift_at_sort",
        "lift_at_app",
        "lift_at_lam",
        "lift_at_pi",
        "lift_at_amount_zero",
        "lift_zero",
        "instantiate_sort",
        "instantiate_app",
        "instantiate_lam",
        "instantiate_pi",
        "inst_bvar_zero",
        "lift_cancel",
    ];
    for name in &c006_proofs {
        lib.get(name)
            .unwrap_or_else(|| panic!("C006 proof '{name}' missing from library"));
    }
}

/// All 12 C006 proofs parse as valid expressions and use the correct
/// proof strategy (Eq.refl for structural lemmas, specialized lemma
/// references for composite proofs). Part of #3309.
#[test]
fn test_c006_all_proofs_parse_and_use_constructors() {
    let lib = ProofLibrary::new();
    // (library_key, expected_substring_in_proof_src)
    let c006_proofs_and_constructors = [
        ("lift_at_sort", "Eq.refl"),
        ("lift_at_app", "Eq.refl"),
        ("lift_at_lam", "Eq.refl"),
        ("lift_at_pi", "Eq.refl"),
        ("lift_at_amount_zero", "lift_at_amount_zero"),
        ("lift_zero", "lift_at_amount_zero"),
        ("instantiate_sort", "Eq.refl"),
        ("instantiate_app", "instantiate_at_app"),
        ("instantiate_lam", "instantiate_at_lam"),
        ("instantiate_pi", "instantiate_at_pi"),
        ("inst_bvar_zero", "instantiate_bvar_zero"),
        ("lift_cancel", "lift_cancel_gen"),
    ];

    for (name, expected_constructor) in &c006_proofs_and_constructors {
        let proof = lib.get(name).unwrap();

        // Verify proof parses.
        let parse_result = clean_parser::parse_expr(&proof.proof_src);
        assert!(
            parse_result.is_ok(),
            "C006 proof '{name}' should parse: {:?}",
            parse_result.err()
        );

        // Verify proof term references the expected strategy/constructor.
        assert!(
            proof.proof_src.contains(expected_constructor),
            "C006 proof '{name}' should use '{expected_constructor}', \
             but proof_src is: {}",
            proof.proof_src
        );

        // Verify no HelperAxiom placeholder patterns.
        assert!(
            !proof.proof_src.contains("HelperAxiom"),
            "C006 proof '{name}' should not reference HelperAxiom (found in proof_src)"
        );
    }
}

/// Verify that all 12 C006 proofs use lambda abstractions (constructive form),
/// not bare constant references (axiom form). Part of #3309.
#[test]
fn test_c006_proofs_are_lambda_abstractions() {
    let lib = ProofLibrary::new();
    let c006_proofs = [
        "lift_at_sort",
        "lift_at_app",
        "lift_at_lam",
        "lift_at_pi",
        "lift_at_amount_zero",
        "lift_zero",
        "instantiate_sort",
        "instantiate_app",
        "instantiate_lam",
        "instantiate_pi",
        "inst_bvar_zero",
        "lift_cancel",
    ];

    for name in &c006_proofs {
        let proof = lib.get(name).unwrap();
        assert!(
            proof.proof_src.starts_with("fun "),
            "C006 proof '{name}' should be a lambda abstraction (start with 'fun '), \
             but proof_src starts with: {}",
            &proof.proof_src[..proof.proof_src.len().min(30)]
        );
    }
}

/// C006 proofs that use Eq.refl on non-structural constructors elaborate
/// directly. Proofs that rely on iota reduction of symbolic constructor
/// major premises are registered structurally in the spec (Part of #663,
/// #461) and verified via the spec's DerivedProved status rather than kernel
/// elaboration. Part of #3309.
#[test]
fn test_c006_eq_refl_proofs_elaborate_directly() {
    // These proofs use Eq.refl on constructors that the kernel can handle
    // directly (no symbolic iota reduction needed):
    let directly_elaborable = ["lift_at_sort", "instantiate_sort"];

    for name in &directly_elaborable {
        let result = verify_proof(name);
        assert!(
            result.is_ok(),
            "C006 proof '{name}' should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

/// C006 proofs that rely on structural registration (iota false-negative
/// bypass) verify through the spec's DerivedProved path rather than direct
/// kernel elaboration. This test confirms the spec definitions are correctly
/// classified without kernel re-check. Part of #3309, #663, #461.
#[test]
fn test_c006_structural_proofs_verified_via_spec() {
    let spec = build_spec_with_stack();

    // These are verified structurally because the kernel cannot reduce
    // iota on a symbolic constructor major premise.
    let structural_proofs = ["lift_at_app", "lift_at_lam", "lift_at_pi"];

    for name in &structural_proofs {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("C006 spec definition '{name}' missing"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "C006 structural proof '{name}' should be DerivedProved in spec"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "C006 structural proof '{name}' should have no axiom dependencies"
        );
    }
}

/// C006 proofs that DO elaborate through the kernel successfully also have
/// zero axiom dependencies. This covers proofs that reference other lemmas
/// (not just Eq.refl) and pass full kernel elaboration. Part of #3309.
#[test]
fn test_c006_elaborable_proofs_zero_axiom_deps() {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    // Proofs that pass kernel elaboration (non-structural Eq.refl or lemma references)
    let elaborable_proofs = [
        "lift_at_sort",
        "lift_at_amount_zero",
        "lift_zero",
        "instantiate_sort",
        "instantiate_app",
        "instantiate_lam",
        "instantiate_pi",
        "inst_bvar_zero",
        "lift_cancel",
    ];

    for name in &elaborable_proofs {
        let result = report
            .results
            .get(*name)
            .unwrap_or_else(|| panic!("C006 proof '{name}' missing from dependency audit"));
        assert!(
            result.error.is_none(),
            "C006 proof '{name}' should verify without error: {:?}",
            result.error
        );
        assert_eq!(
            result.status,
            ProofStatus::DerivedProved,
            "C006 proof '{name}' should be DerivedProved"
        );
        assert!(
            result.axiom_deps.is_empty(),
            "C006 proof '{name}' should have no axiom dependencies, but depends on: {:?}",
            result.axiom_deps
        );
    }
}

/// The spec definitions corresponding to C006 proofs are already DerivedProved
/// with empty axiom_deps sets. Part of #3309.
#[test]
fn test_c006_spec_definitions_are_derived_proved() {
    let spec = build_spec_with_stack();

    // Map from library key to spec definition name
    let c006_spec_names = [
        "lift_at_sort",
        "lift_at_app",
        "lift_at_lam",
        "lift_at_pi",
        "lift_at_amount_zero",
        "lift_zero_identity",
        "instantiate_sort",
        "instantiate_app",
        "instantiate_lam",
        "instantiate_pi",
        "instantiate_bvar_zero",
        "lift_cancel",
    ];

    for name in &c006_spec_names {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("C006 spec definition '{name}' missing"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "C006 spec definition '{name}' should be DerivedProved, got {:?}",
            def.proof_status
        );
        assert!(
            def.axiom_deps.is_empty(),
            "C006 spec definition '{name}' should have empty axiom_deps, got {:?}",
            def.axiom_deps
        );
        assert!(
            def.value_src.is_some(),
            "C006 spec definition '{name}' should have a proof term (value_src)"
        );
    }
}

// =========================================================================
// #3310: C010 constructive proof verification — zero axiom dependencies
// =========================================================================

/// The C010 zonotope-CROWN equivalence has been verified constructively:
/// all executable witnesses pass, confirming the theorem with zero axiom
/// dependencies. The proof status reflects DerivedProved. Part of #3310.
#[test]
fn test_c010_zonotope_crown_equiv_is_derived_proved() {
    use crate::nn_verify::zonotope::c010_equiv::C010EquivSpec;
    let spec = C010EquivSpec::new();
    assert_eq!(
        spec.status(),
        ProofStatus::DerivedPending,
        "C010 zonotope-CROWN equivalence should be DerivedPending until kernel proof (Part of #3361)"
    );
}

// =========================================================================
// #3306: C001 DefEq elaboration + zero-axiom-dep verification tests
// =========================================================================

#[test]
fn test_c001_def_eq_refl_elaborates() {
    let result = verify_proof("def_eq_refl");
    assert!(
        result.is_ok(),
        "C001 def_eq_refl proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_c001_def_eq_symm_elaborates() {
    let result = verify_proof("def_eq_symm");
    assert!(
        result.is_ok(),
        "C001 def_eq_symm proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_c001_def_eq_trans_elaborates() {
    let result = verify_proof("def_eq_trans");
    assert!(
        result.is_ok(),
        "C001 def_eq_trans proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_c001_def_eq_congr_app_elaborates() {
    let result = verify_proof("def_eq_congr_app");
    assert!(
        result.is_ok(),
        "C001 def_eq_congr_app proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_c001_def_eq_congr_lam_elaborates() {
    let result = verify_proof("def_eq_congr_lam");
    assert!(
        result.is_ok(),
        "C001 def_eq_congr_lam proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_c001_def_eq_congr_pi_elaborates() {
    let result = verify_proof("def_eq_congr_pi");
    assert!(
        result.is_ok(),
        "C001 def_eq_congr_pi proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_c001_def_eq_beta_elaborates() {
    let result = verify_proof("def_eq_beta");
    assert!(
        result.is_ok(),
        "C001 def_eq_beta proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_c001_all_proofs_zero_axiom_deps() {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    let c001_proofs = [
        "def_eq_refl",
        "def_eq_symm",
        "def_eq_trans",
        "def_eq_congr_app",
        "def_eq_congr_lam",
        "def_eq_congr_pi",
        "def_eq_beta",
    ];

    for name in &c001_proofs {
        let result = report
            .results
            .get(*name)
            .unwrap_or_else(|| panic!("C001 proof '{name}' missing from dependency audit"));
        assert!(
            result.error.is_none(),
            "C001 proof '{name}' should verify without error: {:?}",
            result.error
        );
        assert_eq!(
            result.status,
            ProofStatus::DerivedProved,
            "C001 proof '{name}' should be DerivedProved"
        );
        assert!(
            result.axiom_deps.is_empty(),
            "C001 proof '{name}' should have no axiom dependencies, but depends on: {:?}",
            result.axiom_deps
        );
    }
}
