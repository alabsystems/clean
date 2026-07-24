// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_def_exists(spec: &Specification, name: &str) {
    // A name is "in the spec" if it is a tracked SpecDefinition OR a kernel
    // primitive registered directly in the env (e.g. `Bool`/`Bool.true`/
    // `Bool.rec`, now provided by the kernel `init_bool` surface so the
    // BoolAnalysis corpus reduces against the kernel recursor). The env is the
    // source of truth — every SpecDefinition is also added to it.
    assert!(
        spec.get_definition(name).is_some()
            || spec
                .env()
                .get_const(&clean_kernel::Name::from_string(name))
                .is_some(),
        "{name} should exist in the spec"
    );
}

#[test]
fn proof_status_invariants() {
    let spec = build_spec_with_stack();
    let mut foundational_count = 0usize;
    let mut derived_axiom = 0usize;
    let mut derived_pending = 0usize;
    let mut derived_proved = 0usize;
    let mut helper_axiom_count = 0usize;

    for def in spec.definitions().values() {
        if def.value_src.is_some() {
            assert!(
                !def.is_axiom,
                "Definition with value_src should not be marked axiom: {}",
                def.name
            );
        }

        match def.category {
            AxiomCategory::FoundationalRule => foundational_count += 1,
            AxiomCategory::DerivedLemma => {
                match def.proof_status {
                    ProofStatus::Axiom => derived_axiom += 1,
                    ProofStatus::DerivedPending => derived_pending += 1,
                    ProofStatus::DerivedProved => derived_proved += 1,
                    _ => panic!("Unknown ProofStatus variant for definition: {}", def.name),
                }

                if def.proof_status == ProofStatus::DerivedPending {
                    // DerivedLemma + DerivedPending should have either a
                    // value_src (proof term pending verification) or explicit
                    // dependencies (proof not yet written but planned, e.g.
                    // needs typing premises from #2872). Without either, the
                    // definition may be a forgotten axiom masquerading as a
                    // pending lemma. Part of #3361.
                    assert!(
                        def.value_src.is_some() || def.dependencies.is_some(),
                        "DerivedLemma with DerivedPending status must have \
                         value_src or dependencies: {}",
                        def.name
                    );
                }
            }
            AxiomCategory::HelperAxiom => helper_axiom_count += 1,
            _ => panic!("Unknown AxiomCategory variant for definition: {}", def.name),
        }
    }

    let total_derived = derived_axiom + derived_pending + derived_proved;
    let total = foundational_count + total_derived + helper_axiom_count;
    assert_eq!(
        total,
        spec.definitions().len(),
        "Category totals should match definition count"
    );

    let def = spec
        .get_definition("nat_add_zero")
        .expect("nat_add_zero should exist");
    assert!(
        def.elaborated_value.is_some(),
        "nat_add_zero should have an elaborated proof term"
    );
    spec.verify_definition("nat_add_zero")
        .expect("nat_add_zero should typecheck in the spec environment");

    // Verify Bool inductive was correctly generated (#804)
    for name in ["Bool", "Bool.true", "Bool.false", "Bool.rec"] {
        assert_def_exists(&spec, name);
    }

    // Verify Bool.not/and/or definitions exist (#814)
    for name in ["Bool.not", "Bool.and", "Bool.or"] {
        assert_def_exists(&spec, name);
    }

    // Verify And inductive was correctly generated (#804)
    for name in ["And", "And.intro", "And.rec"] {
        assert_def_exists(&spec, name);
    }
}

#[test]
fn beta_reduces_preserves_def_eq_is_constructively_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .get_definition("beta_reduces_preserves_def_eq")
        .expect("beta_reduces_preserves_def_eq should exist");

    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "beta_reduces_preserves_def_eq should stay tracked as a derived bridge"
    );
    // DerivedProved: DefEq.beta is now UNTYPED, so the beta_reduces.rec bridge is a
    // genuine kernel-checked term (the former typed-premise blocker is stale).
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduces_preserves_def_eq is constructively proved via untyped beta_reduces.rec"
    );
    assert!(
        !def.is_axiom,
        "beta_reduces_preserves_def_eq should not be an axiom"
    );
    assert!(
        def.value_src.is_some(),
        "beta_reduces_preserves_def_eq should carry the beta_reduces.rec proof source"
    );
    assert!(
        def.elaborated_value.is_some(),
        "beta_reduces_preserves_def_eq should carry a kernel-checked value after registration"
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("beta_reduces_preserves_def_eq should record dependencies");
    for expected in ["DefEq.beta", "beta_reduces.rec", "beta_reduces_def_eq_goal"] {
        assert!(
            deps.contains(expected),
            "beta_reduces_preserves_def_eq should record {expected} in its provenance: {deps:?}"
        );
    }
    for expected in ["DerivedProved", "DefEq.beta", "UNTYPED", "#2872"] {
        assert!(
            def.description.contains(expected),
            "beta_reduces_preserves_def_eq description should explain {expected}: {}",
            def.description
        );
    }
}

/// bootstrap_infer_sound (algorithmic soundness KernelInfers -> TypingCtxConv) is
/// now a value-bearing DerivedProved theorem — the explicit KernelInfers.rec proof
/// term ported back from the Aristotle strategy proof — with an EMPTY kernel-ground
/// -truth axiom closure (the census-14->13 drain). Guards against a silent
/// regression to the former DerivedPending value-less axiom.
#[test]
fn bootstrap_infer_sound_is_constructively_proved() {
    use clean_verify::spec_axiom_closure::{foundational_base, residual_domain_axioms};

    let spec = build_spec_with_stack();
    let def = spec
        .get_definition("bootstrap_infer_sound")
        .expect("bootstrap_infer_sound should exist");

    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "bootstrap_infer_sound stays a derived lemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "bootstrap_infer_sound is now constructively proved via the KernelInfers.rec term"
    );
    assert!(
        !def.is_axiom,
        "bootstrap_infer_sound must no longer be an axiom (census drain)"
    );
    assert!(
        def.value_src.is_some(),
        "bootstrap_infer_sound should carry the KernelInfers.rec proof source"
    );
    let value_src = def
        .value_src
        .as_deref()
        .expect("value source checked above");
    assert!(
        value_src.contains("TypingCtxConv.let_"),
        "bootstrap_infer_sound must consume the KernelInfers let_ recursor minor"
    );
    assert!(
        def.dependencies
            .as_ref()
            .is_some_and(|dependencies| dependencies.contains("TypingCtxConv.let_")),
        "bootstrap_infer_sound provenance must retain its dependent-let constructor"
    );
    assert!(
        def.elaborated_value.is_some(),
        "bootstrap_infer_sound should carry a kernel-checked value after registration"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "bootstrap_infer_sound must declare an empty axiom closure: {:?}",
        def.axiom_deps
    );

    // The real drain: the kernel-ground-truth transitive axiom closure must have
    // an EMPTY residual (⊆ foundational base) — no domain/pending axiom leaf.
    let residual =
        residual_domain_axioms(&spec, "bootstrap_infer_sound", &foundational_base(&spec));
    assert!(
        residual.is_empty(),
        "bootstrap_infer_sound closure must be empty (foundational only); residual: {residual:?}"
    );

    // It re-typechecks against the live kernel environment.
    spec.verify_definition("bootstrap_infer_sound")
        .expect("bootstrap_infer_sound should re-typecheck in the spec environment");
}

/// tc_infer_soundness (KernelInferAccepts -> KernelCheckAccepts) is now a
/// value-bearing DerivedProved theorem — the KernelCheckAccepts.mk term whose
/// admissibility guard is `infer_result_self_admissible` and whose defeq half is
/// reflexive — with an EMPTY kernel-ground-truth axiom closure (the census
/// 12->11 drain, the 3-axiom finish line). Its type carries the four
/// env-closedness interfaces i3..i6 as schematic TYPE hypotheses (NOT axioms).
/// Guards against a silent regression to the former value-less FlagAxiom.
#[test]
fn tc_infer_soundness_is_constructively_proved() {
    use clean_verify::spec_axiom_closure::{foundational_base, residual_domain_axioms};

    let spec = build_spec_with_stack();
    let def = spec
        .get_definition("tc_infer_soundness")
        .expect("tc_infer_soundness should exist");

    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "tc_infer_soundness is now a derived lemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "tc_infer_soundness is now constructively proved via the KernelCheckAccepts.mk term"
    );
    assert!(
        !def.is_axiom,
        "tc_infer_soundness must no longer be an axiom (census 12->11 drain)"
    );
    assert!(
        def.value_src.is_some(),
        "tc_infer_soundness should carry the KernelCheckAccepts.mk proof source"
    );
    assert!(
        def.elaborated_value.is_some(),
        "tc_infer_soundness should carry a kernel-checked value after registration"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "tc_infer_soundness must declare an empty axiom closure: {:?}",
        def.axiom_deps
    );

    // The type carries the i3..i6 env-closedness interfaces as TYPE hypotheses
    // (the schematic-discipline drain), never discharged over the_red_env.
    for iface in [
        "RecEnvClosed (red_rec the_red_env)",
        "RecEnvLiftClosed (red_rec the_red_env)",
        "DefEnvClosed (red_def the_red_env)",
        "DefEnvLiftClosed (red_def the_red_env)",
    ] {
        assert!(
            def.type_src.contains(iface),
            "tc_infer_soundness type must carry the {iface} hypothesis: {}",
            def.type_src
        );
    }

    // The real drain: the kernel-ground-truth transitive axiom closure must have
    // an EMPTY residual (subset of the foundational base) — no domain/pending
    // axiom leaf. The i3..i6 interfaces are TYPE hypotheses, not axiom_deps.
    let residual = residual_domain_axioms(&spec, "tc_infer_soundness", &foundational_base(&spec));
    assert!(
        residual.is_empty(),
        "tc_infer_soundness closure must be empty (foundational only); residual: {residual:?}"
    );

    // It re-typechecks against the live kernel environment.
    spec.verify_definition("tc_infer_soundness")
        .expect("tc_infer_soundness should re-typecheck in the spec environment");
}
