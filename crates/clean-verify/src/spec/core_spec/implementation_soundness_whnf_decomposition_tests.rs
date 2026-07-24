// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::{AxiomCategory, ProofStatus, TrustLevel};
use crate::test_utils::build_spec_with_stack;
use clean_kernel::{ConstantKind, Name, Reducibility};

fn assert_proved_beta_bridge(spec: &crate::Specification) {
    let beta = spec
        .definitions()
        .get("beta_reduces_preserves_def_eq")
        .expect("missing beta bridge");
    assert!(
        !beta.is_axiom,
        "beta_reduces_preserves_def_eq should be a derived bridge, not an axiom"
    );
    assert_eq!(
        beta.category,
        AxiomCategory::DerivedLemma,
        "beta_reduces_preserves_def_eq should be tracked as a DerivedLemma"
    );
    // Part of #2872: DefEq.beta is now UNTYPED, so the beta_reduces.rec bridge is a
    // genuine kernel-checked term (the former typed-premise blocker is stale).
    assert_eq!(
        beta.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduces_preserves_def_eq should be DerivedProved via the untyped beta_reduces.rec bridge"
    );
    assert!(
        beta.value_src.is_some(),
        "beta_reduces_preserves_def_eq should carry a beta_reduces.rec proof term"
    );
    assert_eq!(
        beta.trust_level(),
        TrustLevel::Derived,
        "beta_reduces_preserves_def_eq should surface as a derived (proved) bridge"
    );

    let beta_deps = beta
        .dependencies
        .as_ref()
        .expect("beta_reduces_preserves_def_eq should record dependencies");
    for expected in [
        "beta_reduces.rec",
        "beta_reduces_def_eq_goal",
        "DefEq.beta",
        "DefEq.app_cong",
        "DefEq.refl",
    ] {
        assert!(
            beta_deps.contains(expected),
            "beta_reduces_preserves_def_eq should depend on {expected}: {beta_deps:?}"
        );
    }
    assert!(
        beta.axiom_deps.is_empty(),
        "beta_reduces_preserves_def_eq should not retain HelperAxiom dependencies: {:?}",
        beta.axiom_deps
    );
}

fn assert_constructive_whnf_bridge(spec: &crate::Specification) {
    let whnf = spec
        .definitions()
        .get("whnf_to_preserves_def_eq")
        .expect("missing whnf bridge");
    assert!(
        !whnf.is_axiom,
        "whnf_to_preserves_def_eq should now be a derived bridge"
    );
    assert_eq!(
        whnf.category,
        AxiomCategory::DerivedLemma,
        "whnf_to_preserves_def_eq should be tracked as a DerivedLemma"
    );
    assert_eq!(
        whnf.proof_status,
        ProofStatus::DerivedProved,
        "whnf_to_preserves_def_eq should now be fully constructive"
    );
    assert_eq!(
        whnf.trust_level(),
        TrustLevel::Derived,
        "whnf_to_preserves_def_eq should no longer contribute a pending trust assumption"
    );

    let deps = whnf
        .dependencies
        .as_ref()
        .expect("whnf_to_preserves_def_eq should record dependencies");
    for expected in [
        "whnf_to.rec",
        "whnf_to_def_eq_goal",
        "DefEq.refl",
        "DefEq.trans",
        "whnf_step_preserves_def_eq",
    ] {
        assert!(
            deps.contains(expected),
            "whnf_to_preserves_def_eq should depend on {expected}: {deps:?}"
        );
    }
    assert!(
        whnf.axiom_deps.is_empty(),
        "whnf_to_preserves_def_eq should not retain HelperAxiom dependencies: {:?}",
        whnf.axiom_deps
    );
}

#[test]
fn test_whnf_decomposition_bridge_is_now_derived_proved() {
    // KernelWhnfAccepts is now a faithful inductive (refl-on-WHNF + step over
    // whnf_step), so the implementation/spec bridge is GENUINELY PROVED by
    // KernelWhnfAccepts.rec mapping each ctor to the matching whnf_to ctor —
    // no longer a HelperAxiom. The proof term is kernel-checked by add_decl
    // during spec construction, so a build-time success is itself the witness.
    let spec = build_spec_with_stack();
    let bridge = spec
        .definitions()
        .get("kernel_whnf_reduces_to_spec_whnf")
        .expect("missing whnf decomposition bridge");
    assert!(
        !bridge.is_axiom,
        "kernel_whnf_reduces_to_spec_whnf should no longer be an axiom"
    );
    assert_eq!(
        bridge.category,
        AxiomCategory::DerivedLemma,
        "kernel_whnf_reduces_to_spec_whnf should be a DerivedLemma"
    );
    assert_eq!(
        bridge.proof_status,
        ProofStatus::DerivedProved,
        "kernel_whnf_reduces_to_spec_whnf should be DerivedProved"
    );
    assert!(
        bridge.value_src.is_some(),
        "kernel_whnf_reduces_to_spec_whnf should carry a recursor proof term"
    );
    assert!(
        bridge.axiom_deps.is_empty(),
        "kernel_whnf_reduces_to_spec_whnf should have zero axiom_deps: {:?}",
        bridge.axiom_deps
    );

    let deps = bridge
        .dependencies
        .as_ref()
        .expect("kernel_whnf_reduces_to_spec_whnf should record dependencies");
    for expected in [
        "KernelStateEnvValid",
        "KernelStateLocalCtxWellFormed",
        "KernelInputAdmissible",
        "KernelWhnfAccepts",
        "KernelWhnfAccepts.rec",
        "whnf_to",
        "whnf_to.refl",
        "whnf_to.step",
    ] {
        assert!(
            deps.contains(expected),
            "kernel_whnf_reduces_to_spec_whnf should depend on {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_beta_and_whnf_bridges_track_narrow_trust_cut() {
    let spec = build_spec_with_stack();
    assert_proved_beta_bridge(&spec);
    assert_constructive_whnf_bridge(&spec);
}

#[test]
fn test_whnf_bridge_definitions_stay_opaque_while_goal_aliases_stay_regular() {
    let spec = build_spec_with_stack();

    for name in ["beta_reduces_def_eq_goal", "whnf_to_def_eq_goal"] {
        let info = spec
            .env()
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("missing goal alias {name}"));
        assert!(
            matches!(info.reducibility, Reducibility::Regular(_)),
            "{name} should remain a semireducible goal alias, got {:?}",
            info.reducibility
        );
        assert!(
            !info.is_reducible,
            "{name} should not become fully reducible"
        );
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} should remain a regular definition alias"
        );
    }

    // whnf_to_preserves_def_eq still has a proof term and remains Opaque.
    {
        let name = "whnf_to_preserves_def_eq";
        let info = spec
            .env()
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("missing bridge definition {name}"));
        assert_eq!(
            info.reducibility,
            Reducibility::Opaque,
            "{name} should stay opaque instead of becoming semireducible"
        );
        assert!(!info.is_reducible, "{name} should not become reducible");
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} should stay registered as an opaque proof definition"
        );
    }

    // beta_reduces_preserves_def_eq is now DerivedProved WITH a proof term
    // (#2872: DefEq.beta is untyped). It registers as an Opaque proof definition
    // (a non-Prop valued def → Declaration::Opaque → Reducibility::Opaque), exactly
    // like whnf_to_preserves_def_eq above — NOT a value-less Axiom.
    {
        let name = "beta_reduces_preserves_def_eq";
        let info = spec
            .env()
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("missing bridge definition {name}"));
        assert_eq!(
            info.reducibility,
            Reducibility::Opaque,
            "{name} should stay opaque as a proof definition, got {:?}",
            info.reducibility
        );
        assert!(!info.is_reducible, "{name} should not become reducible");
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} should be registered as an Opaque proof definition after #2872"
        );
    }
}

#[test]
fn test_whnf_step_bridge_is_constructive() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("whnf_step_preserves_def_eq")
        .expect("whnf_step_preserves_def_eq should exist");
    assert!(
        !def.is_axiom,
        "whnf_step_preserves_def_eq should be derived"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "whnf_step_preserves_def_eq should be fully constructive"
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("whnf_step_preserves_def_eq should record dependencies");
    for expected in [
        "whnf_step.rec",
        "whnf_step_def_eq_goal",
        "beta_reduces_preserves_def_eq",
        "DefEq.delta",
    ] {
        assert!(
            deps.contains(expected),
            "whnf_step_preserves_def_eq should depend on {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_kernel_whnf_returns_def_eq_is_now_derived() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_whnf_returns_def_eq")
        .expect("kernel_whnf_returns_def_eq should exist");

    assert!(
        !def.is_axiom,
        "kernel_whnf_returns_def_eq should now be a derived lemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "kernel_whnf_returns_def_eq is now fully DerivedProved: its trace bridge kernel_whnf_reduces_to_spec_whnf is no longer an axiom (KernelWhnfAccepts is a faithful inductive)"
    );
    assert!(
        def.value_src.is_some(),
        "kernel_whnf_returns_def_eq should have a constructive proof term"
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_whnf_returns_def_eq should record dependencies");
    for expected in [
        "whnf_to_preserves_def_eq",
        "kernel_whnf_reduces_to_spec_whnf",
    ] {
        assert!(
            deps.contains(expected),
            "kernel_whnf_returns_def_eq should depend on {expected}: {deps:?}"
        );
    }

    assert!(
        def.axiom_deps.is_empty(),
        "kernel_whnf_returns_def_eq should now have an empty axiom closure (both bridges are constructive): {:?}",
        def.axiom_deps
    );
}

// ─────────────────────────────────────────────────────────────
// WHNF metatheory: formerly HelperAxiom, now DerivedProved
// ─────────────────────────────────────────────────────────────

#[test]
fn test_beta_deterministic_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("beta_deterministic")
        .expect("beta_deterministic should exist");

    assert!(
        !def.is_axiom,
        "beta_deterministic should no longer be a HelperAxiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_deterministic should be fully constructive"
    );
    assert!(
        def.value_src.is_some(),
        "beta_deterministic should have a proof term"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "beta_deterministic should be a DerivedLemma"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "beta_deterministic should have no HelperAxiom dependencies: {:?}",
        def.axiom_deps
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("beta_deterministic should record dependencies");
    for expected in ["beta_reduces_preserves_def_eq", "DefEq.symm", "DefEq.trans"] {
        assert!(
            deps.contains(expected),
            "beta_deterministic should depend on {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_whnf_to_target_is_whnf_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("whnf_to_target_is_whnf")
        .expect("whnf_to_target_is_whnf should exist");

    assert!(
        !def.is_axiom,
        "whnf_to_target_is_whnf should not be an axiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "whnf_to_target_is_whnf should be fully constructive"
    );
    assert!(
        def.value_src.is_some(),
        "whnf_to_target_is_whnf should have a proof term via whnf_to.rec"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "whnf_to_target_is_whnf should have no HelperAxiom dependencies: {:?}",
        def.axiom_deps
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("whnf_to_target_is_whnf should record dependencies");
    for expected in ["whnf_to.rec", "whnf_to_is_whnf_goal"] {
        assert!(
            deps.contains(expected),
            "whnf_to_target_is_whnf should depend on {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_whnf_idempotent_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("whnf_idempotent")
        .expect("whnf_idempotent should exist");

    assert!(
        !def.is_axiom,
        "whnf_idempotent should no longer be a HelperAxiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "whnf_idempotent should be fully constructive"
    );
    assert!(
        def.value_src.is_some(),
        "whnf_idempotent should have a proof term"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "whnf_idempotent should be a DerivedLemma"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "whnf_idempotent should have no HelperAxiom dependencies: {:?}",
        def.axiom_deps
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("whnf_idempotent should record dependencies");
    for expected in ["whnf_to_target_is_whnf", "whnf_to.refl"] {
        assert!(
            deps.contains(expected),
            "whnf_idempotent should depend on {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_whnf_confluent_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("whnf_confluent")
        .expect("whnf_confluent should exist");

    assert!(
        !def.is_axiom,
        "whnf_confluent should no longer be a HelperAxiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "whnf_confluent should be fully constructive"
    );
    assert!(
        def.value_src.is_some(),
        "whnf_confluent should have a proof term"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "whnf_confluent should be a DerivedLemma"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "whnf_confluent should have no HelperAxiom dependencies: {:?}",
        def.axiom_deps
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("whnf_confluent should record dependencies");
    for expected in ["whnf_to_preserves_def_eq", "DefEq.symm", "DefEq.trans"] {
        assert!(
            deps.contains(expected),
            "whnf_confluent should depend on {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_whnf_metatheory_motive_alias_stays_regular() {
    let spec = build_spec_with_stack();
    let info = spec
        .env()
        .get_const(&Name::from_string("whnf_to_is_whnf_goal"))
        .expect("whnf_to_is_whnf_goal should exist in environment");
    assert!(
        matches!(info.reducibility, Reducibility::Regular(_)),
        "whnf_to_is_whnf_goal should be a semireducible goal alias, got {:?}",
        info.reducibility
    );
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "whnf_to_is_whnf_goal should remain a regular definition"
    );
}

#[test]
fn test_whnf_decomposition_summary_transitive_deps() {
    let spec = build_spec_with_stack();

    for name in [
        "KernelWhnfSound",
        "KernelWhnfSound_summary",
        "KernelWhnfPreservesTyping",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("missing whnf simulation theorem {name}"));
        assert!(
            !def.axiom_deps.contains("kernel_whnf_reduces_to_spec_whnf"),
            "{name} should no longer surface kernel_whnf_reduces_to_spec_whnf as an axiom leaf — it is now a proved theorem (KernelWhnfAccepts is a faithful inductive): {:?}",
            def.axiom_deps
        );
        assert!(
            !def.axiom_deps.contains("whnf_to_preserves_def_eq"),
            "{name} should no longer treat whnf_to_preserves_def_eq as pending: {:?}",
            def.axiom_deps
        );
        assert!(
            !def.axiom_deps.contains("beta_reduces_preserves_def_eq"),
            "{name} should no longer treat beta_reduces_preserves_def_eq as pending: {:?}",
            def.axiom_deps
        );
        assert!(
            !def.axiom_deps.contains("kernel_whnf_returns_def_eq"),
            "{name} should not list the derived whnf contract as a pending axiom: {:?}",
            def.axiom_deps
        );
    }
}
