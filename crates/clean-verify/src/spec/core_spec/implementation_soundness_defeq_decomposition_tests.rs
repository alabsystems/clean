// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::build_spec_with_stack;

#[test]
fn test_defeq_joinable_is_faithful_inductive() {
    // DefEqJoinable is the packaged existential that RETIRES the
    // KernelDefEqNormalLeft / KernelDefEqNormalRight skolem functions: its single
    // mk constructor binds the two common reducts nl/nr INTERNALLY with the three
    // def-eq evidence fields, rather than naming them by opaque skolem functions of
    // the inputs. It must be a genuine (non-axiom) inductive.
    let spec = build_spec_with_stack();

    let ind = spec
        .definitions()
        .get("DefEqJoinable")
        .expect("DefEqJoinable should exist");
    assert!(!ind.is_axiom, "DefEqJoinable should be a genuine inductive");

    let ctor = spec
        .definitions()
        .get("DefEqJoinable.mk")
        .expect("DefEqJoinable.mk constructor should be registered");
    assert!(
        !ctor.is_axiom,
        "DefEqJoinable.mk should be a kernel-generated constructor, not an axiom"
    );
    // The mk field carries three DefEq evidence components (DefEq a nl, DefEq b nr,
    // DefEq nl nr) and concludes in DefEqJoinable a b.
    let ctor_ty = format!(
        "{:?}",
        ctor.elaborated_type
            .as_ref()
            .expect("DefEqJoinable.mk should record its elaborated type")
    );
    for pinned in ["DefEq", "DefEqJoinable"] {
        assert!(
            ctor_ty.contains(pinned),
            "DefEqJoinable.mk's elaborated type should reference {pinned}: {ctor_ty}"
        );
    }
    // Faithfulness of the retirement: the packaged existential must NOT name the
    // retired skolem functions.
    for retired in ["KernelDefEqNormalLeft", "KernelDefEqNormalRight"] {
        assert!(
            !ctor_ty.contains(retired),
            "DefEqJoinable.mk must not reference the retired skolem {retired}: {ctor_ty}"
        );
    }
}

#[test]
fn test_kernel_defeq_accepts_is_faithful_inductive() {
    // KernelDefEqAccepts is a faithful inductive whose single mk constructor
    // carries the GUARDED implication from the three state/admissibility predicates
    // to the skolem-free DefEqJoinable packaged existential.
    let spec = build_spec_with_stack();

    let accepts = spec
        .definitions()
        .get("KernelDefEqAccepts")
        .expect("KernelDefEqAccepts should exist");
    assert!(
        !accepts.is_axiom,
        "KernelDefEqAccepts should no longer be an opaque axiom"
    );

    let ctor = spec
        .definitions()
        .get("KernelDefEqAccepts.mk")
        .expect("KernelDefEqAccepts.mk constructor should be registered");
    assert!(
        !ctor.is_axiom,
        "KernelDefEqAccepts.mk should be a kernel-generated constructor, not an axiom"
    );
    // The mk field must be the GUARDED implication — it must reference the three
    // guard predicates (state validity, local-context well-formedness, binary input
    // admissibility) and conclude in the skolem-free DefEqJoinable packaged
    // existential. An UNGUARDED constructor would silently strengthen every producer
    // axiom concluding an Accepts (adversarial-audit finding) — this pin fails
    // closed against that regression.
    let ctor_ty = format!(
        "{:?}",
        ctor.elaborated_type
            .as_ref()
            .expect("KernelDefEqAccepts.mk should record its elaborated type")
    );
    for pinned in [
        "KernelStateEnvValid",
        "KernelStateLocalCtxWellFormed",
        "KernelBinaryInputAdmissible",
        "DefEqJoinable",
    ] {
        assert!(
            ctor_ty.contains(pinned),
            "KernelDefEqAccepts.mk's elaborated type should reference {pinned}: {ctor_ty}"
        );
    }
    // The retired skolems must not appear anywhere in the acceptance judgment.
    for retired in ["KernelDefEqNormalLeft", "KernelDefEqNormalRight"] {
        assert!(
            !ctor_ty.contains(retired),
            "KernelDefEqAccepts.mk must not reference the retired skolem {retired}: {ctor_ty}"
        );
    }
}

#[test]
fn test_def_eq_joinable_reflects_is_derived_proved() {
    // def_eq_joinable_reflects eliminates the DefEqJoinable packaged existential to
    // the skolem-free DefEq a b via DefEqJoinable.rec. It is genuinely DerivedProved
    // with an EMPTY axiom closure (DefEqJoinable / DefEqJoinable.rec are non-axioms;
    // DefEq.trans/symm are FoundationalRules).
    let spec = build_spec_with_stack();

    let def = spec
        .definitions()
        .get("def_eq_joinable_reflects")
        .expect("def_eq_joinable_reflects should exist");
    assert!(
        !def.is_axiom,
        "def_eq_joinable_reflects should not be an axiom"
    );
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "def_eq_joinable_reflects should be DerivedProved (empty axiom closure)"
    );
    let value = def
        .value_src
        .as_ref()
        .expect("def_eq_joinable_reflects should carry a recursor proof term");
    assert!(
        value.contains("DefEqJoinable.rec"),
        "def_eq_joinable_reflects should be proved via DefEqJoinable.rec: {value}"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "def_eq_joinable_reflects should have an empty axiom closure: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_kernel_def_eq_reflects_spec_is_skolem_free() {
    // kernel_def_eq_reflects_spec eliminates a KernelDefEqAccepts acceptance to
    // DefEq a b via KernelDefEqAccepts.rec then def_eq_joinable_reflects. With the
    // skolems retired, its residual axiom closure is now EMPTY.
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_def_eq_reflects_spec")
        .expect("kernel_def_eq_reflects_spec should exist");

    assert!(!def.is_axiom);
    assert_eq!(def.proof_status, ProofStatus::DerivedPending);

    let value = def
        .value_src
        .as_ref()
        .expect("kernel_def_eq_reflects_spec should carry a proof term");
    for snippet in ["def_eq_joinable_reflects", "KernelDefEqAccepts.rec"] {
        assert!(
            value.contains(snippet),
            "kernel_def_eq_reflects_spec proof should mention {snippet}: {value}"
        );
    }

    assert!(
        def.axiom_deps.is_empty(),
        "kernel_def_eq_reflects_spec residual axiom closure should be empty after skolem \
         retirement: {:?}",
        def.axiom_deps
    );
    for retired in [
        "KernelDefEqNormalLeft",
        "KernelDefEqNormalRight",
        "kernel_defeq_decomposition",
        "kernel_defeq_left_normalization_sound",
        "kernel_defeq_right_normalization_sound",
        "kernel_defeq_structural_sound",
    ] {
        assert!(
            !def.axiom_deps.contains(retired),
            "{retired} is retired and should not be in axiom_deps: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_defeq_skolems_and_decomposition_lemmas_are_retired() {
    // The two skolem functions and the four decomposition lemmas that named them
    // are gone from the spec entirely.
    let spec = build_spec_with_stack();
    for retired in [
        "KernelDefEqNormalLeft",
        "KernelDefEqNormalRight",
        "kernel_defeq_decomposition",
        "kernel_defeq_left_normalization_sound",
        "kernel_defeq_right_normalization_sound",
        "kernel_defeq_structural_sound",
    ] {
        assert!(
            !spec.definitions().contains_key(retired),
            "{retired} should be retired from the spec"
        );
    }
}

#[test]
fn test_defeq_summary_transitive_deps_are_skolem_free() {
    let spec = build_spec_with_stack();

    for summary_name in ["KernelDefEqSound", "KernelDefEqSound_summary"] {
        let def = spec
            .definitions()
            .get(summary_name)
            .unwrap_or_else(|| panic!("{summary_name} should exist"));
        for retired in [
            "KernelDefEqNormalLeft",
            "KernelDefEqNormalRight",
            "kernel_defeq_decomposition",
            "kernel_defeq_left_normalization_sound",
            "kernel_defeq_right_normalization_sound",
            "kernel_defeq_structural_sound",
            "kernel_def_eq_reflects_spec",
        ] {
            assert!(
                !def.axiom_deps.contains(retired),
                "{summary_name} should not list retired/derived {retired}: {:?}",
                def.axiom_deps
            );
        }
    }
}
