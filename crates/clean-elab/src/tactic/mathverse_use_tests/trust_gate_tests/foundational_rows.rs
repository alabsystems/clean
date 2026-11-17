// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Test code by its own head: the source gates read a file-level #![cfg(test)]
// as proof (headed_cfg_test in scripts/check_add_decl_ratchet.py).
#![cfg(test)]

use super::*;

/// A theorem whose ONLY non-KV transitive dependency is the foundational
/// axiom `propext`, with NO `propext` in the environment.
///
/// Two rules compose here. Since e20128880 the foundational half of
/// `RelaxedFoundational` admits a name only as the kernel's CANONICAL
/// declaration in the live environment, never as a library row that merely
/// shares the name — and a bare `Environment::new()` holds none. Strict never
/// had a foundational half. So both gates refuse, each for its own reason.
#[test]
fn test_foundational_only_theorem_without_canonical_declaration_is_refused() {
    let shard = build_guard_shard(&[
        (
            "Deep.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        // `propext` is a genuine foundational axiom (no proof value), only
        // ever Axiomatized in the corpus — never KernelVerified.
        (
            "propext",
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            false,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);

    let env = Environment::new();
    assert!(!env.is_canonical_foundational_axiom(&clean_kernel::name::Name::from_string("propext")));
    let candidate = premise_candidate(&lib, 0);

    // Strict: rejects on the foundational dep (it is not KernelVerified),
    // naming the offending dependency.
    let strict_detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));
    assert!(strict_detail.contains("propext"), "{strict_detail}");
    assert!(strict_detail.contains("below Strict"), "{strict_detail}");

    // RelaxedFoundational: the name and kind pass `accepts_dependency`, but
    // the environment holds no canonical declaration for it to denote.
    let relaxed_detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::RelaxedFoundational,
    ));
    assert!(relaxed_detail.contains("propext"), "{relaxed_detail}");
    assert!(
        relaxed_detail.contains("no canonical kernel declaration"),
        "a library row sharing a foundational name must not stand in for the kernel's \
             own declaration: {relaxed_detail}"
    );
}

/// The same foundational-only theorem against the prelude, whose `propext`
/// IS the kernel's canonical declaration and was added through checked
/// `add_decl` (`FullKernelCheck`).
///
/// The residency rule admits a kernel-checked resident under EVERY gate —
/// the loader never installs it, so its shard confidence bounds nothing —
/// after the kind discriminator and `validate_resident_type_agreement`. So
/// when the shard row states the canonical proposition, Strict and
/// RelaxedFoundational both admit. When the row states something else
/// (here `Prop`, as `build_guard_shard` writes every type), both refuse it as
/// a type substitution: the citation would rest on a `propext` other than
/// the one its closure names.
#[test]
fn test_foundational_only_theorem_is_admitted_against_the_canonical_resident() {
    let env = Environment::with_prelude();
    let propext = clean_kernel::name::Name::from_string("propext");
    assert!(env.is_canonical_foundational_axiom(&propext));
    let propext_type = env
        .get_const(&propext)
        .expect("the prelude declares propext")
        .type_
        .clone();

    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort0 = writer.add_expr(FlatExpr::sort(l0));
    let thm_name = writer.add_string("Deep.thm");
    writer.add_constant(MathverseConstantHeader {
        name_idx: thm_name,
        type_idx: sort0,
        value_idx: sort0,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let propext_type_idx = add_kernel_expr(&mut writer, &propext_type);
    let propext_name = writer.add_string("propext");
    writer.add_constant(MathverseConstantHeader {
        name_idx: propext_name,
        type_idx: propext_type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Axiom as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let shard = ShardReader::from_bytes(&buf).unwrap();
    let lib = probe_library(&shard);
    let candidate = premise_candidate(&lib, 0);

    for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
        let admitted = validate_dependency_loader_trust(&env, &candidate, &lib, gate);
        assert!(
            admitted.is_ok(),
            "{gate:?} must admit a foundational-only theorem resting on the kernel's \
                 canonical, kernel-checked `propext`: {admitted:?}"
        );
    }

    // Same closure, but the shard's `propext` row states `Prop`.
    let mismatched = build_guard_shard(&[
        (
            "Deep.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "propext",
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            false,
        ),
    ]);
    let lib = probe_library(&mismatched);
    let candidate = premise_candidate(&lib, 0);
    for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
        let detail = detail_from_result(validate_dependency_loader_trust(
            &env, &candidate, &lib, gate,
        ));
        assert!(detail.contains("propext"), "{detail}");
        assert!(detail.contains("type substitution"), "{detail}");
    }
}

/// No shard AXIOM row is ever replayed into the environment — not even one
/// named like a foundation and stamped `KernelVerified`.
///
/// `add_decl` checks only that an axiom's type is a well-formed sort, so an
/// installed row is asserted on the shard's say-so; and since e20128880 a
/// foundation counts only as the kernel's own canonical declaration, which
/// a shard row by construction is not (it could state `False`). The
/// genuine `propext` arrives through the prelude and is admitted by
/// residency (see the test above).
#[test]
fn test_kernel_verified_foundational_axiom_row_is_never_replayed() {
    let shard = build_guard_shard(&[
        (
            "Deep.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "propext",
            ImportConfidence::KernelVerified,
            DeclKind::Axiom,
            false,
        ),
    ]);
    let lib = probe_library(&shard);
    let env = Environment::new();
    let candidate = premise_candidate(&lib, 0);

    for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
        let detail = detail_from_result(validate_dependency_loader_trust(
            &env, &candidate, &lib, gate,
        ));
        assert!(detail.contains("propext"), "{detail}");
        assert!(detail.contains("not replayable"), "{detail}");
        assert!(detail.contains("reserved"), "{detail}");
    }
}

/// A value-bearing row that takes a name reserved for a kernel foundation
/// is not replayed either: checked `add_decl` would re-check its value, but
/// the result would still be a declaration of `propext` that is not the
/// kernel's — exactly what the elaborator refuses from source in every
/// environment.
#[test]
fn test_value_bearing_row_with_reserved_name_is_never_replayed() {
    let shard = build_guard_shard(&[
        (
            "Deep.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "propext",
            ImportConfidence::KernelVerified,
            DeclKind::Definition,
            true,
        ),
    ]);
    let lib = probe_library(&shard);
    let env = Environment::new();
    let candidate = premise_candidate(&lib, 0);

    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));
    assert!(detail.contains("propext"), "{detail}");
    assert!(detail.contains("reserved"), "{detail}");
}

/// A theorem with a DOMAIN-specific (non-foundational) axiom dependency is
/// rejected under BOTH Strict and RelaxedFoundational, naming the offender.
/// This is the soundness boundary: no domain axiom is ever admitted.
#[test]
fn test_relaxed_foundational_rejects_domain_axiom_under_both_gates() {
    let shard = build_guard_shard(&[
        (
            "Deep.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        // A domain-specific axiom: declared as Axiom, but its name is NOT in
        // the FOUNDATIONAL_AXIOMS allowlist.
        (
            "MyDomain.bigAxiom",
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            false,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);

    let env = Environment::new();
    let candidate = premise_candidate(&lib, 0);

    for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
        let detail = detail_from_result(validate_dependency_loader_trust(
            &env, &candidate, &lib, gate,
        ));
        assert!(
            detail.contains("MyDomain.bigAxiom"),
            "gate {gate:?} must name the offending domain axiom: {detail}"
        );
        assert!(
            detail.contains(&format!("below {gate:?}")),
            "gate {gate:?} must report rejection below itself: {detail}"
        );
    }
}

/// Soundness adversarial guard: a NON-axiom declaration that merely shares a
/// foundational name (here a Definition named `propext`, not
/// KernelVerified) must NOT be admitted by RelaxedFoundational — the
/// foundational branch requires DeclKind::Axiom.
#[test]
fn test_relaxed_foundational_rejects_non_axiom_sharing_foundational_name() {
    let shard = build_guard_shard(&[
        (
            "Deep.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        // Definition (not Axiom) named `propext`, not KernelVerified.
        (
            "propext",
            ImportConfidence::Axiomatized,
            DeclKind::Definition,
            true,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);

    let env = Environment::new();
    let candidate = premise_candidate(&lib, 0);
    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::RelaxedFoundational,
    ));
    assert!(detail.contains("propext"), "{detail}");
    assert!(
        detail.contains("below RelaxedFoundational"),
        "non-axiom sharing a foundational name must still be rejected: {detail}"
    );
}
