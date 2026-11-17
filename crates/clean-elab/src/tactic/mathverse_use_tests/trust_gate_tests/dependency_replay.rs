// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Test code by its own head: the source gates read a file-level #![cfg(test)]
// as proof (headed_cfg_test in scripts/check_add_decl_ratchet.py).
#![cfg(test)]

use super::*;

#[test]
fn test_dependency_loader_rejects_untrusted_transitive_dependency() {
    let shard = build_guard_shard(&[
        (
            "Good.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Bad.dep",
            ImportConfidence::Unverified,
            DeclKind::Axiom,
            false,
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
        TrustGate::Strict,
    ));

    assert!(detail.contains("Bad.dep"), "{detail}");
    assert!(detail.contains("Unverified"), "{detail}");
    assert!(detail.contains("below Strict"), "{detail}");
}

/// A dependency that is RESIDENT but was never fully kernel-checked must not
/// be admitted, even when the shard stamps it `KernelVerified`.
///
/// This is the `.olean`-preload hole. `clean-olean`'s import path registers
/// through `extend_{constants,inductives,constructors,recursors}_unchecked`
/// and records `DeclarationVerification::Unchecked`; a lane such as
/// `MATHVERSE_PRELOAD_OLEAN` therefore makes unchecked material resident.
/// While residency was tested with `Environment::get_const(..).is_some()`,
/// that material was admitted into a `TrustGate::Strict` closure and the
/// probe printed "GOAL CLOSED … via TrustGate::Strict" over declarations no
/// kernel ever validated.
///
/// The shard row here is `KernelVerified`, so the confidence gate alone would
/// pass it. It must still be refused: the loader adds a declaration only when
/// the name is absent, so the ENVIRONMENT's unchecked copy — not the stamped
/// shard row — is what the kernel would type-check the citation against.
///
/// `add_decl_structural` is the public stand-in for that state: it records
/// `StructuralOnly`, i.e. resident without a full kernel check.
#[test]
fn test_dependency_loader_rejects_resident_without_full_kernel_check() {
    let shard = build_guard_shard(&[
        (
            "Good.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Shadowed.dep",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);

    let mut env = Environment::new();
    // Resident, but only structurally validated — exactly the provenance the
    // unchecked `.olean` lane produces.
    env.add_decl_structural(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Shadowed.dep"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("structural registration of the stand-in should succeed");
    assert!(
        env.get_const(&clean_kernel::Name::from_string("Shadowed.dep"))
            .is_some(),
        "precondition: the dependency must be name-resident"
    );
    assert_ne!(
        env.declaration_verification(&clean_kernel::Name::from_string("Shadowed.dep")),
        Some(clean_kernel::DeclarationVerification::FullKernelCheck),
        "precondition: it must NOT carry a full-kernel-check verdict"
    );

    let candidate = premise_candidate(&lib, 0);
    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));

    assert!(detail.contains("Shadowed.dep"), "{detail}");
    assert!(
        detail.contains("without a full kernel check"),
        "the refusal must name the missing kernel check, not a confidence problem: {detail}"
    );
}

/// A kernel-checked resident that is a DIFFERENT DECLARATION than the shard
/// row of the same name must not satisfy that row.
///
/// Residency is matched by name. `Environment::with_prelude` seeds
/// hand-rolled `Declaration::Axiom` stubs called `Fact`, `Fact.mk`,
/// `Fact.out` (plus `Finset`/`Multiset`). The kernel really did check those
/// axioms, so they carry `FullKernelCheck` and the verdict test alone lets
/// them through — but they are Clean's stubs, not Mathlib's structure, and a
/// citation resting on them reports success against something other than the
/// theorem's actual closure.
///
/// Kind is an exact discriminator for this family: only `add_inductive` (or a
/// checked family replay) can produce the structured kernel value an
/// `Inductive` row requires, and an axiom stub never has one.
#[test]
fn test_dependency_loader_rejects_resident_stub_substituting_for_inductive() {
    let shard = build_guard_shard(&[
        (
            "Good.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        // Value-less: can never be stamped KernelVerified, so it is
        // admissible only by residency.
        (
            "Fact",
            ImportConfidence::SourceVerified,
            DeclKind::Inductive,
            false,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);

    let mut env = Environment::new();
    // The stub: genuinely kernel-checked, genuinely NOT an inductive.
    let prop = Expr::sort(Level::zero());
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Fact"),
        level_params: vec![],
        type_: Expr::pi(clean_kernel::BinderInfo::Default, prop.clone(), prop),
    })
    .expect("the axiom stub is well-typed and must register");
    assert_eq!(
        env.declaration_verification(&clean_kernel::Name::from_string("Fact")),
        Some(clean_kernel::DeclarationVerification::FullKernelCheck),
        "precondition: the stub IS fully kernel-checked — that is what makes \
             this hole invisible to a verdict-only test"
    );

    let candidate = premise_candidate(&lib, 0);
    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));

    assert!(detail.contains("Fact"), "{detail}");
    assert!(
        detail.contains("stub substitution"),
        "the refusal must name the substitution, not a confidence problem: {detail}"
    );
}

/// The good path is unchanged: a value-less dependency backed by the kernel's
/// own checked `add_inductive` is still admitted under `Strict`.
///
/// This is the load-bearing counterpart to the two tests above — it pins that
/// tightening residency did not make `Strict` unsatisfiable for the inductive
/// families every real Mathlib closure contains.
///
/// The `Or` / `Or.inl` rows carry the PRELUDE'S OWN types, re-flattened into
/// the shard. That is not decoration: `build_guard_shard` types every row
/// `Prop`, which is not `Or.inl`'s type, and a row claiming to be `Or.inl`
/// while carrying a different type is exactly the substitution
/// `validate_resident_type_agreement` exists to refuse. The test has to state
/// the real types to be asserting what it says it asserts.
#[test]
fn test_dependency_loader_admits_kernel_checked_inductive_resident() {
    // `with_prelude` builds `Or` through the kernel's checked `add_inductive`
    // (positivity, block agreement, a real `TypeChecker` over the type former
    // and constructor types, plus recursor validation).
    let env = Environment::with_prelude();

    let shard = {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let sort0 = writer.add_expr(FlatExpr::sort(l0));
        let root = writer.add_string("Good.thm");
        writer.add_constant(MathverseConstantHeader {
            name_idx: root,
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
        for (name, kind) in [
            ("Or", DeclKind::Inductive),
            ("Or.inl", DeclKind::Constructor),
        ] {
            let info = env
                .get_const(&clean_kernel::Name::from_string(name))
                .unwrap_or_else(|| panic!("`{name}` must be resident in the prelude"))
                .clone();
            assert!(
                info.level_params.is_empty(),
                "`{name}` is expected to be universe-monomorphic in this prelude"
            );
            let type_idx = add_kernel_expr(&mut writer, &info.type_);
            let name_idx = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx,
                type_idx,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::SourceVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: kind as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    };
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);
    lib.add_dependency(0, 2);

    assert_eq!(
        env.declaration_verification(&clean_kernel::Name::from_string("Or")),
        Some(clean_kernel::DeclarationVerification::FullKernelCheck),
    );
    assert!(env
        .get_inductive(&clean_kernel::Name::from_string("Or"))
        .is_some());
    assert!(env
        .get_constructor(&clean_kernel::Name::from_string("Or.inl"))
        .is_some());

    let candidate = premise_candidate(&lib, 0);
    validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict).expect(
        "a value-less dependency the kernel itself built must stay admissible under Strict",
    );
}

#[test]
fn test_dependency_loader_rejects_metadata_only_theorem_candidate() {
    let shard = build_guard_shard(&[(
        "MetaOnly.thm",
        ImportConfidence::KernelVerified,
        DeclKind::Theorem,
        false,
    )]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    let env = Environment::new();
    let candidate = premise_candidate(&lib, 0);
    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));

    assert!(detail.contains("MetaOnly.thm"), "{detail}");
    assert!(detail.contains("theorem"), "{detail}");
    assert!(detail.contains("no proof/value expression"), "{detail}");
}

#[test]
fn test_dependency_loader_rejects_missing_inductive_family_metadata() {
    let shard = build_guard_shard(&[
        (
            "Good.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "MissingInd",
            ImportConfidence::KernelVerified,
            DeclKind::Inductive,
            false,
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
        TrustGate::Strict,
    ));

    assert!(detail.contains("MissingInd"), "{detail}");
    assert!(detail.contains("InductiveDecl"), "{detail}");
    assert!(detail.contains("checked registration"), "{detail}");
}

/// A value-bearing `Definition` dependency is REPLAYABLE and must be admitted.
///
/// This previously asserted the opposite. Rejecting definitions made the lane
/// unusable on real corpora: Mathlib closures are dominated by definitions
/// (match auxiliaries such as `_private.Mathlib.Logic.Unique.1.….match_1_5`),
/// and one rejected definition aborts the whole candidate.
///
/// SOUNDNESS: admitting the kind only makes it ELIGIBLE for registration.
/// `header_to_declaration` now emits a real `Declaration::Definition` (rather
/// than mislabelling it a `Theorem`, which also changed its reduction
/// behaviour), and it still goes through the kernel's checked `add_decl`,
/// which type-checks value against type.
#[test]
fn test_dependency_loader_admits_value_bearing_definition_replay() {
    let shard = build_guard_shard(&[
        (
            "Good.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Replayable.def",
            ImportConfidence::KernelVerified,
            DeclKind::Definition,
            /* has_value */ true,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);

    let env = Environment::new();
    let candidate = premise_candidate(&lib, 0);
    validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict)
        .expect("a KernelVerified definition WITH a value must be replayable");
}

/// …but a `Definition` with NO value still fails closed: there is nothing to
/// register, and it cannot be rebuilt from a header alone.
#[test]
fn test_dependency_loader_rejects_value_less_definition_replay() {
    let shard = build_guard_shard(&[
        (
            "Good.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Missing.def",
            ImportConfidence::KernelVerified,
            DeclKind::Definition,
            /* has_value */ false,
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
        TrustGate::Strict,
    ));

    assert!(detail.contains("Missing.def"), "{detail}");
    assert!(detail.contains("definition"), "{detail}");
}
