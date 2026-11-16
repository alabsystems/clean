// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `mathverse_use` and `mathverse_suggest` tactics.

use clean_kernel::{Environment, Expr, Level};

use super::mathverse_use::{eval_mathverse_suggest, eval_mathverse_use};
use super::{ProofState, TacticError};

#[test]
fn test_mathverse_use_no_goals_returns_error() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    // Close the goal so no goals remain
    let _ = super::sorry(&mut state);
    assert!(state.is_complete());

    let result = eval_mathverse_use(&mut state, &[]);
    assert!(result.is_err());
}

#[test]
fn test_mathverse_suggest_no_goals_returns_error() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    let _ = super::sorry(&mut state);
    assert!(state.is_complete());

    let result = eval_mathverse_suggest(&mut state, &[]);
    assert!(result.is_err());
}

#[test]
fn test_mathverse_use_without_library_returns_search_exhausted() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    let result = eval_mathverse_use(&mut state, &[]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    match &err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_use");
            // Either "not enabled" or "no Mathverse Library loaded" depending on feature
            assert!(
                detail.contains("mathverse") || detail.contains("Mathverse"),
                "detail should mention mathverse: {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

#[test]
fn test_mathverse_suggest_without_library_returns_search_exhausted() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    let result = eval_mathverse_suggest(&mut state, &[]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    match &err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_suggest");
            assert!(
                detail.contains("mathverse") || detail.contains("Mathverse"),
                "detail should mention mathverse: {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

#[test]
fn test_mathverse_use_registered_in_builtins() {
    // Verify the tactics are registered by building a fresh registry
    let patterns = super::builtins::builtin_tactic_patterns();

    assert!(
        patterns.contains_key("mathverse_use"),
        "mathverse_use should be registered in builtin tactics"
    );
    assert!(
        patterns.contains_key("mathverse_suggest"),
        "mathverse_suggest should be registered in builtin tactics"
    );
}

// Trust gate tests (require mathverse-library feature).

#[cfg(feature = "mathverse-library")]
mod trust_gate_tests {
    use super::super::mathverse_use::{validate_dependency_loader_trust, TrustGate};
    use super::*;
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use clean_mathverse::library::MathverseLibrary;
    use clean_mathverse::premise_select::{MatchReason, PremiseCandidate};
    use clean_mathverse::shard::{ShardReader, ShardWriter};
    use clean_mathverse::trust::policy::TrustPolicy;
    use clean_mathverse::types::{
        AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader,
        SourceSystem, TrustLevel, NO_VALUE,
    };

    #[test]
    fn test_trust_gate_strict_rejects_unverified() {
        let gate = TrustGate::Strict;
        assert!(!gate.accepts(ImportConfidence::Unverified));
        assert!(!gate.accepts(ImportConfidence::Translated));
        assert!(!gate.accepts(ImportConfidence::Axiomatized));
        assert!(!gate.accepts(ImportConfidence::SourceVerified));
    }

    #[test]
    fn test_trust_gate_strict_accepts_kernel_verified() {
        let gate = TrustGate::Strict;
        assert!(gate.accepts(ImportConfidence::KernelVerified));
    }

    #[test]
    fn test_trust_gate_relaxed_accepts_source_verified() {
        let gate = TrustGate::Relaxed;
        assert!(gate.accepts(ImportConfidence::KernelVerified));
        assert!(gate.accepts(ImportConfidence::SourceVerified));
        assert!(!gate.accepts(ImportConfidence::Translated));
        assert!(!gate.accepts(ImportConfidence::Unverified));
    }

    #[test]
    fn test_trust_gate_relaxed_foundational_confidence_only_is_kernel_verified() {
        // On confidence alone (the candidate-level pre-filter), RelaxedFoundational
        // is byte-identical to Strict — KernelVerified only. A bare confidence
        // cannot prove a constant is a foundational axiom.
        let gate = TrustGate::RelaxedFoundational;
        assert!(gate.accepts(ImportConfidence::KernelVerified));
        assert!(!gate.accepts(ImportConfidence::SourceVerified));
        assert!(!gate.accepts(ImportConfidence::Translated));
        assert!(!gate.accepts(ImportConfidence::Axiomatized));
        assert!(!gate.accepts(ImportConfidence::Unverified));
    }

    #[test]
    fn test_accepts_dependency_relaxed_foundational_admits_foundational_axiom() {
        let gate = TrustGate::RelaxedFoundational;
        // A genuine foundational axiom: declared as Axiom, name in the kernel's
        // FOUNDATIONAL_AXIOMS allowlist, even though it is not KernelVerified.
        for name in ["propext", "Quot.sound", "Classical.choice"] {
            assert!(
                gate.accepts_dependency(ImportConfidence::Axiomatized, DeclKind::Axiom, name),
                "RelaxedFoundational must admit foundational axiom `{name}`"
            );
            assert!(
                gate.accepts_dependency(ImportConfidence::Unverified, DeclKind::Axiom, name),
                "RelaxedFoundational must admit foundational axiom `{name}` regardless of confidence"
            );
        }
    }

    #[test]
    fn test_accepts_dependency_relaxed_foundational_rejects_domain_axiom() {
        let gate = TrustGate::RelaxedFoundational;
        // A domain-specific axiom (NOT in FOUNDATIONAL_AXIOMS) must be rejected
        // even though it is declared as an Axiom.
        assert!(!gate.accepts_dependency(
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            "MyDomain.bigConjecture"
        ));
        // `Rat.left_distrib` is a real ADMITTED_DOMAIN_AXIOMS-class name that
        // `is_foundational_axiom` returns false for: must be rejected.
        assert!(!gate.accepts_dependency(
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            "Rat.left_distrib"
        ));
        // Trust markers are never foundational.
        assert!(!gate.accepts_dependency(
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            "sorryAx"
        ));
    }

    #[test]
    fn test_accepts_dependency_relaxed_foundational_requires_axiom_kind() {
        let gate = TrustGate::RelaxedFoundational;
        // A NON-axiom declaration that merely shares a foundational name must
        // NOT slip through: the foundational branch requires DeclKind::Axiom.
        // (Only meaningful when not KernelVerified.)
        assert!(!gate.accepts_dependency(
            ImportConfidence::Axiomatized,
            DeclKind::Theorem,
            "propext"
        ));
        assert!(!gate.accepts_dependency(
            ImportConfidence::Axiomatized,
            DeclKind::Definition,
            "Classical.choice"
        ));
    }

    #[test]
    fn test_accepts_dependency_strict_and_relaxed_ignore_foundational_axioms() {
        // Strict / Relaxed must be byte-identical to confidence-only acceptance:
        // a foundational axiom that is NOT KernelVerified is rejected by both
        // (no RelaxedFoundational widening leaks into them).
        assert!(!TrustGate::Strict.accepts_dependency(
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            "propext"
        ));
        assert!(!TrustGate::Relaxed.accepts_dependency(
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
            "propext"
        ));
        // But a KernelVerified dep is accepted by all gates (the shared half).
        for gate in [
            TrustGate::Strict,
            TrustGate::Relaxed,
            TrustGate::RelaxedFoundational,
        ] {
            assert!(gate.accepts_dependency(
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                "Some.kv.theorem"
            ));
        }
    }

    fn build_guard_shard(constants: &[(&str, ImportConfidence, DeclKind, bool)]) -> ShardReader {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let sort0 = writer.add_expr(FlatExpr::sort(l0));

        for &(name, confidence, decl_kind, has_value) in constants {
            let name_idx = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx,
                type_idx: sort0,
                value_idx: if has_value { sort0 } else { NO_VALUE },
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: confidence as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: decl_kind as u8,
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
    }

    fn premise_candidate(lib: &MathverseLibrary, idx: u32) -> PremiseCandidate {
        let header = *lib.get_constant(idx).unwrap();
        PremiseCandidate {
            name: lib.get_name(idx).unwrap().to_string(),
            constant_idx: idx,
            score: 1.0,
            source_system: SourceSystem::Lean4,
            trust_level: TrustLevel::KernelVerified,
            match_reason: MatchReason::TypeUnification,
            header,
        }
    }

    fn detail_from_result(result: Result<(), TacticError>) -> String {
        match result.expect_err("guard should fail closed") {
            TacticError::SearchExhausted { tactic, detail } => {
                assert_eq!(tactic, "mathverse_use");
                detail
            }
            other => panic!("expected SearchExhausted, got {other:?}"),
        }
    }

    /// Same, but tolerant of which tactic label the citation entry point stamps.
    fn detail_from_apply_result(result: Result<(), TacticError>) -> String {
        match result.expect_err("citation should fail closed") {
            TacticError::SearchExhausted { detail, .. } => detail,
            other => panic!("expected SearchExhausted, got {other:?}"),
        }
    }

    /// A two-row shard: `Root.thm` (row 0) depending on `Dep` (row 1), where
    /// `Dep`'s type and universe parameters are given explicitly. Everything is
    /// `KernelVerified` so the confidence gate never fires and the resident-type
    /// comparison is the only thing under test.
    ///
    /// `build_dep_type` receives the writer and returns `Dep`'s `type_idx`.
    fn build_resident_probe_shard(
        dep_name: &str,
        dep_kind: DeclKind,
        dep_level_params: &[&str],
        build_dep_type: impl FnOnce(&mut ShardWriter) -> u32,
        extra_rows: impl FnOnce(&mut ShardWriter),
    ) -> ShardReader {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let sort0 = writer.add_expr(FlatExpr::sort(l0));

        let root_name = writer.add_string("Root.thm");
        writer.add_constant(MathverseConstantHeader {
            name_idx: root_name,
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

        let lp_start = writer.add_string_block(dep_level_params);
        let dep_type = build_dep_type(&mut writer);
        let dep_name_idx = writer.add_string(dep_name);
        let has_value = matches!(
            dep_kind,
            DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque
        );
        writer.add_constant(MathverseConstantHeader {
            name_idx: dep_name_idx,
            type_idx: dep_type,
            value_idx: if has_value { sort0 } else { NO_VALUE },
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: dep_kind as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: lp_start,
            level_params_count: u16::try_from(dep_level_params.len()).unwrap(),
            _pad2: [0u8; 26],
        });

        extra_rows(&mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    }

    fn probe_library(shard: &ShardReader) -> MathverseLibrary {
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(shard).unwrap();
        lib.add_dependency(0, 1);
        lib
    }

    /// Flatten a kernel `Level` into `writer`. Core variants only.
    fn add_kernel_level(writer: &mut ShardWriter, level: &Level) -> u32 {
        match level {
            Level::Zero => writer.add_level(FlatLevel::zero()),
            Level::Succ(inner) => {
                let inner_idx = add_kernel_level(writer, inner);
                writer.add_level(FlatLevel::succ(inner_idx))
            }
            Level::Max(l, r) => {
                let li = add_kernel_level(writer, l);
                let ri = add_kernel_level(writer, r);
                writer.add_level(FlatLevel::max(li, ri))
            }
            Level::Param(name) => {
                let name_idx = writer.add_string(&name.to_string());
                writer.add_level(FlatLevel::param(name_idx))
            }
            // `FlatLevel` exposes no `imax` constructor; no test needs one.
            Level::IMax(..) => panic!("test helper cannot encode an imax level"),
        }
    }

    /// Flatten a kernel `Expr` into `writer`, returning its expression index.
    ///
    /// Core variants only, and it PANICS on anything else rather than encoding
    /// an approximation — a synthetic shard row that silently differs from the
    /// expression the test meant would defeat the very check under test.
    fn add_kernel_expr(writer: &mut ShardWriter, expr: &Expr) -> u32 {
        use clean_kernel::ExprKind;
        match expr.kind() {
            ExprKind::BVar(idx) => writer.add_expr(FlatExpr::bvar(*idx)),
            ExprKind::Sort(level) => {
                let level_idx = add_kernel_level(writer, level);
                writer.add_expr(FlatExpr::sort(level_idx))
            }
            ExprKind::Const(name, levels) => {
                let name_idx = writer.add_string(&name.to_string());
                let list_idx = if levels.is_empty() {
                    u32::MAX
                } else {
                    let indices: Vec<u32> = levels
                        .iter()
                        .map(|level| add_kernel_level(writer, level))
                        .collect();
                    writer.add_level_list(&indices)
                };
                writer.add_expr(FlatExpr::const_ref(name_idx, list_idx))
            }
            ExprKind::App(func, arg) => {
                let fi = add_kernel_expr(writer, func);
                let ai = add_kernel_expr(writer, arg);
                writer.add_expr(FlatExpr::app(fi, ai))
            }
            ExprKind::Lam(bd, ty, body) => {
                let ti = add_kernel_expr(writer, ty);
                let bi = add_kernel_expr(writer, body);
                writer.add_expr(FlatExpr::lam(binder_info_u8(bd.info), ti, bi))
            }
            ExprKind::Pi(bd, ty, body) => {
                let ti = add_kernel_expr(writer, ty);
                let bi = add_kernel_expr(writer, body);
                writer.add_expr(FlatExpr::pi(binder_info_u8(bd.info), ti, bi))
            }
            other => panic!("test helper cannot encode {other:?}"),
        }
    }

    fn binder_info_u8(info: clean_kernel::BinderInfo) -> u8 {
        match info {
            clean_kernel::BinderInfo::Default => 0,
            clean_kernel::BinderInfo::Implicit => 1,
            clean_kernel::BinderInfo::StrictImplicit => 2,
            clean_kernel::BinderInfo::InstImplicit => 3,
        }
    }

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

    // ---------------------------------------------------------------------
    // RelaxedFoundational trust gate (the USABILITY lever).
    //
    // Its foundational half admits a non-KV dependency by NAME and kind, and,
    // since e20128880, only as the kernel's CANONICAL declaration in the live
    // environment. A kernel-checked resident is admitted under every gate by
    // the residency rule (after the kind and type-agreement checks), so on a
    // foundational dependency the two gates agree on the verdict; they differ
    // in the reason they give when the environment holds no canonical one.
    // ---------------------------------------------------------------------

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
        assert!(
            !env.is_canonical_foundational_axiom(&clean_kernel::name::Name::from_string("propext"))
        );
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

    // -----------------------------------------------------------------------
    // mathverse_apply <name> — cite BY NAME with argument synthesis.
    //
    // This is the capability `mathverse_use` cannot express: it is nullary
    // SEARCH, applies whatever premise selection ranks first, and closes only
    // when the candidate's WHOLE type unifies. These pin the by-name contract.
    // -----------------------------------------------------------------------

    /// An unknown name is a clear, actionable refusal — not a silent miss.
    #[test]
    fn test_mathverse_apply_unknown_name_reports_it() {
        let shard = build_guard_shard(&[(
            "Known.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        )]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        super::super::mathverse_use::set_mathverse_library(lib);

        let mut state = ProofState::new(Environment::new(), Expr::prop());
        let err = super::super::mathverse_use::mathverse_apply_named(
            &mut state,
            "Totally.Absent.lemma",
            TrustGate::Strict,
        )
        .expect_err("an unknown name must not silently succeed");
        match err {
            TacticError::SearchExhausted { tactic, detail } => {
                assert_eq!(tactic, "mathverse_apply");
                assert!(
                    detail.contains("Totally.Absent.lemma"),
                    "the refusal must name the constant asked for: {detail}"
                );
            }
            other => panic!("expected SearchExhausted, got {other:?}"),
        }
        super::super::mathverse_use::clear_mathverse_library();
    }

    // -----------------------------------------------------------------------
    // TYPE SUBSTITUTION — the guard, and its permissiveness budget.
    //
    // `validate_dependency_loader_trust`'s residency discriminator used to
    // branch on KIND only:
    //
    //     DeclKind::Inductive   => env.get_inductive(name).is_some(),
    //     DeclKind::Constructor => env.get_constructor(name).is_some(),
    //     DeclKind::Recursor    => env.get_recursor(name).is_some(),
    //     _ => true,                     // Definition/Theorem/Opaque/Axiom
    //
    // so a resident sharing a name AND a kind with a shard row but differing in
    // TYPE was admitted, and the citation reported success about the shard's
    // declaration while resting on Clean's. The first two tests below exercise
    // exactly that path and now assert a REJECTION; the rest pin the
    // permissiveness that keeps the check from mass-rejecting legitimate
    // dependencies.
    // -----------------------------------------------------------------------

    /// Shard `Victim.def : Prop`; resident `Victim.def : Prop → Prop`.
    /// Same name, same kind, DIFFERENT type — and the gate must now say no.
    #[test]
    fn test_resident_definition_with_different_type_is_rejected() {
        let shard = build_guard_shard(&[
            (
                "Good.thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            // `build_guard_shard` gives every row the type `Sort 0` (Prop).
            (
                "Victim.def",
                ImportConfidence::KernelVerified,
                DeclKind::Definition,
                /* has_value */ true,
            ),
        ]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(0, 1);

        let mut env = Environment::new();
        let prop = Expr::sort(Level::zero());
        // Resident type is `Prop → Prop`, NOT the shard's `Prop`. Not even
        // definitionally equal — there is no reduction from one to the other.
        env.add_decl(clean_kernel::Declaration::Definition {
            name: clean_kernel::Name::from_string("Victim.def"),
            level_params: vec![],
            type_: Expr::pi(
                clean_kernel::BinderInfo::Default,
                prop.clone(),
                prop.clone(),
            ),
            value: Expr::lam(clean_kernel::BinderInfo::Default, prop, Expr::bvar(0)),
            is_reducible: false,
        })
        .expect("the resident definition is well-typed and must register");
        assert_eq!(
            env.declaration_verification(&clean_kernel::Name::from_string("Victim.def")),
            Some(clean_kernel::DeclarationVerification::FullKernelCheck),
            "precondition: the resident IS fully kernel-checked — that is what \
             makes this hole invisible to the verdict test and to the kind test"
        );

        let candidate = premise_candidate(&lib, 0);
        for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
            let detail = detail_from_result(validate_dependency_loader_trust(
                &env, &candidate, &lib, gate,
            ));
            assert!(
                detail.contains("Victim.def") && detail.contains("type substitution"),
                "{gate:?} must reject the type-substituted resident by name: {detail}"
            );
        }
        // …and `Relaxed`, the explicitly weaker bang-variant gate, is untouched.
        assert!(
            validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Relaxed).is_ok(),
            "the type-agreement check is scoped to the gates that demand KernelVerified"
        );
    }

    /// The other half of the measurement: a resident that genuinely IS the shard
    /// row must still be admitted. Same shape as the test above — a `Definition`
    /// row against a `Definition` resident — with the type made to agree.
    #[test]
    fn test_resident_definition_with_matching_type_is_admitted() {
        // Shard `Victim.def : Type`; resident `Victim.def : Type := Prop`.
        let shard = build_resident_probe_shard(
            "Victim.def",
            DeclKind::Definition,
            &[],
            |w| {
                let l0 = w.add_level(FlatLevel::zero());
                let l1 = w.add_level(FlatLevel::succ(l0));
                w.add_expr(FlatExpr::sort(l1))
            },
            |_| {},
        );
        let lib = probe_library(&shard);

        let mut env = Environment::new();
        env.add_decl(clean_kernel::Declaration::Definition {
            name: clean_kernel::Name::from_string("Victim.def"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: false,
        })
        .expect("resident registers");

        let candidate = premise_candidate(&lib, 0);
        for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
            assert!(
                validate_dependency_loader_trust(&env, &candidate, &lib, gate).is_ok(),
                "a resident whose type agrees with the shard row must still be admitted under \
                 {gate:?} — over-rejection here collapses citability"
            );
        }
    }

    /// The canonicalization cannot be turned into a false MATCH by pre-spelling
    /// its reserved names. Shard `Dep.{u} : Sort _mathverse_lp_0` (`u` declared
    /// but unused) against resident `Dep.{u} : Sort u`: without the guard the
    /// resident's `u` renames to `_mathverse_lp_0` and the two become
    /// structurally identical.
    #[test]
    fn test_reserved_level_namespace_cannot_forge_a_match() {
        let shard = build_resident_probe_shard(
            "Dep",
            DeclKind::Axiom,
            &["u"],
            |w| {
                let forged = w.add_string("_mathverse_lp_0");
                let level = w.add_level(FlatLevel::param(forged));
                w.add_expr(FlatExpr::sort(level))
            },
            |_| {},
        );
        let lib = probe_library(&shard);

        let mut env = Environment::new();
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Dep"),
            level_params: vec![clean_kernel::Name::from_string("u")],
            type_: Expr::sort(Level::param(clean_kernel::Name::from_string("u"))),
        })
        .expect("resident registers");

        let candidate = premise_candidate(&lib, 0);
        let detail = detail_from_result(validate_dependency_loader_trust(
            &env,
            &candidate,
            &lib,
            TrustGate::Strict,
        ));
        assert!(
            detail.contains("reserved"),
            "the refusal must name the reserved-namespace guard: {detail}"
        );
    }

    /// Universe-parameter ARITY is decided from the header alone, before any
    /// reconstruction, and a mismatch is never benign. (`List.zip` is the
    /// measured real instance: 2 shard params against the prelude's 1.)
    #[test]
    fn test_resident_with_different_universe_arity_is_rejected() {
        // The shard row declares 0 universe parameters; the resident declares 1.
        let shard = build_resident_probe_shard(
            "Poly.def",
            DeclKind::Axiom,
            &[],
            |w| {
                let l0 = w.add_level(FlatLevel::zero());
                w.add_expr(FlatExpr::sort(l0))
            },
            |_| {},
        );
        let lib = probe_library(&shard);

        let mut env = Environment::new();
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Poly.def"),
            level_params: vec![clean_kernel::Name::from_string("u")],
            type_: Expr::sort(Level::zero()),
        })
        .expect("resident registers");

        let candidate = premise_candidate(&lib, 0);
        let detail = detail_from_result(validate_dependency_loader_trust(
            &env,
            &candidate,
            &lib,
            TrustGate::Strict,
        ));
        assert!(
            detail.contains("universe parameter"),
            "the refusal must name the universe-arity difference: {detail}"
        );
    }

    /// PERMISSIVENESS 1 — universe parameter NAMES and ORDER are irrelevant.
    /// Shard `Dep.{a, b} : Sort a → Sort b`, resident `Dep.{v, u} : Sort v → Sort u`.
    /// This is the real `Eq.ndrec` shape (shard `[u1, u2]`, prelude `[v, u]`);
    /// comparing under the declared names would reject it.
    #[test]
    fn test_resident_with_renamed_universe_params_is_admitted() {
        let shard = build_resident_probe_shard(
            "Dep",
            DeclKind::Axiom,
            &["a", "b"],
            |w| {
                let na = w.add_string("a");
                let nb = w.add_string("b");
                let la = w.add_level(FlatLevel::param(na));
                let lb = w.add_level(FlatLevel::param(nb));
                let sa = w.add_expr(FlatExpr::sort(la));
                let sb = w.add_expr(FlatExpr::sort(lb));
                w.add_expr(FlatExpr::pi(0, sa, sb))
            },
            |_| {},
        );
        let lib = probe_library(&shard);

        let mut env = Environment::new();
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Dep"),
            level_params: vec![
                clean_kernel::Name::from_string("v"),
                clean_kernel::Name::from_string("u"),
            ],
            type_: Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::sort(Level::param(clean_kernel::Name::from_string("v"))),
                Expr::sort(Level::param(clean_kernel::Name::from_string("u"))),
            ),
        })
        .expect("resident registers");

        let candidate = premise_candidate(&lib, 0);
        assert!(
            validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict).is_ok(),
            "a universe-parameter RENAMING must not be read as a different declaration"
        );
    }

    /// PERMISSIVENESS 2 — the comparison is DEFINITIONAL, not syntactic.
    /// Shard `Dep : Prop`, resident `Dep : Alias` where `Alias : Type := Prop`.
    /// Structurally `Const Alias` and `Sort 0` are unrelated; one delta step
    /// identifies them. This miniature stands in for the measured real case —
    /// shard `Not p` against the prelude's `p → False` — which is worth 158/308
    /// probes on the Mathlib population.
    #[test]
    fn test_resident_definitionally_equal_type_is_admitted() {
        let shard = build_resident_probe_shard(
            "Dep",
            DeclKind::Axiom,
            &[],
            |w| {
                let l0 = w.add_level(FlatLevel::zero());
                w.add_expr(FlatExpr::sort(l0))
            },
            |_| {},
        );
        let lib = probe_library(&shard);

        let mut env = Environment::new();
        env.add_decl(clean_kernel::Declaration::Definition {
            name: clean_kernel::Name::from_string("Alias"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: false,
        })
        .expect("`Alias : Type := Prop` registers");
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Dep"),
            level_params: vec![],
            type_: Expr::const_str("Alias"),
        })
        .expect("resident registers");

        assert_ne!(
            Expr::const_str("Alias"),
            Expr::sort(Level::zero()),
            "precondition: the two types are NOT structurally equal, so this test \
             genuinely exercises the definitional rung"
        );
        let candidate = premise_candidate(&lib, 0);
        assert!(
            validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict).is_ok(),
            "a definitionally equal resident type must be admitted"
        );
    }

    /// Add a shard row for a binder gadget whose VALUE is `fun a₁ … aₙ => a_k`.
    /// `k == 1` is the genuine identity; anything else must not be erased.
    fn add_gadget_row(writer: &mut ShardWriter, name: &str, arity: usize, returns: usize) {
        let l0 = writer.add_level(FlatLevel::zero());
        let sort0 = writer.add_expr(FlatExpr::sort(l0));
        // de Bruijn: the k-th binder from the outside is index `arity - k`.
        let mut body = writer.add_expr(FlatExpr::bvar(u32::try_from(arity - returns).unwrap()));
        for _ in 0..arity {
            body = writer.add_expr(FlatExpr::lam(0, sort0, body));
        }
        let name_idx = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: sort0,
            value_idx: body,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }

    /// Shard `Dep : outParam Prop` against resident `Dep : Prop`. `outParam` is
    /// absent from the environment, so `is_def_eq` cannot delta it; the erasure
    /// rung must — but ONLY because the shard's own `outParam` value is proved
    /// here to be `fun α => α`. This is the measured `Membership` /
    /// `Membership.mem` case, worth 7/308 probes.
    #[test]
    fn test_resident_under_verified_identity_gadget_is_admitted() {
        let shard = build_resident_probe_shard(
            "Dep",
            DeclKind::Axiom,
            &[],
            |w| {
                let l0 = w.add_level(FlatLevel::zero());
                let sort0 = w.add_expr(FlatExpr::sort(l0));
                let out = w.add_string("outParam");
                let out_ref = w.add_expr(FlatExpr::const_ref(out, u32::MAX));
                w.add_expr(FlatExpr::app(out_ref, sort0))
            },
            |w| add_gadget_row(w, "outParam", 1, 1),
        );
        let lib = probe_library(&shard);

        let mut env = Environment::new();
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Dep"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .expect("resident registers");
        assert!(
            env.get_const(&clean_kernel::Name::from_string("outParam"))
                .is_none(),
            "precondition: the gadget is NOT resident, which is what makes is_def_eq \
             unable to decide this on its own"
        );

        let candidate = premise_candidate(&lib, 0);
        assert!(
            validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict).is_ok(),
            "an `outParam`-wrapped shard type must not be read as a different declaration"
        );
    }

    /// The erasure is EARNED, not assumed. Same shape as above, but the shard's
    /// `outParam` is `fun a b => b` — not the identity on its first argument — so
    /// nothing is erased and the dependency is rejected.
    #[test]
    fn test_gadget_erasure_requires_a_verified_identity_value() {
        let shard = build_resident_probe_shard(
            "Dep",
            DeclKind::Axiom,
            &[],
            |w| {
                let l0 = w.add_level(FlatLevel::zero());
                let sort0 = w.add_expr(FlatExpr::sort(l0));
                let out = w.add_string("outParam");
                let out_ref = w.add_expr(FlatExpr::const_ref(out, u32::MAX));
                w.add_expr(FlatExpr::app(out_ref, sort0))
            },
            // Two binders, returns the SECOND — the shard's `outParam` is not the
            // identity on its first argument.
            |w| add_gadget_row(w, "outParam", 2, 2),
        );
        let lib = probe_library(&shard);

        let mut env = Environment::new();
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Dep"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .expect("resident registers");

        let candidate = premise_candidate(&lib, 0);
        let detail = detail_from_result(validate_dependency_loader_trust(
            &env,
            &candidate,
            &lib,
            TrustGate::Strict,
        ));
        assert!(
            detail.contains("type substitution"),
            "a gadget whose shard value is not the identity must not be erased: {detail}"
        );
    }

    /// End to end. Before the type-agreement check this citation CLOSED the goal
    /// and reported success while a member of the closure it claimed was the
    /// shard's was really Clean's own differently-typed declaration — never
    /// replaced, because the loader only adds names it finds ABSENT. It must now
    /// fail closed, and the resident must be left exactly as it was found.
    #[test]
    fn test_citation_refuses_to_rest_on_differently_typed_resident() {
        use clean_kernel::flat::FlatExpr;
        use clean_mathverse::shard::ShardWriter;

        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let sort0 = writer.add_expr(FlatExpr::sort(l0));
        let true_name = writer.add_string("True");
        let true_intro_name = writer.add_string("True.intro");
        let true_ref = writer.add_expr(FlatExpr::const_ref(true_name, u32::MAX));
        let true_intro_ref = writer.add_expr(FlatExpr::const_ref(true_intro_name, u32::MAX));

        // Row 0 — the cited theorem: `Exploit.thm : True := True.intro`.
        let thm_name = writer.add_string("Exploit.thm");
        writer.add_constant(MathverseConstantHeader {
            name_idx: thm_name,
            type_idx: true_ref,
            value_idx: true_intro_ref,
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
        // Row 1 — a closure member whose shard type is `Prop`.
        let victim_name = writer.add_string("Victim.def");
        writer.add_constant(MathverseConstantHeader {
            name_idx: victim_name,
            type_idx: sort0,
            value_idx: sort0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
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

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(0, 1);
        super::super::mathverse_use::set_mathverse_library(lib);

        // The session environment: a real prelude plus Clean's own `Victim.def`,
        // whose type is `Prop → Prop` where the shard row says `Prop`.
        let mut env = Environment::with_prelude();
        let prop = Expr::sort(Level::zero());
        let resident_type = Expr::pi(
            clean_kernel::BinderInfo::Default,
            prop.clone(),
            prop.clone(),
        );
        env.add_decl(clean_kernel::Declaration::Definition {
            name: clean_kernel::Name::from_string("Victim.def"),
            level_params: vec![],
            type_: resident_type.clone(),
            value: Expr::lam(clean_kernel::BinderInfo::Default, prop, Expr::bvar(0)),
            is_reducible: false,
        })
        .expect("resident registers");

        let goal = Expr::const_str("True");
        let mut state = ProofState::new(env, goal);
        let closed = super::super::mathverse_use::mathverse_apply_named(
            &mut state,
            "Exploit.thm",
            TrustGate::Strict,
        );
        let detail = detail_from_apply_result(closed);
        assert!(
            detail.contains("Victim.def") && detail.contains("type substitution"),
            "the citation must fail CLOSED and name the substituted closure member: {detail}"
        );
        assert!(
            !state.is_complete(),
            "the goal must NOT be discharged — that silent success is the bug"
        );

        // The session is left exactly as it was found.
        let resident_after = state
            .env
            .get_const(&clean_kernel::Name::from_string("Victim.def"))
            .expect("Victim.def is still resident")
            .clone();
        assert_eq!(
            resident_after.type_, resident_type,
            "a refused citation must not mutate the resident declaration"
        );
        super::super::mathverse_use::clear_mathverse_library();
    }

    /// With NO library installed the failure names that cause specifically,
    /// rather than looking like "lemma not found".
    #[test]
    fn test_mathverse_apply_without_library_says_so() {
        super::super::mathverse_use::clear_mathverse_library();
        let mut state = ProofState::new(Environment::new(), Expr::prop());
        let err = super::super::mathverse_use::mathverse_apply_named(
            &mut state,
            "Any.name",
            TrustGate::Strict,
        )
        .expect_err("no library installed must fail");
        match err {
            TacticError::SearchExhausted { detail, .. } => assert!(
                detail.contains("no Mathverse Library loaded"),
                "must distinguish 'no library' from 'no such lemma': {detail}"
            ),
            other => panic!("expected SearchExhausted, got {other:?}"),
        }
    }
}

// Disc-tree regression tests for #3412.
//
// These tests pin the tactic-layer wiring: eval_mathverse_suggest (and thus
// eval_mathverse_use) populate goal_type_idx and exercise the discrimination
// tree. The library side of this fix is covered in
// `clean-mathverse::premise_select` tests; these tests are a tactic-layer guard
// that future refactors do not regress the disc-tree query path back to
// None-only, name-only search.
//
// Distinguishing disc-tree from name/BM25/symbol-overlap channels is done by
// using a candidate whose stored name shares zero tokens with the goal's
// extracted symbols. The only channel that can surface it is the disc tree.

#[cfg(feature = "mathverse-library")]
mod disc_tree_tactic_wiring {
    use super::*;
    use clean_kernel::expr::BinderInfo;
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use clean_mathverse::library::MathverseLibrary;
    use clean_mathverse::shard::{ShardReader, ShardWriter};
    use clean_mathverse::trust::policy::TrustPolicy;
    use clean_mathverse::types::{
        AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
    };

    /// Build a shard holding a single constant whose name has NO token overlap
    /// with the goal's extracted symbols ("Nat"), but whose stored type is
    /// structurally `Pi(Nat, Nat)`. If the discrimination tree is queried, the
    /// constant is found via `MatchReason::TypeUnification`; otherwise BM25
    /// and the symbol-overlap fallback both miss (the constant's tokens are
    /// `zzz`, `qqq`, `unique`, `premise`, `xyz` — none match `Nat`).
    fn build_type_only_shard() -> ShardReader {
        let mut writer = ShardWriter::new();

        // "Nat" is the goal's constant name. Intern it so the disc tree's
        // stored paths share a name_idx with the query expression built at
        // search time (via `MathverseLibrary::add_query_expr`).
        let nat_name_idx = writer.add_string("Nat");

        // Deliberately exotic constant name with zero token overlap with "Nat".
        let cst_name_idx = writer.add_string("zzz_qqq_unique_premise_xyz");

        let l0 = writer.add_level(FlatLevel::zero());
        let sort0 = writer.add_expr(FlatExpr::sort(l0));

        // Pi(Nat, Nat): two separate Nat const refs, bound under a Pi.
        let nat_a = writer.add_expr(FlatExpr::const_ref(nat_name_idx, u32::MAX));
        let nat_b = writer.add_expr(FlatExpr::const_ref(nat_name_idx, u32::MAX));
        let pi_nat_nat = writer.add_expr(FlatExpr::pi(0, nat_a, nat_b));

        writer.add_constant(MathverseConstantHeader {
            name_idx: cst_name_idx,
            type_idx: pi_nat_nat,
            value_idx: sort0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    }

    /// RAII guard that clears the thread-local MathverseLibrary on drop so a
    /// test leak cannot poison sibling tests on the same thread.
    struct MathverseLibGuard;
    impl Drop for MathverseLibGuard {
        fn drop(&mut self) {
            super::super::mathverse_use::clear_mathverse_library();
        }
    }

    #[test]
    fn test_mathverse_suggest_uses_disc_tree_at_tactic_layer() {
        // Regression guard for #3412. Before the fix, `eval_mathverse_suggest`
        // passed `None` for `goal_type_idx`, making the discrimination tree
        // (60% of ranking weight by default) dead code. This test would fail
        // in the pre-fix behavior because no other channel can surface the
        // stored candidate:
        //   - goal symbols: ["Nat"]  -> BM25 against "zzz_qqq_unique_..." = 0
        //   - symbol overlap: tokens ["zzz","qqq","unique","premise","xyz"]
        //     vs ["Nat"] -> 0
        //   - dependency neighbors: empty (no context_names)
        let _guard = MathverseLibGuard;

        let shard = build_type_only_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        super::super::mathverse_use::set_mathverse_library(lib);

        // Goal: Pi(Nat, Nat). eval_mathverse_suggest only reads the goal for
        // search; it never closes. A kernel Expr is fine even though
        // Pi(Nat,Nat) is a type, not a Prop.
        let nat_a = Expr::const_str("Nat");
        let nat_b = Expr::const_str("Nat");
        let goal = Expr::pi(BinderInfo::Default, nat_a, nat_b);

        let env = Environment::new();
        let mut state = ProofState::new(env, goal);

        let result = eval_mathverse_suggest(&mut state, &[]);
        let err = result.expect_err("mathverse_suggest never closes the goal");
        match err {
            TacticError::SearchExhausted { tactic, detail } => {
                assert_eq!(tactic, "mathverse_suggest");
                assert!(
                    detail.contains("showing") && detail.contains("candidate"),
                    "disc tree must surface >=1 candidate; got detail: {detail}"
                );
                assert!(
                    !detail.contains("no candidates found"),
                    "disc tree wired -> must not report 'no candidates found': {detail}"
                );
            }
            other => panic!("expected SearchExhausted, got {other:?}"),
        }
    }

    #[test]
    fn test_mathverse_suggest_returns_no_candidates_when_every_channel_misses() {
        // Negative control. Confirms the positive test above is attributable
        // to the disc tree and not a spurious "everything matches" bug.
        // Goal symbols are unknown strings absent from the shard's string
        // table, so the disc tree's name_idx lookups on the goal's Const
        // nodes miss all stored paths. The symbol-overlap fallback also
        // misses: none of the goal's tokens overlap with the shard constant's
        // exotic name.
        let _guard = MathverseLibGuard;

        let shard = build_type_only_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        super::super::mathverse_use::set_mathverse_library(lib);

        let a = Expr::const_str("UnknownSymA_qq");
        let b = Expr::const_str("UnknownSymB_qq");
        let goal = Expr::pi(BinderInfo::Default, a, b);

        let env = Environment::new();
        let mut state = ProofState::new(env, goal);

        let result = eval_mathverse_suggest(&mut state, &[]);
        let err = result.expect_err("mathverse_suggest never closes the goal");
        match err {
            TacticError::SearchExhausted { tactic, detail } => {
                assert_eq!(tactic, "mathverse_suggest");
                assert!(
                    detail.contains("no candidates found"),
                    "no channel should match; got detail: {detail}"
                );
            }
            other => panic!("expected SearchExhausted, got {other:?}"),
        }
    }
}

#[cfg(feature = "mathverse-library")]
mod native_replay_gate {
    use super::*;
    use clean_kernel::{BinderInfo, Declaration, Name};
    use clean_mathverse::export::kernel_export::KernelShardBuilder;
    use clean_mathverse::library::MathverseLibrary;
    use clean_mathverse::premise_select::{search_for_kernel_goal, PremiseConfig};
    use clean_mathverse::shard::ShardReader;
    use clean_mathverse::shard_verify::verify_native_shard;
    use clean_mathverse::trust::policy::TrustPolicy;

    struct MathverseLibGuard;
    impl Drop for MathverseLibGuard {
        fn drop(&mut self) {
            super::super::mathverse_use::clear_mathverse_library();
        }
    }

    fn native_replay_dependency() -> Declaration {
        Declaration::Theorem {
            name: Name::from_string("MathverseReplayGate.dep"),
            level_params: vec![],
            type_: Expr::const_str("True"),
            value: Expr::const_str("True.intro"),
        }
    }

    fn native_replay_candidate() -> Declaration {
        let true_prop = Expr::const_str("True");
        let goal_type = Expr::apps(
            Expr::const_str("Iff"),
            [true_prop.clone(), true_prop.clone()],
        );
        let dep = Expr::const_str("MathverseReplayGate.dep");
        let forward = Expr::lam(BinderInfo::Default, true_prop.clone(), dep.clone());
        let backward = Expr::lam(BinderInfo::Default, true_prop.clone(), dep);

        Declaration::Theorem {
            name: Name::from_string("MathverseReplayGate.close_iff_true"),
            level_params: vec![],
            type_: goal_type,
            value: Expr::apps(
                Expr::const_str("Iff.intro"),
                [true_prop.clone(), true_prop, forward, backward],
            ),
        }
    }

    fn build_native_replay_library() -> MathverseLibrary {
        let mut builder = KernelShardBuilder::new();
        builder
            .add_declaration(&native_replay_dependency(), &["mathverse-replay-gate"])
            .expect("export native replay dependency");
        builder
            .add_declaration(&native_replay_candidate(), &["mathverse-replay-gate"])
            .expect("export native replay candidate");

        let tmp = tempfile::tempdir().expect("native replay tempdir");
        let shard_path = tmp.path().join("clean-native.mathverse");
        builder
            .write_to_file(&shard_path)
            .expect("write native replay shard");

        let report = verify_native_shard(&shard_path).expect("run native shard gate");
        assert_eq!(
            report.checked, 2,
            "native replay gate should check both declarations"
        );
        assert!(
            report.violations.is_empty(),
            "native replay shard should pass the strict native gate: {report:?}"
        );

        let bytes = std::fs::read(&shard_path).expect("read verified native replay shard");
        let shard = ShardReader::from_bytes(&bytes).expect("load verified native replay shard");
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard)
            .expect("load verified native replay shard into MathverseLibrary");
        lib
    }

    #[test]
    fn test_strict_mathverse_use_search_verifies_loads_native_deps_and_closes_goal() {
        let _guard = MathverseLibGuard;
        let mut lib = build_native_replay_library();
        let true_prop = Expr::const_str("True");
        let target = Expr::apps(Expr::const_str("Iff"), [true_prop.clone(), true_prop]);

        let candidates = search_for_kernel_goal(
            &mut lib,
            &target,
            &[],
            &PremiseConfig {
                max_results: 3,
                ..PremiseConfig::default()
            },
        );
        assert!(
            candidates
                .iter()
                .any(|candidate| candidate.name == "MathverseReplayGate.close_iff_true"),
            "Mathverse search should produce the native replay candidate: {candidates:?}"
        );

        super::super::mathverse_use::set_mathverse_library(lib);
        let mut state = ProofState::new(Environment::with_prelude(), target);
        eval_mathverse_use(&mut state, &[])
            .expect("strict mathverse_use should close via native replay");

        assert!(
            state.is_complete(),
            "strict mathverse_use should close the goal after loading the native dependency"
        );
        assert!(
            state
                .env
                .get_const(&Name::from_string("MathverseReplayGate.dep"))
                .is_some(),
            "mathverse_use should load the native dependency into the proof environment"
        );
        assert!(
            state
                .env
                .get_const(&Name::from_string("MathverseReplayGate.close_iff_true"))
                .is_some(),
            "mathverse_use should load the selected native theorem into the proof environment"
        );
    }
}

// ---------------------------------------------------------------------------
// UNIT REPRODUCTION of the universe-polymorphic citation failure.
//
// Deliberately uses NO mathverse machinery — no shard, no library, no trust
// gate. The failure is in `mk_const` + `exact` alone, and isolating it here
// turns a 75-second rebuild-plus-shard-load into a millisecond test.
// ---------------------------------------------------------------------------

/// `Poly.{u} : ∀ (A : Sort u), A → A`, proved by `fun A a => a`.
#[cfg(feature = "mathverse-library")]
fn register_poly_id(env: &mut Environment) -> clean_kernel::name::Name {
    use clean_kernel::name::Name;
    use clean_kernel::{BinderInfo, Declaration};
    let u = Name::from_string("u");
    let sort_u = Expr::sort(Level::param(u.clone()));
    // ∀ (A : Sort u), A → A
    let ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    // fun (A : Sort u) (a : A) => a
    let val = Expr::lam(
        BinderInfo::Default,
        sort_u,
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let name = Name::from_string("Poly.id");
    // Definition, not Theorem: `∀ (A : Sort u), A → A` lives in
    // `IMax(Succ(..), u)`, not Prop, and the kernel rightly rejects a Theorem
    // whose type is not a proposition.
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![u],
        type_: ty,
        value: val,
        is_reducible: false,
    })
    .expect("fixture must register");
    name
}

/// A universe-MONOMORPHIC citation closes its own type. Control case: proves
/// the harness itself is sound, so a failure below is about universes only.
#[cfg(feature = "mathverse-library")]
#[test]
fn test_exact_mk_const_closes_monomorphic_own_type() {
    use clean_kernel::name::Name;
    use clean_kernel::{BinderInfo, Declaration};
    let mut env = Environment::new();
    // ∀ (P : Prop), P → P   proved by   fun P p => p
    // (NOT `∀ P, P` — that is false, and the kernel correctly refused it.)
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let val = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let name = Name::from_string("Mono.id");
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: ty.clone(),
        value: val,
    })
    .expect("fixture registers");

    let mut state = ProofState::new(env, ty);
    let e = state.mk_const(&name);
    super::exact(&mut state, e).expect("monomorphic citation of its own type must close");
}

/// THE REPRODUCTION: a universe-POLYMORPHIC citation of its own type.
///
/// `mk_const` instantiates `Poly.id`'s `u` with a fresh `u_0`, while the goal
/// carries the declared `u`, so `exact` compares `Sort(Param(u_0))` against
/// `Sort(Param(u))`. Both are `Level::Param`; `unify_levels` must reconcile
/// them by assigning the fresh one.
#[cfg(feature = "mathverse-library")]
#[test]
fn test_exact_mk_const_closes_universe_polymorphic_own_type() {
    let mut env = Environment::new();
    let name = register_poly_id(&mut env);
    let ty = env.get_const(&name).expect("registered").type_.clone();

    let mut state = ProofState::new(env, ty);
    let e = state.mk_const(&name);
    super::exact(&mut state, e).expect(
        "citing a universe-polymorphic constant against its OWN type must close: \
         mk_const's fresh universe param has to unify with the goal's declared one",
    );
}

/// Tests for the FABRICATED-STUB discharge that lets a citation rest on the
/// shard's genuine declaration instead of a hand-rolled prelude carrier.
///
/// The measured instance is `Fact`: `Environment::with_prelude` seeds
/// `Fact`/`Fact.mk`/`Fact.out` as bare `Declaration::Axiom`s, while Mathlib
/// declares `class Fact (p : Prop) : Prop where out : p`. These tests pin the
/// PREDICATE — which stubs may be retired and which must never be — because a
/// discharge that is one notch too wide silently deletes a genuine axiom, and
/// one notch too narrow leaves the citation resting on a fabrication.
#[cfg(feature = "mathverse-library")]
mod fabricated_stub_discharge {
    use super::super::mathverse_use::{
        discharge_fabricated_stubs_for, restore_unreplaced_stubs, TrustGate,
    };
    use super::*;
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use clean_kernel::name::Name;
    use clean_kernel::Declaration;
    use clean_mathverse::library::MathverseLibrary;
    use clean_mathverse::premise_select::{MatchReason, PremiseCandidate};
    use clean_mathverse::shard::{ShardReader, ShardWriter};
    use clean_mathverse::trust::policy::TrustPolicy;
    use clean_mathverse::types::{
        AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader,
        SourceSystem, TrustLevel, NO_VALUE,
    };

    type Row<'a> = (&'a str, ImportConfidence, DeclKind, bool);

    /// A shard where constant 0 is the cited theorem and every later constant is
    /// one of its dependencies.
    fn shard_with_deps(rows: &[Row<'_>]) -> MathverseLibrary {
        shard_with_closure_and_extras(rows, &[])
    }

    /// As [`shard_with_deps`], plus `extras`: rows the shard declares that are
    /// NOT in the cited theorem's dependency closure (a family's constructor
    /// that the closure never names, as `Fact.mk` is for `Fact.out`).
    fn shard_with_closure_and_extras(closure: &[Row<'_>], extras: &[Row<'_>]) -> MathverseLibrary {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let sort0 = writer.add_expr(FlatExpr::sort(l0));
        for &(name, confidence, decl_kind, has_value) in closure.iter().chain(extras) {
            let name_idx = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx,
                type_idx: sort0,
                value_idx: if has_value { sort0 } else { NO_VALUE },
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: confidence as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: decl_kind as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard must serialize");
        let reader = ShardReader::from_bytes(&buf).expect("shard must parse");
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("shard must load");
        for dep in 1..closure.len() as u32 {
            lib.add_dependency(0, dep);
        }
        lib
    }

    /// `Fact.out`'s closure (`Fact`), with `Fact.mk` declared beside it.
    fn fact_closure_with_constructor_row() -> MathverseLibrary {
        shard_with_closure_and_extras(
            &[
                (
                    "Fact.out",
                    ImportConfidence::KernelVerified,
                    DeclKind::Theorem,
                    true,
                ),
                (
                    "Fact",
                    ImportConfidence::SourceVerified,
                    DeclKind::Inductive,
                    true,
                ),
            ],
            &[(
                "Fact.mk",
                ImportConfidence::SourceVerified,
                DeclKind::Constructor,
                false,
            )],
        )
    }

    fn candidate(lib: &MathverseLibrary) -> PremiseCandidate {
        let header = *lib.get_constant(0).expect("root header");
        PremiseCandidate {
            name: lib.get_name(0).expect("root name").to_string(),
            constant_idx: 0,
            score: 1.0,
            source_system: SourceSystem::Lean4,
            trust_level: TrustLevel::KernelVerified,
            match_reason: MatchReason::TypeUnification,
            header,
        }
    }

    /// A value-free `Axiom` of type `Prop` — the shape every prelude carrier
    /// stub has.
    fn seed_axiom_stub(env: &mut Environment, name: &str) {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .expect("axiom stub must register");
    }

    fn seed_definition(env: &mut Environment, name: &str) {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            // `Sort 1 := Prop` — a value-bearing declaration, the shape
            // `Finset` actually has in the prelude.
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        })
        .expect("definition must register");
    }

    fn resident(env: &Environment, name: &str) -> bool {
        env.get_const(&Name::from_string(name)).is_some()
    }

    #[test]
    fn test_discharge_retires_axiom_stub_shadowing_an_inductive_row() {
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Fact",
                ImportConfidence::SourceVerified,
                DeclKind::Inductive,
                true,
            ),
        ]);
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Fact");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert_eq!(taken.len(), 1, "the shadowing stub must be retired");
        assert!(
            !resident(&env, "Fact"),
            "`Fact` must be absent so the checked family replay can install the genuine structure"
        );
    }

    #[test]
    fn test_discharge_sweeps_family_members_outside_the_closure() {
        // THE MEASURED REGRESSION. `Fact.out`'s closure names `Fact` but NOT
        // `Fact.mk`, so a closure-only discharge left `Fact.mk`'s stub in place
        // and `add_inductive` aborted with `Duplicate declaration: Fact.mk` —
        // which the trust gate then misreported as `Fact ... below Strict`.
        // The shard declares `Fact.mk` outside the closure, so the member
        // authenticates against its own row before it is removed.
        let lib = fact_closure_with_constructor_row();
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Fact");
        seed_axiom_stub(&mut env, "Fact.mk");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert_eq!(taken.len(), 2, "head and its namespace member must both go");
        assert!(!resident(&env, "Fact"));
        assert!(
            !resident(&env, "Fact.mk"),
            "a constructor stub the closure never mentions still collides with add_inductive"
        );
    }

    #[test]
    fn test_discharge_keeps_a_member_stub_the_shard_does_not_declare() {
        // AUTHENTICATE BEFORE REMOVAL: a carrier with no shard row of its own
        // name has nothing to be checked against, so it stays resident and the
        // residency rule refuses the citation on its own diagnostic.
        let lib = shard_with_deps(&[
            (
                "Fact.out",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Fact",
                ImportConfidence::SourceVerified,
                DeclKind::Inductive,
                true,
            ),
        ]);
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Fact");
        seed_axiom_stub(&mut env, "Fact.mk");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert_eq!(
            taken.len(),
            1,
            "only the head, which has a row, is discharged"
        );
        assert!(!resident(&env, "Fact"));
        assert!(
            resident(&env, "Fact.mk"),
            "a member the shard never declares must not be removed"
        );
    }

    #[test]
    fn test_discharge_keeps_a_carrier_whose_type_disagrees_with_its_row() {
        // The row exists, but its type (`Prop`) is not the carrier's (`Type`):
        // everything checked against the carrier would describe a different
        // constant after the swap, so the carrier stays.
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Fact",
                ImportConfidence::SourceVerified,
                DeclKind::Inductive,
                true,
            ),
        ]);
        let mut env = Environment::default();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Fact"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
        })
        .expect("axiom stub must register");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert!(taken.is_empty(), "a disagreeing type is never discharged");
        assert!(resident(&env, "Fact"));
    }

    #[test]
    fn test_discharge_never_touches_a_genuine_value_free_axiom_row() {
        // `propext` is a real axiom on BOTH sides. Removing it would delete a
        // foundational assumption the citation legitimately depends on.
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "propext",
                ImportConfidence::SourceVerified,
                DeclKind::Axiom,
                false,
            ),
        ]);
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "propext");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert!(
            taken.is_empty(),
            "an Axiom shard row is never a fabrication"
        );
        assert!(resident(&env, "propext"));
    }

    #[test]
    fn test_discharge_never_touches_quotient_primitives() {
        // `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` are kernel primitives whose
        // prelude axioms ARE the correct representation; the shard's `Quot` rows
        // must not displace them.
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Quot",
                ImportConfidence::KernelVerified,
                DeclKind::Quot,
                true,
            ),
            (
                "Quot.mk",
                ImportConfidence::KernelVerified,
                DeclKind::Quot,
                true,
            ),
        ]);
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Quot");
        seed_axiom_stub(&mut env, "Quot.mk");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert!(taken.is_empty(), "Quot rows are excluded by kind");
        assert!(resident(&env, "Quot"));
        assert!(resident(&env, "Quot.mk"));
    }

    #[test]
    fn test_discharge_requires_kernel_verified_for_value_bearing_rows() {
        // A value-bearing row that the gate would REJECT must not displace the
        // resident carrier: doing so turns a citation that passes today into a
        // failure without putting anything checked in its place.
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Helper",
                ImportConfidence::SourceVerified,
                DeclKind::Definition,
                true,
            ),
        ]);
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Helper");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert!(taken.is_empty());
        assert!(resident(&env, "Helper"));
    }

    #[test]
    fn test_discharge_retires_axiom_stub_shadowing_a_proved_theorem_row() {
        // The SILENT half: kinds do not clash, so the residency rule admits the
        // stub by design and the loader never installs the real proof. Without
        // this arm a by-name citation of `Fact.out` closes against Clean's own
        // assumption.
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Fact.out",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
        ]);
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Fact.out");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert_eq!(taken.len(), 1);
        assert!(!resident(&env, "Fact.out"));
    }

    #[test]
    fn test_discharge_never_touches_a_value_bearing_resident() {
        // `Finset` is seeded as a reducible DEFINITION, not an axiom. Removing a
        // value-bearing declaration would strand every prelude constant typed in
        // terms of it, so the predicate must refuse it.
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Finset",
                ImportConfidence::SourceVerified,
                DeclKind::Inductive,
                true,
            ),
        ]);
        let mut env = Environment::default();
        seed_definition(&mut env, "Finset");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

        assert!(taken.is_empty(), "a value-bearing resident is not a stub");
        assert!(resident(&env, "Finset"));
    }

    #[test]
    fn test_discharge_is_inert_under_the_relaxed_gate() {
        // `Relaxed` is the explicitly weaker bang-variant gate and keeps its
        // previous behavior, exactly as the residency rule does.
        let lib = shard_with_deps(&[
            (
                "thm",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Fact",
                ImportConfidence::SourceVerified,
                DeclKind::Inductive,
                true,
            ),
        ]);
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Fact");

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Relaxed);

        assert!(taken.is_empty());
        assert!(resident(&env, "Fact"));
    }

    #[test]
    fn test_restore_puts_the_stub_back_and_flags_the_closure_member() {
        // Nothing installed the genuine declaration, so the session must be left
        // exactly as it was found AND the caller must be told, so it can refuse
        // to report a citation that would rest on the restored fabrication.
        let lib = fact_closure_with_constructor_row();
        let mut env = Environment::default();
        seed_axiom_stub(&mut env, "Fact");
        seed_axiom_stub(&mut env, "Fact.mk");
        let before = env.get_const(&Name::from_string("Fact")).map(|c| {
            (
                c.level_params.clone(),
                c.type_.clone(),
                c.kind,
                c.value.clone(),
            )
        });

        let taken =
            discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);
        assert_eq!(taken.len(), 2);

        let restored = restore_unreplaced_stubs(&mut env, taken);

        assert_eq!(
            restored.iter().map(ToString::to_string).collect::<Vec<_>>(),
            vec!["Fact".to_string()],
            "only the CLOSURE member is reported; the namespace sweep is routine"
        );
        assert!(resident(&env, "Fact"));
        assert!(resident(&env, "Fact.mk"));
        assert_eq!(
            env.get_const(&Name::from_string("Fact")).map(|c| (
                c.level_params.clone(),
                c.type_.clone(),
                c.kind,
                c.value.clone()
            )),
            before,
            "the restored carrier must be identical to the one that was retired"
        );
    }
}

/// Exercise universe rigidity through the real checked Mathverse citation path.
#[cfg(feature = "mathverse-library")]
mod goal_universe_tests {
    use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker};
    use clean_mathverse::export::kernel_export::KernelShardBuilder;
    use clean_mathverse::library::MathverseLibrary;
    use clean_mathverse::shard::ShardReader;
    use clean_mathverse::shard_verify::verify_native_shard;
    use clean_mathverse::trust::policy::TrustPolicy;

    use super::super::mathverse_use::{
        clear_mathverse_library, mathverse_apply_named, set_mathverse_library, TrustGate,
    };
    use super::super::ProofState;

    struct LibraryGuard;

    impl Drop for LibraryGuard {
        fn drop(&mut self) {
            clear_mathverse_library();
        }
    }

    struct TheoremFixture {
        declaration: Declaration,
        target: Expr,
        name: Name,
        goal_params: [Name; 2],
    }

    fn polymorphic_theorem_fixture(name: &str, depth: usize) -> TheoremFixture {
        let goal_params = [Name::from_string("goal_u"), Name::from_string("goal_v")];
        let sort_u = Expr::sort(Level::param(goal_params[0].clone()));
        let sort_v = Expr::sort(Level::param(goal_params[1].clone()));
        // forall (A : Sort u) (B : Sort v) (P : Prop), P -> P.
        let mut target = Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                sort_v.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
                ),
            ),
        );
        let mut value = Expr::lam(
            BinderInfo::Default,
            sort_u,
            Expr::lam(
                BinderInfo::Default,
                sort_v,
                Expr::lam(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
                ),
            ),
        );
        // These unused Prop binders leave both universe occurrences below the
        // old collector's depth64 cutoff without introducing an axiom.
        for _ in 0..depth {
            target = Expr::pi(BinderInfo::Default, Expr::prop(), target);
            value = Expr::lam(BinderInfo::Default, Expr::prop(), value);
        }
        let name = Name::from_string(name);
        let declaration = Declaration::Theorem {
            name: name.clone(),
            level_params: goal_params.to_vec(),
            type_: target.clone(),
            value,
        };
        TheoremFixture {
            declaration,
            target,
            name,
            goal_params,
        }
    }

    fn checked_library(fixture: &TheoremFixture) -> MathverseLibrary {
        let mut checked = Environment::new();
        checked
            .add_decl(fixture.declaration.clone())
            .expect("the pure polymorphic fixture must pass ordinary kernel admission");
        let mut builder = KernelShardBuilder::new();
        builder
            .add_declaration(&fixture.declaration, &["mathverse-goal-universes"])
            .expect("export the checked polymorphic declaration");
        let directory = tempfile::tempdir().expect("polymorphic citation directory");
        let path = directory.path().join("goal-universes.mathverse");
        builder
            .write_to_file(&path)
            .expect("write the actual polymorphic shard");
        let report = verify_native_shard(&path).expect("verify the actual polymorphic shard");
        assert_eq!(
            report.checked, 1,
            "the real gate must check the declaration"
        );
        assert!(report.violations.is_empty(), "native gate: {report:?}");
        let bytes = std::fs::read(path).expect("read the verified shard");
        let shard = ShardReader::from_bytes(&bytes).expect("decode the verified shard");
        let mut library = MathverseLibrary::new(TrustPolicy::permissive());
        library
            .load_shard(&shard)
            .expect("load the real checked shard");
        library
    }

    fn apply_and_check(fixture: TheoremFixture, target: Expr) {
        let _guard = LibraryGuard;
        set_mathverse_library(checked_library(&fixture));
        let mut state = ProofState::new(Environment::new(), target.clone());
        let outer = Name::from_string("outer_declaration_universe");
        state.metas.add_rigid_level_param(outer.clone());
        assert!(state.metas.is_rigid_level_param(&outer));
        for param in &fixture.goal_params {
            assert!(!state.metas.is_rigid_level_param(param));
        }

        mathverse_apply_named(&mut state, &fixture.name.to_string(), TrustGate::Strict)
            .expect("strict named citation must close its actual polymorphic goal");
        assert!(state.is_complete());
        assert!(
            state.metas.is_rigid_level_param(&outer),
            "citation must retain the outer declaration's rigid parameter"
        );
        for param in &fixture.goal_params {
            assert!(
                state.metas.is_rigid_level_param(param),
                "citation must pin every goal universe: {param}"
            );
        }
        let proof = state
            .closed_proof()
            .expect("extract the actual closed proof");
        let checker = TypeChecker::new(&state.env);
        let inferred = checker
            .infer_type(&proof)
            .expect("kernel-check the cited proof");
        assert!(checker.is_def_eq(&inferred, &target));
    }

    #[test]
    fn named_apply_pins_wrapped_goal_universes_and_keeps_outer_rigidity() {
        let fixture = polymorphic_theorem_fixture("MathverseGoalUniverses.wrapped", 0);
        let target = Expr::mdata(vec![], fixture.target.clone());
        apply_and_check(fixture, target);
    }

    #[test]
    fn named_apply_pins_deep_goal_universes_and_keeps_outer_rigidity() {
        let fixture = polymorphic_theorem_fixture("MathverseGoalUniverses.deep", 72);
        let target = fixture.target.clone();
        apply_and_check(fixture, target);
    }
}
