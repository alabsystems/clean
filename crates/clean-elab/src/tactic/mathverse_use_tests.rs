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

    #[test]
    fn test_dependency_loader_rejects_missing_definition_metadata_replay() {
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
            TrustGate::Strict,
        ));

        assert!(detail.contains("Missing.def"), "{detail}");
        assert!(detail.contains("definition"), "{detail}");
        assert!(detail.contains("DeclKind-preserving"), "{detail}");
    }

    // ---------------------------------------------------------------------
    // RelaxedFoundational trust gate (the USABILITY lever).
    //
    // The closure-level behavior is what makes the KernelVerified corpus
    // consumable: a deep theorem whose only non-KV transitive dependency is a
    // foundational axiom is admitted under RelaxedFoundational but rejected
    // under Strict (which stops on the first non-KV dep).
    // ---------------------------------------------------------------------

    /// A theorem whose ONLY non-KV transitive dependency is the foundational
    /// axiom `propext` is:
    ///   - REJECTED under Strict (propext is not KernelVerified), and
    ///   - ADMITTED under RelaxedFoundational (closure ⊆ KV ∪ FOUNDATIONAL).
    #[test]
    fn test_relaxed_foundational_admits_foundational_only_theorem_strict_rejects() {
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

        // RelaxedFoundational: admits — the whole closure is ⊆ KV ∪ FOUNDATIONAL.
        let relaxed = validate_dependency_loader_trust(
            &env,
            &candidate,
            &lib,
            TrustGate::RelaxedFoundational,
        );
        assert!(
            relaxed.is_ok(),
            "RelaxedFoundational must admit a theorem whose only non-KV dep is a foundational axiom: {relaxed:?}"
        );
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

    use super::super::mathverse_use::{clear_mathverse_library, set_mathverse_library};

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
            clear_mathverse_library();
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
        set_mathverse_library(lib);

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
        set_mathverse_library(lib);

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
    use super::super::mathverse_use::{clear_mathverse_library, set_mathverse_library};
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
            clear_mathverse_library();
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

        set_mathverse_library(lib);
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
