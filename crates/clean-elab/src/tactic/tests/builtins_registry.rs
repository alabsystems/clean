// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Registry dispatch tests for `register_builtin_tactics`.
//!
//! Verifies that all Phase 3B/3C/3D tactic registrations are wired
//! into the central `TacticRegistry` and that compound vs simple
//! dispatch boundaries are correct. Part of #2440.

use super::super::builtins::{builtin_tactic_patterns, register_builtin_tactics};
use super::super::registry::TacticRegistry;

/// Verify that `register_builtin_tactics` populates the expected number
/// of simple and compound tactic entries. This catches accidental
/// regressions where a registration call is dropped or duplicated.
#[test]
fn test_register_builtin_tactics_total_count() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    // The registry must be non-empty and contain a reasonable number.
    // As of the Phase 3C/3D migration completion, the registry has 68+
    // entries (44 simple + 24 compound). We assert a lower bound to
    // detect accidental removals without pinning to an exact count
    // (which would break on every future tactic addition).
    assert!(
        registry.len() >= 60,
        "expected at least 60 registered tactics (simple + compound), got {}",
        registry.len()
    );
}

/// Verify that all core nullary tactics are present in the registry.
#[test]
fn test_core_nullary_tactics_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    let core_tactics = [
        "assumption",
        "constructor",
        "left",
        "right",
        "split",
        "exfalso",
        "omega",
        "cert_mathverse",
        "decide",
        "contradiction",
        "trivial",
        "congr",
        "aesop",
        "tauto",
        "cert_simp",
        "norm_num",
        "ring",
        "ring_nf",
        "symm",
        "native_decide",
        "delta",
        "admit",
    ];
    for name in core_tactics {
        assert!(
            registry.get(name).is_some(),
            "core nullary tactic '{name}' should be registered"
        );
    }
}

/// Verify that Phase 3D keyword-parsed tactics are registered.
#[test]
fn test_phase3d_keyword_tactics_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    for name in ["rfl", "reduce_eq", "sorry", "show"] {
        assert!(
            registry.get(name).is_some(),
            "phase 3D keyword tactic '{name}' should be registered"
        );
    }
}

/// Verify that Phase 3C wave tactics are registered.
#[test]
fn test_phase3c_wave_tactics_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    let wave_tactics = [
        // Wave 1: nullary
        "intros",
        "skip",
        "done",
        "lhs",
        "rhs",
        // Wave 2: term-arg + expr-list + opt-nat
        "exact",
        "apply",
        "refine",
        "change",
        "trans",
        "injection",
        "use",
        "exists",
        "rotate_left",
        "rotate_right",
        // Wave 3: ident-list + nonempty-ident + compound + search
        "intro",
        "ext",
        "funext",
        "by_contra",
        "subst",
        "revert",
        "clear",
        "rename_i",
        "by_cases",
        "specialize",
        "generalize",
        "exact?",
        "apply?",
    ];
    for name in wave_tactics {
        assert!(
            registry.get(name).is_some(),
            "phase 3C wave tactic '{name}' should be registered"
        );
    }
}

/// Verify that all compound tactics are registered in the registry.
#[test]
fn test_compound_tactics_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    let compound_tactics = [
        // Wave 5: combinators
        "paren",
        "try",
        "focus",
        "focus_block",
        "repeat",
        "all_goals",
        "any_goals",
        "first",
        "seq_focus",
        "case",
        // Wave 6: expression-dependent
        "have",
        "let",
        "suffices",
        "match",
        // Wave 4: conv
        "conv",
        "conv_arg",
        "conv_enter",
        // Wave 3: rewrite/simp
        "rw",
        "rewrite",
        "simp",
        "simp_all",
        "simp_rw",
        "simpa",
        // Wave 4: cases/induction
        "cases",
        "induction",
    ];
    for name in compound_tactics {
        assert!(
            registry.get_compound(name).is_some(),
            "compound tactic '{name}' should be registered"
        );
    }
}

/// Verify that location-aware tactics (Phase 3D Wave 1) are registered.
#[test]
fn test_location_aware_tactics_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    for name in ["push_neg", "dsimp", "unfold"] {
        assert!(
            registry.get(name).is_some(),
            "location-aware tactic '{name}' should be registered"
        );
    }
}

/// Verify that `builtin_tactic_patterns` returns patterns for all simple
/// (Named-dispatched) tactics but excludes compound tactics.
#[test]
fn test_builtin_tactic_patterns_excludes_compound() {
    let patterns = builtin_tactic_patterns();

    // Should include simple tactics
    assert!(
        patterns.contains_key("assumption"),
        "patterns should include simple tactic 'assumption'"
    );
    assert!(
        patterns.contains_key("exact"),
        "patterns should include simple tactic 'exact'"
    );

    // Should exclude compound-only tactics (they use dedicated variants)
    assert!(
        !patterns.contains_key("all_goals"),
        "patterns should NOT include compound-only 'all_goals'"
    );
    assert!(
        !patterns.contains_key("rw"),
        "patterns should NOT include compound-only 'rw'"
    );
}

/// Verify that ay SMT tactics are registered.
#[test]
fn test_ay_tactics_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    for name in ["ay_omega", "ay_bv", "ay_smt", "ay_decide", "ay_lra"] {
        assert!(
            registry.get(name).is_some(),
            "ay tactic '{name}' should be registered"
        );
    }
}

/// Verify that Mathlib-critical P1 tactics are registered.
#[test]
fn test_mathlib_critical_tactics_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    let p1_tactics = [
        "contrapose",
        "field_simp",
        "norm_cast",
        "positivity",
        "polyrith",
        "linarith",
        "nlinarith",
        "push_cast",
        "gcongr",
        "split_ifs",
    ];
    for name in p1_tactics {
        assert!(
            registry.get(name).is_some(),
            "Mathlib-critical P1 tactic '{name}' should be registered"
        );
    }
}

/// Exercise the real encoded-name/intro path, rather than installing a
/// hand-written local context. The codec carries a template reference's
/// section-origin mark, which differs from the binder's section-variable mark.
fn template_origin_shadow_state(
    older: clean_parser::SurfaceName,
    newer: clean_parser::SurfaceName,
) -> (super::super::ProofState, clean_kernel::Expr, TacticRegistry) {
    use clean_kernel::{Environment, Expr, Name};
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat));
    let mut state = super::super::ProofState::new(Environment::with_prelude(), target.clone());
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let intro = registry.get("intro").expect("intro").handler.clone();
    for name in [older, newer] {
        intro(
            &mut state,
            &[super::super::registry::encode_name_argument(&name)],
        )
        .expect("encoded intro");
    }
    (state, target, registry)
}

fn section_origin_h() -> clean_parser::SurfaceName {
    clean_parser::SurfaceName::component("h", false).with_template_origin(std::sync::Arc::new(
        clean_parser::TemplateOrigin {
            namespace: clean_kernel::Name::anon(),
            section_variable: true,
            site: None,
        },
    ))
}

#[test]
fn test_rename_i_template_origin_on_older_local_keeps_shadow_direction() {
    use clean_kernel::{Expr, TypeChecker};
    use clean_parser::SurfaceName;
    let (mut state, target, registry) =
        template_origin_shadow_state(section_origin_h(), SurfaceName::component("h", false));
    let older = state.current_goal().expect("goal").local_ctx[0].fvar;
    let rename = registry.get("rename_i").expect("rename_i").handler.clone();
    let hp = SurfaceName::component("hp", false);
    rename(
        &mut state,
        &[super::super::registry::encode_name_argument(&hp)],
    )
    .expect("the newer ordinary name shadows the older local");
    let goal = state.current_goal().expect("goal");
    assert_eq!(goal.local_ctx[0].fvar, older);
    assert_eq!(goal.local_ctx[0].name, hp);
    super::super::exact(&mut state, Expr::fvar(older)).expect("exact renamed older local");
    let proof = state.closed_proof().expect("closed proof");
    TypeChecker::new(state.env())
        .check_type(&proof, &target)
        .expect("kernel-checked projection");
}

#[test]
fn test_rename_i_template_origin_on_newer_reference_keeps_its_restriction() {
    use clean_parser::SurfaceName;
    let (mut state, _, registry) =
        template_origin_shadow_state(SurfaceName::component("h", false), section_origin_h());
    let before = state.current_goal().expect("goal").local_ctx.clone();
    let rename = registry.get("rename_i").expect("rename_i").handler.clone();
    let result = rename(
        &mut state,
        &[super::super::registry::encode_name_argument(
            &SurfaceName::component("hp", false),
        )],
    );
    assert!(
        matches!(result, Err(super::super::TacticError::GoalMismatch(ref detail))
        if detail.contains("too many variable names")),
        "{result:?}"
    );
    let after = &state.current_goal().expect("goal").local_ctx;
    assert_eq!(after.len(), before.len());
    for (old, new) in before.iter().zip(after) {
        assert_eq!(old.fvar, new.fvar);
        assert!(old.name.same_syntax(&new.name));
    }
}
