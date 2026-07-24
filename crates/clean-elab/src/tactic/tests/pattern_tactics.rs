// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern-based tactic tests (rintro, peel, split_ifs)
//! Split from advanced.rs
//!
//! Related test files:
//! - advanced.rs: remaining advanced tactics
//! - conv.rs: conv tactic tests
//! - library_search.rs: library search tests
//! - mathlib_tactics.rs: mathlib-style tactics
//! - propositional.rs: propositional logic tactics

use super::*;

// ========== End-to-end kernel-checked rintro / obtain destructuring ==========
//
// These tests pin the #9510 fix: rintro/obtain And/Exists destructuring must
// build a genuine, kernel-accepted eliminator (casesOn) proof term so that a
// proof which *uses* a destructured hypothesis closes its goal with a term the
// kernel accepts (no dangling FVar, no close_fvars debug-assert panic).
//
// Each test assembles the full proof via tactics, then type-checks the closed
// proof term against the original target with the kernel TypeChecker — exactly
// the boundary that the old raw-FVar implementation failed.

/// Environment with And, Exists, classical logic, plus:
/// - `P`, `Q` : Prop and witnesses `p : P`, `q : Q`
/// - `A : Type`, predicate `pr : A → Prop`
fn setup_env_for_rintro() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_and().unwrap();
    env.init_classical().unwrap();
    env.init_exists().unwrap();

    let prop = Expr::prop();
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    // A : Type (Sort 1), predicate pr : A → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pr"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_(Name::from_string("A"), vec![]), Expr::prop()),
    })
    .unwrap();

    env
}

fn prop_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `And P Q`
fn and_pq(p: Expr, q: Expr) -> Expr {
    Expr::app(Expr::app(prop_const("And"), p), q)
}

/// `@Exists A (fun x : A => pr x)`
fn exists_pr() -> Expr {
    let a = prop_const("A");
    let pred = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::app(prop_const("pr"), Expr::bvar(0)),
    );
    Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            a,
        ),
        pred,
    )
}

/// Find the fvar of a hypothesis by name in the current goal.
fn hyp_fvar(state: &ProofState, name: &str) -> FVarId {
    state
        .current_goal()
        .expect("goal exists")
        .local_ctx
        .iter()
        .find(|d| d.name == name)
        .unwrap_or_else(|| panic!("hypothesis '{name}' not found in context"))
        .fvar
}

#[test]
fn test_rintro_and_destruct_exact_left_kernel_accepts() {
    // (P ∧ Q) → P  via  rintro ⟨hp, hq⟩; exact hp
    let env = setup_env_for_rintro();
    let target = Expr::arrow(and_pq(prop_const("P"), prop_const("Q")), prop_const("P"));

    let mut state = ProofState::new(env.clone(), target.clone());
    rintro(&mut state, vec!["<hp, hq>".to_string()]).expect("rintro ⟨hp, hq⟩ should succeed");

    let hp = hyp_fvar(&state, "hp");
    exact(&mut state, Expr::fvar(hp)).expect("exact hp should close the goal");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist (closed_proof)");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the casesOn proof term for (P ∧ Q) → P");
}

#[test]
fn test_rintro_and_destruct_exact_right_kernel_accepts() {
    // (P ∧ Q) → Q  via  rintro ⟨hp, hq⟩; exact hq
    let env = setup_env_for_rintro();
    let target = Expr::arrow(and_pq(prop_const("P"), prop_const("Q")), prop_const("Q"));

    let mut state = ProofState::new(env.clone(), target.clone());
    rintro(&mut state, vec!["<hp, hq>".to_string()]).expect("rintro ⟨hp, hq⟩ should succeed");

    let hq = hyp_fvar(&state, "hq");
    exact(&mut state, Expr::fvar(hq)).expect("exact hq should close the goal");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist (closed_proof)");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the casesOn proof term for (P ∧ Q) → Q");
}

#[test]
fn test_rintro_and_wildcard_kernel_accepts() {
    // (P ∧ Q) → P  via  rintro ⟨hp, _⟩; exact hp  (wildcard on the right field)
    let env = setup_env_for_rintro();
    let target = Expr::arrow(and_pq(prop_const("P"), prop_const("Q")), prop_const("P"));

    let mut state = ProofState::new(env.clone(), target.clone());
    rintro(&mut state, vec!["<hp, _>".to_string()]).expect("rintro ⟨hp, _⟩ should succeed");

    let hp = hyp_fvar(&state, "hp");
    exact(&mut state, Expr::fvar(hp)).expect("exact hp should close the goal");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist (closed_proof)");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the casesOn proof term for ⟨hp, _⟩");
}

#[test]
fn test_rintro_nested_and_kernel_accepts() {
    // (P ∧ (Q ∧ R)) → R  via  rintro ⟨a, ⟨b, c⟩⟩; exact c
    let env = setup_env_for_rintro();
    let inner = and_pq(prop_const("Q"), prop_const("R"));
    let target = Expr::arrow(and_pq(prop_const("P"), inner), prop_const("R"));

    let mut state = ProofState::new(env.clone(), target.clone());
    rintro(&mut state, vec!["<a, <b, c>>".to_string()])
        .expect("nested rintro ⟨a, ⟨b, c⟩⟩ should succeed");

    let c = hyp_fvar(&state, "c");
    exact(&mut state, Expr::fvar(c)).expect("exact c should close the goal");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist (closed_proof)");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the composed casesOn proof term for ⟨a, ⟨b, c⟩⟩");
}

#[test]
fn test_rintro_exists_destruct_kernel_accepts() {
    // (∃ x, pr x) → (∃ x, pr x)  via  rintro ⟨w, hw⟩; exact (Exists.intro w hw)
    let env = setup_env_for_rintro();
    let target = Expr::arrow(exists_pr(), exists_pr());

    let mut state = ProofState::new(env.clone(), target.clone());
    rintro(&mut state, vec!["<w, hw>".to_string()]).expect("rintro ⟨w, hw⟩ on ∃ should succeed");

    // Reconstruct the existential from the destructured witness + proof.
    let w = hyp_fvar(&state, "w");
    let hw = hyp_fvar(&state, "hw");
    let a = prop_const("A");
    let pred = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::app(prop_const("pr"), Expr::bvar(0)),
    );
    // @Exists.intro.{1} A pred w hw
    let intro_term = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists.intro"),
                        vec![Level::succ(Level::zero())],
                    ),
                    a,
                ),
                pred,
            ),
            Expr::fvar(w),
        ),
        Expr::fvar(hw),
    );
    exact(&mut state, intro_term).expect("rebuilding the existential should close the goal");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist (closed_proof)");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the Exists.casesOn proof term");
}

#[test]
fn test_rintro_and_destruct_type_mismatch_errors_not_panics() {
    // Using the wrong field must error (not panic, not be accepted): on
    // (P ∧ Q) → P, `exact hq` supplies Q where P is required.
    let env = setup_env_for_rintro();
    let target = Expr::arrow(and_pq(prop_const("P"), prop_const("Q")), prop_const("P"));

    let mut state = ProofState::new(env, target);
    rintro(&mut state, vec!["<hp, hq>".to_string()]).expect("rintro ⟨hp, hq⟩ should succeed");

    let hq = hyp_fvar(&state, "hq");
    let err = exact(&mut state, Expr::fvar(hq)).expect_err("exact hq must fail for goal P");
    assert!(
        matches!(
            err,
            TacticError::TypeMismatch { .. } | TacticError::UnificationFailed(_)
        ),
        "wrong-field exact should be a type/unification error, got: {err:?}"
    );
}

#[test]
fn test_obtain_exists_destruct_kernel_accepts() {
    // obtain analog: (∃ x, pr x) → (∃ x, pr x). Intro the existential, then
    // `obtain` destructs it into witness `w` and proof `hw`, and we rebuild it.
    let env = setup_env_for_rintro();
    let target = Expr::arrow(exists_pr(), exists_pr());

    let mut state = ProofState::new(env.clone(), target.clone());
    intro(&mut state, "h").expect("intro the existential hypothesis");
    obtain(&mut state, "h", "w", "hw").expect("obtain ⟨w, hw⟩ on ∃ should succeed");

    let w = hyp_fvar(&state, "w");
    let hw = hyp_fvar(&state, "hw");
    let a = prop_const("A");
    let pred = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::app(prop_const("pr"), Expr::bvar(0)),
    );
    let intro_term = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists.intro"),
                        vec![Level::succ(Level::zero())],
                    ),
                    a,
                ),
                pred,
            ),
            Expr::fvar(w),
        ),
        Expr::fvar(hw),
    );
    exact(&mut state, intro_term).expect("rebuilding the existential should close the goal");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist (closed_proof)");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the obtain Exists.casesOn proof term");
}

#[test]
fn test_obtain_on_non_existential_errors_not_panics() {
    // obtain on a non-∃/Σ hypothesis must error (mirrors Lean), not panic.
    let env = setup_env_for_rintro();
    let target = Expr::arrow(prop_const("P"), prop_const("P"));

    let mut state = ProofState::new(env, target);
    intro(&mut state, "h").expect("intro P");
    let err = obtain(&mut state, "h", "w", "hw").expect_err("obtain on P : Prop must fail");
    assert!(
        matches!(err, TacticError::GoalMismatch(_)),
        "obtain on non-existential should be a GoalMismatch, got: {err:?}"
    );
}

// ========== Tests for rintro tactic ==========

#[test]
fn test_rintro_pattern_parse_name() {
    let pattern = RIntroPattern::parse("x").unwrap();
    assert!(matches!(pattern, RIntroPattern::Name(s) if s == "x"));
}

#[test]
fn test_rintro_pattern_parse_wildcard() {
    let pattern = RIntroPattern::parse("_").unwrap();
    assert!(matches!(pattern, RIntroPattern::Wildcard));
}

#[test]
fn test_rintro_pattern_parse_rfl() {
    let pattern = RIntroPattern::parse("rfl").unwrap();
    assert!(matches!(pattern, RIntroPattern::Rfl));
}

#[test]
fn test_rintro_pattern_parse_tuple() {
    let pattern = RIntroPattern::parse("<a, b>").unwrap();
    if let RIntroPattern::Tuple(parts) = pattern {
        assert_eq!(parts.len(), 2);
        assert!(matches!(&parts[0], RIntroPattern::Name(s) if s == "a"));
        assert!(matches!(&parts[1], RIntroPattern::Name(s) if s == "b"));
    } else {
        panic!("Expected Tuple pattern");
    }
}

#[test]
fn test_rintro_pattern_parse_or() {
    let pattern = RIntroPattern::parse("h1 | h2").unwrap();
    if let RIntroPattern::Or(parts) = pattern {
        assert_eq!(parts.len(), 2);
        assert!(matches!(&parts[0], RIntroPattern::Name(s) if s == "h1"));
        assert!(matches!(&parts[1], RIntroPattern::Name(s) if s == "h2"));
    } else {
        panic!("Expected Or pattern");
    }
}

#[test]
fn test_rintro_pattern_parse_or_of_tuples() {
    // Lean 4: `rintro ⟨a, b⟩ | ⟨c, d⟩` is an alternation (Or) of two
    // anonymous-constructor (Tuple) patterns, NOT a single tuple. The
    // top-level `|` binds looser than the `⟨⟩` grouping, so the parse must
    // split at the depth-0 `|` first.
    let pattern = RIntroPattern::parse("<a, b> | <c, d>").unwrap();
    let RIntroPattern::Or(alts) = pattern else {
        panic!("expected Or of two tuples, got: {pattern:?}");
    };
    assert_eq!(alts.len(), 2, "expected two alternatives");
    assert!(
        matches!(&alts[0], RIntroPattern::Tuple(p) if p.len() == 2),
        "first alternative should be a 2-element tuple, got: {:?}",
        alts[0]
    );
    assert!(
        matches!(&alts[1], RIntroPattern::Tuple(p) if p.len() == 2),
        "second alternative should be a 2-element tuple, got: {:?}",
        alts[1]
    );
}

#[test]
fn test_rintro_pattern_parse_or_unicode_tuples() {
    // Same divergence but with the Unicode anonymous-constructor brackets.
    let pattern = RIntroPattern::parse("\u{27E8}a, b\u{27E9} | \u{27E8}c\u{27E9}").unwrap();
    let RIntroPattern::Or(alts) = pattern else {
        panic!("expected Or of two tuples, got: {pattern:?}");
    };
    assert_eq!(alts.len(), 2);
    assert!(matches!(&alts[0], RIntroPattern::Tuple(p) if p.len() == 2));
    assert!(matches!(&alts[1], RIntroPattern::Tuple(p) if p.len() == 1));
}

#[test]
fn test_rintro_pattern_parse_nested_or_inside_tuple() {
    // A `|` nested inside a tuple group must NOT cause a top-level Or split:
    // `<h | h'>` is a single tuple whose sole element is an Or pattern.
    let pattern = RIntroPattern::parse("<h | h'>").unwrap();
    let RIntroPattern::Tuple(parts) = pattern else {
        panic!("expected single Tuple, got: {pattern:?}");
    };
    assert_eq!(parts.len(), 1, "tuple should have one (Or) element");
    assert!(
        matches!(&parts[0], RIntroPattern::Or(alts) if alts.len() == 2),
        "tuple element should be an Or of two names, got: {:?}",
        parts[0]
    );
}

#[test]
fn test_rintro_pattern_parse_three_way_or() {
    // Three-way alternation `a | b | c` is a single flat Or with 3 parts.
    let pattern = RIntroPattern::parse("a | b | c").unwrap();
    let RIntroPattern::Or(alts) = pattern else {
        panic!("expected Or, got: {pattern:?}");
    };
    assert_eq!(alts.len(), 3);
    assert!(matches!(&alts[0], RIntroPattern::Name(s) if s == "a"));
    assert!(matches!(&alts[1], RIntroPattern::Name(s) if s == "b"));
    assert!(matches!(&alts[2], RIntroPattern::Name(s) if s == "c"));
}

#[test]
fn test_rintro_pattern_parse_empty() {
    let err = RIntroPattern::parse("").unwrap_err();
    assert!(
        matches!(err, TacticError::MissingArgument { .. }),
        "empty pattern should produce MissingArgument error, got: {err:?}"
    );
}

#[test]
fn test_split_pattern_args_simple() {
    let result = split_pattern_args("a, b, c");
    assert_eq!(result, vec!["a", "b", "c"]);
}

#[test]
fn test_split_pattern_args_nested() {
    let result = split_pattern_args("a, <b, c>, d");
    assert_eq!(result, vec!["a", "<b, c>", "d"]);
}

#[test]
fn test_rintro_simple_name() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a, b);

    let mut state = ProofState::new(env, target);
    rintro(&mut state, vec!["h".to_string()])
        .expect("rintro with simple name on arrow type should succeed");

    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx.len(), 1);
    assert_eq!(goal.local_ctx[0].name, "h");
}

#[test]
fn test_rename_hypothesis() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    state.goals[0].local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "old_name".to_string(),
        ty: Expr::const_(Name::from_string("A"), vec![]),
        value: None,
    });

    rename_hypothesis(&mut state, "old_name", "new_name")
        .expect("renaming existing hypothesis should succeed");
    assert_eq!(state.goals[0].local_ctx[0].name, "new_name");
}

#[test]
fn test_rename_hypothesis_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let err = rename_hypothesis(&mut state, "nonexistent", "new_name").unwrap_err();
    assert!(
        matches!(err, TacticError::HypothesisNotFound(ref msg) if msg.contains("not found")),
        "renaming nonexistent hypothesis should produce 'not found' error, got: {err:?}"
    );
}

// ========== Tests for peel tactic ==========

#[test]
fn test_peel_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let err = peel(&mut state, "h").unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "peel on empty goals should produce NoGoals, got: {err:?}"
    );
}

#[test]
fn test_peel_hyp_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let err = peel(&mut state, "nonexistent").unwrap_err();
    assert!(
        matches!(err, TacticError::HypothesisNotFound(_)),
        "peel with missing hypothesis should produce HypothesisNotFound error, got: {err:?}"
    );
}

#[test]
fn test_peel_not_quantified() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    state.goals[0].local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "h".to_string(),
        ty: Expr::const_(Name::from_string("A"), vec![]),
        value: None,
    });

    let err = peel(&mut state, "h").unwrap_err();
    assert!(
        matches!(err, TacticError::InvalidTarget { .. }),
        "peel on non-quantified hypothesis should produce InvalidTarget error, got: {err:?}"
    );
}

#[test]
fn test_count_foralls_zero() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    assert_eq!(count_foralls(&a), 0);
}

#[test]
fn test_count_foralls_one() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let forall = Expr::pi(BinderInfo::Default, a, b);
    assert_eq!(count_foralls(&forall), 1);
}

#[test]
fn test_count_foralls_two() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);
    let inner = Expr::pi(BinderInfo::Default, b, c);
    let outer = Expr::pi(BinderInfo::Default, a, inner);
    assert_eq!(count_foralls(&outer), 2);
}

// ========== Tests for split_ifs tactic ==========

#[test]
fn test_split_ifs_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let err = split_ifs(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "split_ifs on empty goals should produce NoGoals, got: {err:?}"
    );
}

#[test]
fn test_split_ifs_no_ite_found() {
    let env = setup_env();
    // Goal without any if-then-else
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let err = split_ifs(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::InvalidTarget { .. }),
        "split_ifs without ite in goal should produce InvalidTarget error, got: {err:?}"
    );
}

#[test]
fn test_split_ifs_config_new() {
    let config = SplitIfsConfig::new();
    assert_eq!(config.max_depth, 10);
    assert!(config.hyp_names.is_empty());
    assert!(!config.split_hyps);
}

#[test]
fn test_split_ifs_config_builder() {
    let config = SplitIfsConfig::new()
        .with_max_depth(5)
        .with_hyp_names(vec!["h1".to_string(), "h2".to_string()])
        .split_hyps(true);

    assert_eq!(config.max_depth, 5);
    assert_eq!(config.hyp_names.len(), 2);
    assert!(config.split_hyps);
}

#[test]
fn test_is_ite_const() {
    let ite = Expr::const_(Name::from_string("ite"), vec![]);
    assert!(is_ite_const(&ite));

    let ite_full = Expr::const_(Name::from_string("Core.ite"), vec![]);
    assert!(is_ite_const(&ite_full));

    let not_ite = Expr::const_(Name::from_string("foo"), vec![]);
    assert!(!is_ite_const(&not_ite));
}

#[test]
fn test_is_dite_const() {
    let dite = Expr::const_(Name::from_string("dite"), vec![]);
    assert!(is_dite_const(&dite));

    let not_dite = Expr::const_(Name::from_string("ite"), vec![]);
    assert!(!is_dite_const(&not_dite));
}

#[test]
fn test_generate_fresh_hyp_name_unused() {
    let ctx: Vec<LocalDecl> = vec![];
    assert_eq!(generate_fresh_hyp_name(&ctx, "h"), "h");
}

#[test]
fn test_generate_fresh_hyp_name_used() {
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(1),
        name: "h".to_string(),
        ty: Expr::prop(),
        value: None,
    }];
    assert_eq!(generate_fresh_hyp_name(&ctx, "h"), "h1");
}

#[test]
fn test_generate_fresh_hyp_name_multiple_used() {
    let ctx = vec![
        LocalDecl {
            fvar: FVarId::new(1),
            name: "h".to_string(),
            ty: Expr::prop(),
            value: None,
        },
        LocalDecl {
            fvar: FVarId::new(2),
            name: "h1".to_string(),
            ty: Expr::prop(),
            value: None,
        },
    ];
    assert_eq!(generate_fresh_hyp_name(&ctx, "h"), "h2");
}
