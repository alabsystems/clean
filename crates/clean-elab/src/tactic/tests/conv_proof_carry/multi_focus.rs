// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! N-ary multi-focus `conv => congr` proof-carry tests (#2477 Phase 4).
//!
//! These exercise the REAL surface path: `conv => congr; arg i; rw [..]`
//! opens one independently-rewritable sub-focus per argument of an
//! application, and the reconstruction boundary recombines the per-focus
//! equalities into ONE proof of the whole-application equality. The proof is
//! kernel-type-checked against the original goal and its axiom closure is
//! asserted to stay foundational.

use super::super::*;
use crate::infer::ElabCtx;
use crate::tactic::registry::TacticEval;
use clean_kernel::env::Declaration;
use clean_parser::{Span, SurfaceExpr, SurfaceRwRule, SurfaceTactic, SurfaceTacticLocation};
use serial_test::serial;

/// Transitive axiom closure of `expr` in `env` (local copy of the helper in
/// `compound.rs`; kept independent so this test module is self-contained).
fn transitive_axioms(env: &Environment, expr: &Expr) -> std::collections::BTreeSet<Name> {
    let mut axioms = std::collections::BTreeSet::new();
    let mut seen: std::collections::HashSet<Name> = std::collections::HashSet::new();
    let mut frontier: Vec<Name> = expr.collect_constants().into_iter().collect();
    while let Some(name) = frontier.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if info.value.is_none() && info.kind == clean_kernel::env::ConstantKind::Axiom {
            axioms.insert(name.clone());
        }
        if let Some(value) = &info.value {
            frontier.extend(value.collect_constants());
        }
    }
    axioms
}

fn rw_rule_named(name: &str) -> SurfaceRwRule {
    SurfaceRwRule {
        span: Span::dummy(),
        reverse: false,
        term: SurfaceExpr::Ident(Span::dummy(), name.to_string()),
    }
}

fn n_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn n_ty() -> Expr {
    Expr::const_(Name::from_string("N"), vec![])
}

/// Environment with Eq, base type `N`, constants `a a' b b' : N`, and a binary
/// `f : N → N → N`.
fn setup_env_binary_f() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init Eq");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add N");
    for name in ["a", "a'", "b", "b'"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: n_ty(),
        })
        .expect("add const");
    }
    // f : N → N → N
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n_ty(),
            Expr::pi(BinderInfo::Default, n_ty(), n_ty()),
        ),
    })
    .expect("add f");
    env
}

fn make_f(x: Expr, y: Expr) -> Expr {
    Expr::app(Expr::app(n_const("f"), x), y)
}

/// PROVE IT: rewrite TWO DIFFERENT arguments via multi-focus congr.
///
/// Goal `(a = a') → (b = b') → (f a b = f a' b')`. Body:
/// `conv => congr; arg 1; rw [ha]; arg 2; rw [hb]` opens one sub-focus per
/// argument, rewrites each independently, recombines into a kernel-checked
/// proof of `f a b = f a' b'` (turning the goal into `f a' b' = f a' b'`,
/// closed by rfl). Asserts the closed term kernel-type-checks against the
/// ORIGINAL goal and that no non-foundational axiom is introduced.
#[test]
#[serial]
fn test_conv_congr_two_args_kernel_checked_no_new_axioms() {
    reset_all_counters();
    let env = setup_env_binary_f();
    let (a, ap, b, bp) = (n_const("a"), n_const("a'"), n_const("b"), n_const("b'"));

    // (a = a') → (b = b') → (f a b = f a' b')
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(a.clone(), ap.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_eq_n(b.clone(), bp.clone()),
            make_eq(
                n_ty(),
                make_f(a.clone(), b.clone()),
                make_f(ap.clone(), bp.clone()),
            ),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "ha").expect("intro ha : a = a'");
    intro(&mut state, "hb").expect("intro hb : b = b'");

    // The goal is `f a b = f a' b'`. Navigate the RHS-argument structure: the
    // equality's RHS focus is `f a' b'` — but we want to rewrite the LHS `f a b`
    // into `f a' b'`. Enter the LHS of the equality first, then congr its app.
    let axiom_before = axiom_snapshot();
    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                // Focus the LHS `f a b` of the equality goal.
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                // Open the application: foci = [head f, arg a, arg b].
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                // Select first argument and rewrite a → a'.
                SurfaceTactic::ConvArg(Span::dummy(), 1),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("ha")],
                    SurfaceTacticLocation::Goal,
                ),
                // Select second argument and rewrite b → b'.
                SurfaceTactic::ConvArg(Span::dummy(), 2),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("hb")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv => arg -2; congr; arg 1; rw[ha]; arg 2; rw[hb] should rewrite both args");

    // After conv: f a' b' = f a' b'.
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(
            n_ty(),
            make_f(ap.clone(), bp.clone()),
            make_f(ap.clone(), bp.clone())
        ),
        "multi-focus congr should rewrite BOTH arguments of the LHS application"
    );

    rfl(&mut state).expect("f a' b' = f a' b' closes by rfl");
    assert_no_trusted_axiom_usage("conv multi-focus congr", "two-arg rewrite", axiom_before);

    // (1) Closed proof extractable.
    let proof = state
        .closed_proof()
        .expect("multi-focus conv-congr proof must be a closed term");

    // (2) Kernel-type-check against the ORIGINAL goal type.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&proof)
        .expect("multi-focus conv-congr proof must kernel-type-check");
    assert!(
        tc.is_def_eq(&inferred, &goal_ty),
        "proof must have the ORIGINAL goal type; inferred {inferred:?}, expected {goal_ty:?}"
    );

    // (3) Teeth: kernel must reject a wrong claimed type.
    let wrong_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(a.clone(), ap.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_eq_n(b.clone(), bp.clone()),
            make_eq(n_ty(), make_f(a.clone(), b.clone()), make_f(a, b)),
        ),
    );
    assert!(
        !tc.is_def_eq(&inferred, &wrong_ty),
        "kernel must reject a wrong claimed type for the multi-focus conv-congr proof"
    );

    // (4) No escape hatches.
    for forbidden in ["sorry", "trustedArith", "trustedAy"] {
        assert!(
            !super::expr_contains_const(&proof, forbidden),
            "multi-focus conv-congr proof must not contain `{forbidden}`"
        );
    }

    // (5) Axiom closure ⊆ statement vocabulary (foundational Eq core + f,a,a',b,b').
    let stmt_axioms = transitive_axioms(&env, &goal_ty);
    let proof_axioms = transitive_axioms(&env, &proof);
    let introduced: Vec<Name> = proof_axioms.difference(&stmt_axioms).cloned().collect();
    assert!(
        introduced.is_empty(),
        "multi-focus conv-congr proof introduced axioms beyond the statement: {introduced:?}"
    );
}

/// One argument rewritten, the other carried by `Eq.refl` (untouched focus).
///
/// Goal `(a = a') → (f a b = f a' b)`. Body rewrites only the first argument;
/// the second focus is never selected, so recombination synthesizes `Eq.refl`
/// for `b` and `congr`/`congrArg` glue the spine. Verifies INV-5 (refl is real)
/// end-to-end.
#[test]
#[serial]
fn test_conv_congr_one_arg_other_refl_kernel_checked() {
    reset_all_counters();
    let env = setup_env_binary_f();
    let (a, ap, b) = (n_const("a"), n_const("a'"), n_const("b"));

    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(a.clone(), ap.clone()),
        make_eq(
            n_ty(),
            make_f(a.clone(), b.clone()),
            make_f(ap.clone(), b.clone()),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "ha").expect("intro ha : a = a'");

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::ConvArg(Span::dummy(), 1),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("ha")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("conv with one-arg rewrite + refl-carried arg should close");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(
            n_ty(),
            make_f(ap.clone(), b.clone()),
            make_f(ap.clone(), b.clone())
        ),
        "only the first argument should change; the second is carried by refl"
    );
    rfl(&mut state).expect("closes by rfl");

    let proof = state.closed_proof().expect("closed proof");
    let tc = TypeChecker::new(&env);
    let inferred = tc.infer_type(&proof).expect("kernel-type-check");
    assert!(
        tc.is_def_eq(&inferred, &goal_ty),
        "one-arg + refl proof must have the original goal type"
    );
    let stmt_axioms = transitive_axioms(&env, &goal_ty);
    let proof_axioms = transitive_axioms(&env, &proof);
    let introduced: Vec<Name> = proof_axioms.difference(&stmt_axioms).cloned().collect();
    assert!(
        introduced.is_empty(),
        "one-arg + refl proof introduced axioms beyond statement: {introduced:?}"
    );
}

/// NEGATIVE: a WRONG sub-rewrite must NOT yield a proof of the original goal.
///
/// Goal `(a = a') → (b = b') → (f a b = f a' b')` but we rewrite the FIRST
/// argument with `hb : b = b'` — `hb`'s LHS `b` does not occur in the focused
/// `a`, so the `rw` must fail (RewriteNoMatch). The conv block therefore does
/// not close the goal: the machinery is fail-closed, never miscertifying.
#[test]
#[serial]
fn test_conv_congr_wrong_rewrite_fails_closed() {
    reset_all_counters();
    let env = setup_env_binary_f();
    let (a, ap, b, bp) = (n_const("a"), n_const("a'"), n_const("b"), n_const("b'"));

    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(a.clone(), ap.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_eq_n(b.clone(), bp.clone()),
            make_eq(
                n_ty(),
                make_f(a.clone(), b.clone()),
                make_f(ap.clone(), bp.clone()),
            ),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "ha").expect("intro ha");
    intro(&mut state, "hb").expect("intro hb");

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                // Select the FIRST argument (`a`) but try to rewrite with `hb`
                // (b = b'); `b` does not occur in `a`, so this must fail.
                SurfaceTactic::ConvArg(Span::dummy(), 1),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("hb")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    );
    assert!(
        result.is_err(),
        "rewriting argument `a` with `hb : b = b'` must fail-closed, not miscertify"
    );
    // The goal must remain unproved.
    assert!(
        state.closed_proof().is_none(),
        "no closed proof may exist after a failed sub-rewrite"
    );
}

// ===================== ADVERSARIAL REVIEW ADDITIONS =====================

/// Ternary `g : N -> N -> N -> N` env with constants a a' b b' c c'.
fn setup_env_ternary_g() -> Environment {
    let mut env = setup_env_binary_f();
    for name in ["c", "c'"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: n_ty(),
        })
        .expect("add const");
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n_ty(),
            Expr::pi(
                BinderInfo::Default,
                n_ty(),
                Expr::pi(BinderInfo::Default, n_ty(), n_ty()),
            ),
        ),
    })
    .expect("add g");
    env
}

fn make_g(x: Expr, y: Expr, z: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(n_const("g"), x), y), z)
}

/// ADVERSARIAL: 3-ary, rewrite ONLY the MIDDLE argument. This exercises the
/// fold's `congrFun'` arm (a trailing UNCHANGED arg after a changed prefix).
/// `g a b c = g a b' c` with only `hb : b = b'`. The first arg is untouched
/// (refl-prefix), the middle changes (congrArg), the last is untouched but the
/// prefix has now changed (congrFun'). Must kernel-check, no new axioms.
#[test]
#[serial]
fn adversarial_ternary_middle_arg_only_kernel_checked() {
    reset_all_counters();
    let env = setup_env_ternary_g();
    let (a, b, bp, c) = (n_const("a"), n_const("b"), n_const("b'"), n_const("c"));

    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(b.clone(), bp.clone()),
        make_eq(
            n_ty(),
            make_g(a.clone(), b.clone(), c.clone()),
            make_g(a.clone(), bp.clone(), c.clone()),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "hb").expect("intro hb");

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::ConvArg(Span::dummy(), 2),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("hb")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    )
    .expect("ternary middle-arg conv should close");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(
            n_ty(),
            make_g(a.clone(), bp.clone(), c.clone()),
            make_g(a.clone(), bp.clone(), c.clone())
        ),
        "only middle arg should change"
    );
    rfl(&mut state).expect("closes by rfl");

    let proof = state.closed_proof().expect("closed proof");
    let tc = TypeChecker::new(&env);
    let inferred = tc.infer_type(&proof).expect("kernel-type-check");
    assert!(
        tc.is_def_eq(&inferred, &goal_ty),
        "ternary middle-arg proof must have original goal type; inferred {inferred:?}"
    );
    let stmt_axioms = transitive_axioms(&env, &goal_ty);
    let proof_axioms = transitive_axioms(&env, &proof);
    let introduced: Vec<Name> = proof_axioms.difference(&stmt_axioms).cloned().collect();
    assert!(
        introduced.is_empty(),
        "ternary middle-arg proof introduced axioms beyond statement: {introduced:?}"
    );
}

/// ADVERSARIAL FALSE-GOAL: try to certify `f a b = f a' b'` while only
/// `ha : a = a'` is in scope (NO hb). Rewrite arg1 with ha (legit), leave
/// arg2 (b) untouched -> recombination synthesizes refl for b -> the conv
/// reconstructs `f a b -> f a' b`, NOT `f a' b'`. The remaining goal is
/// `f a' b = f a' b'` which is NOT closable by rfl (b != b'). The machinery
/// must NOT produce a closed proof of the original (false-without-hb) goal.
#[test]
#[serial]
fn adversarial_cannot_close_missing_hypothesis() {
    reset_all_counters();
    let env = setup_env_binary_f();
    let (a, ap, b, bp) = (n_const("a"), n_const("a'"), n_const("b"), n_const("b'"));

    // Goal: (a = a') -> (f a b = f a' b')   [NOTE: no hb provided!]
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(a.clone(), ap.clone()),
        make_eq(
            n_ty(),
            make_f(a.clone(), b.clone()),
            make_f(ap.clone(), bp.clone()),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "ha").expect("intro ha");

    let mut ctx = ElabCtx::new(&env);
    let _ = ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::ConvArg(Span::dummy(), 1),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("ha")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    );
    // After conv (best case for the attacker): goal becomes f a' b = f a' b'.
    // Try to close by rfl — must FAIL (b != b').
    let rfl_res = rfl(&mut state);
    assert!(
        rfl_res.is_err() || state.closed_proof().is_none(),
        "MUST NOT close f a' b = f a' b' by rfl (b != b')"
    );
    // And there must be no closed proof of the original FALSE-shaped goal.
    assert!(
        state.closed_proof().is_none(),
        "ESCALATE: machinery closed a goal that requires a missing hypothesis"
    );
}

/// ADVERSARIAL MIS-PAIR: both args are the SAME constant `a`. Goal
/// `(a = a') -> (f a a = f a' a)`. We `congr` then select arg 1 and rewrite
/// a -> a'. The rw sees the focus narrowed to ONLY arg1's expr (`a`), so it
/// must rewrite ONLY that focus, leaving arg2 (`a`) intact. If focus narrowing
/// leaked, it would rewrite BOTH a's and produce `f a' a'`, mismatching the
/// goal RHS `f a' a`. Confirms per-focus isolation (INV-3).
#[test]
#[serial]
fn adversarial_duplicate_arg_focus_isolation() {
    reset_all_counters();
    let env = setup_env_binary_f();
    let (a, ap) = (n_const("a"), n_const("a'"));

    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(a.clone(), ap.clone()),
        make_eq(
            n_ty(),
            make_f(a.clone(), a.clone()),
            make_f(ap.clone(), a.clone()),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "ha").expect("intro ha");

    let mut ctx = ElabCtx::new(&env);
    let res = ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::ConvArg(Span::dummy(), 1),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("ha")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    );
    res.expect("conv arg1-only rewrite over duplicate args should succeed");
    // Goal must be exactly f a' a = f a' a (only arg1 changed). If arg2 also
    // changed we'd see f a' a' on the LHS and the assert_eq would fail.
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(
            n_ty(),
            make_f(ap.clone(), a.clone()),
            make_f(ap.clone(), a.clone())
        ),
        "ESCALATE: focus leaked — arg2 was rewritten too (both a's changed)"
    );
    rfl(&mut state).expect("closes by rfl");
    let proof = state.closed_proof().expect("closed proof");
    let tc = TypeChecker::new(&env);
    let inferred = tc.infer_type(&proof).expect("kernel-type-check");
    assert!(
        tc.is_def_eq(&inferred, &goal_ty),
        "duplicate-arg proof must have original goal type; inferred {inferred:?}"
    );
}

/// ADVERSARIAL DEPENDENT HEAD: a function whose RESULT TYPE depends on the
/// first argument cannot be handled by the non-dependent congr family. The
/// machinery must FAIL CLOSED (kernel reject at the boundary), never produce a
/// closed proof. `dh : (n : N) -> (P n)` where P : N -> Type. Goal shape uses
/// HEq-free but dependent application `dh a` vs `dh a'`. We try to rewrite the
/// argument; recombination would emit a non-dependent `congrArg`/`congr` whose
/// kernel type does not match -> rejected.
#[test]
#[serial]
fn adversarial_dependent_head_fails_closed() {
    reset_all_counters();
    let mut env = setup_env_binary_f();
    // P : N -> Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty(), Expr::type_()),
    })
    .expect("add P");
    // dh : (n : N) -> P n   (dependent result type)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("dh"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n_ty(),
            Expr::app(n_const("P"), Expr::bvar(0)),
        ),
    })
    .expect("add dh");
    let (a, ap) = (n_const("a"), n_const("a'"));
    let dh = n_const("dh");

    // We can't even state `dh a = dh a'` homogeneously (types P a vs P a' differ).
    // Instead state a goal where the dependent app appears under a wrapper that
    // forces the congr machinery to engage on the dependent argument. Use:
    //   (a = a') -> (Q (dh a) = Q (dh a'))   is also heterogeneous.
    // Simplest honest probe: HEq-free homogeneous equality is impossible, so the
    // attacker's best move is `dh a = dh a` (refl-shaped) and try to rewrite the
    // arg to a' under congr — that would change ONE side to `dh a'` whose type
    // differs, so the kernel boundary must reject.
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq_n(a.clone(), ap.clone()),
        make_eq(
            Expr::app(n_const("P"), a.clone()),
            Expr::app(dh.clone(), a.clone()),
            Expr::app(dh.clone(), a.clone()),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "ha").expect("intro ha");

    let mut ctx = ElabCtx::new(&env);
    let res = ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                SurfaceTactic::ConvArg(Span::dummy(), 1),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("ha")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    );
    // Either the conv errors (fail-closed) or it "succeeds" leaving an unclosable
    // goal. In NO case may there be a closed proof of a wrong-typed equality.
    if res.is_ok() {
        // If it claims success, the goal can only be honestly closed if it is
        // genuinely true; attempt rfl and verify any closed proof kernel-checks.
        let _ = rfl(&mut state);
    }
    if let Some(proof) = state.closed_proof() {
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(&proof)
            .expect("any closed proof MUST kernel-type-check");
        assert!(
            tc.is_def_eq(&inferred, &goal_ty),
            "ESCALATE: dependent-head produced a closed proof whose type is NOT the goal"
        );
    }
}

/// ADVERSARIAL HEAD-REWRITE: rewrite the HEAD focus (arg 0 = the function
/// itself) f -> f2, plus an arg. Goal `(f = f2) -> (a = a') -> (f a = f2 a')`.
/// Tests the `mk_congr` (both prefix and arg changed) arm with a real head eq.
#[test]
#[serial]
fn adversarial_head_and_arg_rewrite_kernel_checked() {
    reset_all_counters();
    let mut env = setup_env_binary_f();
    // unary h, h2 : N -> N
    for name in ["h", "h2"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, n_ty(), n_ty()),
        })
        .expect("add h");
    }
    let (a, ap) = (n_const("a"), n_const("a'"));
    let h = n_const("h");
    let h2 = n_const("h2");
    let arrow = Expr::pi(BinderInfo::Default, n_ty(), n_ty());

    // (h = h2) -> (a = a') -> (h a = h2 a')
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        make_eq(arrow.clone(), h.clone(), h2.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_eq_n(a.clone(), ap.clone()),
            make_eq(
                n_ty(),
                Expr::app(h.clone(), a.clone()),
                Expr::app(h2.clone(), ap.clone()),
            ),
        ),
    );
    let mut state = ProofState::new(env.clone(), goal_ty.clone());
    intro(&mut state, "hf").expect("intro hf : h = h2");
    intro(&mut state, "ha").expect("intro ha : a = a'");

    let mut ctx = ElabCtx::new(&env);
    let res = ctx.eval(
        &mut state,
        &SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::ConvArg(Span::dummy(), -2),
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "congr".into(),
                    args: vec![],
                },
                // arg 0 selects the HEAD focus (h); rewrite h -> h2.
                SurfaceTactic::ConvArg(Span::dummy(), 0),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("hf")],
                    SurfaceTacticLocation::Goal,
                ),
                SurfaceTactic::ConvArg(Span::dummy(), 1),
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![rw_rule_named("ha")],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
    );
    // If head rewrite is unsupported it should fail-closed (no miscertify).
    match res {
        Ok(()) => {
            assert_eq!(
                state.current_goal().unwrap().target,
                make_eq(
                    n_ty(),
                    Expr::app(h2.clone(), ap.clone()),
                    Expr::app(h2.clone(), ap.clone())
                ),
                "head+arg rewrite should land f2 a'"
            );
            rfl(&mut state).expect("closes by rfl");
            let proof = state.closed_proof().expect("closed proof");
            let tc = TypeChecker::new(&env);
            let inferred = tc.infer_type(&proof).expect("kernel-type-check");
            assert!(
                tc.is_def_eq(&inferred, &goal_ty),
                "head+arg proof must have original goal type; inferred {inferred:?}"
            );
            let stmt_axioms = transitive_axioms(&env, &goal_ty);
            let proof_axioms = transitive_axioms(&env, &proof);
            let introduced: Vec<Name> = proof_axioms.difference(&stmt_axioms).cloned().collect();
            assert!(
                introduced.is_empty(),
                "head+arg proof introduced axioms beyond statement: {introduced:?}"
            );
        }
        Err(_) => {
            // Fail-closed is acceptable; just ensure no bogus closed proof.
            assert!(
                state.closed_proof().is_none(),
                "head rewrite failed but left a closed proof"
            );
        }
    }
}
