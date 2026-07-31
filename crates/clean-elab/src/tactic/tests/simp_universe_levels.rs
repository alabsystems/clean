// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-level instantiation in simp's proof reconstruction (RC-E.1).
//!
//! `simp`'s `proof_expr: None` reconstruction path assigned the *same* hardcoded
//! level param (`u_simp`) to every level param of the lemma constant. `u_simp`
//! is a convention of Clean's hand-written builtin patterns
//! (`simp/lemmas_builtin.rs`) only; a lemma taken from the environment
//! (`simp [X]`, `simp only [X]`, the `@[simp]` registry) carries its
//! DECLARATION's real level-param names, so `u_simp` was never constrained by
//! unification, the assembled proof carried an unassigned level,
//! `proof_matches_rewrite` rejected it, and the rewrite was silently dropped as
//! `NoProgress`. 37% of Lean core's `@[simp]` set is universe-polymorphic, so
//! this was most of the imported simp set.
//!
//! The polymorphic test is paired with a MONOMORPHIC control so the fix cannot
//! silently trade one class of lemma for another, and with a builtin-pattern
//! control that pins the `u_simp` convention still working.
//!
//! The sibling defect in `unfold`/`delta` (RC-E.2) is covered by
//! `unfold_universe_levels.rs`.

use super::*;

/// Collect every `Level::Param` name reachable from `expr` (Sort levels and
/// `Const` level arguments). A closed, fully-instantiated term produced from a
/// level-0 goal must have none.
fn level_params_in(expr: &Expr) -> Vec<String> {
    fn from_level(level: &Level, out: &mut Vec<String>) {
        match level {
            Level::Param(n) => out.push(n.to_string()),
            Level::Succ(inner) => from_level(inner, out),
            Level::Max(a, b) | Level::IMax(a, b) => {
                from_level(a, out);
                from_level(b, out);
            }
            Level::Zero => {}
        }
    }
    fn go(expr: &Expr, out: &mut Vec<String>) {
        match expr.kind() {
            ExprKind::Sort(level) => from_level(level, out),
            ExprKind::Const(_, levels) => {
                for level in levels.iter() {
                    from_level(level, out);
                }
            }
            ExprKind::App(f, a) => {
                go(f, out);
                go(a, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                go(ty, out);
                go(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                go(ty, out);
                go(val, out);
                go(body, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => go(inner, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(expr, &mut out);
    out
}

fn u() -> Name {
    Name::from_string("u")
}

fn type_u() -> Expr {
    Expr::sort(Level::succ(Level::param(u())))
}

fn n_ty() -> Expr {
    Expr::const_(Name::from_string("N"), vec![])
}

/// `@Eq.{lvl} ty lhs rhs`
fn eq_at(lvl: Level, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![lvl]), ty),
            lhs,
        ),
        rhs,
    )
}

/// Env with `Eq`, a base type `N : Type 0`, a constant `n : N`, and:
///
/// * `Wrap.{u} : {α : Type u} → α → α`                          (axiom)
/// * `Wrap_id.{u} : {α : Type u} → (x : α) → @Wrap.{u} α x = x`  (axiom)
/// * `WrapN : N → N`                                            (axiom)
/// * `WrapN_id : (x : N) → WrapN x = x`                          (axiom)
///
/// The polymorphic and monomorphic lemmas state the SAME shape; only the
/// universe quantification differs. That is the whole discriminator.
fn setup_polymorphic_wrap_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init Eq");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("register N");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: n_ty(),
    })
    .expect("register n");

    // Wrap.{u} : {α : Type u} → α → α
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Wrap"),
        level_params: vec![u()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            type_u(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
    })
    .expect("register Wrap");

    // Wrap_id.{u} : {α : Type u} → (x : α) → @Eq.{u+1} α (@Wrap.{u} α x) x
    let wrap_app = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Wrap"), vec![Level::param(u())]),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Wrap_id"),
        level_params: vec![u()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            type_u(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                eq_at(
                    Level::succ(Level::param(u())),
                    Expr::bvar(1),
                    wrap_app,
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .expect("register Wrap_id");

    // WrapN : N → N  (monomorphic control)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("WrapN"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty(), n_ty()),
    })
    .expect("register WrapN");

    // WrapN_id : (x : N) → @Eq.{1} N (WrapN x) x
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("WrapN_id"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n_ty(),
            eq_at(
                Level::succ(Level::zero()),
                n_ty(),
                Expr::app(
                    Expr::const_(Name::from_string("WrapN"), vec![]),
                    Expr::bvar(0),
                ),
                Expr::bvar(0),
            ),
        ),
    })
    .expect("register WrapN_id");

    env
}

/// RC-E.1 — the defect. `simp only [Wrap_id]` on `@Wrap.{0} N n = n`.
///
/// Before the fix the reconstructed proof was `@Wrap_id.{u_simp} N n`: `u_simp`
/// never appears in the lemma's pattern (which carries the declaration's real
/// `u`), so it was never solved, `proof_matches_rewrite` rejected the proof and
/// simp reported no progress.
#[test]
fn test_simp_only_universe_polymorphic_lemma_rewrites() {
    let env = setup_polymorphic_wrap_env();
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let wrap_n = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Wrap"), vec![Level::zero()]),
            n_ty(),
        ),
        n.clone(),
    );
    let target = eq_at(Level::succ(Level::zero()), n_ty(), wrap_n, n);
    let mut state = ProofState::new(env, target);

    simp_only(&mut state, vec!["Wrap_id".to_string()]).expect(
        "simp only must use a UNIVERSE-POLYMORPHIC registry lemma \
         (RC-E.1: the reconstructed proof carried an unsolved `u_simp`)",
    );
    assert!(
        state.is_complete(),
        "rewriting `@Wrap.{{0}} N n` to `n` leaves the reflexive goal `n = n`, \
         which simp closes"
    );

    let proof = state
        .closed_proof()
        .expect("polymorphic simp rewrite must produce an extractable closed proof");
    assert!(
        level_params_in(&proof).is_empty(),
        "the assembled proof must carry the SOLVED level (0), not a dangling \
         level param; got params {:?}",
        level_params_in(&proof)
    );
}

/// RC-E.1 control — the monomorphic sibling of the test above must keep
/// working, so the fix cannot trade one class of lemma for another.
#[test]
fn test_simp_only_monomorphic_lemma_still_rewrites() {
    let env = setup_polymorphic_wrap_env();
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let wrap_n = Expr::app(Expr::const_(Name::from_string("WrapN"), vec![]), n.clone());
    let target = eq_at(Level::succ(Level::zero()), n_ty(), wrap_n, n);
    let mut state = ProofState::new(env, target);

    simp_only(&mut state, vec!["WrapN_id".to_string()])
        .expect("simp only must keep using a MONOMORPHIC registry lemma");
    assert!(
        state.is_complete(),
        "monomorphic rewrite leaves `n = n`, which simp closes"
    );
    assert!(
        state.closed_proof().is_some(),
        "monomorphic simp rewrite must produce an extractable closed proof"
    );
}

/// RC-E.1 control — Clean's hand-written builtin patterns deliberately spell a
/// single `u_simp` level param that has NO counterpart in the proof
/// declaration's level params (`List.append_nil.{u}`). Threading the real
/// level-param names must not break them.
#[test]
fn test_simp_builtin_u_simp_pattern_still_fires() {
    let env = Environment::with_prelude();
    if env
        .get_const(&Name::from_string("List.append_nil"))
        .is_none()
    {
        // The builtin rule is only registered when its kernel-proved theorem
        // exists; nothing to guard if the prelude did not seed it.
        return;
    }
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat.clone(),
    );
    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat,
    );

    // ∀ (xs : List Nat), @List.append.{0} Nat xs (@List.nil.{0} Nat) = xs
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        list_nat.clone(),
        eq_at(
            Level::succ(Level::zero()),
            list_nat,
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("List.append"), vec![Level::zero()]),
                        Expr::const_(Name::from_string("Nat"), vec![]),
                    ),
                    Expr::bvar(0),
                ),
                nil,
            ),
            Expr::bvar(0),
        ),
    );
    let mut state = ProofState::new(env, goal_ty);
    intro(&mut state, "xs").expect("intro the list variable");

    simp(&mut state, SimpConfig::new())
        .expect("the builtin `List.append_nil` u_simp pattern must still fire");
    assert!(
        state.is_complete(),
        "`xs ++ [] = xs` is closed by the builtin List.append_nil rewrite"
    );
    let proof = state
        .closed_proof()
        .expect("builtin u_simp rewrite must produce an extractable closed proof");
    assert!(
        level_params_in(&proof).is_empty(),
        "builtin path must still resolve `u_simp` to the solved level; got {:?}",
        level_params_in(&proof)
    );
}
