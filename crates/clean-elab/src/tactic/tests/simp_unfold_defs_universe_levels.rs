// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-level instantiation in `simp`'s DELTA-UNFOLD path (`unfold_defs`).
//!
//! Queue-C bricks 3 and 6 (`docs/plans/BRICK_QUEUE_2026-08-31-C.md` §7.3, §7.6)
//! — `Function.invFun_eq` at `Mathlib/Logic/Function/Basic.lean:415` and
//! `dite_ne_right_iff` at `Mathlib/Logic/Basic.lean:841` — both fail as:
//!
//! ```text
//! Tactic failed: goal mismatch: replace_target_def_eq: new target is not
//! definitionally equal to current target
//! ```
//!
//! Both are `simp only [<a definition>, …]`:
//! `simp only [invFun, dif_pos h, h.choose_spec]` and
//! `simp only [Ne, dite_eq_right_iff, not_forall]`. `invFun` and `Ne` are
//! universe-polymorphic `def`s, so `resolve_unfold_defs` registers them for
//! delta-unfolding and `simp_expr` splices their bodies in.
//!
//! ## The mechanism
//!
//! `unfold_named_consts` matched a `Const(name, levels)` node against the
//! unfold map and returned the stored body while DISCARDING `levels`. The body
//! of a universe-polymorphic definition is written over that declaration's own
//! `Level::Param`s, so the spliced target carried a level parameter that is not
//! bound at the use site — it is not definitionally equal to the constant it
//! replaced. `simp` reports a body substitution as a proof-free change
//! (`SimpResult { proof: None }`), so the result goes to
//! `ProofState::replace_target_def_eq`, whose def-eq check then rejects the
//! whole `simp` step.
//!
//! This is **RC-E.2 at a second site**. The same defect in the `unfold` /
//! `delta` tactic was found and fixed with `substitute_const` — see
//! `unfold_universe_levels.rs`, whose header records the symptom
//! `TypeMismatch { expected: Sort(Param(u)), inferred: Sort(Succ(Zero)) }`.
//! `simp`'s copy of the substitution was left behind, and its own contract
//! block said so in as many words: *"universe parameters are currently not
//! substituted into the body (matches the existing `unfold` tactic
//! behavior)"* — a note that had gone stale on the day `unfold` was fixed.
//!
//! ## The controls
//!
//! Every polymorphic arm is paired with a MONOMORPHIC one of the same shape.
//! The monomorphic arm passed before the fix and must keep passing: it is what
//! shows the defect is the level discard and not `simp only [<def>]` in
//! general. It is also the pair that reproduces at the surface, in four lines
//! against `target/release/clean` with no imports — `PolyNe` fails, `MonoNe`
//! passes, and the source arms below are that pair.
//!
//! The third arm pins the CONVENIENT APPROXIMATION. "Splice the body whatever
//! the levels say" is one line shorter than instantiating, and it passes both
//! arms above whenever the level counts happen to line up. The guard is that a
//! `Const` whose level count disagrees with the stored declaration's parameter
//! count is left FOLDED rather than substituted, because there is no
//! substitution to make — and an unguarded splice would put the declaration's
//! parameters back in the goal, which is the very bug.

use super::*;
use crate::elaborate_decl_and_register_with_warning;
use crate::tactic::simp::types::UnfoldDef;
use crate::tactic::SimpConfig;
use clean_kernel::env::Declaration;
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Surface arms — the reproduction pair, run through the real elaborator.
// ---------------------------------------------------------------------------

/// Elaborate every declaration in `src`, returning the first error's `Debug`
/// rendering or `None` when all of them registered.
fn elab_all(src: &str) -> Option<String> {
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(&mut env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// The polymorphic arm — `Ne`'s shape, reduced to what is needed to fail.
///
/// Before the fix this is the brick's verbatim message; the assertion names it
/// so that a future unrelated failure here cannot be mistaken for this row.
#[test]
fn test_simp_only_unfolds_a_universe_polymorphic_definition() {
    let src = "def PolyNe {a : Sort u} (x y : a) : Prop := Not (x = y)\n\
               theorem armC (m n : Nat) : PolyNe m n -> True := by\n\
               \x20 simp only [PolyNe]\n\
               \x20 intro _\n\
               \x20 trivial\n";
    if let Some(e) = elab_all(src) {
        assert!(
            !e.contains("replace_target_def_eq"),
            "RC-E.2 at simp's unfold path: splicing `PolyNe`'s body without \
             instantiating its level parameter leaves `Sort u` dangling, so \
             the rewritten target is not def-eq to the old one. Got: {e}"
        );
        panic!("the polymorphic arm must elaborate, got: {e}");
    }
}

/// The monomorphic control — identical shape, no universe parameter.
///
/// Green before the fix and after it. If this ever goes red, the arm above
/// stops discriminating and proves nothing about levels.
#[test]
fn test_simp_only_unfolds_a_monomorphic_definition_unchanged() {
    let src = "def MonoNe (x y : Nat) : Prop := Not (x = y)\n\
               theorem armD (m n : Nat) : MonoNe m n -> True := by\n\
               \x20 simp only [MonoNe]\n\
               \x20 intro _\n\
               \x20 trivial\n";
    assert!(
        elab_all(src).is_none(),
        "the monomorphic control must elaborate both before and after the fix"
    );
}

// ---------------------------------------------------------------------------
// The approximation guard — a hand-built config, so the level counts can be
// made to disagree on purpose.
// ---------------------------------------------------------------------------

/// A `Const(F, [])` occurrence against a stored definition declaring one level
/// parameter has no instantiation to make, so it must be left FOLDED.
///
/// The arm is written against `simp`'s VERDICT, not against the installed
/// goal, and that is load-bearing: when a splice produces a target simp cannot
/// justify, `replace_target_def_eq` refuses and the goal is left UNCHANGED —
/// so an assertion that inspects the surviving target is green under both
/// rules and pins nothing. The two rules are distinguishable only by which
/// refusal they produce:
///
/// * guarded (shipped): the constant is untouched, nothing changes, `simp`
///   reports `NoProgress`;
/// * "splice regardless" (the approximation): `Sort u` lands in the target,
///   `simp` calls it progress, and `replace_target_def_eq` rejects it with the
///   bricks' own `GoalMismatch`.
#[test]
fn test_level_arity_mismatch_leaves_the_constant_folded() {
    let mut env = Environment::new();
    env.init_eq().expect("init Eq");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("register A");
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("aa"),
        level_params: vec![],
        type_: a_ty.clone(),
    })
    .expect("register aa");

    // The stored body MENTIONS the declaration's own `u`, so a
    // levels-discarding splice is observable in the rewritten target.
    let u = Name::from_string("u");
    let body_with_u = Expr::sort(Level::param(u.clone()));

    // `@Eq.{1} A F aa`, where the `F` occurrence carries ZERO levels while the
    // stored declaration declares one.
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            Expr::const_(Name::from_string("F"), vec![]),
        ),
        Expr::const_(Name::from_string("aa"), vec![]),
    );

    let mut state = ProofState::new(env, target);
    let mut config = SimpConfig::new();
    config.only_simplify = true;
    config.unfold_defs.insert(
        Name::from_string("F"),
        UnfoldDef {
            level_params: vec![u],
            value: body_with_u,
        },
    );

    let err = format!("{:?}", simp(&mut state, config));
    assert!(
        !err.contains("replace_target_def_eq"),
        "a level-arity mismatch must leave the constant FOLDED; splicing the \
         body regardless reintroduces the declaration's own `u` and lands on \
         the bricks' own def-eq refusal: {err}"
    );
}
