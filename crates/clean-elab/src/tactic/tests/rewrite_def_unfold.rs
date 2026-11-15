// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rewriting by a DEFINITION name — `rw [Xor']`-shaped δβ unfold rules.
//!
//! `Mathlib/Logic/Basic` declarations such as `xor_iff_or_and_not_and`
//! (`rw [Xor', or_and_right, …]`, source line 365) failed with
//! *"rewrite rule 'Xor'' is not an equation"* because `rw [X]` only admitted
//! `Eq`/`Iff`-typed rules. `tactic::equality::rewrite_delta` now handles a
//! `Definition`-kind name at the `rw` / `rw … at` ENTRY POINTS as a bounded
//! δβ unfold — no unification, no synthesized proof term, no fixpoint.
//!
//! These tests pin the behaviour; they are explicitly NOT the acceptance
//! evidence for the brick. A previous version of this feature passed a
//! comparable unit set and then wedged Mathlib elaboration for 17 h; the
//! acceptance set must include the timed corpus canary described in
//! `patches/rw-def-unfold-v2/NOTES.md`.
//!
//! Pinned here:
//!
//! - the canonical two-`Prop`-binder def unfold at the goal (red → green),
//! - a universe-polymorphic definition (per-occurrence level instantiation,
//!   the RC-E.2 shape),
//! - unfold at a hypothesis (`rw [X] at h`),
//! - a definition absent from the goal reports `RewriteNoMatch`,
//! - controls that must NOT take the delta path: an equation-typed THEOREM, an
//!   equation-typed DEFINITION, an axiom, a non-equation theorem, an opaque
//!   constant, and the backward direction `rw [← X]`.

use super::*;
use crate::unify::MetaId;

/// `@Eq.{1} Prop lhs rhs`.
fn make_eq_prop(lhs: Expr, rhs: Expr) -> Expr {
    make_eq(Expr::prop(), lhs, rhs)
}

/// `Or (And a b) (And b a)` — the `Xor'`-shaped body over two Prop args.
fn or_and_body(a: Expr, b: Expr) -> Expr {
    let and_ = |x: Expr, y: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("And"), vec![]), x),
            y,
        )
    };
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            and_(a.clone(), b.clone()),
        ),
        and_(b, a),
    )
}

/// Env with Eq machinery, And/Or, two Prop atoms `p`/`q`, and the canonical
/// definition-shaped rewrite source
/// `def PXor (a b : Prop) : Prop := Or (And a b) (And b a)`
/// (Mathlib's `Xor'` with `Not` elided — the unfold machinery only sees a
/// `Definition`-kind constant whose type is not an equation).
fn setup_env_with_prop_def() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_and().unwrap();
    env.init_or().unwrap();

    for name in ["p", "q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }

    // (a b : Prop) → Prop
    let pxor_ty = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
    );
    // fun (a b : Prop) => Or (And a b) (And b a)   (a = bvar 1, b = bvar 0)
    let pxor_val = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            or_and_body(Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("PXor"),
        level_params: vec![],
        type_: pxor_ty,
        value: pxor_val,
        // Regular (not eagerly-reducible) — matches an ordinary `def`; the
        // def-eq re-check in `replace_target_def_eq` must still δ-unfold it.
        is_reducible: false,
    })
    .unwrap();

    env
}

/// `PXor p q`.
fn pxor_pq() -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("PXor"), vec![]),
            Expr::const_(Name::from_string("p"), vec![]),
        ),
        Expr::const_(Name::from_string("q"), vec![]),
    )
}

/// Confirm `close_goal` accepted a kernel-valid proof for the closed goal: the
/// term assigned to the original root metavariable infers a type def-eq to the
/// original target. (Local copy of `rewrite_subst::assert_root_proof_checks`,
/// which is file-private there.)
fn assert_root_proof_checks(state: &ProofState, root: MetaId, original_target: &Expr) {
    let proof = state
        .metas()
        .get_assignment(root)
        .expect("root goal should be closed with a proof term")
        .clone();
    let proof = state.metas().instantiate(&proof);
    let probe_goal = state.current_goal().cloned().unwrap_or_else(|| Goal {
        meta_id: root,
        target: original_target.clone(),
        local_ctx: Vec::new(),
        tag: None,
        case_binders: Vec::new(),
    });
    let inferred = state
        .infer_type(&probe_goal, &proof)
        .expect("rewrite proof term must type-check in the kernel");
    assert!(
        state.is_def_eq(&probe_goal, &inferred, original_target),
        "rewrite proof has type {inferred:?}, expected {original_target:?}"
    );
}

// ==========================================================================
// Red → green: the canonical `rw [Xor']` shape
// ==========================================================================

#[test]
fn test_rewrite_definition_name_unfolds_goal_occurrence() {
    // Goal `PXor p q = Or (And p q) (And q p)`; `rw [PXor]` must δ-unfold the
    // occurrence, β-apply `p`/`q`, and leave the reflexive equality for `rfl`.
    let env = setup_env_with_prop_def();
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    let unfolded = or_and_body(p, q);

    let target = make_eq_prop(pxor_pq(), unfolded.clone());
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("PXor"),
    )
    .expect("rw [PXor] should delta-unfold the Definition");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_prop(unfolded.clone(), unfolded),
        "the PXor occurrence must be replaced by the BETA-APPLIED body: a leftover \
         `(fun a b => …) p q` redex would be def-eq but would defeat the syntactic \
         occurrence search of every later rule in a `rw [Xor', or_and_right, …]` chain"
    );

    rfl(&mut state).expect("rfl should close the unfolded reflexive equality");
    assert!(
        state.current_goal().is_none(),
        "no goals should remain after rw [PXor]; rfl"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_definition_name_universe_polymorphic() {
    // `def dupDef.{u} : (α : Sort u) → α → α := fun α x => x` used as a rewrite
    // rule on `P (dupDef.{1} N x)`. Exercises level instantiation of the stored
    // value at the OCCURRENCE's levels (the RC-E.2 hazard: substituting a
    // polymorphic body verbatim leaves dangling `Sort (Param u)`s).
    let mut env = setup_env_with_full_eq();
    let u = Name::from_string("u");
    let sort_u = Expr::sort(Level::param(u.clone()));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("dupDef"),
        level_params: vec![u],
        // (α : Sort u) → α → α
        type_: Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
        // fun (α : Sort u) (x : α) => x
        value: Expr::lam(
            BinderInfo::Default,
            sort_u,
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
        is_reducible: false,
    })
    .unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    // @dupDef.{1} N x  (N : Type = Sort 1)
    let dup_app = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("dupDef"),
                vec![Level::succ(Level::zero())],
            ),
            n_ty,
        ),
        x.clone(),
    );

    let target = make_p(dup_app);
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("dupDef"),
    )
    .expect("rw [dupDef] should unfold the universe-polymorphic definition");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "goal should become P x after unfolding dupDef"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_definition_name_at_hypothesis() {
    // `rw [PXor] at h` where `h : PXor p q` — the whole hypothesis type is the
    // occurrence; `replace_local_decl_def_eq` re-checks def-eq before
    // installing the new type.
    let env = setup_env_with_prop_def();
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    let unfolded = or_and_body(p, q);

    let mut state = ProofState::with_context(
        env,
        unfolded.clone(), // target: the unfolded form, closable by `exact h` after the rw
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: pxor_pq(),
            value: None,
        }],
    );

    rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("PXor"),
        &clean_parser::SurfaceName::generated_path("h"),
        false,
    )
    .expect("rw [PXor] at h should unfold the Definition in the hypothesis type");

    let goal = state.current_goal().expect("goal remains after rw at h");
    let h_ty = &goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .expect("hypothesis h survives the rewrite")
        .ty;
    assert_eq!(
        *h_ty, unfolded,
        "h's type should be the beta-applied definition body"
    );
}

#[test]
fn test_rewrite_definition_name_absent_from_goal_reports_no_match() {
    // The delta path must report a rewrite no-match — never a silent success,
    // and never a `replace_target_def_eq` no-op — when the definition does not
    // occur in the rewritten location.
    let env = setup_env_with_prop_def();
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    let already_unfolded = or_and_body(p, q);

    let mut state = ProofState::new(env, already_unfolded);

    let err = rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("PXor"),
    )
    .expect_err("rw [PXor] with no PXor occurrence must fail, not silently succeed");
    match err {
        TacticError::RewriteNoMatch { rule, tactic, .. } => {
            assert_eq!(rule, "PXor");
            assert_eq!(tactic, "rewrite");
        }
        other => panic!("expected RewriteNoMatch, got: {other:?}"),
    }
}

// ==========================================================================
// Controls: everything that must NOT take the delta path
// ==========================================================================

#[test]
fn test_rewrite_definition_name_backward_is_still_rejected() {
    // Narrowness gate: `rw [← X]` would need the definition's BODY as a match
    // pattern, which re-enters the unifier this brick deliberately avoids. It
    // keeps the unchanged admission error.
    let env = setup_env_with_prop_def();
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    let unfolded = or_and_body(p, q);

    let mut state = ProofState::new(env, make_eq_prop(unfolded, pxor_pq()));

    let err = rewrite_rtl(
        &mut state,
        &clean_parser::SurfaceName::generated_path("PXor"),
    )
    .expect_err("rw [← PXor] is out of scope for the delta path and must stay rejected");
    match err {
        TacticError::GoalMismatch(msg) => assert!(
            msg.contains("is not an equation"),
            "backward rejection should keep the admission diagnostic, got: {msg}"
        ),
        other => panic!("expected GoalMismatch admission error, got: {other:?}"),
    }
}

#[test]
fn test_rewrite_theorem_name_with_equation_type_still_works() {
    // A THEOREM whose type is an equation must keep rewriting through the
    // ordinary equation path — the `Definition`-kind gate must not disturb it.
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xy_ax"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y.clone()),
    })
    .unwrap();
    // Theorem restating the axiom — registered with ConstantKind::Theorem
    // (restatement is fine for a tactic-dispatch control; not a proof metric).
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("xy_thm"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y.clone()),
        value: Expr::const_(Name::from_string("xy_ax"), vec![]),
    })
    .unwrap();

    let target = make_p(x);
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("xy_thm"),
    )
    .expect("rw [xy_thm] should use the theorem's equation");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(y),
        "goal should become P y via the theorem equation"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_equation_typed_definition_takes_the_equation_path() {
    // Gate 4 in `rewrite_delta::delta_rule`: a `Definition` whose TYPE is an
    // equation is a rewrite lemma, not an unfold target. It must still rewrite
    // `P x` to `P y` (equation path), NOT unfold `eq_def` to its proof value.
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xy_ax"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y.clone()),
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("xy_def"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y.clone()),
        value: Expr::const_(Name::from_string("xy_ax"), vec![]),
        is_reducible: false,
    })
    .unwrap();

    let target = make_p(x);
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("xy_def"),
    )
    .expect("an equation-typed Definition must still rewrite via the equation path");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(y),
        "goal should become P y — the equation path, not a delta unfold"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_axiom_name_without_equation_type_still_errors() {
    // An AXIOM with a function type (same shape as a definition's, but no
    // value) must keep the fail-closed admission error verbatim.
    let mut env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f_ax"),
        level_params: vec![],
        type_: Expr::arrow(n_ty, Expr::const_(Name::from_string("N"), vec![])),
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let f_x = Expr::app(Expr::const_(Name::from_string("f_ax"), vec![]), x);
    let mut state = ProofState::new(env, make_p(f_x));

    let err = rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("f_ax"),
    )
    .expect_err("rw by a non-equation AXIOM name must stay rejected");
    match err {
        TacticError::GoalMismatch(msg) => assert!(
            msg.contains("is not an equation"),
            "axiom rejection should keep the admission diagnostic, got: {msg}"
        ),
        other => panic!("expected GoalMismatch admission error, got: {other:?}"),
    }
}

#[test]
fn test_rewrite_theorem_name_without_equation_type_still_errors() {
    // A THEOREM whose type is NOT an equation has a value, but Theorem-kind
    // constants are not unfold sources (proof terms are opaque to rw, exactly
    // as in simp's Definition-only unfold gate) — the admission error stands.
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("px_ax"),
        level_params: vec![],
        type_: make_p(x.clone()),
    })
    .unwrap();
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("px_thm"),
        level_params: vec![],
        type_: make_p(x.clone()),
        value: Expr::const_(Name::from_string("px_ax"), vec![]),
    })
    .unwrap();

    let mut state = ProofState::new(env, make_p(x));

    let err = rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("px_thm"),
    )
    .expect_err("rw by a non-equation THEOREM name must stay rejected");
    match err {
        TacticError::GoalMismatch(msg) => assert!(
            msg.contains("is not an equation"),
            "theorem rejection should keep the admission diagnostic, got: {msg}"
        ),
        other => panic!("expected GoalMismatch admission error, got: {other:?}"),
    }
}

#[test]
fn test_rewrite_opaque_constant_is_not_an_unfold_source() {
    // `Declaration::Opaque` has a value but must never be δ-unfolded (Lean's
    // `opaque`/`@[irreducible]` semantics; the kernel does not unfold it during
    // def-eq either, so a delta step would fail closed later anyway).
    let mut env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("opaqueX"),
        level_params: vec![],
        type_: n_ty,
        value: Expr::const_(Name::from_string("x"), vec![]),
    })
    .unwrap();

    let opaque_x = Expr::const_(Name::from_string("opaqueX"), vec![]);
    let mut state = ProofState::new(env, make_p(opaque_x));

    let err = rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("opaqueX"),
    )
    .expect_err("rw by an OPAQUE constant name must stay rejected");
    match err {
        TacticError::GoalMismatch(msg) => assert!(
            msg.contains("is not an equation"),
            "opaque rejection should keep the admission diagnostic, got: {msg}"
        ),
        other => panic!("expected GoalMismatch admission error, got: {other:?}"),
    }
}

#[test]
fn test_local_hypothesis_shadows_the_definition_name() {
    // Lean 4 resolution order: a local hypothesis named `PXor` shadows the
    // environment definition, so `rw [PXor]` uses the hypothesis (here a
    // non-equation, which fails cleanly) and never reaches the delta path.
    let env = setup_env_with_prop_def();
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);

    let mut state = ProofState::with_context(
        env,
        make_eq_prop(pxor_pq(), or_and_body(p, q)),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("PXor"),
            ty: Expr::const_(Name::from_string("p"), vec![]),
            value: None,
        }],
    );

    let result = rewrite_ltr(
        &mut state,
        &clean_parser::SurfaceName::generated_path("PXor"),
    );
    assert!(
        result.is_err(),
        "a local hypothesis of the same name shadows the definition; a non-equation \
         local must fail rather than silently delta-unfolding the env constant"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_prop(
            pxor_pq(),
            or_and_body(
                Expr::const_(Name::from_string("p"), vec![]),
                Expr::const_(Name::from_string("q"), vec![])
            )
        ),
        "the shadowed rewrite must leave the goal untouched"
    );
}
