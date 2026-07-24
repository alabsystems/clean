// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: instance search must POSTPONE (not force-resolve) an
//! input-only class goal whose INPUT position is still a bare, unassigned
//! metavariable.
//!
//! ## The bug
//!
//! `resolve_instance_candidates` (`crates/clean-elab/src/infer/instance.rs`)
//! unifies a candidate's non-out-parameter (INPUT) arguments against the goal
//! in phase 1 with `try_unify(inst_arg, goal_arg)`. When `goal_arg` is a bare
//! unassigned metavariable `?a` (an UNDETERMINED input, e.g. `?a` in an
//! `Inhabited ?a` / `Decidable ?a` goal) and the candidate's `inst_arg` is a
//! rigid/concrete term, `try_unify` happily assigns `?a := <candidate
//! concrete>` — i.e. the CANDIDATE determines the input, and the FIRST
//! candidate tried wins. That is a wrong-instance grab: for an input position
//! the GOAL must determine the argument, never the candidate.
//!
//! Lean's `synthInstance` POSTPONES a goal whose input positions are still
//! metavariables and retries once the surrounding term pins them; it never
//! lets a candidate backfill an undetermined input. Clean instead
//! force-resolved and committed garbage.
//!
//! ## What this test pins
//!
//! With a decoy `Inhabited DecoyType` instance registered and a goal
//! `Inhabited ?a` (`?a` unassigned):
//!
//!  - PRE-FIX (buggy): `resolve_instance` returned `Some(decoyInh)` and left
//!    `?a := DecoyType` — a wrong grab. (Documented, reproduced on the
//!    unmodified tree before the fix landed.)
//!  - POST-FIX: `resolve_instance` returns `None` (postpone) and `?a` is left
//!    UNASSIGNED, so the caller can pin the input first and retry.
//!
//! And the fix must NOT over-fire: once the input IS determined
//! (`Inhabited DecoyType`, a concrete goal), the same decoy still resolves.
//!
//! The fix is gated to input-only classes with no out-parameters
//! ({Decidable, DecidableEq, Inhabited, BEq}); out-param / arithmetic classes
//! (HAdd/HMod/…) never enter phase 1 for their out positions and are
//! structurally untouched.

use clean_elab::{ElabCtx, MetaState};
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, KernelClassInfo, KernelInstanceInfo,
    Level, Name,
};

/// Build an environment with:
///   DecoyType : Type                       (a concrete carrier, axiom)
///   Inhabited : Type → Type                (an input-only class, axiom)
///   decoyInh  : Inhabited DecoyType        (the decoy instance)
///
/// `Inhabited` is named verbatim so it lands on the resolver's input-only
/// postpone allowlist. It has ONE parameter and NO out-params — the exact
/// shape where an undetermined input must postpone rather than force-resolve.
fn env_with_decoy_inhabited() -> Environment {
    let mut env = Environment::new();

    let type_ = Expr::type_();

    // DecoyType : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("DecoyType"),
        level_params: vec![],
        type_: type_.clone(),
    })
    .expect("DecoyType should declare");

    // Inhabited : Type → Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Inhabited"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, type_.clone(), type_),
    })
    .expect("Inhabited should declare");

    // decoyInh : Inhabited DecoyType
    let inhabited_decoy = Expr::app(
        Expr::const_(Name::from_string("Inhabited"), Vec::<Level>::new()),
        Expr::const_(Name::from_string("DecoyType"), Vec::<Level>::new()),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("decoyInh"),
        level_params: vec![],
        type_: inhabited_decoy,
    })
    .expect("decoyInh should declare");

    env.register_class(KernelClassInfo {
        name: Name::from_string("Inhabited"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("decoyInh"),
        class_name: Name::from_string("Inhabited"),
        priority: 100,
        type_: None,
        value: None,
    });
    env
}

fn inhabited_of(arg: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Inhabited"), Vec::<Level>::new()),
        arg,
    )
}

/// Extract the metavariable id from a bare-metavar expression produced by
/// [`ElabCtx::fresh_meta`].
fn meta_id_of(e: &Expr) -> clean_elab::MetaId {
    match e.kind() {
        ExprKind::FVar(id) => {
            MetaState::from_fvar(*id).expect("fresh_meta must produce a meta-encoded FVar")
        }
        other => panic!("expected a bare metavar, got {other:?}"),
    }
}

/// CORE REGRESSION: `Inhabited ?a` with `?a` undetermined must POSTPONE
/// (return None) and leave `?a` unassigned — NOT grab the decoy and backfill
/// `?a := DecoyType`.
#[test]
fn test_undetermined_input_metavar_goal_is_postponed_not_grabbed() {
    let env = env_with_decoy_inhabited();
    let mut ctx = ElabCtx::new(&env);

    // A fresh, unassigned type metavariable `?a : Type` — the undetermined
    // input. Nothing in scope pins it.
    let meta = ctx.fresh_meta(Expr::type_());
    let meta_id = meta_id_of(&meta);
    let goal = inhabited_of(meta.clone());

    let result = ctx.resolve_instance(&goal);

    assert!(
        result.is_none(),
        "instance search over `Inhabited ?a` with `?a` undetermined must \
         POSTPONE (return None), not grab the decoy; got {result:?}"
    );
    assert!(
        !ctx.metas().is_assigned(meta_id),
        "the undetermined input `?a` must be left UNASSIGNED after a postpone \
         (pre-fix it was wrongly backfilled to DecoyType by the decoy candidate)"
    );
    // Doubly explicit: instantiating `?a` must still be the bare metavar.
    let instantiated = ctx.metas().instantiate(&meta);
    assert!(
        matches!(instantiated.kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id) == Some(meta_id)),
        "`?a` must instantiate to itself (unassigned), got {instantiated:?}"
    );
}

/// GUARD: the postpone must NOT over-fire. Once the input is DETERMINED
/// (`Inhabited DecoyType`, a concrete goal), the decoy still resolves — the
/// fix only rejects a candidate for a BARE unassigned input, never for a
/// concrete one.
#[test]
fn test_determined_input_still_resolves_the_decoy() {
    let env = env_with_decoy_inhabited();
    let mut ctx = ElabCtx::new(&env);

    let goal = inhabited_of(Expr::const_(
        Name::from_string("DecoyType"),
        Vec::<Level>::new(),
    ));
    let result = ctx.resolve_instance(&goal);

    let witness = result.expect("`Inhabited DecoyType` (determined input) must still resolve");
    let head = witness.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("decoyInh")),
        "the determined-input goal must resolve to the decoy instance, got {head:?}"
    );
}
