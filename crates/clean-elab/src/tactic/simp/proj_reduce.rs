// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proj-of-constructor iota for `simp` — Lean's `reduceProj?`.
//!
//! `simp [Class.field]` delta-unfolds the field accessor by substituting its
//! VALUE (`lemmas::resolve_unfold_defs` stores `name -> body`,
//! `expr::unfold_named_consts` folds it in). A class field's body is a
//! projection, so `Class.field inst x` becomes the kernel node
//! `Proj(Class, i, inst) x` — and before this module nothing in `tactic/simp/`
//! ever reduced that node. The only `Proj` arm in the traversal re-simplified
//! the structure argument and rebuilt the projection by congruence, so the
//! goal stuck even when the structure argument was already a LITERAL
//! constructor application.
//!
//! Measured at Mathlib (`Mathlib/Order/Basic.lean`, `compl_lt`/`compl_le`/
//! `compl_gt`/`compl_ge`): `simp [Compl.compl]` unfolded to
//! `Compl.0.(Pi.instCompl A …) (LT.lt …)` and stopped. The stuck term is
//! FUNCTION-valued, so there is not even a binder for simp to descend under
//! and `not_lt`/`not_not` could never fire.
//!
//! Lean's `simpProj` (`Lean/Meta/Tactic/Simp/Main.lean:299`) dispatches a
//! `.proj` node to `reduceProj?` (`Lean/Meta/WHNF.lean:580-583`), which whnf's
//! the structure argument and reads field `i` out of the constructor
//! application.
//!
//! # The transparency ceiling, and why it is not optional
//!
//! The structure argument is normalised at **reducible + instances**
//! transparency (`ProofState::whnf_instances`), which is Lean's
//! `withReducibleAndInstances` — the transparency `reduceProjFn?` uses on the
//! branch the user reached by writing `simp [Class.field]`
//! (`Simp/Main.lean:110`). It is enough to turn a registered instance constant
//! (`Pi.instCompl`) into its `Class.mk …` constructor and no more. A blanket
//! `whnf` would δ-unfold ordinary semireducible definitions, which is exactly
//! what destroys the heads lemma matching is keyed on — the measured hazard
//! recorded at `Unifier::with_env_reducible`.
//!
//! Lean's own comment (`Simp/Main.lean:100-108`) records that `simp [X.x]`
//! legitimately LEAVES `(instX a').1` stuck when the structure argument is not
//! a constructor application at that transparency. So does this: the
//! constant-head pre-check below refuses a projection on a goal LOCAL outright
//! — that is the `BEq.beq inst a b` shape the simp lemma registry indexes on,
//! and reducing it would erase the very head those lemmas match.
//!
//! # What this does NOT cover
//!
//! A class whose accessor was compiled to a RECURSOR rather than to a `Proj`
//! — which is how much of Clean's own hand-rolled prelude spells them
//! (`clean-kernel`'s `env/data_typeclasses.rs`) — unfolds to `S.rec … inst`,
//! not to a `Proj` node, and this module never sees it. Measured by the
//! diagnosis this module closes: under `import Init`, `simp [Inhabited.default]`
//! yields `Inhabited.rec Nat (fun x => Nat) (fun n => n) instInhabitedNat` and
//! sticks there even at a CONSTANT instance. Every IMPORTED Lean structure
//! carries the `lam*. Proj(..)` spelling (`clean-olean`'s
//! `convert::is_projection_fn_body` confirms it), which is why the Mathlib rows
//! this closes are all of that shape. The recursor form is a separate,
//! unmeasured increment and is deliberately NOT guessed at here: a recursor
//! step is where the `Nat.rec` tower classes live, so it needs its own
//! measurement rather than a reduction bolted onto this one.
//!
//! # Soundness
//!
//! The step is definitional (ι), so the caller records `proof: None` exactly
//! as the neighbouring delta/beta/eta rewrites do, and the assembled proof
//! term is kernel-rechecked regardless. It can only make MORE rewrites
//! reachable, never justify one.

use clean_kernel::{Expr, ExprKind};

use crate::tactic::core::{Goal, ProofState};

/// One `reduceProj?` step.
///
/// REQUIRES: `expr` is a subterm of `goal`'s target or of one of its
///   hypotheses.
/// ENSURES: On `Some(field)`, `field` is definitionally equal to `expr` — it
///   is the constructor argument the projection selects.
/// ENSURES: On `None`, `expr` is left exactly as it was: it is not a `Proj`
///   node, its structure argument is not constant-headed, that argument does
///   not weak-head-normalise to a constructor application at reducible +
///   instances transparency, or the field index is out of range.
pub(in crate::tactic) fn reduce_proj(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<Expr> {
    let ExprKind::Proj(_struct_name, idx, inner) = expr.kind() else {
        return None;
    };
    // Cheap refusal BEFORE any reduction: only a constant-headed structure
    // argument can become a constructor application at this transparency. A
    // projection on a goal local / local instance, on a metavariable, or on a
    // binder-opened temporary therefore costs nothing — no context build, no
    // WHNF — and stays untouched, which is the ceiling this module's module
    // doc argues for.
    if !matches!(inner.get_app_fn().kind(), ExprKind::Const(..)) {
        return None;
    }
    let structure = state.whnf_instances(goal, inner);
    let ExprKind::Const(ctor_name, _) = structure.get_app_fn().kind() else {
        return None;
    };
    // Lean's `projectCore?` does NOT check that the constructor's inductive
    // matches the projection's struct name (`type_checker.cpp:358-373`), and
    // neither does the kernel's own `reduce_proj_with_mode`: a structure
    // spelled through an abbreviation must still project. Only
    // constructor-hood and the field index are checked.
    let ctor = state.env().get_constructor(ctor_name)?;
    // Bound the index by the constructor's FIELD count, not merely by how many
    // arguments the spine happens to carry, so an OVER-applied constructor can
    // never hand back an argument that is not a field. (The kernel's own
    // `reduce_proj_with_mode` bounds only by the spine; this is the narrower
    // of the two and can only refuse where that one would reduce.)
    if *idx >= ctor.num_fields {
        return None;
    }
    let field_idx = (ctor.num_params as usize).checked_add(*idx as usize)?;
    // Bound to a named local rather than chained: `AppArgs` borrows
    // `structure`, and a temporary in TAIL position outlives the block's
    // locals, so the chained spelling does not borrow-check.
    let args = structure.get_app_args();
    args.get(field_idx).copied().cloned()
}

/// Simplify a registered field application once its receiver exposes a
/// constructor. Class projections on a named instance require an explicit
/// unfold request, handled by the ordinary named-unfold path.
pub(super) fn reduce_field_app(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<Expr> {
    // The simplifier treats an OfNat literal as atomic, including its instance.
    if super::expr::is_of_nat_nat_lit(expr) {
        return None;
    }
    let env = state.env();
    let (owner, index, param_count, binder) =
        crate::structure_cmd::named_field_accessor(env, expr)?;
    let args = expr.get_app_args();
    let receiver = *args.get(param_count)?;
    if binder == clean_kernel::BinderInfo::InstImplicit || env.is_class(owner) {
        let ExprKind::Const(head, _) = receiver.get_app_fn().kind() else {
            return None;
        };
        env.get_constructor(head)?;
    }
    let projection = Expr::proj(owner.clone(), index, receiver.clone());
    let value = reduce_proj(state, goal, &projection)?;
    Some(Expr::apps(
        value,
        args.iter().skip(param_count + 1).copied().cloned(),
    ))
}
