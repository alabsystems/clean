// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Motive construction and eliminator layout for **indexed** inductive families.
//!
//! An inductive family's arguments split into *parameters* (shared by every
//! constructor) and *indices* (which each constructor is free to constrain):
//!
//! ```text
//! inductive Vector (α : Type u) : Nat → Type u   -- 1 param, 1 index
//!   | nil  : Vector α 0
//!   | cons : α → Vector α n → Vector α (n + 1)
//! ```
//!
//! The eliminators the kernel derives for such a family take the indices as
//! real arguments, and their motive abstracts over them:
//!
//! ```text
//! T.casesOn : {params} → {motive : (i…) → T params i… → Sort u}
//!           → {i…} → (t : T params i…) → minors… → motive i… t
//! T.rec     : {params} → {motive : (i…) → T params i… → Sort u}
//!           → minors… → {i…} → (t : T params i…) → motive i… t
//! ```
//!
//! Note the two layouts differ: `casesOn` takes `indices, major` immediately
//! after the motive, `rec` takes them *after* the minor premises. Both are
//! honoured by the callers (`proof_manipulation::cases_core`,
//! `induction::assemble_induction_proof`); this module only supplies the motive
//! and the index arguments.
//!
//! Before this module existed, `cases`/`induction` built a **one-binder** motive
//! `fun (x : T params i…) => target` and applied the eliminator as
//! `T.casesOn params motive major minors…` — no indices anywhere. On a family
//! with `k > 0` indices that puts the major premise in the *first index* slot
//! and shifts every later argument left by `k`, so the assembled term was
//! garbage: the reported type came out as an unapplied `Pi`, and the still-open
//! minor-premise metavariable was printed through its FVar encoding
//! (`MetaState::to_fvar(MetaId(1))` = `FVarId(9223372036854775809)` = `2^63+1`)
//! in the slot where the major premise belonged. That number is **not** a
//! fabricated free variable — it is the ordinary meta-FVar tag
//! (`MetaState::META_FVAR_TAG | 1`) surfacing an unassigned case metavariable
//! that landed in the wrong argument position.
//!
//! # Which families this handles
//!
//! The motive is built by *generalizing* the major premise's actual index
//! arguments out of the goal. When every index is a local variable — `h : n ≤ m`,
//! `h : l₁ <+ l₂`, `h : Vector α n` — that generalization **is** index
//! unification, and the per-constructor goals come out exactly as Lean's do
//! (`Nat.le.refl` specialises the goal at `m := n`, `Nat.le.step` at
//! `m := m' + 1`). When an index is a compound term the generalization is still
//! sound but weaker than Lean's: Lean would additionally discharge the branches
//! whose constructor index cannot unify. A plain motive leaves those as extra
//! goals; named `cases` now carries compound-index equations through the
//! motive via `cases_index_constraints` and solves them before exposing the
//! branches. Induction and other callers still use the plain motive. Nothing is ever accepted without the kernel re-checking the
//! assembled term (`close_goal_assembled` → `verify_tactic_proof` → `add_decl`),
//! so the weaker case costs completeness, never soundness.

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, InductiveVal};

use super::core::{ProofState, TacticError};
use super::equality::replace_expr;

/// A motive for an inductive family, together with the major premise's actual
/// index arguments in eliminator order.
pub(crate) struct FamilyMotive {
    /// `fun (i₁ …) (x : T params i…) => target[indices ↦ i, major ↦ x]`.
    ///
    /// Exactly `index_args.len() + 1` leading lambda binders. For a
    /// non-indexed type this is the same single-binder motive the tactics
    /// built before indices were handled at all.
    pub(crate) motive: Expr,
    /// The major premise's index arguments, in declaration order. Empty for a
    /// non-indexed inductive, in which case every code path below is a no-op
    /// and the caller's behaviour is unchanged.
    pub(crate) index_args: Vec<Expr>,
}

/// Beta-apply `f` to `args`, reducing a leading `Lam` per argument.
///
/// Used to compute a minor premise's goal (`motive ctor_indices… (C fields…)`)
/// from the same motive that goes into the eliminator, so the branch goal and
/// the eliminator's own expectation cannot drift apart. Falls back to building
/// an `App` node if `f` runs out of binders, which keeps the result
/// type-correct (and therefore still kernel-checkable) rather than silently
/// dropping an argument.
pub(crate) fn beta_apply(f: &Expr, args: &[Expr]) -> Expr {
    let mut cur = f.clone();
    for arg in args {
        let next = match cur.kind() {
            ExprKind::Lam(_, _, body) => body.instantiate(arg),
            _ => Expr::app(cur.clone(), arg.clone()),
        };
        cur = next;
    }
    cur
}

/// The index arguments of an applied inductive type `T params… idx…`.
///
/// Returns `None` when `ty`'s head is not `ind_info.name` or when it is applied
/// to fewer arguments than the family's declared arity — the caller must then
/// fail closed rather than guess.
pub(crate) fn applied_index_args(ind_info: &InductiveVal, ty: &Expr) -> Option<Vec<Expr>> {
    let num_params = ind_info.num_params as usize;
    let num_indices = ind_info.num_indices as usize;
    match ty.get_app_fn().kind() {
        ExprKind::Const(name, _) if *name == ind_info.name => {}
        _ => return None,
    }
    let args: Vec<&Expr> = ty.get_app_args().into_iter().collect();
    if args.len() < num_params + num_indices {
        return None;
    }
    Some(
        args[num_params..num_params + num_indices]
            .iter()
            .map(|e| (*e).clone())
            .collect(),
    )
}

/// Build the eliminator motive for a major premise of type
/// `head params… idx…`.
///
/// * `ind_head` / `args` — the *whnf'd* major-premise type, split into its head
///   constant and argument list. The indices are read positionally from `args`,
///   never by matching free variables, so an index that happens to be equal to
///   a parameter (`h : a ≤ a`) still lands in the right binder.
/// * `hyp_ty` — the major premise's type as it appears in the goal, used
///   verbatim as the motive's last binder type on the non-indexed path so that
///   the pre-existing behaviour is preserved exactly.
/// * `major_fvar` — the free variable standing for the major premise inside
///   `body` (a real hypothesis fvar for `cases h`, a sentinel for
///   `cases <term>`). `None` means the goal does not mention the major premise
///   at all, in which case the motive is constant in its last binder.
/// * `body` — the goal target with the major premise already replaced by
///   `major_fvar`.
///
/// # Errors
/// [`TacticError::GoalMismatch`] when the family declares more parameters and
/// indices than the major premise's type supplies, which would make any
/// positional reading of the indices a guess.
pub(crate) fn build_family_motive(
    state: &mut ProofState,
    ind_head: &Expr,
    ind_info: &InductiveVal,
    args: &[Expr],
    hyp_ty: &Expr,
    major_fvar: Option<FVarId>,
    body: &Expr,
) -> Result<FamilyMotive, TacticError> {
    let num_params = ind_info.num_params as usize;
    let num_indices = ind_info.num_indices as usize;

    // Non-indexed family: reproduce the historical single-binder motive
    // verbatim. Every caller below then sees an empty `index_args` and behaves
    // exactly as it did before this module existed.
    if num_indices == 0 {
        return Ok(FamilyMotive {
            motive: Expr::lam(
                BinderInfo::Default,
                hyp_ty.clone(),
                major_fvar.map_or_else(|| body.clone(), |f| body.abstract_fvar(f)),
            ),
            index_args: Vec::new(),
        });
    }

    if args.len() < num_params + num_indices {
        return Err(TacticError::GoalMismatch(format!(
            "cases/induction on indexed family '{}': its type supplies {} argument(s) but the \
             family declares {num_params} parameter(s) and {num_indices} index(es)",
            ind_info.name,
            args.len()
        )));
    }

    let index_args: Vec<Expr> = args[num_params..num_params + num_indices].to_vec();

    // One sentinel free variable per index. These are abstracted straight back
    // out below and never survive into the assembled proof term, exactly like
    // `cases_core`'s `motive_fvar`. They are drawn from the global counter,
    // which is independent of the per-branch base the callers derive from the
    // goal itself, so branch field numbering is unaffected.
    let index_fvars: Vec<FVarId> = (0..num_indices).map(|_| state.fresh_fvar()).collect();

    // Index binder types, read off the family's own type after instantiating
    // the parameters with the major premise's actual arguments. Index `i`'s
    // domain may mention indices `< i`; instantiating with the sentinels keeps
    // those references as free variables until the enclosing binder abstracts
    // them.
    //
    // The family's stored type carries its OWN universe parameters, so it is
    // level-instantiated with the major premise's ACTUAL levels first — the same
    // `instantiate_level_params_direct` guard the constructor-field walk uses,
    // so an index whose type mentions a universe (`inductive F : (a : Type u) →
    // a → Prop`) does not leak `Type u` into a motive the kernel will check at
    // `Type 0`. Length-guarded: on a params/levels mismatch the stored type is
    // used as-is and the kernel re-check fails closed rather than mis-substitute.
    let head_levels: &[clean_kernel::Level] = match ind_head.kind() {
        ExprKind::Const(_, lvls) => lvls,
        _ => &[],
    };
    let mut fam_ty = if ind_info.level_params.len() == head_levels.len() {
        ind_info
            .type_
            .instantiate_level_params_direct(&ind_info.level_params, head_levels)
    } else {
        ind_info.type_.clone()
    };
    for arg in args.iter().take(num_params) {
        match fam_ty.kind() {
            ExprKind::Pi(_, _, codomain) => fam_ty = codomain.instantiate(arg),
            _ => {
                return Err(TacticError::GoalMismatch(format!(
                    "cases/induction on indexed family '{}': its declared type has fewer \
                     parameter binders than the family claims",
                    ind_info.name
                )))
            }
        }
    }
    let mut index_tys: Vec<Expr> = Vec::with_capacity(num_indices);
    for fvar in &index_fvars {
        match fam_ty.kind() {
            ExprKind::Pi(_, domain, codomain) => {
                index_tys.push(domain.as_ref().clone());
                fam_ty = codomain.instantiate(&Expr::fvar(*fvar));
            }
            _ => {
                return Err(TacticError::GoalMismatch(format!(
                    "cases/induction on indexed family '{}': its declared type has fewer index \
                     binders than the family claims",
                    ind_info.name
                )))
            }
        }
    }

    // The major premise's binder type, rebuilt POSITIONALLY as
    // `T params… sentinel…`. Substituting the index terms into `hyp_ty` instead
    // would be wrong whenever an index is syntactically equal to a parameter
    // (`h : a ≤ a`), because that would also generalise the parameter slot.
    let mut major_ty = ind_head.clone();
    for arg in args.iter().take(num_params) {
        major_ty = Expr::app(major_ty, arg.clone());
    }
    for fvar in &index_fvars {
        major_ty = Expr::app(major_ty, Expr::fvar(*fvar));
    }

    // Generalise the actual index terms out of the goal.
    let mut generalized = body.clone();
    for (idx_arg, fvar) in index_args.iter().zip(&index_fvars) {
        // `generalize` restricted to closed-at-the-top terms: index arguments
        // come from the major premise's *type*, which is already
        // instantiated, so no de Bruijn shifting is required — an occurrence
        // of the needle is the same expression at any depth.
        generalized = replace_expr(&generalized, idx_arg, &Expr::fvar(*fvar));
    }

    let mut motive = Expr::lam(
        BinderInfo::Default,
        major_ty,
        match major_fvar {
            Some(f) => generalized.abstract_fvar(f),
            None => generalized,
        },
    );
    for (ty, fvar) in index_tys.iter().zip(&index_fvars).rev() {
        // `abstract_fvar` on the whole lambda also rewrites occurrences of this
        // sentinel inside the binder types it already wrapped, which is what
        // makes a dependent index telescope come out right.
        motive = Expr::lam(BinderInfo::Default, ty.clone(), motive.abstract_fvar(*fvar));
    }

    Ok(FamilyMotive { motive, index_args })
}
