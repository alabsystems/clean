// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type **inference** / **checking** / **sort inference** over [`Term`] with an
//! explicit local typing context (design §5, §3.2 "infer/check/infer_sort").
//!
//! The local context is a `Vec<Term>` of de Bruijn-indexed binder types: the
//! innermost binder is last. `BVar(i)` looks up `ctx[len-1-i]` and **lifts** the
//! stored type by `i+1` so it is expressed under the current binder depth (the
//! stored type was valid one binder shallower per position).
//!
//! Typing rules implemented at M1:
//! * `Sort l            : Sort (succ l)`
//! * `Pi (x:A) B         : Sort (imax (sort A) (sort B))`
//! * `Lam (x:A). b       : Pi (x:A) (typeof b)`
//! * `App f a            : (typeof f as Pi).codomain[a]`   (after checking `a`'s type)
//! * `Let _:A := v; b    : (typeof b)[v]`
//! * `Const c            : declared type, level-instantiated`
//! * `Lit (Nat/Str)      : Nat / String`
//! * `Proj S i e         : field type from `e`'s inferred structure type`
//!
//! **`Elim` typing is deferred to M2**: recursor signatures are kernel-derived
//! there. M1 returns [`InferError::ElimUnsupported`] — a clear error, never a
//! fabricated type (design: "return a clear 'unsupported at M1' error, NOT a
//! fake type").
//!
//! Every function is `Result`-returning and budget-threaded; conversion is
//! delegated to [`crate::def_eq`].

use crate::budget::{Budget, BudgetError};
use crate::def_eq::is_def_eq_checked_types;
use crate::level::Level;
use crate::name::Name;
use crate::term::{Lit, Term, TermKind};
use crate::validate::Env;
use crate::whnf::whnf_in_context;

mod projection;
mod query;
pub(crate) use query::{clear_type_query_cache, infer_for_conversion, TypeQueryScope};

/// A type known well formed from completed full inference or sort checking.
/// Only this module can construct the witness; conversion cannot assume it.
pub(crate) struct CheckedType<'a>(&'a Term);
impl CheckedType<'_> {
    pub(crate) fn term(&self) -> &Term {
        self.0
    }
}

/// Errors from inference / checking.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum InferError {
    /// Budget exhausted during inference or a delegated conversion/reduction.
    /// Soundness callers collapse this to *reject* (never fail open).
    #[error("out of budget (deterministic, genesis-pinned)")]
    OutOfBudget,
    /// A `BVar` index escaped the local context (should be impossible for a
    /// validated, context-closed term; kept as a fail-closed assertion).
    #[error("unbound BVar({index}) in context of depth {depth}")]
    UnboundVar {
        /// The offending index.
        index: u32,
        /// The context depth.
        depth: usize,
    },
    /// A constant has no declared type in the env.
    #[error("unknown constant '{name}' (no declared type)")]
    UnknownConst {
        /// The constant.
        name: Name,
    },
    /// Expected a `Sort` (e.g. a binder's domain type did not infer to a sort).
    #[error("expected a Sort, got a non-sort type")]
    NotASort,
    /// Expected a `Pi` (applied a non-function).
    #[error("expected a function type in application head")]
    NotAFunction,
    /// Expected a structure type for a projection, or the field index/structure
    /// info was unavailable.
    #[error("projection '{struct_name}.{idx}' on a non-structure or unknown structure")]
    NotAStructure {
        /// The structure name on the projection.
        struct_name: Name,
        /// The field index.
        idx: u32,
    },
    /// `check`: the inferred type was not definitionally equal to the expected.
    #[error("type mismatch: inferred type is not def-eq to the expected type")]
    TypeMismatch,
    /// Eliminator (`Elim`) typing is deferred to M2 (recursor derivation). M1
    /// reports this rather than fabricating a type.
    #[error("Elim typing is unsupported at M1 (recursor derivation is M2)")]
    ElimUnsupported,
    /// A `Const`'s universe-level count did not match the declaration's
    /// `num_level_params`. `infer` re-validates this (defense in depth) because
    /// `ConstRef::mk_unchecked_levels` (recursor derivation) bypasses the
    /// construction-time arity check, and `instantiate_levels` would otherwise
    /// silently leave over-indexed `Param`s unsubstituted / drop extras.
    #[error("const '{name}' applied to {got} universe level(s), expected {expected}")]
    LevelArity {
        /// The offending constant.
        name: Name,
        /// The declaration's `num_level_params`.
        expected: u32,
        /// The supplied level count.
        got: u32,
    },
}

impl From<BudgetError> for InferError {
    fn from(_: BudgetError) -> Self {
        InferError::OutOfBudget
    }
}

/// A level past the depth bound is refused as the frame cap and the reduct
/// bound are: out of budget, so every soundness caller rejects (R166).
impl From<crate::level::LevelTooDeep> for InferError {
    fn from(_: crate::level::LevelTooDeep) -> Self {
        InferError::OutOfBudget
    }
}

/// A local typing context: de Bruijn binder types, innermost last.
type Ctx = Vec<Term>;

/// Infer the type of `e` in the empty context.
pub fn infer(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Term, InferError> {
    let _scope = crate::whnf::DecisionScope::enter();
    let _unknown = TypeQueryScope::unknown();
    let mut ctx = Ctx::new();
    infer_in(env, &mut ctx, e, budget)
}

/// Infer the *sort* of a type `e` (its type, reduced to a [`Level`]). Errors
/// with [`InferError::NotASort`] if `e`'s type is not a `Sort`.
pub fn infer_sort(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Level, InferError> {
    let _scope = crate::whnf::DecisionScope::enter();
    let _unknown = TypeQueryScope::unknown();
    let mut ctx = Ctx::new();
    infer_sort_in(env, &mut ctx, e, budget)
}

/// Infer the type of `e` under an explicit local context `ctx` (de Bruijn binder
/// types, innermost last) — the under-binder typing entry point added in M2. The
/// context lets `infer` type *open* terms (constructor field types, recursor
/// telescopes), which also lets `def_eq` run proof-irrelevance / structure-η
/// under binders (closing the M1 top-level-only gap).
pub fn infer_in_context(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, InferError> {
    let _scope = crate::whnf::DecisionScope::enter();
    let _unknown = TypeQueryScope::unknown();
    let mut ctx = ctx.to_vec();
    infer_in(env, &mut ctx, e, budget)
}

/// Infer the *sort* of a type `e` under an explicit local context (M2).
pub fn infer_sort_in_context(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Level, InferError> {
    let _scope = crate::whnf::DecisionScope::enter();
    let _unknown = TypeQueryScope::unknown();
    let mut ctx = ctx.to_vec();
    infer_sort_in(env, &mut ctx, e, budget)
}

/// Check that `e` has type `expected` (infer then convert). A *positive* check;
/// budget exhaustion collapses to error (the soundness caller treats it as
/// reject), never accept.
pub fn check(
    env: &dyn Env,
    e: &Term,
    expected: &Term,
    budget: &mut Budget,
) -> Result<(), InferError> {
    let _scope = crate::whnf::DecisionScope::enter();
    let _unknown = TypeQueryScope::unknown();
    let mut ctx = Ctx::new();
    let _ = infer_sort_in(env, &mut ctx, expected, budget)?;
    let inferred = infer_in(env, &mut ctx, e, budget)?;
    // Both witness constructors follow completed full checks. The actual body
    // has still been checked, including every application argument.
    if is_def_eq_checked_types(
        env,
        &ctx,
        CheckedType(&inferred),
        CheckedType(expected),
        budget,
    )? {
        Ok(())
    } else {
        Err(InferError::TypeMismatch)
    }
}

/// One fuel step per call, then the decision's earlier result for `e` in `ctx`
/// if there is one (the infer cache beside `whnf`'s, in `crate::whnf`), else
/// the inference, whose success is remembered for the rest of the decision.
fn infer_in(
    env: &dyn Env,
    ctx: &mut Ctx,
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, InferError> {
    budget.step()?;
    if let Some(ty) = crate::whnf::cached_infer(ctx, e) {
        return Ok(ty);
    }
    let ty = infer_uncached(env, ctx, e, budget)?;
    crate::whnf::remember_infer(ctx, e, &ty);
    Ok(ty)
}

fn infer_uncached(
    env: &dyn Env,
    ctx: &mut Ctx,
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, InferError> {
    match e.kind() {
        TermKind::BVar(i) => {
            let depth = ctx.len();
            let idx =
                usize::try_from(*i).map_err(|_| InferError::UnboundVar { index: *i, depth })?;
            // innermost binder is last; BVar(0) is the innermost.
            let pos = depth
                .checked_sub(1)
                .and_then(|d| d.checked_sub(idx))
                .ok_or(InferError::UnboundVar { index: *i, depth })?;
            let stored = ctx
                .get(pos)
                .ok_or(InferError::UnboundVar { index: *i, depth })?
                .clone();
            // The stored type was valid one binder shallower for each binder
            // between it and the use site: lift by i+1.
            Ok(stored.lift(i.saturating_add(1)))
        }
        TermKind::Sort(l) => Ok(Term::sort(Level::try_succ(l.clone())?)),
        TermKind::Const(cref) => {
            // A derived ι-rule names its recursor as `Const(I.rec)` in the IH
            // calls of its right-hand side; the untrusted boundary never
            // produces that form (`validate` refuses a recursor name in `Const`
            // position). It denotes the same recursor as `Elim(I)`, which `whnf`
            // and `def_eq` already treat it as, so it has the same type. Lean
            // types `I.rec` as a constant, by its recursor type. A reduct holding
            // an IH call is inferred since R147: `infer_proj`'s `is_prop` takes
            // the sort of a whnf'd structure type.
            let ty = env
                .const_type(cref.name())
                .or_else(|| {
                    env.recursor_inductive(cref.name())
                        .and_then(|ind| env.recursor_type(&ind))
                })
                .ok_or_else(|| InferError::UnknownConst {
                    name: cref.name().clone(),
                })?;
            // Re-validate level arity HERE (defense in depth, #17): recursor
            // derivation builds `ConstRef`s via `mk_unchecked_levels`, bypassing
            // the construction-time arity check, and `instantiate_levels`
            // silently leaves over-indexed `Param`s unsubstituted / ignores
            // extras — so a wrong-arity derived const must be caught here for the
            // generated recursor type's kernel-check to genuinely re-establish
            // the arity guarantee the design promises.
            let expected =
                env.num_level_params(cref.name())
                    .ok_or_else(|| InferError::UnknownConst {
                        name: cref.name().clone(),
                    })?;
            let got = u32::try_from(cref.levels().len()).unwrap_or(u32::MAX);
            if got != expected {
                return Err(InferError::LevelArity {
                    name: cref.name().clone(),
                    expected,
                    got,
                });
            }
            Ok(ty.instantiate_levels(cref.levels())?)
        }
        TermKind::Elim(eref) => {
            // Elim typing (M2): the recursor type stored for the inductive,
            // instantiated with the ElimRef's kernel-derived level vector. The
            // derived vector is `[motive_level, ind_levels...]` (large-elim) or
            // `[ind_levels...]` (small), matching the recursor's level-param
            // order exactly (design §4.2 / §5.2). No fabricated type: an unknown
            // recursor is `UnknownConst`, never a fake.
            let rec_ty =
                env.recursor_type(eref.inductive())
                    .ok_or_else(|| InferError::UnknownConst {
                        name: eref.inductive().clone(),
                    })?;
            Ok(rec_ty.instantiate_levels(eref.levels())?)
        }
        TermKind::App(f, a) => {
            let f_ty = infer_in(env, ctx, f, budget)?;
            let f_ty = whnf_in_context(env, ctx, &f_ty, budget)?;
            let TermKind::Pi(_, dom, codom) = f_ty.kind() else {
                return Err(InferError::NotAFunction);
            };
            // check the argument against the domain (positive check; exhaustion
            // -> error -> reject).
            let a_ty = infer_in(env, ctx, a, budget)?;
            if !is_def_eq_checked_types(env, ctx, CheckedType(&a_ty), CheckedType(dom), budget)? {
                return Err(InferError::TypeMismatch);
            }
            Ok(codom.instantiate(a))
        }
        TermKind::Lam(bi, dom, body) => {
            // domain must be a type (its sort must infer).
            let _ = infer_sort_in(env, ctx, dom, budget)?;
            ctx.push(dom.clone());
            let body_ty = infer_in(env, ctx, body, budget);
            ctx.pop();
            let body_ty = body_ty?;
            Ok(Term::pi(*bi, dom.clone(), body_ty))
        }
        TermKind::Pi(_, dom, codom) => {
            let dom_sort = infer_sort_in(env, ctx, dom, budget)?;
            ctx.push(dom.clone());
            let codom_sort = infer_sort_in(env, ctx, codom, budget);
            ctx.pop();
            let codom_sort = codom_sort?;
            Ok(Term::sort(Level::try_imax(dom_sort, codom_sort)?))
        }
        TermKind::Let(ty, val, body) => {
            // ty must be a type; val must check against ty.
            let _ = infer_sort_in(env, ctx, ty, budget)?;
            let val_ty = infer_in(env, ctx, val, budget)?;
            if !is_def_eq_checked_types(env, ctx, CheckedType(&val_ty), CheckedType(ty), budget)? {
                return Err(InferError::TypeMismatch);
            }
            // The body is typed with the let-bound value substituted (ζ first,
            // R162): a `let` is a local DEFINITION, so its body may need the
            // variable to be its value (Lean's kernel types the body with the
            // variable as a local definition). Typing the body over an opaque
            // variable refused such bodies (`funext`, `Nat.le_trans`, every
            // structural-recursion proof whose `let` binds the motive).
            infer_in(env, ctx, &body.instantiate(val), budget)
        }
        TermKind::Lit(Lit::Nat(_)) => Ok(Term::native_const(Name::from_dotted("Nat"))),
        TermKind::Lit(Lit::Str(_)) => Ok(Term::native_const(Name::from_dotted("String"))),
        TermKind::Proj(struct_name, idx, inner) => {
            projection::infer_proj(env, ctx, struct_name, *idx, inner, budget, false)
        }
    }
}

fn infer_sort_in(
    env: &dyn Env,
    ctx: &mut Ctx,
    e: &Term,
    budget: &mut Budget,
) -> Result<Level, InferError> {
    let ty = infer_in(env, ctx, e, budget)?;
    let ty = whnf_in_context(env, ctx, &ty, budget)?;
    match ty.kind() {
        TermKind::Sort(l) => Ok(l.clone()),
        _ => Err(InferError::NotASort),
    }
}

#[cfg(test)]
mod arity_check_tests {
    use super::*;
    use crate::term::ConstRef;
    use crate::MinimalEnv;

    /// #17: `infer` re-checks a `Const`'s universe-level arity, so a wrong-arity
    /// `ConstRef` (as `mk_unchecked_levels` can build during recursor derivation)
    /// is REJECTED rather than silently instantiated with missing/extra levels.
    #[test]
    fn test_infer_rejects_wrong_arity_const() {
        let foo = Name::from_dotted("Foo");
        // `Foo : Sort 0`, declared with 1 universe parameter.
        let env = MinimalEnv::new().with_const_typed(foo.clone(), 1, Term::sort(Level::zero()));

        // Too few levels (0) for a 1-param const -> LevelArity.
        let wrong = Term::const_ref(ConstRef::mk_unchecked_levels(foo.clone(), vec![]));
        let mut b = Budget::default_budget();
        assert!(
            matches!(
                infer(&env, &wrong, &mut b),
                Err(InferError::LevelArity {
                    expected: 1,
                    got: 0,
                    ..
                })
            ),
            "0 levels for a 1-param const must be rejected"
        );

        // Too many levels (2) -> LevelArity.
        let too_many = Term::const_ref(ConstRef::mk_unchecked_levels(
            foo.clone(),
            vec![Level::zero(), Level::zero()],
        ));
        let mut b2 = Budget::default_budget();
        assert!(
            matches!(
                infer(&env, &too_many, &mut b2),
                Err(InferError::LevelArity {
                    expected: 1,
                    got: 2,
                    ..
                })
            ),
            "2 levels for a 1-param const must be rejected"
        );

        // Correct arity (1) -> ok.
        let ok = Term::const_ref(ConstRef::mk_unchecked_levels(foo, vec![Level::zero()]));
        let mut b3 = Budget::default_budget();
        assert!(
            infer(&env, &ok, &mut b3).is_ok(),
            "correct arity must type-check"
        );
    }
}
