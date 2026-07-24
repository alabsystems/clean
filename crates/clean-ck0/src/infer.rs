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
use crate::def_eq::is_def_eq;
use crate::level::Level;
use crate::name::Name;
use crate::term::{Lit, Term, TermKind};
use crate::validate::Env;
use crate::whnf::whnf;

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

/// A local typing context: de Bruijn binder types, innermost last.
type Ctx = Vec<Term>;

/// Infer the type of `e` in the empty context.
pub fn infer(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Term, InferError> {
    let mut ctx = Ctx::new();
    infer_in(env, &mut ctx, e, budget)
}

/// Infer the *sort* of a type `e` (its type, reduced to a [`Level`]). Errors
/// with [`InferError::NotASort`] if `e`'s type is not a `Sort`.
pub fn infer_sort(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Level, InferError> {
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
    let mut ctx = Ctx::new();
    let inferred = infer_in(env, &mut ctx, e, budget)?;
    // Conversion exhaustion -> error -> reject (never accept).
    if is_def_eq(env, &inferred, expected, budget)? {
        Ok(())
    } else {
        Err(InferError::TypeMismatch)
    }
}

fn infer_in(
    env: &dyn Env,
    ctx: &mut Ctx,
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, InferError> {
    budget.step()?;
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
            let stored = ctx[pos].clone();
            // The stored type was valid one binder shallower for each binder
            // between it and the use site: lift by i+1.
            Ok(stored.lift(i.saturating_add(1)))
        }
        TermKind::Sort(l) => Ok(Term::sort(Level::succ(l.clone()))),
        TermKind::Const(cref) => {
            let ty = env
                .const_type(cref.name())
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
            Ok(ty.instantiate_levels(cref.levels()))
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
            Ok(rec_ty.instantiate_levels(eref.levels()))
        }
        TermKind::App(f, a) => {
            let f_ty = infer_in(env, ctx, f, budget)?;
            let f_ty = whnf(env, &f_ty, budget)?;
            let TermKind::Pi(_, dom, codom) = f_ty.kind() else {
                return Err(InferError::NotAFunction);
            };
            // check the argument against the domain (positive check; exhaustion
            // -> error -> reject).
            let a_ty = infer_in(env, ctx, a, budget)?;
            if !is_def_eq(env, &a_ty, dom, budget)? {
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
            Ok(Term::sort(Level::imax(dom_sort, codom_sort)))
        }
        TermKind::Let(ty, val, body) => {
            // ty must be a type; val must check against ty.
            let _ = infer_sort_in(env, ctx, ty, budget)?;
            let val_ty = infer_in(env, ctx, val, budget)?;
            if !is_def_eq(env, &val_ty, ty, budget)? {
                return Err(InferError::TypeMismatch);
            }
            // body is typed with the let-bound variable; its inferred type may
            // mention BVar(0), which we instantiate with `val` (ζ on the type).
            ctx.push(ty.clone());
            let body_ty = infer_in(env, ctx, body, budget);
            ctx.pop();
            let body_ty = body_ty?;
            Ok(body_ty.instantiate(val))
        }
        TermKind::Lit(Lit::Nat(_)) => Ok(Term::native_const(Name::from_dotted("Nat"))),
        TermKind::Lit(Lit::Str(_)) => Ok(Term::native_const(Name::from_dotted("String"))),
        TermKind::Proj(struct_name, idx, inner) => {
            infer_proj(env, ctx, struct_name, *idx, inner, budget)
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
    let ty = whnf(env, &ty, budget)?;
    match ty.kind() {
        TermKind::Sort(l) => Ok(l.clone()),
        _ => Err(InferError::NotASort),
    }
}

/// Type a projection. The field type is pulled from `inner`'s inferred
/// *structure* type — it does **not** require `inner` to be a constructor head
/// (design: "Proj typing pulls the field type from e's inferred structure type;
/// does NOT require a constructor head; Proj reduction on a constructor is
/// separate").
fn infer_proj(
    env: &dyn Env,
    ctx: &mut Ctx,
    struct_name: &Name,
    idx: u32,
    inner: &Term,
    budget: &mut Budget,
) -> Result<Term, InferError> {
    let inner_ty = infer_in(env, ctx, inner, budget)?;
    let inner_ty = whnf(env, &inner_ty, budget)?;
    let (head, ty_args) = inner_ty.unfold_apps();
    let TermKind::Const(ty_cref) = head.kind() else {
        return Err(InferError::NotAStructure {
            struct_name: struct_name.clone(),
            idx,
        });
    };
    let info = env
        .structure_info(ty_cref.name())
        .ok_or_else(|| InferError::NotAStructure {
            struct_name: struct_name.clone(),
            idx,
        })?;
    if idx >= info.num_fields {
        return Err(InferError::NotAStructure {
            struct_name: struct_name.clone(),
            idx,
        });
    }
    // The constructor's type, level-instantiated, is a telescope:
    //   (params...) -> (field_0 : F0) -> ... -> StructTy
    // Field `idx`'s type is the domain of the (num_params + idx)-th Pi, with the
    // preceding params instantiated by `ty_args` and the preceding fields by the
    // projections `inner.0 .. inner.(idx-1)`.
    let ctor_ty = env
        .const_type(&info.ctor)
        .ok_or_else(|| InferError::UnknownConst {
            name: info.ctor.clone(),
        })?
        .instantiate_levels(ty_cref.levels());
    let mut cur = whnf(env, &ctor_ty, budget)?;
    // Instantiate the parameters with the structure type's arguments.
    let num_params = usize::try_from(info.num_params).unwrap_or(usize::MAX);
    for p in ty_args.iter().take(num_params) {
        let TermKind::Pi(_, _, codom) = cur.kind() else {
            return Err(InferError::NotAStructure {
                struct_name: struct_name.clone(),
                idx,
            });
        };
        cur = whnf(env, &codom.instantiate(p), budget)?;
    }
    // Walk `idx` fields, instantiating each with the projection of `inner`.
    for field in 0..idx {
        let TermKind::Pi(_, _, codom) = cur.kind() else {
            return Err(InferError::NotAStructure {
                struct_name: struct_name.clone(),
                idx,
            });
        };
        let proj = Term::proj(struct_name.clone(), field, inner.clone());
        cur = whnf(env, &codom.instantiate(&proj), budget)?;
    }
    // The current Pi's domain is field `idx`'s type.
    match cur.kind() {
        TermKind::Pi(_, dom, _) => Ok(dom.clone()),
        _ => Err(InferError::NotAStructure {
            struct_name: struct_name.clone(),
            idx,
        }),
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
