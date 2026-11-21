// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Induction hypotheses as calls where they occur (X4, R1.1 and R1.2).
//!
//! A structural recursor application is compiled to a synthesized local
//! recursive function `go` (`lower::lower_rec_apply`). Its arms used to bind
//! every induction hypothesis eagerly, `let ih := go(field)`, at the head of
//! the arm. With a function-typed motive (`Nat.rec (motive := fun _ => Nat →
//! Tm → …)`, how a structurally recursive definition with more than one
//! parameter elaborates) that made `go(field)` return a CLOSURE and the
//! recursive step a `clean_apply_n` of it: no step was a direct call, none was
//! in tail position, and a head loop of 10⁵ steps overflowed an 8 MB stack.
//!
//! # Uncurrying by syntactic arity
//!
//! `go` takes the motive's leading arguments itself: `go(minors.., scrut,
//! a₁ … aₖ)`. `k` is the smallest number of leading `fun` binders any arm's
//! minor has after its fields and IHs (looking through metadata only: no
//! `let`, beta or delta), capped by the length of the motive body's Pi
//! telescope after beta and zeta. That is the arity Lean compiles: the
//! pre-definition's syntactic telescope. No arm has fewer binders than `k`,
//! so nothing is eta-expanded and nothing is floated across a `fun`.
//!
//! # IH placeholders
//!
//! An arm pushes a placeholder for each IH; an occurrence becomes a call of
//! `go` THERE ([`ih_value`]):
//!
//! * applied to at least `k` arguments: `go(prefix, args[..k])`, the rest
//!   applied to its result as a closure;
//! * applied to fewer, or used as a value: the partial application
//!   `go(prefix, args)`;
//! * with `k = 0`: `go(prefix)`, as before but where it is used.
//!
//! `prefix` is the arm's `go` prefix: the minor parameters and the recursive
//! field. Each distinct application is bound at most once on a path (a scoped
//! memo, see `LcnfContext::take_pending`), so a pure IH used twice costs one
//! call at every optimisation level, unless its type is an action
//! ([`is_action_type`]): then every occurrence runs, as in Lean. A
//! placeholder that reaches a runtime value position of the lowered code is a
//! compile error ([`refuse_placeholder_leak`]), never a dangling reference.

use super::LcnfContext;
use crate::error::CompilerError;
use crate::lcnf::{Alt, Arg, Code, LetValue};
use clean_kernel::{tc::TypeChecker, Environment, Expr, ExprKind, FVarId, Name};

/// What an IH placeholder stands for.
#[derive(Clone, Debug)]
pub(crate) struct IhRef {
    /// The synthesized recursive function.
    go: FVarId,
    /// `go`'s leading arguments for this IH: minor parameters, then the
    /// recursive field (or `Nat`'s predecessor).
    prefix: Vec<FVarId>,
    /// `go`'s uncurried motive arguments.
    k: usize,
    /// The type of a full application (`_` when unknown).
    call_ty: Expr,
    /// A full application is an action: never shared.
    action: bool,
    /// For a lifted mutual block (`rec_select`): the member this IH
    /// projects and the pads after its `k` arguments.
    select: Option<(u32, usize)>,
}

/// An IH application bound on the current path: the placeholder and its
/// arguments (`None` for an erased one).
pub(crate) type MemoKey = (FVarId, Vec<Option<FVarId>>);

/// The shape of `go` beyond its scrutinee, computed once per recursor
/// application by [`go_telescope`].
pub(super) struct GoTelescope {
    /// `go`'s uncurried motive arguments.
    pub(super) k: usize,
    /// Their types (`Object` where a domain depends on an earlier binder).
    pub(super) arg_tys: Vec<Expr>,
    /// The type of a full application (`_` when it depends on a binder).
    pub(super) call_ty: Expr,
    /// Whether a full application is an action ([`is_action_type`]).
    pub(super) action: bool,
}

/// Register a placeholder for one IH of an arm of `go`.
pub(super) fn register_ih(
    ctx: &mut LcnfContext<'_>,
    go: FVarId,
    prefix: Vec<FVarId>,
    tele: &GoTelescope,
) -> FVarId {
    let ph = ctx.fresh_fvar();
    ctx.ih_refs.insert(
        ph,
        IhRef {
            go,
            prefix,
            k: tele.k,
            call_ty: tele.call_ty.clone(),
            action: tele.action,
            select: None,
        },
    );
    ph
}

/// Register the placeholder for member `leaf` of an IH of a selector `go`
/// (`rec_select`).
pub(super) fn register_selected_ih(
    ctx: &mut LcnfContext<'_>,
    go: FVarId,
    prefix: Vec<FVarId>,
    plan: &super::rec_select::SelectPlan,
    leaf: usize,
) -> FVarId {
    let tele = &plan.leaves[leaf];
    let ph = ctx.fresh_fvar();
    ctx.ih_refs.insert(
        ph,
        IhRef {
            go,
            prefix,
            k: tele.k,
            call_ty: tele.call_ty.clone(),
            action: tele.action,
            select: Some((leaf as u32, plan.width() - tele.k)),
        },
    );
    ph
}

/// Whether `fvar` is an IH placeholder.
pub(super) fn is_ih(ctx: &LcnfContext<'_>, fvar: FVarId) -> bool {
    ctx.ih_refs.contains_key(&fvar)
}

/// A variable holding the value of IH placeholder `ph` applied to `args`
/// (see the module documentation), bound in the current scope unless the same
/// application is already bound on this path and is not an action.
pub(super) fn ih_value(
    ctx: &mut LcnfContext<'_>,
    ph: FVarId,
    args: Vec<Arg>,
) -> Result<FVarId, CompilerError> {
    let Some(ih) = ctx.ih_refs.get(&ph).cloned() else {
        return Err(CompilerError::InvalidExpr(format!(
            "{ph:?} is not an induction-hypothesis placeholder"
        )));
    };
    let split = ih.k.min(args.len());
    let (now, later) = args.split_at(split);
    let full = now.len() == ih.k;
    let pads = match ih.select {
        Some((_, pads)) if !full && pads > 0 => {
            return Err(CompilerError::InvalidExpr(
                "a lifted mutual member is applied to fewer arguments than its arity".into(),
            ))
        }
        Some((_, pads)) => pads,
        None => 0,
    };
    // A partial application only allocates a closure: always shareable.
    let shareable = !full || !ih.action;
    let key = memo_key(ph, now).filter(|_| shareable);
    let bound = match key.as_ref().and_then(|key| ctx.ih_memo.get(key)) {
        Some(bound) => *bound,
        None => {
            let ty = if full {
                ih.call_ty.clone()
            } else {
                Expr::const_str("_")
            };
            let mut call_args: Vec<Arg> = Vec::new();
            if let Some((leaf, _)) = ih.select {
                let sel = ctx.add_let(
                    Name::anon(),
                    Expr::const_str("Nat"),
                    LetValue::nat(u64::from(leaf)),
                );
                call_args.push(Arg::FVar(sel));
            }
            call_args.extend(ih.prefix.iter().copied().map(Arg::FVar));
            call_args.extend(now.iter().cloned());
            call_args.extend(std::iter::repeat_n(Arg::Erased, pads));
            let bound = ctx.add_let(
                Name::anon(),
                ty,
                LetValue::FVar {
                    fvar: ih.go,
                    args: call_args,
                },
            );
            if let Some(key) = key {
                ctx.ih_memo.insert(key.clone(), bound);
                ctx.ih_memo_log.push(key);
            }
            bound
        }
    };
    if later.is_empty() {
        return Ok(bound);
    }
    Ok(ctx.add_let(
        Name::anon(),
        Expr::const_str("_"),
        LetValue::FVar {
            fvar: bound,
            args: later.to_vec(),
        },
    ))
}

fn memo_key(ph: FVarId, args: &[Arg]) -> Option<MemoKey> {
    let args = args
        .iter()
        .map(|arg| match arg {
            Arg::FVar(id) => Some(Some(*id)),
            Arg::Erased => Some(None),
            Arg::Type(_) | Arg::Index(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some((ph, args))
}

/// `e` without leading metadata wrappers.
fn strip_mdata(mut e: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner.as_ref();
    }
    e
}

/// The number of leading `fun` binders of `e`, looking through metadata only.
pub(super) fn syntactic_arity(e: &Expr) -> usize {
    let mut n = 0;
    let mut cur = strip_mdata(e);
    while let ExprKind::Lam(_, _, body) = cur.kind() {
        n += 1;
        cur = strip_mdata(body);
    }
    n
}

/// `e` with its first `n` leading `fun` binders removed (their variables left
/// loose), looking through metadata only.
pub(super) fn peel_lams(e: &Expr, n: usize) -> Option<Expr> {
    let mut cur = strip_mdata(e);
    for _ in 0..n {
        let ExprKind::Lam(_, _, body) = cur.kind() else {
            return None;
        };
        cur = strip_mdata(body);
    }
    Some(cur.clone())
}

/// Head beta and zeta reduction (no delta), through metadata.
pub(super) fn whnf_beta_zeta(e: &Expr) -> Expr {
    let mut cur = strip_mdata(e).clone();
    for _ in 0..256 {
        let next = match cur.kind() {
            ExprKind::Let(_, _, val, body, _) => body.instantiate(val),
            ExprKind::App(..) => {
                let (head, args) = super::lower::collect_app_args(&cur);
                if !matches!(strip_mdata(head).kind(), ExprKind::Lam(..)) {
                    return cur;
                }
                let mut reduced = strip_mdata(head).clone();
                for arg in args {
                    reduced = match reduced.kind() {
                        ExprKind::Lam(_, _, body) => body.instantiate(arg),
                        _ => Expr::app(reduced.clone(), arg.clone()),
                    };
                }
                reduced
            }
            _ => return cur,
        };
        cur = strip_mdata(&next).clone();
    }
    cur
}

/// `go`'s telescope for a recursor application whose motive is `motive`
/// (already closed over the enclosing locals), taking at most `want`
/// arguments: the motive body's Pi telescope after beta and zeta caps `k`.
pub(super) fn go_telescope(env: &Environment, motive: &Expr, want: usize) -> GoTelescope {
    let unknown = |k| GoTelescope {
        k,
        arg_tys: vec![Expr::const_str("Object"); k],
        call_ty: Expr::const_str("_"),
        action: false,
    };
    // The motive of a non-indexed family binds the major premise only.
    let ExprKind::Lam(_, _, body) = strip_mdata(motive).kind() else {
        return unknown(0);
    };
    telescope_of(env, body, want)
}

/// The telescope of a motive body (or one member's component of it) `ty`,
/// taking at most `want` arguments: its Pi telescope after beta and zeta.
pub(super) fn telescope_of(env: &Environment, ty: &Expr, want: usize) -> GoTelescope {
    let mut cur = whnf_beta_zeta(ty);
    let mut arg_tys = Vec::new();
    while arg_tys.len() < want {
        let ExprKind::Pi(_, dom, rest) = cur.kind() else {
            break;
        };
        arg_tys.push(if dom.has_loose_bvars() {
            Expr::const_str("Object")
        } else {
            dom.as_ref().clone()
        });
        cur = whnf_beta_zeta(rest);
    }
    let action = is_action_type(env, &cur);
    GoTelescope {
        k: arg_tys.len(),
        arg_tys,
        action,
        call_ty: if cur.has_loose_bvars() {
            Expr::const_str("_")
        } else {
            cur
        },
    }
}

/// The monads whose values the native door runs where they are evaluated
/// (the eager `IO` model): two evaluations are two runs.
const ACTION_HEADS: &[&str] = &["IO", "BaseIO", "EIO", "EStateM", "ST", "EST"];

/// Whether a value of type `ty` is an action: `IO α` and its relatives, or
/// `Unit → ` one (the eager-IO thunk), after reducible unfolding. A type
/// this cannot read (`_`) is not called an action: an IH of unknown type is
/// shared, as it always was.
pub(crate) fn is_action_type(env: &Environment, ty: &Expr) -> bool {
    if syntactic_action(ty) {
        return true;
    }
    if ty.has_loose_bvars() {
        return false;
    }
    let tc = TypeChecker::with_mode(env, env.mode());
    let reduced = tc.whnf_with_transparency(ty, clean_kernel::TransparencyMode::Reducible);
    syntactic_action(&reduced)
}

/// [`is_action_type`] without unfolding: the head names an action monad, or
/// the type is `Unit → ` (or `PUnit → `) one.
pub(crate) fn syntactic_action(ty: &Expr) -> bool {
    let ty = strip_mdata(ty);
    if let ExprKind::Pi(_, dom, body) = ty.kind() {
        let unit = matches!(
            strip_mdata(dom).get_app_fn().kind(),
            ExprKind::Const(name, _) if matches!(name.to_string().as_str(), "Unit" | "PUnit")
        );
        return unit && syntactic_action(body);
    }
    matches!(
        ty.get_app_fn().kind(),
        ExprKind::Const(name, _) if ACTION_HEADS.contains(&name.to_string().as_str())
    )
}

/// Refuse lowered code in which an IH placeholder reached a runtime value
/// position: it names no binding, so the code would be ill-scoped.
pub(super) fn refuse_placeholder_leak(
    ctx: &LcnfContext<'_>,
    code: &Code,
) -> Result<(), CompilerError> {
    let leak = |fvar: &FVarId| ctx.ih_refs.contains_key(fvar);
    let arg_leak = |arg: &Arg| matches!(arg, Arg::FVar(id) if leak(id));
    let mut stack = vec![code];
    while let Some(code) = stack.pop() {
        let found = match code {
            Code::Let(decl, body) => {
                stack.push(body);
                match &decl.value {
                    LetValue::FVar { fvar, args } => leak(fvar) || args.iter().any(arg_leak),
                    LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
                        args.iter().any(arg_leak)
                    }
                    LetValue::Reuse { slot, args, .. } => leak(slot) || args.iter().any(arg_leak),
                    LetValue::Proj { structure, .. } => leak(structure),
                    LetValue::Lit(_) | LetValue::Erased => false,
                }
            }
            Code::Fun(decl, body) | Code::JoinPoint(decl, body) => {
                stack.push(&decl.body);
                stack.push(body);
                false
            }
            Code::Cases(cases) => {
                for alt in &cases.alts {
                    stack.push(match alt {
                        Alt::Ctor { body, .. } | Alt::Default(body) => body,
                    });
                }
                leak(&cases.scrutinee)
            }
            Code::Jmp { args, .. } => args.iter().any(arg_leak),
            Code::Return(fvar) => leak(fvar),
            Code::Unreachable(_) => false,
        };
        if found {
            return Err(CompilerError::InvalidExpr(
                "an induction hypothesis reached a runtime value position without becoming \
                 a call of its recursive function"
                    .into(),
            ));
        }
    }
    Ok(())
}
