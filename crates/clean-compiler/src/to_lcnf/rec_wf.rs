// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Well-founded recursion with a syntactic step: the induction hypothesis as
//! a direct call (X4, R1.4).
//!
//! `lower::lower_wf_rec_apply` compiles `WellFounded.fix{,F} F x` and
//! `Acc.rec minor x t` to a synthesized `go` that closure-applies the step
//! `F` to the value and the partial application `go F`: every recursive step
//! is a `clean_apply_n` of a closure, never a direct call, and never in tail
//! position. When the step is a syntactic `fun x ih => body` (`fun x h ih =>`
//! for `Acc.rec`), this module inlines `body` into `go` instead, with `ih` an
//! IH placeholder (`rec_ih`): `ih y hy a₁ … aₖ` becomes the call
//! `go(y, hy, a₁ … aₖ)` where it occurs, `hy` erased, and `k` follows the
//! syntactic-arity rule of structural recursion (the step's binders past
//! `x`, `h` and `ih`, capped by the Pi telescope of the IH's result type,
//! read from the step's own `ih` binder). A step that is not a syntactic
//! lambda, or that uses `ih` unapplied, keeps the closure lowering.
//!
//! ```text
//! fun go (v) (hr) (a₁ … aₖ) :=   -- hr: the erased `r v _` slot
//!   body[x := v, ih := placeholder]
//! in go index ⟨erased⟩ e₁ … eₖ
//! ```
//!
//! `go` never inspects the erased accessibility proof: the decreasing value
//! is the recursor INDEX, as on the closure path.

use super::lower::{expr_to_arg, infer_type_or_placeholder, lower_code, WfRecParts};
use super::rec_ih::{self, peel_lams, syntactic_arity, telescope_of, whnf_beta_zeta, GoTelescope};
use super::LcnfContext;
use crate::error::CompilerError;
use crate::lcnf::{Arg, FunDecl, LetValue, Param};
use clean_kernel::{Expr, ExprKind, FVarId, Name};

/// Lower `parts` with its step inlined, or `None` when the step is not a
/// syntactic lambda binding the value, (`Acc.rec`'s erased `h`,) and the IH.
pub(super) fn lower_wf_rec_inline(
    ctx: &mut LcnfContext<'_>,
    expr: &Expr,
    parts: &WfRecParts,
) -> Result<Option<(LetValue, Expr)>, CompilerError> {
    let pre = if parts.has_erased_hyp { 3 } else { 2 };
    let arity = syntactic_arity(&parts.step);
    if arity < pre {
        return Ok(None);
    }
    let want = arity - pre;
    let tele = match ih_result_type(&parts.step, pre) {
        Some(ty) => telescope_of(ctx.env, &ty, want),
        None => GoTelescope {
            k: 0,
            arg_tys: Vec::new(),
            call_ty: Expr::const_str("_"),
            action: false,
        },
    };

    let body = peel_lams(&parts.step, pre + tele.k)
        .ok_or_else(|| CompilerError::InvalidExpr("well-founded step lost its binders".into()))?;
    // `go` has no leading arguments of its own, so an IH used unapplied would
    // be `go` itself as a value; such a step keeps the closure lowering.
    if !ih_always_applied(&body, tele.k as u32, 0) {
        return Ok(None);
    }
    // Call-site value (outer scope): the starting value.
    let index = match expr_to_arg(ctx, &parts.index)? {
        Arg::FVar(id) => id,
        other => {
            return Err(CompilerError::InvalidExpr(format!(
                "well-founded index did not lower to a variable: {other:?}"
            )))
        }
    };
    let go = ctx.fresh_fvar();
    let obj = || Expr::const_str("Object");
    // The value parameter takes the step's binder type where it is closed, so
    // a scalar value stays unboxed inside `go`; the closure path boxed it.
    let value_ty = match parts.step.strip_mdata().kind() {
        ExprKind::Lam(_, ty, _) if !ty.has_loose_bvars() => ty.as_ref().clone(),
        _ => obj(),
    };
    let value = Param::new(ctx.fresh_fvar(), Name::anon(), value_ty.clone());
    ctx.local_types.insert(value.fvar_id, value_ty);
    let proof = Param::new(ctx.fresh_fvar(), Name::anon(), obj());
    let arg_params: Vec<Param> = tele
        .arg_tys
        .iter()
        .map(|ty| {
            let fvar = ctx.fresh_fvar();
            ctx.local_types.insert(fvar, ty.clone());
            Param::new(fvar, Name::anon(), ty.clone())
        })
        .collect();
    let arg_fvars: Vec<FVarId> = arg_params.iter().map(|p| p.fvar_id).collect();

    // `ih y hy a₁ … aₖ` is `go(y, hy, a₁ … aₖ)`: the placeholder's `go`
    // arguments are the value, the proof slot and the `k` motive arguments.
    let ih_tele = GoTelescope {
        k: 2 + tele.k,
        arg_tys: Vec::new(),
        call_ty: tele.call_ty.clone(),
        action: tele.action,
    };
    let outer = ctx.take_pending();
    let mut pushed = 0usize;
    ctx.bvar_stack.push(value.fvar_id);
    pushed += 1;
    if parts.has_erased_hyp {
        // `Acc.rec`'s `h : ∀ y, r y x → Acc r y` is a proof: erased.
        let dummy = ctx.add_let(Name::anon(), Expr::const_str("_"), LetValue::Erased);
        ctx.bvar_stack.push(dummy);
        pushed += 1;
    }
    let ih = rec_ih::register_ih(ctx, go, Vec::new(), &ih_tele);
    ctx.bvar_stack.push(ih);
    pushed += 1;
    ctx.bvar_stack.extend_from_slice(&arg_fvars);
    pushed += arg_fvars.len();
    let lowered = lower_code(ctx, &body);
    for _ in 0..pushed {
        ctx.bvar_stack.pop();
    }
    let code = match lowered {
        Ok(code) => {
            let code = ctx.wrap_lets(code);
            ctx.restore_pending(outer);
            code
        }
        Err(err) => {
            ctx.abandon_pending(outer);
            return Err(err);
        }
    };
    rec_ih::refuse_placeholder_leak(ctx, &code)?;

    let go_result_ty = if tele.k > 0 {
        tele.call_ty.clone()
    } else {
        infer_type_or_placeholder(ctx.env, &parts.rec_app)
    };
    let mut params = vec![value, proof];
    params.extend(arg_params);
    ctx.add_fun(FunDecl::new(
        go,
        Name::from_string("_wf_rec"),
        params,
        go_result_ty.clone(),
        code,
    ));

    // Entry: go index ⟨erased⟩ e₁ … eₖ, the rest closure-applied.
    let mut extras = parts
        .extras
        .iter()
        .map(|extra| expr_to_arg(ctx, extra))
        .collect::<Result<Vec<_>, _>>()?;
    let later = extras.split_off(tele.k.min(extras.len()));
    let full = extras.len() == tele.k;
    let mut call_args = vec![Arg::FVar(index), Arg::Erased];
    call_args.extend(extras);
    let call = LetValue::FVar {
        fvar: go,
        args: call_args,
    };
    if later.is_empty() {
        let ty = if full {
            go_result_ty
        } else {
            infer_type_or_placeholder(ctx.env, expr)
        };
        return Ok(Some((call, ty)));
    }
    let bound = ctx.add_let(Name::anon(), go_result_ty, call);
    Ok(Some((
        LetValue::FVar {
            fvar: bound,
            args: later,
        },
        infer_type_or_placeholder(ctx.env, expr),
    )))
}

/// Whether every occurrence of the IH, `BVar(ih + depth)` under `depth`
/// further binders, is the head of an application to at least one argument.
fn ih_always_applied(e: &Expr, ih: u32, depth: u32) -> bool {
    let is_ih = |e: &Expr| matches!(e.strip_mdata().kind(), ExprKind::BVar(i) if *i == ih + depth);
    if let ExprKind::App(..) = e.kind() {
        let (head, args) = super::lower::collect_app_args(e);
        if is_ih(head) {
            return args.iter().all(|a| ih_always_applied(a, ih, depth));
        }
    }
    match e.kind() {
        ExprKind::BVar(i) => *i != ih + depth,
        ExprKind::App(f, a) => ih_always_applied(f, ih, depth) && ih_always_applied(a, ih, depth),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            ih_always_applied(ty, ih, depth) && ih_always_applied(body, ih, depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            ih_always_applied(ty, ih, depth)
                && ih_always_applied(val, ih, depth)
                && ih_always_applied(body, ih, depth + 1)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            ih_always_applied(inner, ih, depth)
        }
        _ => true,
    }
}

/// The type of an IH application to its value and proof, read from the
/// step's own IH binder `ih : (y : α) → r y x → C y` (for `Acc.rec`,
/// `→ motive y (h y _)`): the motive applied to `y`, beta reduced. It may
/// mention the step's binders; `telescope_of` boxes what it cannot type.
fn ih_result_type(step: &Expr, pre: usize) -> Option<Expr> {
    let mut cur = step.strip_mdata();
    for _ in 1..pre {
        let ExprKind::Lam(_, _, body) = cur.kind() else {
            return None;
        };
        cur = body.strip_mdata();
    }
    let ExprKind::Lam(_, ih_ty, _) = cur.kind() else {
        return None;
    };
    let mut ty = whnf_beta_zeta(ih_ty);
    for _ in 0..2 {
        let ExprKind::Pi(_, _, rest) = ty.kind() else {
            return None;
        };
        ty = whnf_beta_zeta(rest);
    }
    Some(ty)
}
