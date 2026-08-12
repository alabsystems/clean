// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lowering a validated corecursor into ExtractionIR (rank 7).
//!
//! This joins stage 2 (validated recognition) to stage 3 (the IR): it consumes
//! a [`RecognizedCorec`] — which by construction has already had its origin
//! re-checked and its canonical body replayed — and produces an
//! [`extraction_ir::Corec`].
//!
//! # Both lanes
//!
//! The generated plain-lane body is
//!
//! ```text
//! codef f (p …) : C  ⇒  λp…. C.corec S (λs. observe) (λs. step) init
//! ```
//!
//! so `observe` and `step` are exactly the two slot lambdas over a single state
//! slot.
//!
//! The INDEXED lane carries `[index, state]`, and its index advance is NOT in
//! the corecursor application — it lives in the carrier's `tgtF` descriptor,
//! `λ index shape pos. <target index>`, so lowering reads a second constant out
//! of the environment. `tgtF` is required to depend on the index ALONE: a
//! target computed from the shape or position would mean the next index depends
//! on which observation was taken, which the flat target cannot express, so the
//! resolver refuses those binders rather than inventing a reading.
//!
//! (An earlier revision of this comment said the indexed lane was "deliberately
//! not handled here", and stayed that way after `lower_indexed` landed twenty
//! lines below. An adversarial review flagged it: a reader trusting the doc
//! would conclude the tgtF path was unreachable and skip reviewing the only
//! code in this module that reads a second constant.)
//!
//! # Fail-closed translation
//!
//! [`expr_to_op`] refuses anything outside the tiny first-order fragment the
//! IR can express. There is no "best effort" case: an unrecognized operation
//! returns `None` and the whole lowering declines, because an IR term that
//! silently dropped an operation would produce a target that disagrees with the
//! source in exactly the way the observational claim is supposed to forbid.

use clean_kernel::{Environment, Expr, ExprKind, Name};

use super::{Corec, Op};
use crate::to_lcnf::codata_recognize::RecognizedCorec;
use clean_kernel::CodataLane;

/// Lower a validated corecursor into ExtractionIR.
///
/// Returns `None` — decline — for anything outside the supported fragment.
pub fn lower_recognized(env: &Environment, rec: &RecognizedCorec) -> Option<Corec> {
    if rec.lane == CodataLane::Indexed {
        return lower_indexed(env, rec);
    }

    // Plain-lane application: [S, <slot lambdas…>, init].
    // Recognition already established saturation, so the slots and the init
    // argument are present; what is checked here is that the SHAPE is the one
    // this lowering knows how to read.
    if rec.slot_count != 2 {
        // v1 handles a single observation and a single step (a stream).
        return None;
    }
    if rec.args.len() != 1 + rec.slot_count + 1 {
        return None;
    }
    let observe_lam = &rec.args[1];
    let step_lam = &rec.args[2];
    let init_arg = &rec.args[3];

    // Each slot lambda binds the state. One state slot in v1.
    let observe =
        under_one_binder(observe_lam).and_then(|body| expr_to_op(body, 1, rec.param_count))?;
    let step = under_one_binder(step_lam).and_then(|body| expr_to_op(body, 1, rec.param_count))?;

    // `init` is written in the codef's parameter scope, with no state in scope.
    let init = expr_to_op(init_arg, 0, rec.param_count)?;

    Some(Corec {
        init: vec![init],
        observe,
        step: vec![step],
    })
}

/// Lower the INDEXED lane.
///
/// The indexed application is `[S, <slots…>, index, init]`, and the state the
/// target carries is the pair `[index, state]` — because the index is part of
/// what an observer sees advancing, and the source's own `nth` walks it.
///
/// The index's advance is NOT in the application: it lives in the carrier's
/// `tgtF` descriptor, `λ index shape pos. <target index>`. That is why this
/// needed a second constant read, and why guessing was the wrong move.
///
/// `tgtF` is required to depend on the index ALONE. A target index computed
/// from the shape or position would mean the next index depends on which
/// observation was taken, which the flat `[index, state]` target cannot
/// express — so it declines rather than silently dropping the dependence.
fn lower_indexed(env: &Environment, rec: &RecognizedCorec) -> Option<Corec> {
    if rec.slot_count != 2 {
        return None;
    }
    // [S, observe, step, index, init]
    if rec.args.len() != 1 + rec.slot_count + 2 {
        return None;
    }
    let observe_lam = &rec.args[1];
    let step_lam = &rec.args[2];
    let index_arg = &rec.args[3];
    let init_arg = &rec.args[4];

    // Slot lambdas bind (index, state); state slots are [0]=index, [1]=state.
    let two = |i: usize| -> Option<Op> {
        match i {
            0 => Some(Op::State(1)), // innermost binder: the state
            1 => Some(Op::State(0)), // outer binder: the index
            _ => {
                let p = i - 2;
                (p < rec.param_count).then(|| Op::Param(rec.param_count - 1 - p))
            }
        }
    };
    let observe = expr_to_op_with(under_binders(observe_lam, 2)?, &two)?;
    let state_step = expr_to_op_with(under_binders(step_lam, 2)?, &two)?;

    // The index step, from `tgtF : λ index shape pos. <target>`.
    let tgt_name = Name::from_string(&format!("{}.tgtF", rec.carrier));
    let tgt_value = env.get_const(&tgt_name)?.value.clone()?;
    let tgt_body = under_binders(&tgt_value, 3)?;
    // Only the index (outermost of the three) is readable.
    let index_only = |i: usize| -> Option<Op> {
        match i {
            2 => Some(Op::State(0)),
            _ => None,
        }
    };
    let index_step = expr_to_op_with(tgt_body, &index_only)?;

    let idx_init = expr_to_op(index_arg, 0, rec.param_count)?;
    let st_init = expr_to_op(init_arg, 0, rec.param_count)?;

    Some(Corec {
        init: vec![idx_init, st_init],
        observe,
        step: vec![index_step, state_step],
    })
}

/// Peel exactly `n` lambdas, returning the body.
fn under_binders(e: &Expr, n: usize) -> Option<&Expr> {
    let mut cur = e;
    for _ in 0..n {
        let ExprKind::Lam(_, _, body) = cur.kind() else {
            return None;
        };
        cur = body.as_ref();
    }
    Some(cur)
}

/// Peel exactly one lambda, returning its body.
fn under_one_binder(e: &Expr) -> Option<&Expr> {
    match e.kind() {
        ExprKind::Lam(_, _, body) => Some(body.as_ref()),
        _ => None,
    }
}

/// Translate a kernel expression into an [`Op`], resolving de Bruijn indices
/// through `resolve`.
///
/// `resolve` returning `None` REFUSES that variable. That is how a translation
/// says "this term depends on something the target cannot see" — the indexed
/// index-step, for instance, may depend on the index and on nothing else, so it
/// resolves the index binder and refuses the shape and position binders rather
/// than inventing a reading for them.
///
/// The recognized fragment is deliberately tiny: exactly what the width-1 chain
/// uses. Widening it is a job for a second real chain, not for anticipation.
pub(crate) fn expr_to_op_with(e: &Expr, resolve: &dyn Fn(usize) -> Option<Op>) -> Option<Op> {
    match e.kind() {
        ExprKind::BVar(i) => resolve(*i as usize),
        ExprKind::Lit(lit) => nat_lit_value(lit).map(Op::Lit),
        ExprKind::App(_, _) => {
            let (head, args) = collect(e);
            let ExprKind::Const(name, _) = head.kind() else {
                return None;
            };
            match (name.to_string().as_str(), args.len()) {
                ("Nat.succ", 1) => Some(Op::Succ(Box::new(expr_to_op_with(args[0], resolve)?))),
                // `HAdd.hAdd α β γ inst a b`. The TYPE arguments must all be
                // `Nat`: matching on arity alone would lower `Float`, `Int` or
                // `Fin` addition to u64 wrapping addition, which is not a
                // faithful encoding of any of them -- a silently wrong program
                // rather than a decline. The instance prefix is then erased.
                ("HAdd.hAdd", 6) => {
                    if !args[..3].iter().all(|t| is_const(t, "Nat")) {
                        return None;
                    }
                    let a = expr_to_op_with(args[4], resolve)?;
                    let b = expr_to_op_with(args[5], resolve)?;
                    Some(Op::Add(Box::new(a), Box::new(b)))
                }
                ("Nat.add", 2) => {
                    let a = expr_to_op_with(args[0], resolve)?;
                    let b = expr_to_op_with(args[1], resolve)?;
                    Some(Op::Add(Box::new(a), Box::new(b)))
                }
                _ => None,
            }
        }
        ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => Some(Op::Lit(0)),
        _ => None,
    }
}

/// The standard resolution: `state_binders` innermost binders are state slots
/// (innermost last), anything beyond them is a parameter of the enclosing
/// definition (again innermost last).
pub(crate) fn scope_resolver(
    state_binders: usize,
    param_count: usize,
) -> impl Fn(usize) -> Option<Op> {
    move |i| {
        if i < state_binders {
            Some(Op::State(state_binders - 1 - i))
        } else {
            let p = i - state_binders;
            (p < param_count).then(|| Op::Param(param_count - 1 - p))
        }
    }
}

/// Translate under the standard scope resolution.
pub(crate) fn expr_to_op(e: &Expr, state_binders: usize, param_count: usize) -> Option<Op> {
    expr_to_op_with(e, &scope_resolver(state_binders, param_count))
}

/// Is `e` exactly the constant named `name`?
fn is_const(e: &Expr, name: &str) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

fn collect(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut cur = e;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

fn nat_lit_value(lit: &clean_kernel::expr::Literal) -> Option<u64> {
    match lit {
        clean_kernel::expr::Literal::Nat(n) => n.to_u64(),
        clean_kernel::expr::Literal::String(_) => None,
    }
}
