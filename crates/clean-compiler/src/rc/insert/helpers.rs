// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helper functions for RC insertion: let-value processing, inc/dec wrappers.
//! Part of #963 - Compiler IR infrastructure.

use std::collections::HashSet;
use std::sync::LazyLock;

use super::{LiveVars, RCContext};
use crate::lcnf::{Arg, Code, LetDecl, LetValue};
use crate::rc::borrow::Ownership;
use crate::rc::pseudo_op;
use clean_kernel::{Expr, FVarId};

static EXPR_UNIT: LazyLock<Expr> = LazyLock::new(|| Expr::const_str("_"));

/// Process a let-value, inserting inc/dec as needed.
pub(super) fn process_let_value(
    decl: &LetDecl,
    rest: Code,
    was_live: bool,
    live: &mut LiveVars,
    ctx: &mut RCContext,
) -> Code {
    match &decl.value {
        // Constructor: the allocation STORES the args (ownership moves into
        // the object), so each consumed occurrence either transfers its last
        // use or is compensated with an inc (`add_inc_for_consumed`). The
        // args are then marked live for the code ABOVE this binding —
        // without the marks, an arg's own binding saw it dead and inserted
        // a death `dec` BEFORE the constructor consumed it (a use-after-free
        // ordering), while the unconditional ctor inc leaked the reference
        // the dec was supposed to retire.
        LetValue::Ctor { args, .. } => {
            let occurrences = fvar_occurrences(args);
            let rest = add_inc_for_consumed(&occurrences, &HashSet::new(), rest, live, ctx);
            let code = Code::Let(decl.clone(), Box::new(rest));
            for fvar in occurrences {
                live.mark_live(fvar);
            }
            code
        }

        // Projection: track derivation for borrowed propagation
        LetValue::Proj { structure, .. } => {
            ctx.derived_from.insert(decl.fvar_id, *structure);
            if live.is_borrowed(*structure) {
                live.mark_borrowed(decl.fvar_id);
            }
            live.mark_live(*structure);
            let mut result_rest = rest;
            if was_live && ctx.needs_rc(decl.fvar_id, live) {
                result_rest = wrap_inc(decl.fvar_id, result_rest, ctx);
            }
            Code::Let(decl.clone(), Box::new(result_rest))
        }

        // Constant function call: a compiled callee CONSUMES its owned args
        // (decs them, possibly to zero) during the call.
        //
        // The compensating incs go BEFORE the binding: an inc sequenced
        // after the call line touches freed memory (R1: heap-use-after-free
        // caught by the synthesized-recursion behavior differential — `go`'s
        // self-call consumes the minors the continuation still applies).
        // Placing the inc first pays for the callee's dec while the caller
        // still holds its own reference. (Ctor allocation stays on the
        // inc-after layout: it stores without ever dec'ing, and
        // `reset_reuse` pattern-matches that window.)
        //
        // Only OWNED callee positions consume; a var also passed in a
        // BORROWED position of the same call must stay owned across the
        // call, so it is exempted from the last-use transfer.
        LetValue::Const { name, args, .. } => {
            let callee_borrow = ctx.borrow_map.get(name);
            let position_owned = |idx: usize| {
                callee_borrow
                    .map(|b| idx < b.params.len() && b.params[idx] == Ownership::Owned)
                    .unwrap_or(true)
            };
            let mut occurrences: Vec<FVarId> = Vec::new();
            let mut keep_owned: HashSet<FVarId> = HashSet::new();
            for (idx, arg) in args.iter().enumerate() {
                if let Arg::FVar(fvar) = arg {
                    if position_owned(idx) {
                        occurrences.push(*fvar);
                    } else {
                        keep_owned.insert(*fvar);
                    }
                }
            }
            let code = Code::Let(decl.clone(), Box::new(rest));
            let code = add_inc_for_consumed(&occurrences, &keep_owned, code, live, ctx);
            for arg in args {
                if let Arg::FVar(fvar) = arg {
                    live.mark_live(*fvar);
                }
            }
            code
        }

        // FVar application (higher-order): the closure itself AND all args
        // are consumed by the dynamic apply, so they form ONE consuming
        // site (the closure is the first consumed occurrence) with the
        // compensating incs BEFORE the binding (same use-after-free
        // reasoning as `Const`).
        LetValue::FVar { fvar, args } => {
            let mut occurrences = vec![*fvar];
            occurrences.extend(fvar_occurrences(args));
            let code = Code::Let(decl.clone(), Box::new(rest));
            let code = add_inc_for_consumed(&occurrences, &HashSet::new(), code, live, ctx);
            for fvar in occurrences {
                live.mark_live(fvar);
            }
            code
        }

        // Literals and erased don't affect RC
        LetValue::Lit(_) | LetValue::Erased => Code::Let(decl.clone(), Box::new(rest)),

        // Reuse: slot is consumed (in-place mutation or free on the shared
        // path), args are transferred to the object — one consuming site
        // (slot first), compensating incs BEFORE the binding, like
        // `Const`/`FVar`.
        LetValue::Reuse { slot, args, .. } => {
            let mut occurrences = vec![*slot];
            occurrences.extend(fvar_occurrences(args));
            let code = Code::Let(decl.clone(), Box::new(rest));
            let code = add_inc_for_consumed(&occurrences, &HashSet::new(), code, live, ctx);
            for fvar in occurrences {
                live.mark_live(fvar);
            }
            code
        }
    }
}

/// The `FVar` operands of an argument list, in order.
fn fvar_occurrences(args: &[Arg]) -> Vec<FVarId> {
    args.iter()
        .filter_map(|arg| match arg {
            Arg::FVar(fvar) => Some(*fvar),
            _ => None,
        })
        .collect()
}

/// Compensating incs for the consumed operands of ONE consuming site (a
/// constructor store, an owned call arg, a dynamic apply's closure + args, a
/// reuse slot + args), applying the Perceus LAST-USE TRANSFER:
///
/// * an operand still LIVE after the site is inc'd — the consumer takes the
///   inc'd reference and the caller keeps its own;
/// * a NON-PARAM operand at its last use (dead in the continuation)
///   TRANSFERS its ownership to the consumer: no inc here, and no death
///   `dec` anywhere (its binding saw it live). Exactly ONE occurrence per
///   variable may transfer — further occurrences in the same site are
///   duplicates the consumer consumes separately, so they are inc'd;
/// * a PARAM is always inc'd: params take their death `dec` on every return
///   path ([`super::insert_rc_return`]), which balances against the
///   caller's reference, not against consuming uses;
/// * operands in `keep_owned` (same-site borrowed-position duplicates) are
///   always inc'd — the borrowed position reads the object DURING the call,
///   so ownership must survive the consumer's dec.
///
/// Everything not [`RCContext::needs_rc`] (scalars, borrowed values) is
/// untouched, as before.
fn add_inc_for_consumed(
    occurrences: &[FVarId],
    keep_owned: &HashSet<FVarId>,
    mut rest: Code,
    live: &LiveVars,
    ctx: &mut RCContext,
) -> Code {
    let mut transferred: HashSet<FVarId> = HashSet::new();
    for fvar in occurrences {
        if !ctx.needs_rc(*fvar, live) {
            continue;
        }
        let transferable = !live.is_live(*fvar)
            && !ctx.is_param(*fvar)
            && !keep_owned.contains(fvar)
            && transferred.insert(*fvar);
        if transferable {
            continue;
        }
        rest = wrap_inc(*fvar, rest, ctx);
    }
    rest
}

/// Wrap code with an inc operation.
pub(super) fn wrap_inc(fvar: FVarId, rest: Code, ctx: &mut RCContext) -> Code {
    Code::Let(
        LetDecl::new(
            ctx.fresh_fvar(),
            pseudo_op::NAME_INC.clone(),
            EXPR_UNIT.clone(),
            LetValue::Const {
                name: pseudo_op::NAME_INC.clone(),
                levels: vec![],
                args: vec![Arg::FVar(fvar)],
            },
        ),
        Box::new(rest),
    )
}

/// Wrap code with a dec operation.
pub(super) fn wrap_dec(fvar: FVarId, rest: Code, ctx: &mut RCContext) -> Code {
    Code::Let(
        LetDecl::new(
            ctx.fresh_fvar(),
            pseudo_op::NAME_DEC.clone(),
            EXPR_UNIT.clone(),
            LetValue::Const {
                name: pseudo_op::NAME_DEC.clone(),
                levels: vec![],
                args: vec![Arg::FVar(fvar)],
            },
        ),
        Box::new(rest),
    )
}
