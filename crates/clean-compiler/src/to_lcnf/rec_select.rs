// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One recursive function for every member of a lifted mutual block (X4,
//! R1.3).
//!
//! `mutual_lift` compiles a structural mutual block to ONE recursor
//! application whose motive is a right-nested `PProd` of the members' result
//! types; each member reads its component back by projection (`(rec n).2.1
//! a b`), and each minor is a `PProd.mk` tree of the members' arms, whose
//! recursive calls are projections of the IH (`ih.1 x`). Lowered as is, every
//! step builds the whole tuple of closures for the predecessor eagerly, and a
//! member's head loop is a chain of closure applications: c36 overflowed 8 MB
//! after 130,721 levels.
//!
//! When the shape allows it ([`plan`]), the synthesized `go` instead takes a
//! selector and the members' uncurried arguments:
//!
//! ```text
//! go(sel : Nat, scrut, s₁ … s_K)    -- K = the largest member arity kⱼ
//! ```
//!
//! Each arm dispatches on `sel` to member `sel`'s arm; an IH projection
//! `ih.(path to member j) a₁ … a_kⱼ` becomes the call `go(j, field, a₁ … a_kⱼ,
//! pads…)` (`rec_ih::ih_value`), and the entry `(rec n).(path p) e…` the call
//! `go(p, n, e…, pads…)`. Calls between members are self calls of `go`, so a
//! member's tail call is a loop jump (`tail_loop`).
//!
//! # When it fires
//!
//! Every rewrite is the projection of a constructor, so it is correct on any
//! shape where it fires; the guards keep it from rebuilding tuples:
//!
//! * the motive body is a `PProd` tuple of `n ≥ 2` leaf types;
//! * every arm is inlined and its body a `PProd.mk` tree of `n` leaves;
//! * every occurrence of an IH is a projection path that ends at a leaf
//!   (`Nat.brecOn`'s minor uses its IH whole, as `below`, and falls back);
//! * a slot some member does not take (a pad) holds an object, and no member
//!   takes or returns a scalar where the members disagree, so `go`'s boxed
//!   slots and result never hide a scalar;
//! * a member called with fewer than its `kⱼ` arguments has `kⱼ = K` (a
//!   partial application of `go` must not await a pad).
//!
//! Otherwise the recursor is lowered as before (`k = 0` for a `PProd`
//! motive). The selector is a `Nat` dispatched with `Nat.zero`/`Default`
//! alternatives: LCNF's `Cases` has no literal alternatives, and a small
//! `Nat` is an unboxed scalar at run time.

use super::lower::{lower_code, RecApplyParts, RecMinorStrategy};
use super::rec_ih::{self, peel_lams, syntactic_arity, telescope_of, whnf_beta_zeta, GoTelescope};
use super::LcnfContext;
use crate::error::CompilerError;
use crate::ir::IRType;
use crate::lcnf::{Alt, Arg, Cases, Code, LetDecl, LetValue};
use crate::to_ir::types::expr_to_ir_type;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};

/// The selector shape of one recursor application ([`plan`]).
pub(super) struct SelectPlan {
    /// Each member's telescope, in tuple order.
    pub(super) leaves: Vec<GoTelescope>,
    /// `go`'s argument slots: the members' common type, else `Object`.
    pub(super) slot_tys: Vec<Expr>,
    /// The member the entry projects.
    pub(super) entry: usize,
}

impl SelectPlan {
    pub(super) fn width(&self) -> usize {
        self.slot_tys.len()
    }
}

/// `go`'s selector parameter and argument slots, inside its arms.
pub(super) struct SelectShape<'a> {
    pub(super) plan: &'a SelectPlan,
    pub(super) sel: FVarId,
}

fn pprod_args(e: &Expr, name: &str, arity: usize) -> Option<Vec<Expr>> {
    let e = e.strip_mdata();
    let ExprKind::Const(head, _) = e.get_app_fn().kind() else {
        return None;
    };
    if head.to_string() != name {
        return None;
    }
    let args = e.get_app_args();
    (args.len() == arity).then(|| args.iter().map(|a| (*a).clone()).collect())
}

/// The right-nested `PProd` components of the motive body `ty`.
fn tuple_types(ty: &Expr) -> Vec<Expr> {
    let mut leaves = Vec::new();
    let mut cur = whnf_beta_zeta(ty);
    while let Some(args) = pprod_args(&cur, "PProd", 2) {
        leaves.push(args[0].clone());
        cur = whnf_beta_zeta(&args[1]);
    }
    leaves.push(cur);
    leaves
}

/// The `n` leaves of a right-nested `PProd.mk` tree.
fn tuple_values(e: &Expr, n: usize) -> Option<Vec<Expr>> {
    let mut leaves = Vec::with_capacity(n);
    let mut cur = e.strip_mdata().clone();
    while leaves.len() + 1 < n {
        let args = pprod_args(&cur, "PProd.mk", 4)?;
        leaves.push(args[2].clone());
        cur = args[3].strip_mdata().clone();
    }
    leaves.push(cur);
    Some(leaves)
}

/// The leaf a projection path selects, given its projection indices from the
/// innermost out: `.2` `j` times then `.1` is leaf `j`; `.2` `n - 1` times is
/// the last leaf.
fn leaf_of_path(inner_first: &[u32], n: usize) -> Option<usize> {
    let twos = inner_first.iter().take_while(|&&i| i == 1).count();
    match &inner_first[twos..] {
        [] if twos == n - 1 => Some(n - 1),
        [0] if twos < n - 1 => Some(twos),
        _ => None,
    }
}

/// `e` as `Proj^path(core)`, the path innermost first.
fn proj_path(e: &Expr) -> (Vec<u32>, &Expr) {
    let mut path = Vec::new();
    let mut cur = e.strip_mdata();
    while let ExprKind::Proj(name, idx, inner) = cur.kind() {
        if name.to_string() != "PProd" {
            break;
        }
        path.push(*idx);
        cur = inner.strip_mdata();
    }
    path.reverse();
    (path, cur)
}

/// Whether `ty` is represented by an object (or erased) at run time.
fn object_like(ty: &Expr) -> bool {
    ty.has_loose_bvars()
        || matches!(
            expr_to_ir_type(ty),
            Ok(IRType::Object | IRType::Erased) | Err(_)
        )
}

/// The selector plan for the entry `Proj^path(rec_app)` applied to `extras`
/// arguments (`motive` resolved over the enclosing locals), or `None` when a guard of the module documentation fails.
pub(super) fn plan(
    env: &Environment,
    parts: &RecApplyParts,
    motive: &Expr,
    entry_path: &[u32],
    extras: usize,
) -> Option<SelectPlan> {
    if parts.major.is_none() || !parts.extras.is_empty() {
        return None;
    }
    let ExprKind::Lam(_, _, motive_body) = motive.strip_mdata().kind() else {
        return None;
    };
    let leaf_tys = tuple_types(motive_body);
    let n = leaf_tys.len();
    if n < 2 {
        return None;
    }
    let entry = leaf_of_path(entry_path, n)?;
    let mut arm_leaves: Vec<(usize, Vec<Expr>)> = Vec::new();
    for arm in &parts.arms {
        let RecMinorStrategy::Inline { body } = &arm.strategy else {
            return None;
        };
        let ihs = arm.fields.iter().filter(|f| f.recursive).count();
        arm_leaves.push((ihs, tuple_values(body, n)?));
    }
    let leaves: Vec<GoTelescope> = (0..n)
        .map(|j| {
            let want = arm_leaves
                .iter()
                .map(|(_, vals)| syntactic_arity(&vals[j]))
                .min()
                .unwrap_or(0);
            telescope_of(env, &leaf_tys[j], want)
        })
        .collect();
    let width = leaves.iter().map(|t| t.k).max().unwrap_or(0);
    let mut slot_tys = Vec::with_capacity(width);
    for s in 0..width {
        let tys: Vec<&Expr> = leaves.iter().filter_map(|t| t.arg_tys.get(s)).collect();
        let padded = tys.len() < n;
        let agree = tys.iter().all(|ty| *ty == tys[0]);
        if (padded || !agree) && !tys.iter().all(|ty| object_like(ty)) {
            return None;
        }
        slot_tys.push(if agree && !tys[0].has_loose_bvars() {
            tys[0].clone()
        } else {
            Expr::const_str("Object")
        });
    }
    if leaves.iter().any(|t| !object_like(&t.call_ty)) {
        return None;
    }
    let short_ok = |leaf: usize, args: usize| args >= leaves[leaf].k || leaves[leaf].k == width;
    if !short_ok(entry, extras) {
        return None;
    }
    for (ihs, vals) in &arm_leaves {
        for val in vals {
            if !ih_uses_ok(val, *ihs, n, 0, &short_ok) {
                return None;
            }
        }
    }
    Some(SelectPlan {
        leaves,
        slot_tys,
        entry,
    })
}

/// The IH a de Bruijn index names at binder depth `depth`, for an arm whose
/// peeled body binds `ihs` IHs innermost (IH `i` is `BVar(ihs - 1 - i)`).
fn ih_of(idx: u32, depth: u32, ihs: usize) -> Option<usize> {
    let rel = idx.checked_sub(depth)? as usize;
    (rel < ihs).then(|| ihs - 1 - rel)
}

/// Every IH occurrence in `e` is a leaf projection path, applied to enough
/// arguments (`short_ok`).
fn ih_uses_ok(
    e: &Expr,
    ihs: usize,
    n: usize,
    depth: u32,
    short_ok: &dyn Fn(usize, usize) -> bool,
) -> bool {
    let (head, args) = super::lower::collect_app_args(e);
    let (path, core) = proj_path(head);
    if let ExprKind::BVar(idx) = core.kind() {
        if ih_of(*idx, depth, ihs).is_some() {
            let Some(leaf) = leaf_of_path(&path, n) else {
                return false;
            };
            return short_ok(leaf, args.len())
                && args.iter().all(|a| ih_uses_ok(a, ihs, n, depth, short_ok));
        }
    }
    let go = |e: &Expr, d: u32| ih_uses_ok(e, ihs, n, d, short_ok);
    match e.kind() {
        ExprKind::BVar(idx) => ih_of(*idx, depth, ihs).is_none(),
        ExprKind::App(f, a) => go(f, depth) && go(a, depth),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            go(ty, depth) && go(body, depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            go(ty, depth) && go(val, depth) && go(body, depth + 1)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => go(inner, depth),
        _ => true,
    }
}

/// `e` with each IH leaf projection replaced by its placeholder
/// (`phs[ih][leaf]`), or `None` if an occurrence is not one ([`ih_uses_ok`]
/// checked that it is).
fn rewrite_ih_paths(e: &Expr, ihs: usize, phs: &[Vec<FVarId>], depth: u32) -> Option<Expr> {
    let (path, core) = proj_path(e);
    if let ExprKind::BVar(idx) = core.kind() {
        if let Some(ih) = ih_of(*idx, depth, ihs) {
            let leaf = leaf_of_path(&path, phs[ih].len())?;
            return Some(Expr::fvar(phs[ih][leaf]));
        }
    }
    let go = |e: &Expr, d: u32| rewrite_ih_paths(e, ihs, phs, d);
    Some(match e.kind() {
        ExprKind::BVar(idx) if ih_of(*idx, depth, ihs).is_some() => return None,
        ExprKind::App(f, a) => Expr::app(go(f, depth)?, go(a, depth)?),
        ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, go(ty, depth)?, go(body, depth + 1)?),
        ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, go(ty, depth)?, go(body, depth + 1)?),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            go(ty, depth)?,
            go(val, depth)?,
            go(body, depth + 1)?,
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => Expr::proj(name.clone(), *idx, go(inner, depth)?),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), go(inner, depth)?),
        _ => e.clone(),
    })
}

/// Lower an inlined arm of a selector `go`: its peeled `body` (fields
/// already on the binder stack), with one placeholder per IH and member
/// (`prefixes[ih]` is that IH's `go` prefix), dispatched on the selector.
pub(super) fn lower_selected_arm(
    ctx: &mut LcnfContext<'_>,
    go: FVarId,
    select: &SelectShape<'_>,
    slots: &[FVarId],
    body: &Expr,
    prefixes: &[Vec<FVarId>],
) -> Result<Code, CompilerError> {
    let plan = select.plan;
    let n = plan.leaves.len();
    let phs: Vec<Vec<FVarId>> = prefixes
        .iter()
        .map(|prefix| {
            (0..n)
                .map(|leaf| rec_ih::register_selected_ih(ctx, go, prefix.clone(), plan, leaf))
                .collect()
        })
        .collect();
    let mismatch =
        || CompilerError::InvalidExpr("a lifted mutual arm lost its selector shape".into());
    let rewritten = rewrite_ih_paths(body, prefixes.len(), &phs, 0).ok_or_else(mismatch)?;
    let leaves = tuple_values(&rewritten, n).ok_or_else(mismatch)?;
    // The IH binders are never read: every occurrence became a placeholder.
    let poison: Vec<FVarId> = prefixes.iter().map(|_| ctx.fresh_fvar()).collect();
    ctx.bvar_stack.extend_from_slice(&poison);
    let mut codes = Vec::with_capacity(n);
    let mut failure = None;
    for (leaf, value) in leaves.iter().enumerate() {
        match lower_leaf(ctx, value, &slots[..plan.leaves[leaf].k]) {
            Ok(code) => codes.push(code),
            Err(err) => {
                failure = Some(err);
                break;
            }
        }
    }
    for _ in &poison {
        ctx.bvar_stack.pop();
    }
    if let Some(err) = failure {
        return Err(err);
    }
    Ok(dispatch(ctx, select.sel, codes))
}

/// One member's arm, in its own scope, with its `k` slots bound.
fn lower_leaf(
    ctx: &mut LcnfContext<'_>,
    value: &Expr,
    slots: &[FVarId],
) -> Result<Code, CompilerError> {
    let body = peel_lams(value, slots.len()).ok_or_else(|| {
        CompilerError::InvalidExpr("a lifted mutual member has fewer binders than its arity".into())
    })?;
    let outer = ctx.take_pending();
    ctx.bvar_stack.extend_from_slice(slots);
    let result = lower_code(ctx, &body);
    for _ in slots {
        ctx.bvar_stack.pop();
    }
    match result {
        Ok(code) => {
            ctx.restore_pending(outer);
            Ok(code)
        }
        Err(err) => {
            ctx.abandon_pending(outer);
            Err(err)
        }
    }
}

/// `case sel of 0 => codes[0] | _ => case sel - 1 of …`.
fn dispatch(ctx: &mut LcnfContext<'_>, sel: FVarId, mut codes: Vec<Code>) -> Code {
    if codes.len() <= 1 {
        return codes
            .pop()
            .unwrap_or(Code::Unreachable(Expr::const_str("_")));
    }
    let first = codes.remove(0);
    let one = ctx.fresh_fvar();
    let pred = ctx.fresh_fvar();
    let rest = dispatch(ctx, pred, codes);
    let nat = Expr::const_str("Nat");
    let rest = Code::Let(
        LetDecl::new(one, Name::anon(), nat.clone(), LetValue::nat(1)),
        Box::new(Code::Let(
            LetDecl::new(
                pred,
                Name::anon(),
                nat.clone(),
                LetValue::Const {
                    name: Name::from_string("Nat.sub"),
                    levels: Vec::new(),
                    args: vec![Arg::FVar(sel), Arg::FVar(one)],
                },
            ),
            Box::new(rest),
        )),
    );
    Code::Cases(Cases::new(
        Name::from_string("Nat"),
        Expr::const_str("_"),
        sel,
        vec![
            Alt::ctor(Name::from_string("Nat.zero"), Vec::new(), first),
            Alt::default(rest),
        ],
    ))
}
