// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's constructor injectivity simp lemmas (`C.injEq`, generated for every
//! constructor with fields and in the default simp set): an equation between
//! two applications of the SAME constructor simplifies to the conjunction of
//! its fields' equations,
//!
//! ```text
//!   (C ps a₁ … aₙ = C ps b₁ … bₙ) = (a₁ = b₁ ∧ … ∧ aₙ = bₙ)
//! ```
//!
//! Clean had only the distinct-constructor half (`super::ctor_eq`), so `simp
//! at h` made no progress on `h : some (0, a) = some (0, b)`, where pinned
//! Lean 4.8.0 leaves `h : a = b` (gap G70, ledger (140); trust-ir
//! `Proofs/PredLatticeProps.lean` `constantKey_inj`, whose `simp [constantKey]
//! at hc hd hcd ⊢` relies on `Option.some.injEq`, `Prod.mk.injEq` and
//! `Constant.int.injEq`).
//!
//! The step runs under a full `simp` only: `injEq` lemmas are simp-set
//! members, so `simp only [l]` does not use them unless named. Scope:
//! constructors whose fields are non-dependent and not propositions (a
//! dependent field needs `HEq`, a proof field is dropped by Lean's lemma);
//! anything else is left alone.
//!
//! SOUNDNESS: the proof is `propext` over an `Iff` whose forward direction is
//! the type's `noConfusion` (`tactic/noconfusion_app.rs`) and whose backward
//! direction is a `congrArg`/`congr` chain; simp's result is re-checked by the
//! kernel at `close_goal`.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::types::SimpResult;
use crate::tactic::core::{Goal, ProofState};

fn c(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

/// One injectivity rewrite: `C ps as = C ps bs` and its fields' equations.
struct Inj {
    /// The two sides, constructor applications.
    lhs: Expr,
    rhs: Expr,
    /// The constructor's parameter count.
    np: usize,
    /// Each field's type and its sort's level.
    fields: Vec<(Expr, Level)>,
    /// The constructor application's type.
    result_ty: Expr,
    /// `aᵢ = bᵢ`, per field.
    eqs: Vec<Expr>,
    /// Their right-nested conjunction.
    conj: Expr,
}

/// `expr = (a₁ = b₁ ∧ … ∧ aₙ = bₙ)` when `expr` equates two applications of
/// one constructor with fields, else `None`.
pub(super) fn simp_ctor_inj(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<SimpResult> {
    let ExprKind::Const(head, _) = expr.get_app_fn().kind() else {
        return None;
    };
    let args = expr.get_app_args();
    if *head != Name::from_string("Eq") || args.len() != 3 {
        return None;
    }
    let lhs = constructor_app(state, goal, args[1])?;
    let rhs = constructor_app(state, goal, args[2])?;
    let (ExprKind::Const(ctor_name, ctor_levels), ExprKind::Const(rhs_ctor, _)) =
        (lhs.get_app_fn().kind(), rhs.get_app_fn().kind())
    else {
        return None;
    };
    if ctor_name != rhs_ctor {
        return None;
    }
    let ctor = state.env().get_constructor(ctor_name)?.clone();
    let (np, nf) = (ctor.num_params as usize, ctor.num_fields as usize);
    let (largs, rargs) = (lhs.get_app_args(), rhs.get_app_args());
    if nf == 0 || largs.len() != np + nf || rargs.len() != np + nf {
        return None;
    }
    if ctor.level_params.len() != ctor_levels.len() {
        return None;
    }
    // The field types, at the left side's parameters; every one closed (no
    // field depends on an earlier one) and not a proposition.
    let mut ty = ctor
        .type_
        .instantiate_level_params_direct(&ctor.level_params, ctor_levels);
    for param in largs.iter().take(np) {
        let ExprKind::Pi(_, _, body) = ty.kind() else {
            return None;
        };
        ty = body.instantiate(param);
    }
    let mut fields: Vec<(Expr, Level)> = Vec::with_capacity(nf);
    for _ in 0..nf {
        let ExprKind::Pi(_, domain, body) = ty.kind() else {
            return None;
        };
        // Non-dependent: no later field type (nor the result) names it.
        if domain.has_loose_bvars() || body.has_loose_bvars() {
            return None;
        }
        let level = sort_level(state, goal, domain)?;
        if level == Level::zero() {
            return None;
        }
        fields.push((domain.as_ref().clone(), level));
        ty = body.as_ref().clone();
    }
    if ty.has_loose_bvars() {
        return None;
    }
    let eqs: Vec<Expr> = fields
        .iter()
        .zip(largs.iter().skip(np).zip(rargs.iter().skip(np)))
        .map(|((fty, level), (a, b))| {
            Expr::apps(
                c("Eq", vec![level.clone()]),
                [fty.clone(), (*a).clone(), (*b).clone()],
            )
        })
        .collect();
    let conj = conjunction(&eqs);
    let inj = Inj {
        lhs: lhs.clone(),
        rhs: rhs.clone(),
        np,
        fields,
        result_ty: ty,
        eqs,
        conj,
    };
    let forward = forward_direction(state, goal, expr, &inj)?;
    let backward = backward_direction(state, goal, &inj)?;
    let iff = Expr::apps(
        c("Iff.intro", vec![]),
        [expr.clone(), inj.conj.clone(), forward, backward],
    );
    let proof = Expr::apps(c("propext", vec![]), [expr.clone(), inj.conj.clone(), iff]);
    Some(SimpResult {
        expr: inj.conj,
        proof: Some(proof),
    })
}

/// `side`, or its weak-head normal form at instance transparency, when that
/// is an application of a constructor.
fn constructor_app(state: &ProofState, goal: &Goal, side: &Expr) -> Option<Expr> {
    let is_ctor = |e: &Expr| match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => state.env().get_constructor(name).is_some(),
        _ => false,
    };
    if is_ctor(side) {
        return Some(side.clone());
    }
    let reduced = state.whnf_instances(goal, side);
    is_ctor(&reduced).then_some(reduced)
}

fn sort_level(state: &ProofState, goal: &Goal, ty: &Expr) -> Option<Level> {
    match state.infer_type(goal, ty).ok()?.kind() {
        ExprKind::Sort(level) => Some(level.clone()),
        _ => None,
    }
}

/// `e₁ ∧ (e₂ ∧ … ∧ eₙ)`, right-nested as Lean's `injEq` states it.
fn conjunction(eqs: &[Expr]) -> Expr {
    let Some((last, init)) = eqs.split_last() else {
        // The empty conjunction. No caller passes one: a constructor with no
        // non-`Prop` field gets no injectivity step.
        return c("True", vec![]);
    };
    init.iter().rev().fold(last.clone(), |acc, eq| {
        Expr::apps(c("And", vec![]), [eq.clone(), acc])
    })
}

/// `fun h : lhs = rhs => T.noConfusion … h (fun e₁ … eₙ => ⟨e₁, …, eₙ⟩)`,
/// each `HEq` premise (a heterogeneous `noConfusion`) turned into `Eq`.
fn forward_direction(state: &ProofState, goal: &Goal, expr: &Expr, inj: &Inj) -> Option<Expr> {
    let (lhs, rhs, conj, eqs) = (&inj.lhs, &inj.rhs, &inj.conj, &inj.eqs[..]);
    let ExprKind::Const(ctor_name, _) = lhs.get_app_fn().kind() else {
        return None;
    };
    state.env().get_constructor(ctor_name)?;
    // `h` is the forward lambda's own binder, bound variable 0; the
    // application's type is read off `noConfusion`'s declared type, so the
    // loose `h` is never type-checked here (the whole lemma is, by the caller).
    let alpha = state.infer_type(goal, lhs).ok()?;
    let (nc_app, nc_ty) = crate::tactic::noconfusion_app::mk_no_confusion_typed(
        state,
        goal,
        conj,
        &alpha,
        (lhs, rhs),
        &Expr::bvar(0),
    )
    .ok()?;
    let nc_ty = state.whnf(goal, &nc_ty);
    let ExprKind::Pi(_, continuation_ty, _) = nc_ty.kind() else {
        return None;
    };
    // The premises, one per field, in order.
    let mut premises: Vec<Expr> = Vec::with_capacity(eqs.len());
    let mut cursor = continuation_ty.as_ref().clone();
    while let ExprKind::Pi(_, domain, body) = cursor.kind() {
        if body.has_loose_bvars() {
            return None;
        }
        premises.push(domain.as_ref().clone());
        cursor = body.as_ref().clone();
    }
    if premises.len() != eqs.len() {
        return None;
    }
    // Under the continuation's n binders premise i is bound variable n-1-i.
    let n = premises.len();
    let as_eqs: Vec<Expr> = premises
        .iter()
        .enumerate()
        .map(|(i, premise)| to_eq(state, goal, premise, Expr::bvar((n - 1 - i) as u32)))
        .collect::<Option<_>>()?;
    let mut continuation = and_intro(eqs, &as_eqs);
    for premise in premises.iter().rev() {
        continuation = Expr::lam(BinderInfo::Default, premise.clone(), continuation);
    }
    // `nc_app` mentions bound variable 0 (`h`); the continuation is closed.
    Some(Expr::lam(
        BinderInfo::Default,
        expr.clone(),
        Expr::app(nc_app, continuation),
    ))
}

/// A `noConfusion` premise as an `Eq` proof: itself, or `eq_of_heq` of it.
fn to_eq(state: &ProofState, goal: &Goal, premise: &Expr, proof: Expr) -> Option<Expr> {
    let args = premise.get_app_args();
    match premise.get_app_fn().kind() {
        ExprKind::Const(name, _) if *name == Name::from_string("Eq") && args.len() == 3 => {
            Some(proof)
        }
        ExprKind::Const(name, levels) if *name == Name::from_string("HEq") && args.len() == 4 => {
            if !state.is_def_eq(goal, args[0], args[2]) {
                return None;
            }
            Some(Expr::apps(
                c("eq_of_heq", levels.to_vec()),
                [args[0].clone(), args[1].clone(), args[3].clone(), proof],
            ))
        }
        _ => None,
    }
}

/// `⟨p₁, ⟨p₂, … pₙ⟩⟩ : e₁ ∧ … ∧ eₙ`.
fn and_intro(eqs: &[Expr], proofs: &[Expr]) -> Expr {
    if eqs.len() == 1 {
        return proofs[0].clone();
    }
    let rest = conjunction(&eqs[1..]);
    Expr::apps(
        c("And.intro", vec![]),
        [
            eqs[0].clone(),
            rest,
            proofs[0].clone(),
            and_intro(&eqs[1..], &proofs[1..]),
        ],
    )
}

/// `fun c : e₁ ∧ … ∧ eₙ => congr (… (congrArg (C ps) c.1) …) cₙ`.
///
/// `fields` are closed and non-dependent, so `C ps a₁ … aₖ`'s type is the
/// closed arrow `Fₖ₊₁ → … → Fₙ → T` and each step is an ordinary
/// `congrArg`/`congr`.
fn backward_direction(state: &ProofState, goal: &Goal, inj: &Inj) -> Option<Expr> {
    let (conj, eqs, fields) = (&inj.conj, &inj.eqs[..], &inj.fields[..]);
    let (lhs, rhs, np, result_ty) = (&inj.lhs, &inj.rhs, inj.np, &inj.result_ty);
    let n = eqs.len();
    let (largs, rargs) = (lhs.get_app_args(), rhs.get_app_args());
    // `Fₖ → … → Fₙ → T`, closed.
    let rest_ty = |k: usize| -> Expr {
        fields[k..]
            .iter()
            .rev()
            .fold(result_ty.clone(), |acc, (fty, _)| {
                Expr::pi(BinderInfo::Default, fty.clone(), acc)
            })
    };
    // The proof of `eᵢ` out of the conjunction, bound variable 0.
    let component = |i: usize| -> Expr {
        let mut proof = Expr::bvar(0);
        for j in 0..i {
            let rest = conjunction(&eqs[j + 1..]);
            proof = Expr::apps(c("And.right", vec![]), [eqs[j].clone(), rest, proof]);
        }
        if i + 1 < n {
            let rest = conjunction(&eqs[i + 1..]);
            proof = Expr::apps(c("And.left", vec![]), [eqs[i].clone(), rest, proof]);
        }
        proof
    };
    let mut ctor_ps = lhs.get_app_fn().clone();
    for param in largs.iter().take(np) {
        ctor_ps = Expr::app(ctor_ps, (*param).clone());
    }
    let (mut f_left, mut f_right) = (ctor_ps.clone(), ctor_ps.clone());
    let mut proof: Option<Expr> = None;
    for (i, (fty, level)) in fields.iter().enumerate() {
        let beta = rest_ty(i + 1);
        let beta_level = sort_level(state, goal, &beta)?;
        let (a, b) = (largs[np + i].clone(), rargs[np + i].clone());
        let step = match proof {
            None => Expr::apps(
                c("congrArg", vec![level.clone(), beta_level]),
                [
                    fty.clone(),
                    beta,
                    a.clone(),
                    b.clone(),
                    ctor_ps.clone(),
                    component(i),
                ],
            ),
            Some(prev) => Expr::apps(
                c("congr", vec![level.clone(), beta_level]),
                [
                    fty.clone(),
                    beta,
                    f_left.clone(),
                    f_right.clone(),
                    a.clone(),
                    b.clone(),
                    prev,
                    component(i),
                ],
            ),
        };
        f_left = Expr::app(f_left, a);
        f_right = Expr::app(f_right, b);
        proof = Some(step);
    }
    Some(Expr::lam(BinderInfo::Default, conj.clone(), proof?))
}
