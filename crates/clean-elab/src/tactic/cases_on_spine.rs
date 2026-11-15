// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `T.casesOn` application `cases` assembles (ledger class (92), brick B5
//! of `designs/2026-10-08-mutual-nested-recursion.md`).
//!
//! Lean's `T.casesOn` always takes ONE motive and the minors of `T`'s own
//! constructors. Clean's kernel builds `casesOn` for a mutual block, and for a
//! nested inductive after the auxiliary types are restored, the way it builds
//! the recursor: one motive per member of the block and per auxiliary
//! container, and the minors of every constructor of every one of them
//! (`inductive P | leaf : Nat → P | conj : List P → P` gives
//! `P.casesOn : (motive : P → Sort u) → (motive_1 : List P → Sort u) → (t : P)
//! → leaf-minor → conj-minor → nil-minor → cons-minor → motive t`). The tactic
//! assembled the one-motive Lean shape, so `cases p` on such a type was
//! refused by the kernel's application check.
//!
//! The design keeps the kernel's shape and fills the other slots on the
//! tactic side, as the match compiler already does
//! (`infer/elab_match/mod.rs`, the "plain multi-motive match"): a motive slot
//! that is not the major premise's own gets the constant `PUnit.{u}` at the
//! slot's own universe, and a minor of a constructor that is not the major
//! premise's gets `fun fields => PUnit.unit.{u}`. The major premise belongs to
//! the selected member, so `casesOn` never reduces through one of those slots:
//! they are dead code with genuine inhabitants, not axioms. The assembled
//! term is re-checked by the kernel like every `cases` proof.
//!
//! Every slot is read off the eliminator's own declared type, instantiated
//! argument by argument, so the layout is the kernel's authority, never a
//! reconstruction: which minor belongs to the major premise's type is the
//! constructor its conclusion applies the motive to.

use clean_kernel::name::Name;
use clean_kernel::{BinderData, Expr, ExprKind, InductiveVal, Level};

use super::core::{ProofState, TacticError};

/// The arguments of one `casesOn` application, in source terms.
pub(crate) struct CasesOnArgs<'a> {
    /// The eliminator, `T.casesOn`.
    pub(crate) rec_name: &'a Name,
    /// Its universe levels (motive level first when it has one).
    pub(crate) rec_levels: Vec<Level>,
    /// The inductive's parameters.
    pub(crate) params: &'a [Expr],
    /// The motive of the major premise's own type.
    pub(crate) motive: Expr,
    /// The major premise's indices.
    pub(crate) index_args: &'a [Expr],
    /// The major premise.
    pub(crate) major: Expr,
    /// The minors of the major premise's type, one per constructor of
    /// `ind_info.constructor_names`, in that order.
    pub(crate) minors: Vec<Expr>,
}

/// `T.casesOn params motive(s) indices major minors`.
///
/// One-motive eliminators — every ordinary inductive, and every `casesOn`
/// imported from Lean, which is a definition rather than a registered
/// recursor — keep the layout `cases` always built. A registered
/// eliminator that declares several motives takes the PUnit slots described
/// in the module documentation.
///
/// ENSURES: on `Ok`, the result applies `rec_name` to exactly the binders its
///   declared type has (params, motives, indices, major, minors), and every
///   minor of `ind_info`'s constructors is the caller's.
pub(crate) fn assemble_cases_on(
    state: &ProofState,
    ind_info: &InductiveVal,
    args: CasesOnArgs<'_>,
) -> Result<Expr, TacticError> {
    let registered = state.env.get_recursor(args.rec_name);
    let num_motives = registered.map_or(1, |rec| rec.num_motives as usize);
    let mut proof = Expr::const_(args.rec_name.clone(), args.rec_levels.clone());
    for param in args.params {
        proof = Expr::app(proof, param.clone());
    }
    if num_motives <= 1 {
        proof = Expr::app(proof, args.motive);
        for idx in args.index_args {
            proof = Expr::app(proof, idx.clone());
        }
        proof = Expr::app(proof, args.major);
        for minor in args.minors {
            proof = Expr::app(proof, minor);
        }
        return Ok(proof);
    }
    let Some(rec) = registered else {
        return Err(layout_error(
            args.rec_name,
            "is not a registered eliminator",
        ));
    };
    let selected = ind_info
        .all_names
        .iter()
        .position(|name| name == &ind_info.name)
        .filter(|&index| index < num_motives)
        .ok_or_else(|| {
            layout_error(
                args.rec_name,
                &format!(
                    "has no motive slot for `{}` among its {num_motives} motives",
                    ind_info.name
                ),
            )
        })?;
    if args.minors.len() != ind_info.constructor_names.len() {
        return Err(layout_error(
            args.rec_name,
            "was given a minor count that is not the constructor count",
        ));
    }

    let mut ty = rec
        .type_
        .instantiate_level_params_direct(&rec.level_params, &args.rec_levels);
    for param in args.params {
        ty = take_binder(args.rec_name, &ty, param)?;
    }
    for slot in 0..num_motives {
        let motive = if slot == selected {
            args.motive.clone()
        } else {
            let domain = binder_domain(args.rec_name, &ty)?;
            constant_punit_motive(args.rec_name, domain)?
        };
        ty = take_binder(args.rec_name, &ty, &motive)?;
        proof = Expr::app(proof, motive);
    }
    for idx in args.index_args {
        ty = take_binder(args.rec_name, &ty, idx)?;
        proof = Expr::app(proof, idx.clone());
    }
    ty = take_binder(args.rec_name, &ty, &args.major)?;
    proof = Expr::app(proof, args.major);

    let mut own: Vec<Option<Expr>> = args.minors.into_iter().map(Some).collect();
    for _ in 0..rec.num_minors {
        let domain = binder_domain(args.rec_name, &ty)?.clone();
        let ctor = minor_constructor(&domain);
        let own_slot = ctor.as_ref().and_then(|ctor| {
            ind_info
                .constructor_names
                .iter()
                .position(|name| name == ctor)
        });
        let minor = match own_slot {
            Some(index) => own[index].take().ok_or_else(|| {
                layout_error(
                    args.rec_name,
                    &format!(
                        "declares two minors for `{}`",
                        ind_info.constructor_names[index]
                    ),
                )
            })?,
            None => constant_punit_minor(args.rec_name, &domain, &ty)?,
        };
        ty = take_binder(args.rec_name, &ty, &minor)?;
        proof = Expr::app(proof, minor);
    }
    if let Some(index) = own.iter().position(Option::is_some) {
        return Err(layout_error(
            args.rec_name,
            &format!(
                "declares no minor for `{}`",
                ind_info.constructor_names[index]
            ),
        ));
    }
    Ok(proof)
}

fn layout_error(rec_name: &Name, detail: &str) -> TacticError {
    TacticError::GoalMismatch(format!("cases: the eliminator `{rec_name}` {detail}"))
}

/// The domain of the leading binder of `ty`.
fn binder_domain<'a>(rec_name: &Name, ty: &'a Expr) -> Result<&'a Expr, TacticError> {
    match ty.kind() {
        ExprKind::Pi(_, domain, _) => Ok(domain.as_ref()),
        _ => Err(layout_error(rec_name, "has fewer binders than it declares")),
    }
}

/// `ty`'s body after its leading binder is instantiated with `arg`.
fn take_binder(rec_name: &Name, ty: &Expr, arg: &Expr) -> Result<Expr, TacticError> {
    match ty.kind() {
        ExprKind::Pi(_, _, body) => Ok(body.instantiate(arg)),
        _ => Err(layout_error(rec_name, "has fewer binders than it declares")),
    }
}

/// The constructor a minor premise's conclusion applies its motive to:
/// `Π fields, motive indices (C params fields)` gives `C`.
fn minor_constructor(minor_ty: &Expr) -> Option<Name> {
    let mut conclusion = minor_ty;
    while let ExprKind::Pi(_, _, body) = conclusion.kind() {
        conclusion = body;
    }
    let target = conclusion.get_app_args_iter().next()?;
    match target.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// `fun binders => PUnit.{u}` over a motive slot `Π binders, Sort u`.
///
/// The binder domains are copied as declared, so the de Bruijn structure of
/// the telescope is kept and nothing needs re-abstracting.
fn constant_punit_motive(rec_name: &Name, motive_ty: &Expr) -> Result<Expr, TacticError> {
    let mut binders: Vec<(BinderData, Expr)> = Vec::new();
    let mut cursor = motive_ty;
    while let ExprKind::Pi(info, domain, body) = cursor.kind() {
        binders.push((*info, domain.as_ref().clone()));
        cursor = body;
    }
    let ExprKind::Sort(level) = cursor.kind() else {
        return Err(layout_error(
            rec_name,
            "has a motive slot that is not a sort",
        ));
    };
    let mut motive = Expr::const_(Name::from_string("PUnit"), vec![level.clone()]);
    for (info, domain) in binders.into_iter().rev() {
        motive = Expr::lam(info, domain, motive);
    }
    Ok(motive)
}

/// `fun fields => PUnit.unit.{u}` for a minor of an auxiliary constructor,
/// whose conclusion is a constant `PUnit.{u}` motive applied to it.
fn constant_punit_minor(
    rec_name: &Name,
    minor_ty: &Expr,
    rest: &Expr,
) -> Result<Expr, TacticError> {
    let mut binders: Vec<(BinderData, Expr)> = Vec::new();
    let mut cursor = minor_ty;
    while let ExprKind::Pi(info, domain, body) = cursor.kind() {
        binders.push((*info, domain.as_ref().clone()));
        cursor = body;
    }
    let level = punit_level_of_conclusion(cursor).ok_or_else(|| {
        layout_error(
            rec_name,
            &format!(
                "has a minor whose motive is not a constant PUnit slot: {}",
                crate::error_render::term(rest)
            ),
        )
    })?;
    let mut minor = Expr::const_(Name::from_string("PUnit.unit"), vec![level]);
    for (info, domain) in binders.into_iter().rev() {
        minor = Expr::lam(info, domain, minor);
    }
    Ok(minor)
}

/// The level `u` of a conclusion `(fun binders => PUnit.{u}) args`: an
/// auxiliary minor's conclusion applies one of the constant motives
/// [`constant_punit_motive`] built.
fn punit_level_of_conclusion(conclusion: &Expr) -> Option<Level> {
    let mut head = conclusion.get_app_fn();
    while let ExprKind::Lam(_, _, body) = head.kind() {
        head = body;
    }
    match head.kind() {
        ExprKind::Const(name, levels)
            if *name == Name::from_string("PUnit") && levels.len() == 1 =>
        {
            Some(levels[0].clone())
        }
        _ => None,
    }
}
