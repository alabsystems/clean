// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minor premise builders and shared helpers for `.below` and `.brecOn`
//! generation.
//!
//! Extracted from `inductive_below.rs` to stay within the 500-line limit.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::InductiveDecl;
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

use super::decl_builder::EnvDeclBuilder;
use super::Environment;

/// Build a minor premise for `.brecOn`. Each constructor minor binds fields
/// and induction hypotheses, constructs a `PProd (motive ctor_app) (below ctor_app)`
/// pair using F and a below-witness chain.
pub(super) fn build_brec_on_minor(
    parent: &EnvDeclBuilder,
    decl: &InductiveDecl,
    ctor_name: &Name,
    num_fields: u32,
    recursive_flags: &[bool],
    field_types: &[Expr],
    param_fvars: &[Expr],
    motive_level: &Level,
    rlvl: &Level,
    motive_fv: &Expr,
    f_fv: &Expr,
    below_app: &Expr,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let mut field_ids = Vec::new();
    let mut field_fvars = Vec::new();
    let mut field_tys = Vec::new();

    for i in 0..num_fields as usize {
        let ft = field_types
            .get(i)
            .map(|field_ty| instantiate_ctor_field_type(field_ty, param_fvars, &field_fvars))
            .unwrap_or_else(Expr::prop);
        let (id, fv) = cb.fresh_local(ft.clone());
        field_ids.push(id);
        field_fvars.push(fv);
        field_tys.push(ft);
    }

    let mut ih_ids = Vec::new();
    let mut ih_fvars = Vec::new();
    let mut ih_tys = Vec::new();
    for i in 0..num_fields as usize {
        if i < recursive_flags.len() && recursive_flags[i] {
            let ih_ty = mk_pprod(
                Expr::app(motive_fv.clone(), field_fvars[i].clone()),
                Expr::app(below_app.clone(), field_fvars[i].clone()),
                motive_level,
                rlvl,
            );
            let (id, fv) = cb.fresh_local(ih_ty.clone());
            ih_ids.push(id);
            ih_fvars.push(fv);
            ih_tys.push(ih_ty);
        }
    }

    let mut ctor_app = Expr::const_(
        ctor_name.clone(),
        decl.level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect::<Vec<_>>(),
    );
    for fv in param_fvars {
        ctor_app = Expr::app(ctor_app, fv.clone());
    }
    for fv in &field_fvars {
        ctor_app = Expr::app(ctor_app, fv.clone());
    }

    let mut below_witness_ty = Expr::const_(Name::from_string("PUnit"), vec![rlvl.clone()]);
    let mut below_witness = Expr::const_(Name::from_string("PUnit.unit"), vec![rlvl.clone()]);
    let mut ih_idx = ih_fvars.len();
    for i in (0..num_fields as usize).rev() {
        if i < recursive_flags.len() && recursive_flags[i] {
            ih_idx -= 1;
            let alpha_ty = ih_tys[ih_idx].clone();
            below_witness = mk_pprod_mk(
                alpha_ty.clone(),
                below_witness_ty.clone(),
                ih_fvars[ih_idx].clone(),
                below_witness,
                rlvl,
                rlvl,
            );
            below_witness_ty = mk_pprod(alpha_ty, below_witness_ty, rlvl, rlvl);
        }
    }

    let current = Expr::app(
        Expr::app(f_fv.clone(), ctor_app.clone()),
        below_witness.clone(),
    );
    let pair = mk_pprod_mk(
        Expr::app(motive_fv.clone(), ctor_app.clone()),
        Expr::app(below_app.clone(), ctor_app),
        current,
        below_witness,
        motive_level,
        rlvl,
    );

    let mut result = pair;
    for j in (0..ih_ids.len()).rev() {
        result = cb.mk_lam(ih_ids[j], BinderInfo::Default, ih_tys[j].clone(), result);
    }
    for i in (0..field_ids.len()).rev() {
        result = cb.mk_lam(
            field_ids[i],
            BinderInfo::Default,
            field_tys[i].clone(),
            result,
        );
    }
    cb.finish_child(result)
}

/// Build a minor premise for `.below`. Recursive fields contribute
/// `PProd (motive field) ih`; non-recursive fields are bound but ignored.
pub(super) fn build_below_minor(
    rlvl_sort: &Expr,
    motive_level: &Level,
    motive_fv: &Expr,
    ind_app: &Expr,
    param_fvars: &[Expr],
    num_fields: u32,
    recursive_flags: &[bool],
    field_types: &[Expr],
    parent_builder: &EnvDeclBuilder,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent_builder);
    let mut field_ids = Vec::new();
    let mut field_fvars = Vec::new();
    let mut field_tys = Vec::new();

    for i in 0..num_fields as usize {
        let ft = if let Some(field_ty) = field_types.get(i) {
            instantiate_ctor_field_type(field_ty, param_fvars, &field_fvars)
        } else {
            ind_app.clone()
        };
        let (id, fv) = cb.fresh_local(ft.clone());
        field_ids.push(id);
        field_fvars.push(fv);
        field_tys.push(ft);
    }

    // Bind IH arguments for recursive fields
    let mut ih_ids = Vec::new();
    let mut ih_fvars = Vec::new();
    for i in 0..num_fields as usize {
        if i < recursive_flags.len() && recursive_flags[i] {
            let (id, fv) = cb.fresh_local(rlvl_sort.clone());
            ih_ids.push(id);
            ih_fvars.push(fv);
        }
    }

    // Build product of (motive field, ih) pairs
    let rlvl = sort_level(rlvl_sort);
    let punit = Expr::const_(Name::from_string("PUnit"), vec![rlvl.clone()]);
    let mut result = punit;
    let mut ih_idx = ih_fvars.len();

    for i in (0..num_fields as usize).rev() {
        if i < recursive_flags.len() && recursive_flags[i] {
            ih_idx -= 1;
            let motive_applied = Expr::app(motive_fv.clone(), field_fvars[i].clone());
            let ih = ih_fvars[ih_idx].clone();
            let pair = mk_pprod(motive_applied, ih, motive_level, &rlvl);
            result = mk_pprod(pair, result, &rlvl, &rlvl);
        }
    }

    // Close IH binders
    for j in (0..ih_ids.len()).rev() {
        result = cb.mk_lam(ih_ids[j], BinderInfo::Default, rlvl_sort.clone(), result);
    }

    // Close field binders
    for i in (0..field_ids.len()).rev() {
        result = cb.mk_lam(
            field_ids[i],
            BinderInfo::Default,
            field_tys[i].clone(),
            result,
        );
    }

    cb.finish_child(result)
}

// --- Shared helpers ---

/// Extract the level from a Sort expression, defaulting to zero.
pub(super) fn sort_level(e: &Expr) -> Level {
    match &e.kind {
        ExprKind::Sort(l) => l.clone(),
        _ => Level::zero(),
    }
}

/// Build `PProd a b` expression with separate universe levels.
pub(super) fn mk_pprod(a: Expr, b: Expr, lhs_lvl: &Level, rhs_lvl: &Level) -> Expr {
    let pprod = Expr::const_(
        Name::from_string("PProd"),
        vec![lhs_lvl.clone(), rhs_lvl.clone()],
    );
    Expr::app(Expr::app(pprod, a), b)
}

/// Build `PProd.mk a_ty b_ty a b` expression with separate universe levels.
pub(super) fn mk_pprod_mk(
    a_ty: Expr,
    b_ty: Expr,
    a: Expr,
    b: Expr,
    lhs_lvl: &Level,
    rhs_lvl: &Level,
) -> Expr {
    let mk = Expr::const_(
        Name::from_string("PProd.mk"),
        vec![lhs_lvl.clone(), rhs_lvl.clone()],
    );
    Expr::apps(mk, [a_ty, b_ty, a, b])
}

/// Get the universe level of the inductive type former itself.
///
/// For sort-valued type formers like `Nat : Type`, use the sort level directly.
/// For parameterized formers like `List : Sort u -> Sort u`, infer the universe
/// of the Pi-expression (`max 1 u` in this example).
pub(super) fn get_ind_universe(env: &Environment, ind_type: &Expr) -> Level {
    match &ind_type.kind {
        ExprKind::Sort(l) => l.clone(),
        _ => TypeChecker::new(env)
            .infer_sort(ind_type)
            .unwrap_or_else(|_| Level::zero()),
    }
}

/// Build the universe-level list for an inductive's own parameters.
pub(super) fn make_ind_levels(decl: &InductiveDecl) -> Vec<Level> {
    decl.level_params
        .iter()
        .map(|n| Level::param(n.clone()))
        .collect()
}

/// Build below-level params: `[motive_univ, ind_levels...]`.
pub(super) fn make_below_levels(motive_univ_name: &Name, ind_levels: &[Level]) -> Vec<Level> {
    let mut lvls = vec![Level::param(motive_univ_name.clone())];
    lvls.extend_from_slice(ind_levels);
    lvls
}

/// Bind parameters from an inductive type using an EnvDeclBuilder.
pub(super) fn bind_params(
    b: &mut EnvDeclBuilder,
    ind_type: &Expr,
    num_params: u32,
) -> (Vec<crate::expr::FVarId>, Vec<Expr>) {
    let mut ids = Vec::new();
    let mut fvars = Vec::new();
    let mut cursor = ind_type.clone();
    for _ in 0..num_params {
        if let ExprKind::Pi(_, domain, body) = &cursor.kind {
            let (id, fv) = b.fresh_local((**domain).clone());
            ids.push(id);
            fvars.push(fv);
            cursor = (**body).clone();
        }
    }
    (ids, fvars)
}

/// Build `Ind` applied to parameter FVars.
pub(super) fn build_ind_app(ind_name: &Name, ind_levels: &[Level], param_fvars: &[Expr]) -> Expr {
    let mut app = Expr::const_(ind_name.clone(), ind_levels.to_vec());
    for fv in param_fvars {
        app = Expr::app(app, fv.clone());
    }
    app
}

/// Get the i-th Pi domain from a type expression.
pub(super) fn get_nth_pi_domain(ty: &Expr, idx: usize) -> Expr {
    let mut cursor = ty;
    for i in 0..=idx {
        if let ExprKind::Pi(_, domain, body) = &cursor.kind {
            if i == idx {
                return (**domain).clone();
            }
            cursor = body;
        } else {
            break;
        }
    }
    Expr::prop()
}

/// Build the F type: `(t : Ind) -> below t -> motive t`
pub(super) fn build_f_type(
    parent: &EnvDeclBuilder,
    ind_app: &Expr,
    below_app: &Expr,
    motive_fv: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (ft_id, ft_fv) = fb.fresh_local(ind_app.clone());
    let below_of_ft = Expr::app(below_app.clone(), ft_fv.clone());
    let motive_of_ft = Expr::app(motive_fv.clone(), ft_fv);
    let (bel_id, _) = fb.fresh_local(below_of_ft.clone());
    let inner = fb.mk_pi(bel_id, BinderInfo::Default, below_of_ft, motive_of_ft);
    let pi = fb.mk_pi(ft_id, BinderInfo::Default, ind_app.clone(), inner);
    fb.finish_child(pi)
}

/// Instantiate a constructor field type with the current parameter and prior
/// field locals.
///
/// In `field_types[i]`, loose `BVar`s are ordered from innermost to outermost:
/// prior fields in reverse order, then parameters in reverse order.
pub(super) fn instantiate_ctor_field_type(
    field_ty: &Expr,
    param_fvars: &[Expr],
    field_fvars: &[Expr],
) -> Expr {
    let mut instantiated = field_ty.clone();
    for fv in field_fvars.iter().rev() {
        instantiated = instantiated.instantiate(fv);
    }
    for fv in param_fvars.iter().rev() {
        instantiated = instantiated.instantiate(fv);
    }
    instantiated
}
