// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.below` and `.brecOn` generation for recursive inductive types.
//! Reference: `lean4/src/Lean/Meta/Constructions/BRecOn.lean`

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::inductive::{InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

use super::decl_builder::EnvDeclBuilder;
use super::inductive_below_minors::{
    bind_params, build_below_minor, build_brec_on_minor, build_f_type, build_ind_app,
    get_ind_universe, get_nth_pi_domain, instantiate_ctor_field_type, make_below_levels,
    make_ind_levels, mk_pprod,
};
use super::inductive_fixed_indices::CtorInfo;
use super::types::{Declaration, EnvError};
use super::Environment;

impl Environment {
    /// Generate `.below` and `.brecOn` for an inductive type if applicable.
    /// On failure, silently skips (matching Lean 4 behavior).
    pub(crate) fn generate_below_brec_on(
        &mut self,
        ind_type: &InductiveType,
        decl: &InductiveDecl,
        ctor_infos: &[CtorInfo],
    ) {
        if !self.should_generate_below(ind_type) {
            return;
        }
        let Ok(below) = self.build_below(ind_type, decl, ctor_infos) else {
            return;
        };
        if self.add_decl(below).is_err() {
            return;
        }
        let Ok(brec_on) = self.build_brec_on(ind_type, decl, ctor_infos) else {
            return;
        };
        // The checked below family is independently useful. Do not publish a
        // prefix of the recursion wrapper group if a member is rejected.
        let mut staged = self.clone();
        for member in brec_on {
            if staged.add_decl(member).is_err() {
                return;
            }
        }
        *self = staged;
    }

    /// Check whether `.below`/`.brecOn` should be generated.
    fn should_generate_below(&self, ind_type: &InductiveType) -> bool {
        // An artifact import provides the checked families without running
        // Clean's synthetic PUnit/PProd initialization routines.
        let imported_products = self
            .get_constructor(&Name::from_string("PUnit.unit"))
            .is_some()
            && self
                .get_constructor(&Name::from_string("PProd.mk"))
                .is_some();
        if !(imported_products || self.has_punit() && self.has_pprod()) {
            return false;
        }
        let ind_val = match self.inductives.get(&ind_type.name) {
            Some(v) => v,
            None => return false,
        };
        if !ind_val.is_recursive {
            return false;
        }
        // The result sort up to whnf (Lean `isPropFormerType` reduces too): a
        // `δ`-`Prop` family gets no `.below`, and neither does a type former
        // that is not a sort even after reduction.
        self.type_former_is_prop(&ind_type.type_) == Some(false)
    }

    /// Build `.below`: `{motive : Ind → Sort u} → Ind → Sort (max 1 u)`
    fn build_below(
        &self,
        ind_type: &InductiveType,
        decl: &InductiveDecl,
        ctor_infos: &[CtorInfo],
    ) -> Result<Declaration, EnvError> {
        let ind_name = &ind_type.name;
        let below_name = ind_name.clone().str("below");
        let rec_name = ind_name.clone().str("rec");

        let rec_val = self
            .recursors
            .get(&rec_name)
            .ok_or_else(|| EnvError::UnknownInductive(rec_name.clone()))?;

        let below_level_params = rec_val.level_params.clone();
        let motive_univ_name = &below_level_params[0];
        let ind_univ = get_ind_universe(self, &ind_type.type_);
        let motive_level = Level::param(motive_univ_name.clone());
        let rlvl = Level::max(ind_univ.clone(), motive_level.clone());
        let rlvl_sort = Expr::from_kind(ExprKind::Sort(rlvl.clone()));
        let ind_levels = make_ind_levels(decl);

        let value = build_below_value(
            ind_type,
            decl,
            ctor_infos,
            ind_name,
            &rec_name,
            &ind_levels,
            &motive_level,
            &rlvl,
            &rlvl_sort,
        );
        let below_type = build_below_type(
            ind_type,
            decl,
            ind_name,
            motive_univ_name,
            &ind_levels,
            rlvl_sort,
        );

        Ok(Declaration::Definition {
            name: below_name,
            level_params: below_level_params,
            type_: below_type,
            value,
            is_reducible: true,
        })
    }

    /// Build `.brecOn`: `{motive} → (t : Ind) → (Ind → below t → motive t) → motive t`
    fn build_brec_on(
        &self,
        ind_type: &InductiveType,
        decl: &InductiveDecl,
        ctor_infos: &[CtorInfo],
    ) -> Result<Vec<Declaration>, EnvError> {
        let ind_name = &ind_type.name;
        let rec_name = ind_name.clone().str("rec");

        let rec_val = self
            .recursors
            .get(&rec_name)
            .ok_or_else(|| EnvError::UnknownInductive(rec_name.clone()))?;

        let brec_level_params = rec_val.level_params.clone();
        let motive_univ_name = &brec_level_params[0];
        let motive_level = Level::param(motive_univ_name.clone());
        let ind_levels = make_ind_levels(decl);
        let ind_univ = get_ind_universe(self, &ind_type.type_);
        let cases_name = ind_name.clone().str("casesOn");
        let equation = decl.num_params == 0
            && decl.types.len() == 1
            && rec_val.num_indices == 0
            && rec_val.num_motives == 1
            && self.get_const(&cases_name).is_some()
            && self.get_const(&Name::from_string("Eq.refl")).is_some();
        Ok(build_brec_on_decls(
            ind_type,
            decl,
            ctor_infos,
            &ind_univ,
            &ind_levels,
            &motive_level,
            &brec_level_params,
            equation.then_some(cases_name),
        ))
    }
}

/// Build the value expression for `.below` using the recursor.
fn build_below_value(
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    ctor_infos: &[CtorInfo],
    ind_name: &Name,
    rec_name: &Name,
    ind_levels: &[Level],
    motive_level: &Level,
    rlvl: &Level,
    rlvl_sort: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (param_ids, param_fvars) = bind_params(&mut b, &ind_type.type_, decl.num_params);
    let ind_app = build_ind_app(ind_name, ind_levels, &param_fvars);
    let motive_sort = Expr::from_kind(ExprKind::Sort(motive_level.clone()));
    let motive_ty = Expr::arrow(ind_app.clone(), motive_sort);
    let (motive_id, motive_fv) = b.fresh_local(motive_ty.clone());
    let (major_id, major_fv) = b.fresh_local(ind_app.clone());

    let rec_levels = {
        let mut lvls = vec![Level::succ(rlvl.clone())];
        lvls.extend_from_slice(ind_levels);
        lvls
    };
    let mut rec_app = Expr::const_(rec_name.clone(), rec_levels);
    for fv in &param_fvars {
        rec_app = Expr::app(rec_app, fv.clone());
    }
    // Motive for rec: fun _ => Sort rlvl
    rec_app = Expr::app(
        rec_app,
        Expr::lam(BinderInfo::Default, ind_app.clone(), rlvl_sort.clone()),
    );
    for (_cname, nf, rec_flags, ftypes, _ridx) in ctor_infos {
        let minor = build_below_minor(
            rlvl_sort,
            motive_level,
            &motive_fv,
            &ind_app,
            &param_fvars,
            *nf,
            rec_flags,
            ftypes,
            &b,
        );
        rec_app = Expr::app(rec_app, minor);
    }
    rec_app = Expr::app(rec_app, major_fv.clone());

    let mut value = rec_app;
    value = b.mk_lam(major_id, BinderInfo::Default, ind_app.clone(), value);
    value = b.mk_lam(motive_id, BinderInfo::Implicit, motive_ty, value);
    for i in (0..param_ids.len()).rev() {
        let pty = get_nth_pi_domain(&ind_type.type_, i);
        value = b.mk_lam(param_ids[i], BinderInfo::Implicit, pty, value);
    }
    b.finish(value)
}

/// Build the type expression for `.below`.
fn build_below_type(
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    ind_name: &Name,
    motive_univ_name: &Name,
    ind_levels: &[Level],
    rlvl_sort: Expr,
) -> Expr {
    let mut b2 = EnvDeclBuilder::new();
    let (p2_ids, p2_fvs) = bind_params(&mut b2, &ind_type.type_, decl.num_params);
    let ind_app2 = build_ind_app(ind_name, ind_levels, &p2_fvs);
    let motive_ty2 = Expr::arrow(
        ind_app2.clone(),
        Expr::from_kind(ExprKind::Sort(Level::param(motive_univ_name.clone()))),
    );
    let (motive_id2, _) = b2.fresh_local(motive_ty2.clone());
    let (major_id2, _) = b2.fresh_local(ind_app2.clone());

    let mut below_type = rlvl_sort;
    below_type = b2.mk_pi(major_id2, BinderInfo::Default, ind_app2, below_type);
    below_type = b2.mk_pi(motive_id2, BinderInfo::Implicit, motive_ty2, below_type);
    for i in (0..p2_ids.len()).rev() {
        let pty = get_nth_pi_domain(&ind_type.type_, i);
        below_type = b2.mk_pi(p2_ids[i], BinderInfo::Implicit, pty, below_type);
    }
    b2.finish(below_type)
}

/// The `go` definition builds the dependent pair. The public recursion
/// wrapper projects its first field and its equation exposes the second.
fn build_brec_on_decls(
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    ctor_infos: &[CtorInfo],
    ind_univ: &Level,
    ind_levels: &[Level],
    motive_level: &Level,
    level_params: &[Name],
    cases_name: Option<Name>,
) -> Vec<Declaration> {
    let ind_name = &ind_type.name;
    let brec_name = ind_name.clone().str("brecOn");
    let below_levels = make_below_levels(&level_params[0], ind_levels);
    let go_name = brec_name.clone().str("go");
    let mut b = EnvDeclBuilder::new();
    let (param_ids, param_fvars) = bind_params(&mut b, &ind_type.type_, decl.num_params);
    let ind_app = build_ind_app(ind_name, ind_levels, &param_fvars);
    let motive_sort = Expr::from_kind(ExprKind::Sort(motive_level.clone()));
    let motive_ty = Expr::arrow(ind_app.clone(), motive_sort);
    let (motive_id, motive_fv) = b.fresh_local(motive_ty.clone());
    let (major_id, major_fv) = b.fresh_local(ind_app.clone());

    let mut below_app = Expr::const_(ind_name.clone().str("below"), below_levels.clone());
    for fv in &param_fvars {
        below_app = Expr::app(below_app, fv.clone());
    }
    below_app = Expr::app(below_app, motive_fv.clone());

    let f_type = build_f_type(&b, &ind_app, &below_app, &motive_fv);
    let (f_id, f_fv) = b.fresh_local(f_type.clone());
    let rlvl = Level::max(ind_univ.clone(), motive_level.clone());
    let pair_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x_fv) = mb.fresh_local(ind_app.clone());
        let pair_ty = mk_pprod(
            Expr::app(motive_fv.clone(), x_fv.clone()),
            Expr::app(below_app.clone(), x_fv),
            motive_level,
            &rlvl,
        );
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, ind_app.clone(), pair_ty))
    };

    let rec_name = ind_name.clone().str("rec");
    let rec_levels = {
        let mut lvls = vec![rlvl.clone()];
        lvls.extend_from_slice(ind_levels);
        lvls
    };
    let mut rec_app = Expr::const_(rec_name, rec_levels);
    for fv in &param_fvars {
        rec_app = Expr::app(rec_app, fv.clone());
    }
    rec_app = Expr::app(rec_app, pair_motive);
    for (ctor_name, nf, rec_flags, field_tys, _ridx) in ctor_infos {
        let minor = build_brec_on_minor(
            &b,
            decl,
            ctor_name,
            *nf,
            rec_flags,
            field_tys,
            &param_fvars,
            motive_level,
            &rlvl,
            &motive_fv,
            &f_fv,
            &below_app,
        );
        rec_app = Expr::app(rec_app, minor);
    }
    let result_ty = Expr::app(motive_fv.clone(), major_fv.clone());
    let go_ty = mk_pprod(
        result_ty.clone(),
        Expr::app(below_app, major_fv.clone()),
        motive_level,
        &rlvl,
    );
    let go_app = Expr::apps(
        Expr::const_(go_name.clone(), below_levels.clone()),
        param_fvars
            .iter()
            .cloned()
            .chain([motive_fv.clone(), major_fv.clone(), f_fv.clone()]),
    );
    let mut binders: Vec<_> = param_ids
        .into_iter()
        .enumerate()
        .map(|(index, id)| {
            (
                id,
                BinderInfo::Implicit,
                get_nth_pi_domain(&ind_type.type_, index),
            )
        })
        .collect();
    binders.extend([
        (motive_id, BinderInfo::Implicit, motive_ty),
        (major_id, BinderInfo::Default, ind_app.clone()),
        (f_id, BinderInfo::Default, f_type),
    ]);
    let pi = |expr| close_brec_binders(&b, &binders, expr, EnvDeclBuilder::mk_pi);
    let lam = |expr| close_brec_binders(&b, &binders, expr, EnvDeclBuilder::mk_lam);
    let mut declarations = vec![
        Declaration::Definition {
            name: go_name.clone(),
            level_params: level_params.to_vec(),
            type_: pi(go_ty),
            value: lam(Expr::app(rec_app, major_fv.clone())),
            is_reducible: true,
        },
        Declaration::Definition {
            name: brec_name.clone(),
            level_params: level_params.to_vec(),
            type_: pi(result_ty),
            value: lam(Expr::proj(Name::from_string("PProd"), 0, go_app)),
            is_reducible: true,
        },
    ];
    if let Some(cases_name) = cases_name {
        let equation = |major: Expr| {
            let args = [motive_fv.clone(), major.clone(), f_fv.clone()];
            let lhs = Expr::apps(
                Expr::const_(brec_name.clone(), below_levels.clone()),
                args.clone(),
            );
            let go = Expr::apps(Expr::const_(go_name.clone(), below_levels.clone()), args);
            let ty = Expr::app(motive_fv.clone(), major.clone());
            let rhs = Expr::apps(
                f_fv.clone(),
                [major, Expr::proj(Name::from_string("PProd"), 1, go)],
            );
            (ty, lhs, rhs)
        };
        let eq = |major| {
            let (ty, lhs, rhs) = equation(major);
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![motive_level.clone()]),
                [ty, lhs, rhs],
            )
        };
        let mut motive = EnvDeclBuilder::child_of(&b);
        let (id, fv) = motive.fresh_local(ind_app.clone());
        let branches = ctor_infos.iter().map(|(name, _, _, field_types, _)| {
            let mut branch = EnvDeclBuilder::child_of(&b);
            let mut args = Vec::with_capacity(field_types.len());
            let mut fields = Vec::with_capacity(field_types.len());
            for ty in field_types {
                let ty = instantiate_ctor_field_type(ty, &[], &args);
                let (id, var) = branch.fresh_local(ty.clone());
                fields.push((id, BinderInfo::Default, ty));
                args.push(var);
            }
            let ctor = Expr::apps(Expr::const_(name.clone(), ind_levels.to_vec()), args);
            let (ty, lhs, _) = equation(ctor);
            let refl = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![motive_level.clone()]),
                [ty, lhs],
            );
            branch.finish_child(bind_brec_binders(
                &branch,
                &fields,
                refl,
                EnvDeclBuilder::mk_lam,
            ))
        });
        let cases = Expr::apps(
            Expr::const_(
                cases_name,
                std::iter::once(Level::zero())
                    .chain(ind_levels.iter().cloned())
                    .collect::<Vec<_>>(),
            ),
            [
                motive.finish_child(motive.mk_lam(id, BinderInfo::Default, ind_app, eq(fv))),
                major_fv.clone(),
            ]
            .into_iter()
            .chain(branches),
        );
        let type_ = pi(eq(major_fv));
        declarations.push(Declaration::Theorem {
            name: brec_name.str("eq"),
            level_params: level_params.to_vec(),
            type_,
            value: lam(cases),
        });
    }
    declarations
}

fn bind_brec_binders(
    builder: &EnvDeclBuilder,
    binders: &[(FVarId, BinderInfo, Expr)],
    mut expr: Expr,
    close: fn(&EnvDeclBuilder, FVarId, BinderInfo, Expr, Expr) -> Expr,
) -> Expr {
    for (id, binder, ty) in binders.iter().rev() {
        expr = close(builder, *id, *binder, ty.clone(), expr);
    }
    expr
}

fn close_brec_binders(
    builder: &EnvDeclBuilder,
    binders: &[(FVarId, BinderInfo, Expr)],
    expr: Expr,
    close: fn(&EnvDeclBuilder, FVarId, BinderInfo, Expr, Expr) -> Expr,
) -> Expr {
    builder.finish(bind_brec_binders(builder, binders, expr, close))
}
