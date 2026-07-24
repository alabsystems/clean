// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.below` and `.brecOn` generation for recursive inductive types.
//! Reference: `lean4/src/Lean/Meta/Constructions/BRecOn.lean`

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

use super::decl_builder::EnvDeclBuilder;
use super::inductive_below_minors::{
    bind_params, build_below_minor, build_brec_on_minor, build_f_type, build_ind_app,
    get_ind_universe, get_nth_pi_domain, make_below_levels, make_ind_levels, mk_pprod,
};
use super::inductive_fixed_indices::{is_prop_former_type, CtorInfo};
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
        if let Ok(below_decl) = self.build_below(ind_type, decl, ctor_infos) {
            // Silently skip on either failure, matching Lean 4 behavior.
            if self.add_decl(below_decl).is_ok() {
                let _ = self
                    .build_brec_on(ind_type, decl, ctor_infos)
                    .and_then(|decl| self.add_decl(decl));
            }
        }
    }

    /// Check whether `.below`/`.brecOn` should be generated.
    fn should_generate_below(&self, ind_type: &InductiveType) -> bool {
        if !self.has_punit() || !self.has_pprod() {
            return false;
        }
        let ind_val = match self.inductives.get(&ind_type.name) {
            Some(v) => v,
            None => return false,
        };
        if !ind_val.is_recursive {
            return false;
        }
        !is_prop_former_type(&ind_type.type_)
    }

    /// Build `.below`: `{motive : Ind → Sort u} → Ind → Sort (max 1 u)`
    fn build_below(
        &self,
        ind_type: &InductiveType,
        decl: &InductiveDecl,
        ctor_infos: &[CtorInfo],
    ) -> Result<Declaration, EnvError> {
        let ind_name = &ind_type.name;
        let below_name = Name::from_string(&format!("{ind_name}.below"));
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

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
    ) -> Result<Declaration, EnvError> {
        let ind_name = &ind_type.name;
        let below_name = Name::from_string(&format!("{ind_name}.below"));
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        let rec_val = self
            .recursors
            .get(&rec_name)
            .ok_or_else(|| EnvError::UnknownInductive(rec_name.clone()))?;

        let brec_level_params = rec_val.level_params.clone();
        let motive_univ_name = &brec_level_params[0];
        let motive_level = Level::param(motive_univ_name.clone());
        let ind_levels = make_ind_levels(decl);
        let below_levels = make_below_levels(motive_univ_name, &ind_levels);
        let ind_univ = get_ind_universe(self, &ind_type.type_);

        let brec_type = build_brec_on_type(
            ind_type,
            decl,
            ind_name,
            &ind_levels,
            &motive_level,
            &below_name,
            &below_levels,
        );
        let value = build_brec_on_value(
            ind_type,
            decl,
            ctor_infos,
            ind_name,
            &ind_univ,
            &ind_levels,
            &motive_level,
            &below_name,
            &below_levels,
        );

        Ok(Declaration::Definition {
            name: Name::from_string(&format!("{ind_name}.brecOn")),
            level_params: brec_level_params,
            type_: brec_type,
            value,
            is_reducible: true,
        })
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

/// Build the type expression for `.brecOn`.
fn build_brec_on_type(
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    ind_name: &Name,
    ind_levels: &[Level],
    motive_level: &Level,
    below_name: &Name,
    below_levels: &[Level],
) -> Expr {
    let mut b2 = EnvDeclBuilder::new();
    let (p2_ids, p2_fvs) = bind_params(&mut b2, &ind_type.type_, decl.num_params);
    let ind_app2 = build_ind_app(ind_name, ind_levels, &p2_fvs);
    let motive_ty2 = Expr::arrow(
        ind_app2.clone(),
        Expr::from_kind(ExprKind::Sort(motive_level.clone())),
    );
    let (motive_id2, motive_fv2) = b2.fresh_local(motive_ty2.clone());
    let (major_id2, major_fv2) = b2.fresh_local(ind_app2.clone());

    let mut below_app2 = Expr::const_(below_name.clone(), below_levels.to_vec());
    for fv in &p2_fvs {
        below_app2 = Expr::app(below_app2, fv.clone());
    }
    below_app2 = Expr::app(below_app2, motive_fv2.clone());

    let f_type2 = build_f_type(&b2, &ind_app2, &below_app2, &motive_fv2);
    let (f_id2, _) = b2.fresh_local(f_type2.clone());

    let result_ty = Expr::app(motive_fv2.clone(), major_fv2);
    let mut brec_type = result_ty;
    brec_type = b2.mk_pi(f_id2, BinderInfo::Default, f_type2, brec_type);
    brec_type = b2.mk_pi(major_id2, BinderInfo::Default, ind_app2.clone(), brec_type);
    brec_type = b2.mk_pi(motive_id2, BinderInfo::Implicit, motive_ty2, brec_type);
    for i in (0..p2_ids.len()).rev() {
        let pty = get_nth_pi_domain(&ind_type.type_, i);
        brec_type = b2.mk_pi(p2_ids[i], BinderInfo::Implicit, pty, brec_type);
    }
    b2.finish(brec_type)
}

/// Build the value expression for `.brecOn`: `fun {motive} t F => F t (below t)`.
fn build_brec_on_value(
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    ctor_infos: &[CtorInfo],
    ind_name: &Name,
    ind_univ: &Level,
    ind_levels: &[Level],
    motive_level: &Level,
    below_name: &Name,
    below_levels: &[Level],
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (param_ids, param_fvars) = bind_params(&mut b, &ind_type.type_, decl.num_params);
    let ind_app = build_ind_app(ind_name, ind_levels, &param_fvars);
    let motive_sort = Expr::from_kind(ExprKind::Sort(motive_level.clone()));
    let motive_ty = Expr::arrow(ind_app.clone(), motive_sort);
    let (motive_id, motive_fv) = b.fresh_local(motive_ty.clone());
    let (major_id, major_fv) = b.fresh_local(ind_app.clone());

    let mut below_app = Expr::const_(below_name.clone(), below_levels.to_vec());
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

    let rec_name = Name::from_string(&format!("{ind_name}.rec"));
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
    rec_app = Expr::app(rec_app, major_fv.clone());
    let value_body = Expr::proj(Name::from_string("PProd"), 0, rec_app);

    let mut value = value_body;
    value = b.mk_lam(f_id, BinderInfo::Default, f_type, value);
    value = b.mk_lam(major_id, BinderInfo::Default, ind_app.clone(), value);
    value = b.mk_lam(motive_id, BinderInfo::Implicit, motive_ty, value);
    for i in (0..param_ids.len()).rev() {
        let pty = get_nth_pi_domain(&ind_type.type_, i);
        value = b.mk_lam(param_ids[i], BinderInfo::Implicit, pty, value);
    }
    b.finish(value)
}
