// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-constructor equations of a lifted DEFINITION member (design §5.5 item
//! 1, brick B3), the rules `simp [f]` / `simp only [f] at h` rewrite with.
//!
//! For each constructor `c` of the member's major premise type:
//!
//! ```text
//!   ∀ params… fields…, f params…[major := c params fields…] = rhs
//! ```
//!
//! where `rhs` is the member's PRE-DEFINITION body (siblings and itself still
//! forward locals, later replaced by the member constants) with the major
//! premise replaced by the constructor and the case splits that become redexes
//! contracted by the lift's own [`Specializer`]. The right-hand side therefore
//! speaks in surface form — sibling calls are member applications, never a
//! recursor — with no fold-back step. A field of a single-constructor
//! structure type that the body still case-splits (`| (_, c) :: fs => …`) is
//! split into its constructor first, as Lean's equation for that arm is.
//!
//! Each equation is definitionally true: δ of the member, ι of the shared
//! recursor and δ of each sibling call give both sides the same normal form.
//! It is stored as a CLOSED statement and offered to simp with an `Eq.refl`
//! proof template that `proof_matches_rewrite` and `close_goal` re-check in the
//! kernel, so a wrong equation refuses a rewrite; it cannot prove anything.
//! Synthesis is all-or-nothing per member: a constructor whose equation does
//! not synthesize leaves the member with no equations at all.

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::SurfaceName;

use super::assemble::{abstract_params, Opened, Param};
use super::specialize::{eliminates_fvar, strip_mdata, Specializer};
use super::PreDef;
use crate::infer::ElabCtx;

/// A field split into the constructor of its single-constructor structure.
struct Split {
    fvar: FVarId,
    ctor_app: Expr,
    fields: Vec<Param>,
}

impl ElabCtx<'_> {
    /// The per-constructor equations of member `i` (major parameter `major`),
    /// as closed statements over the block's forward locals; empty for a
    /// theorem or when any constructor's equation does not synthesize.
    pub(super) fn constructor_equations(
        &mut self,
        def: &PreDef,
        opened: &Opened,
        i: usize,
        major: usize,
    ) -> Vec<Expr> {
        if def.is_theorem {
            return Vec::new();
        }
        let depth = self.locals.len();
        let out = self.constructor_equations_inner(def, opened, i, major);
        self.locals.truncate(depth);
        out.unwrap_or_default()
    }

    fn constructor_equations_inner(
        &mut self,
        def: &PreDef,
        opened: &Opened,
        i: usize,
        major: usize,
    ) -> Option<Vec<Expr>> {
        let params = opened.params.get(i)?;
        let major_param = params.get(major)?.clone();
        let major_ty = self.metas.instantiate(&major_param.ty);
        let ExprKind::Const(ind_name, levels) = strip_mdata(major_ty.get_app_fn()).kind() else {
            return None;
        };
        let ind = self.env.get_inductive(ind_name)?.clone();
        let ind_args: Vec<Expr> = major_ty.get_app_args().into_iter().cloned().collect();
        if ind.num_indices != 0 || ind_args.len() != ind.num_params as usize {
            return None;
        }
        let levels: Vec<Level> = levels.to_vec();
        let mut out = Vec::with_capacity(ind.constructor_names.len());
        for ctor_name in &ind.constructor_names {
            let (ctor_app, fields) = self.open_constructor(ctor_name, &levels, &ind_args)?;
            let body = opened.bodies[i].subst_fvar(major_param.fvar, &ctor_app);
            let mut rhs = Specializer::new(self.env).run(&body)?;
            // Split the structure fields the body still case-splits.
            let mut substs: Vec<(FVarId, Expr)> = vec![(major_param.fvar, ctor_app)];
            let mut binders: Vec<Param> = Vec::with_capacity(fields.len());
            for field in fields {
                match self.split_field(&rhs, &field) {
                    Some(split) => {
                        rhs = Specializer::new(self.env)
                            .run(&rhs.subst_fvar(split.fvar, &split.ctor_app))?;
                        substs.push((split.fvar, split.ctor_app));
                        binders.extend(split.fields);
                    }
                    None => binders.push(field),
                }
            }
            let subst_all = |e: &Expr| {
                substs
                    .iter()
                    .fold(e.clone(), |acc, (fvar, val)| acc.subst_fvar(*fvar, val))
            };
            let mut all: Vec<Param> = Vec::with_capacity(params.len() + binders.len());
            let mut args: Vec<Expr> = Vec::with_capacity(params.len());
            for (pos, param) in params.iter().enumerate() {
                args.push(subst_all(&Expr::fvar(param.fvar)));
                if pos == major {
                    all.extend(binders.iter().cloned());
                } else {
                    all.push(Param {
                        fvar: param.fvar,
                        info: param.info,
                        ty: subst_all(&param.ty),
                    });
                }
            }
            let result_ty = subst_all(&opened.codomains[i]);
            let level = self.infer_sort(&result_ty).ok()?;
            let level = self.metas.instantiate_level(&level);
            let lhs = Expr::apps(Expr::fvar(def.fvar), args);
            let eq = Expr::apps(
                Expr::const_str_levels("Eq", vec![level]),
                [result_ty, lhs, rhs],
            );
            out.push(abstract_params(&all, eq, true));
        }
        Some(out)
    }

    /// `c params fields…` over fresh field locals.
    fn open_constructor(
        &mut self,
        ctor_name: &clean_kernel::Name,
        levels: &[Level],
        params: &[Expr],
    ) -> Option<(Expr, Vec<Param>)> {
        let ctor = self.env.get_constructor(ctor_name)?.clone();
        if ctor.level_params.len() != levels.len() || ctor.num_params as usize != params.len() {
            return None;
        }
        let mut ty = ctor
            .type_
            .instantiate_level_params_direct(&ctor.level_params, levels);
        for param in params {
            let ExprKind::Pi(_, _, body) = ty.kind() else {
                return None;
            };
            ty = body.instantiate(param);
        }
        let mut fields = Vec::with_capacity(ctor.num_fields as usize);
        for idx in 0..ctor.num_fields {
            let ExprKind::Pi(bd, dom, body) = ty.kind() else {
                return None;
            };
            let name = SurfaceName::unspellable("y✝", u64::from(idx));
            let fvar = self.push_local(name, dom.as_ref().clone());
            fields.push(Param {
                fvar,
                info: if bd.info == BinderInfo::InstImplicit {
                    BinderInfo::InstImplicit
                } else {
                    BinderInfo::Default
                },
                ty: dom.as_ref().clone(),
            });
            ty = body.instantiate(&Expr::fvar(fvar));
        }
        let app = Expr::apps(
            Expr::const_(ctor_name.clone(), levels.to_vec()),
            params
                .iter()
                .cloned()
                .chain(fields.iter().map(|f| Expr::fvar(f.fvar))),
        );
        Some((app, fields))
    }

    /// `field` split into its structure's constructor, when its type is a
    /// single-constructor, index-free, non-recursive inductive and `rhs` still
    /// case-splits on it.
    fn split_field(&mut self, rhs: &Expr, field: &Param) -> Option<Split> {
        if !eliminates_fvar(self.env, rhs, field.fvar) {
            return None;
        }
        let ty = self.metas.instantiate(&field.ty);
        let ExprKind::Const(name, levels) = strip_mdata(ty.get_app_fn()).kind() else {
            return None;
        };
        let ind = self.env.get_inductive(name)?;
        if ind.constructor_names.len() != 1 || ind.num_indices != 0 || ind.is_recursive {
            return None;
        }
        let ctor_name = ind.constructor_names[0].clone();
        let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
        let levels = levels.to_vec();
        let (ctor_app, fields) = self.open_constructor(&ctor_name, &levels, &args)?;
        Some(Split {
            fvar: field.fvar,
            ctor_app,
            fields,
        })
    }
}
