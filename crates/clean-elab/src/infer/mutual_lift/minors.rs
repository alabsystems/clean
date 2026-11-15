// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The minor premises of a lifted block (design §5.3 step 6 and §5.4).
//!
//! * An owned slot's minor is the tuple of its owners' specialized bodies:
//!   each owner's body with its major premise replaced by the constructor,
//!   the resulting redexes contracted, and every sibling call on a field
//!   replaced by that field's (projected) induction hypothesis.
//! * A transparent intermediate's minor is the tuple of its fields'
//!   induction hypotheses.
//! * A `PUnit` slot's minor is `PUnit.unit`.
//!
//! Before calls are replaced, a case split on a field of a transparent
//! intermediate (`match hd with | (_, c) => … c …`, elaborated as
//! `Prod.casesOn M hd (fun s c => …)`) is opened into its projections
//! (`… hd.2 …`): `S.casesOn M x f ≡ f x.1 … x.n` by structure η, a kernel
//! definitional equality, so the kernel's re-check of the member covers it.
//! Only a split whose branch calls a member is opened.

use clean_kernel::inductive::RecursorArgOrder;
use clean_kernel::{Environment, Expr, ExprFolder, ExprKind, FVarId};
use clean_parser::SurfaceName;

use super::assemble::{abstract_params, Param};
use super::motives::{Layout, Motives, SlotPlan};
use super::replace::{CallShape, FieldIh, IhReplacer};
use super::slots::MinorShape;
use super::specialize::{head_beta, strip_mdata, Specializer};
use super::LiftError;
use crate::infer::ElabCtx;

/// What a minor needs to know about the block.
pub(super) struct MinorCtx<'a> {
    pub(super) layout: &'a Layout<'a>,
    pub(super) motives: &'a Motives,
    pub(super) shapes: &'a [CallShape],
    pub(super) fixed: &'a [FVarId],
    pub(super) unit: Option<&'a Expr>,
}

impl ElabCtx<'_> {
    pub(super) fn build_minor(
        &mut self,
        ctx: &MinorCtx<'_>,
        shape: &MinorShape,
        minor_ty: &Expr,
    ) -> Result<Expr, LiftError> {
        let depth = self.locals.len();
        let result = self.build_minor_inner(ctx, shape, minor_ty);
        // On a refusal the minor's locals stay until the lift renders the
        // message (it names the offending call's fields); the lift truncates
        // everything it pushed when it returns.
        if result.is_ok() {
            self.locals.truncate(depth);
        }
        result
    }

    fn build_minor_inner(
        &mut self,
        ctx: &MinorCtx<'_>,
        shape: &MinorShape,
        minor_ty: &Expr,
    ) -> Result<Expr, LiftError> {
        let mut binders: Vec<Param> = Vec::new();
        let mut cursor = minor_ty.clone();
        while binders.len() < shape.num_fields + shape.ihs.len() {
            let ExprKind::Pi(bd, dom, body) = cursor.kind() else {
                return Err(LiftError::block("malformed minor premise".to_string()));
            };
            let ty = head_beta(dom);
            let fvar = self.push_local(SurfaceName::generated_path("y✝"), ty.clone());
            binders.push(Param {
                fvar,
                info: bd.info,
                ty,
            });
            cursor = body.instantiate(&Expr::fvar(fvar));
        }
        let kind = &ctx.motives.kind;
        let ihs = &binders[shape.num_fields..];
        let body = match &ctx.motives.plans[shape.slot] {
            SlotPlan::Unit { .. } => ctx
                .unit
                .cloned()
                .ok_or_else(|| LiftError::block("an unused slot needs `PUnit.unit`".to_string()))?,
            SlotPlan::Intermediate { .. } => {
                let tys: Vec<Expr> = ihs.iter().map(|p| p.ty.clone()).collect();
                let vals: Vec<Expr> = ihs.iter().map(|p| Expr::fvar(p.fvar)).collect();
                kind.val(&tys, &vals)
            }
            SlotPlan::Owned { owners } => {
                let fields: Vec<Expr> = binders[..shape.num_fields]
                    .iter()
                    .map(|p| Expr::fvar(p.fvar))
                    .collect();
                let ctor_app = Expr::apps(shape.ctor_head.clone(), fields);
                let field_ihs: Vec<FieldIh> = shape
                    .ihs
                    .iter()
                    .zip(ihs)
                    .map(|((field_idx, slot), ih)| FieldIh {
                        field: binders[*field_idx].fvar,
                        slot: *slot,
                        ih: ih.fvar,
                    })
                    .collect();
                let mut tys = Vec::with_capacity(owners.len());
                let mut vals = Vec::with_capacity(owners.len());
                for owner in owners {
                    let (ty, val) = self.specialize_owner(ctx, *owner, &ctor_app, &field_ihs)?;
                    tys.push(ty);
                    vals.push(val);
                }
                kind.val(&tys, &vals)
            }
        };
        Ok(abstract_params(&binders, body, false))
    }

    /// Owner `i`'s body at `ctor_app`, its sibling calls replaced: `(type,
    /// fun rest => body)`.
    fn specialize_owner(
        &mut self,
        ctx: &MinorCtx<'_>,
        i: usize,
        ctor_app: &Expr,
        field_ihs: &[FieldIh],
    ) -> Result<(Expr, Expr), LiftError> {
        let layout = ctx.layout;
        let def = layout.defs[i];
        let major = layout.major(i).fvar;
        let budget = || {
            LiftError::member(
                &def.name,
                "specializing its body to a constructor did not finish within budget".to_string(),
            )
        };
        let body = layout.opened.bodies[i].subst_fvar(major, ctor_app);
        let mut reduced = Specializer::new(self.env).run(&body).ok_or_else(budget)?;
        // Open case splits on transparent-intermediate fields.
        let through: Vec<FVarId> = field_ihs
            .iter()
            .filter(|f| {
                matches!(
                    ctx.motives.plans[f.slot],
                    SlotPlan::Intermediate { .. } | SlotPlan::Unit { reason: Some(_) }
                )
            })
            .map(|f| f.field)
            .collect();
        if !through.is_empty() {
            let members: Vec<FVarId> = ctx.shapes.iter().map(|s| s.fvar).collect();
            let mut opener = SplitOpener {
                env: self.env,
                fields: &through,
                members: &members,
                opened: false,
            };
            let opened = opener.fold_expr(&reduced);
            if opener.opened {
                reduced = Specializer::new(self.env).run(&opened).ok_or_else(budget)?;
            }
        }
        let mut replacer = IhReplacer {
            members: ctx.shapes,
            fixed: ctx.fixed,
            fields: field_ihs,
            plans: &ctx.motives.plans,
            kind: &ctx.motives.kind,
            major_premise: ctor_app,
            refusal: None,
        };
        let replaced = replacer.fold_expr(&reduced);
        if let Some(refusal) = replacer.refusal {
            return Err(LiftError::Call {
                caller: def.name.clone(),
                refusal,
            });
        }
        let rest: Vec<Param> = layout.rest[i]
            .iter()
            .map(|p| Param {
                fvar: p.fvar,
                info: p.info,
                ty: p.ty.subst_fvar(major, ctor_app),
            })
            .collect();
        let ty = layout.body_tys[i].subst_fvar(major, ctor_app);
        Ok((ty, abstract_params(&rest, replaced, false)))
    }
}

/// Opens `S.casesOn M x f` / `S.rec M f x` on a listed field `x` of a
/// single-constructor structure `S` into `f x.1 … x.n` when `f` calls a
/// member.
struct SplitOpener<'a> {
    env: &'a Environment,
    fields: &'a [FVarId],
    members: &'a [FVarId],
    opened: bool,
}

impl SplitOpener<'_> {
    fn open(&self, name: &clean_kernel::Name, args: &[Expr]) -> Option<Expr> {
        let rec = self.env.get_recursor(name)?;
        if rec.num_minors != 1 || rec.num_indices != 0 || rec.num_motives != 1 {
            return None;
        }
        let rule = rec.rules.first()?;
        let ctor = self.env.get_constructor(&rule.constructor_name)?;
        let ind = self.env.get_inductive(&ctor.inductive_name)?;
        if ind.constructor_names.len() != 1 || ind.num_indices != 0 {
            return None;
        }
        let np = rec.num_params as usize;
        let (major_idx, minor_idx, extras) = match rec.arg_order {
            RecursorArgOrder::MajorAfterMinors => (np + 2, np + 1, np + 3),
            RecursorArgOrder::MajorAfterMotive => (np + 1, np + 2, np + 3),
        };
        if args.len() < extras {
            return None;
        }
        let ExprKind::FVar(major) = strip_mdata(&args[major_idx]).kind() else {
            return None;
        };
        if !self.fields.contains(major) {
            return None;
        }
        let minor = &args[minor_idx];
        if super::scc::mentioned_members(self.members, &[minor]).is_empty() {
            return None;
        }
        let mut cur = minor.clone();
        for idx in 0..ctor.num_fields {
            let ExprKind::Lam(_, _, body) = cur.kind() else {
                return None;
            };
            let field = Expr::proj(ctor.inductive_name.clone(), idx, Expr::fvar(*major));
            cur = body.instantiate(&field);
        }
        Some(Expr::apps(cur, args[extras..].iter().cloned()))
    }
}

impl ExprFolder for SplitOpener<'_> {
    fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
        let whole = Expr::app(f.clone(), a.clone());
        if let ExprKind::Const(name, _) = whole.get_app_fn().kind() {
            let args: Vec<Expr> = whole.get_app_args().into_iter().cloned().collect();
            if let Some(opened) = self.open(name, &args) {
                self.opened = true;
                return self.fold_expr(&opened);
            }
        }
        Expr::app(self.fold_expr(f), self.fold_expr(a))
    }
}
