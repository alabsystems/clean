// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The one rule Lean applies to the `termination_by` measures of a `mutual`
//! block that Clean's structural lift never looked at.
//!
//! Lean lowers a `mutual` block whose members carry `termination_by`
//! measures by well-founded recursion over ONE packed relation, so the
//! measures must all have the same type (`checkCodomains`,
//! `Lean/Elab/PreDefinition/WF/Rel.lean`): "The termination measures of
//! mutually recursive functions must have the same return type". Clean lowers
//! such a block structurally (gap G23, [`super::mutual_lift`]) and elaborated
//! no measure, so it accepted a block Lean refuses: lean4
//! `tests/elab_fail/mutwftypemismatch.lean`, a `Nat` measure beside a `Prop`
//! one, and a `Nat` measure beside a `Fin fixed` one. Before the lift landed
//! (318e491ac) every recursive `mutual` block was refused, so that agreement
//! with Lean had been vacuous.
//!
//! [`ElabCtx::check_mutual_measure_types`] elaborates each member's measure
//! where Lean's `TerminationMeasure.elab` does — the header parameters in
//! scope, the measure's own binders on the first parameters after the colon —
//! and refuses the block when two measure types differ. It only refuses: a
//! measure Clean cannot elaborate leaves the block to the structural lowering,
//! as before. Two CLOSED measure types are compared by def-eq; two that
//! depend on header parameters are compared syntactically after renaming the
//! shared parameter prefix, so a dependent pair equal only up to reduction is
//! reported as different. Lean refuses that pair too (with its own message,
//! not this one), so the verdict matches and only the wording differs.

use clean_kernel::{Expr, ExprKind, FVarId, Name};
use clean_parser::{SurfaceBinder, SurfaceDecl, SurfaceExpr, SurfaceName, TerminationKind};

use super::mutual_lift::PreDef;
use super::ElabCtx;
use crate::ElabError;

/// One member's elaborated measure type, with the locals it was elaborated over.
struct MeasureType {
    name: Name,
    ty: Expr,
    /// The header parameters' locals and types, in order (auto-implicits first).
    header: Vec<(FVarId, Expr)>,
    /// Every local the measure was elaborated over (header, then its binders).
    locals: Vec<FVarId>,
}

impl MeasureType {
    /// The measure's type mentions none of the member's parameters.
    fn is_closed(&self) -> bool {
        !self
            .locals
            .iter()
            .any(|fvar| self.ty.abstract_fvar(*fvar) != self.ty)
    }
}

impl<'a> ElabCtx<'a> {
    /// Refuse a `mutual` block whose members' well-founded `termination_by`
    /// measures have different types, as Lean does (module docs).
    ///
    /// `predefs` and `auto_implicit_counts` are indexed like the block's
    /// `def`/`theorem` members, in order.
    pub(super) fn check_mutual_measure_types(
        &mut self,
        decls: &[SurfaceDecl],
        predefs: &[PreDef],
        auto_implicit_counts: &[usize],
    ) -> Result<(), ElabError> {
        let mut measured: Vec<MeasureType> = Vec::new();
        let mut index = 0;
        for decl in decls {
            let (binders, termination) = match decl {
                SurfaceDecl::Def {
                    binders,
                    termination,
                    ..
                }
                | SurfaceDecl::Theorem {
                    binders,
                    termination,
                    ..
                } => (binders, termination),
                _ => continue,
            };
            let (Some(predef), Some(&autos)) =
                (predefs.get(index), auto_implicit_counts.get(index))
            else {
                return Ok(());
            };
            index += 1;
            let Some(tb) = termination.termination_by.as_ref() else {
                continue;
            };
            if !matches!(tb.kind, TerminationKind::WellFounded) {
                continue;
            }
            let Some(measure) = tb.measure.as_deref() else {
                continue;
            };
            match self.elab_member_measure_type(predef, autos, binders, &tb.params, measure) {
                Some(measure_type) => measured.push(measure_type),
                // Clean cannot elaborate this measure: nothing to compare.
                None => return Ok(()),
            }
        }
        let Some((first, rest)) = measured.split_first() else {
            return Ok(());
        };
        for other in rest {
            if !self.measure_types_agree(first, other) {
                return Err(ElabError::MutualMeasureTypeMismatch {
                    first: first.name.to_string(),
                    first_ty: first.ty.to_string(),
                    other: other.name.to_string(),
                    other_ty: other.ty.to_string(),
                });
            }
        }
        Ok(())
    }

    /// The type of `measure`, elaborated over `predef`'s header parameters
    /// (`autos` auto-implicits, then `binders`) and, under `vars`, the first
    /// parameters after the colon; `None` when Clean cannot elaborate it.
    fn elab_member_measure_type(
        &mut self,
        predef: &PreDef,
        autos: usize,
        binders: &[SurfaceBinder],
        vars: &[SurfaceName],
        measure: &SurfaceExpr,
    ) -> Option<MeasureType> {
        let header_len = autos + binders.len();
        let wanted = header_len + vars.len();
        let mut ty = predef.ty.clone();
        let mut locals: Vec<(FVarId, Expr)> = Vec::with_capacity(wanted);
        for position in 0..wanted {
            let ExprKind::Pi(_, domain, body) = ty.kind() else {
                break;
            };
            let name = if position < autos {
                SurfaceName::unspellable(
                    "measure_header",
                    u64::try_from(position).unwrap_or(u64::MAX),
                )
            } else if position < header_len {
                binders[position - autos].name.clone()
            } else {
                vars[position - header_len].clone()
            };
            let (domain, body) = (domain.as_ref().clone(), body.as_ref().clone());
            let fvar = self.push_local(name, domain.clone());
            locals.push((fvar, domain));
            ty = body.instantiate(&Expr::fvar(fvar));
        }
        let elaborated = if locals.len() == wanted {
            self.with_term_body_scope(|this| this.elaborate(measure))
                .ok()
                .map(|expr| {
                    self.metas
                        .instantiate_levels(&self.metas.instantiate(&expr))
                })
                .and_then(|expr| self.infer_type_full(&expr).ok())
                .map(|ty| self.metas.instantiate_levels(&self.metas.instantiate(&ty)))
        } else {
            None
        };
        for _ in &locals {
            self.pop_local();
        }
        let ty = elaborated?;
        Some(MeasureType {
            name: predef.name.clone(),
            ty,
            header: locals[..header_len].to_vec(),
            locals: locals.into_iter().map(|(fvar, _)| fvar).collect(),
        })
    }

    /// Whether two members' measure types may be the same type. Closed types
    /// are compared definitionally. A type over the parameters is the same
    /// only as the same term over header parameters of the same types at the
    /// same positions (Lean compares after instantiating the block's fixed
    /// parameters, which this reading stands in for); anything else is a
    /// different type, as Lean finds it.
    fn measure_types_agree(&self, first: &MeasureType, other: &MeasureType) -> bool {
        if first.is_closed() && other.is_closed() {
            return self.is_def_eq(&first.ty, &other.ty);
        }
        let mut renamed = other.ty.clone();
        let mut renames: Vec<(FVarId, Expr)> = Vec::new();
        for ((theirs, their_ty), (ours, our_ty)) in other.header.iter().zip(&first.header) {
            let mut their_ty = their_ty.clone();
            for (from, to) in &renames {
                their_ty = their_ty.subst_fvar(*from, to);
            }
            if their_ty != *our_ty {
                break;
            }
            renames.push((*theirs, Expr::fvar(*ours)));
        }
        for (from, to) in &renames {
            renamed = renamed.subst_fvar(*from, to);
        }
        renamed == first.ty
    }
}

impl ElabCtx<'_> {
    /// Resolve a structural hint in Lean's scope: written header binders,
    /// followed by the clause's names for arguments after the colon.
    /// Never infer a different decreasing parameter when an explicit hint fails.
    pub(super) fn structural_hint_index(
        hint: &clean_parser::TerminationBy,
        header: &[SurfaceBinder],
        total: usize,
    ) -> Result<Option<usize>, String> {
        let TerminationKind::Structural(param) = &hint.kind else {
            return Ok(None);
        };
        if hint.params.len() > total.saturating_sub(header.len()) {
            return Err("too many parameters in `termination_by structural`".into());
        }
        if param.is_anonymous() {
            return Err("`termination_by structural` must select a parameter".into());
        }
        let index = hint
            .params
            .iter()
            .rposition(|p| p == param)
            .map(|i| header.len() + i)
            .or_else(|| header.iter().rposition(|b| &b.name == param));
        index
            .map(Some)
            .ok_or_else(|| format!("termination_by structural {param} (unknown parameter)"))
    }
}
