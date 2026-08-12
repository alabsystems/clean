// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deep induction principles for nested inductives — the `Scheme All`
//! analog (rung P4, `designs/2026-08-06-deep-induction-scheme-all.md`).
//!
//! For a nested `T` (e.g. `Term | app : List Term → Term`), the
//! post-restore recursor is MULTI-MOTIVE — the user must invent a
//! free-standing container motive. This generator produces the usable
//! elementwise principle instead:
//!
//! ```text
//! Term.deep_ind : ∀ (motive : Term → Prop),
//!   (∀ (ts : List Term), List.All Term motive ts → motive (Term.app ts)) →
//!   ∀ (t : Term), motive t
//! ```
//!
//! Proof: ONE application of `T.rec` with the container motive CHOSEN as
//! `λ x. C.All ā P̄ x` — the aux minors then discharge by the `C.All`
//! constructors with IHs slotted in (identified BY TYPE, never position).
//! Every defeq obligation is pure beta; the kernel's `is_def_eq` closes
//! them at `add_decl`. Non-trust-bearing: the caller registers the All
//! family through checked `add_inductive` and the theorem through checked
//! `add_decl`.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::RecursorArgOrder;
use crate::level::Level;
use crate::name::Name;

use super::decl_builder::EnvDeclBuilder;
use super::rec_apply::{close_lams, walk_telescope, RecApply};
use super::types::Declaration;
use super::Environment;

/// Result of deep-induction synthesis.
#[derive(Debug)]
#[non_exhaustive]
pub enum DeepIndOutcome {
    /// Declarations to register, in order: All families (checked
    /// `add_inductive`) first, then the theorems (checked `add_decl`).
    Decls {
        /// Container All families still missing from the environment.
        all_families: Vec<crate::inductive::InductiveDecl>,
        /// The `T.deep_ind` theorem(s).
        theorems: Vec<Declaration>,
    },
    /// A declared v1 limitation; callers skip additively (or loudly, for
    /// an explicit `deriving DeepInduction`).
    OutOfScope {
        /// Stable human-readable reason.
        reason: String,
    },
}

/// Synthesis invariant violations (caller must not register anything).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DeepIndError {
    /// The synthesizer's own coherence checks failed.
    #[error("deep-induction synthesis invariant violated: {0}")]
    Invariant(String),
}

fn inv(msg: impl Into<String>) -> DeepIndError {
    DeepIndError::Invariant(msg.into())
}

fn oos(reason: impl Into<String>) -> Result<DeepIndOutcome, DeepIndError> {
    Ok(DeepIndOutcome::OutOfScope {
        reason: reason.into(),
    })
}

impl Environment {
    /// Synthesize `T.deep_ind` for a registered nested inductive `T`.
    ///
    /// Read-only: returns the declarations for the caller to register
    /// through the checked paths. Declared v1 limitations come back as
    /// [`DeepIndOutcome::OutOfScope`]; coherence failures as
    /// [`DeepIndError::Invariant`].
    ///
    /// # Errors
    ///
    /// [`DeepIndError::Invariant`] when the synthesizer's own checks fail.
    pub fn synthesize_deep_induction(&self, ind: &Name) -> Result<DeepIndOutcome, DeepIndError> {
        // ── Target gates ───────────────────────────────────────────────────
        let Some(tv) = self.inductives.get(ind) else {
            return oos(format!("{ind} is not a registered inductive"));
        };
        if !tv.is_nested {
            return oos(format!("{ind} is not a nested inductive"));
        }
        if tv.all_names.len() != 1 {
            return oos(format!("{ind} is part of a mutual block (v1 single)"));
        }
        if tv.num_indices != 0 {
            return oos(format!("{ind} is indexed (v1 non-indexed)"));
        }
        if !tv.is_large_elim {
            return oos(format!("{ind} has restricted elimination (v1 Type-valued)"));
        }
        let deep_name = Name::from_string(&format!("{ind}.deep_ind"));
        if self.constants.contains_key(&deep_name) {
            return oos(format!("{deep_name} already exists"));
        }
        if self.get_const(&Name::from_string("True")).is_none()
            || self.get_const(&Name::from_string("True.intro")).is_none()
        {
            return oos("True/True.intro are not registered in this environment");
        }
        let rec_name = Name::from_string(&format!("{ind}.rec"));
        let Some(rec) = self.get_recursor(&rec_name).cloned() else {
            return oos(format!("{rec_name} is not registered"));
        };
        if rec.arg_order != RecursorArgOrder::MajorAfterMinors {
            return oos(format!("{rec_name} has a non-standard argument order"));
        }
        if rec.num_motives != 2 {
            return oos(format!(
                "{ind} has {} motives (v1 supports single-level nesting: exactly 2)",
                rec.num_motives
            ));
        }
        // Elim level: rec carries [elim] ++ T's own level params.
        if rec.level_params.len() != tv.level_params.len() + 1 {
            return oos(format!(
                "{rec_name} does not carry a free elimination level"
            ));
        }
        let rec_levels: Vec<Level> = std::iter::once(Level::zero())
            .chain(tv.level_params.iter().map(|n| Level::param(n.clone())))
            .collect();
        let rec_ty = rec
            .type_
            .instantiate_level_params_direct(&rec.level_params, &rec_levels);

        // ── Walk the recursor, building the proof ──────────────────────────
        let mut b = EnvDeclBuilder::new();
        let mut ra = RecApply::new(Expr::const_(rec_name.clone(), rec_levels), rec_ty);

        // Params p̄.
        let np = rec.num_params as usize;
        let mut p_locals = Vec::with_capacity(np);
        for _ in 0..np {
            let dom = ra.peek_domain().map_err(inv)?;
            let (id, fv) = b.fresh_local(dom.clone());
            ra.apply(fv.clone()).map_err(inv)?;
            p_locals.push((id, fv, dom));
        }
        let t_applied = Expr::apps(
            Expr::const_(
                ind.clone(),
                tv.level_params
                    .iter()
                    .map(|n| Level::param(n.clone()))
                    .collect::<Vec<_>>(),
            ),
            p_locals.iter().map(|(_, fv, _)| fv.clone()),
        );
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Motive 1: the user's motive.
        {
            let dom = ra.peek_domain().map_err(inv)?;
            // Sanity: motive over T p̄.
            let ExprKind::Pi(_, major, _) = &dom.kind else {
                return Err(inv("motive slot 1 is not a Pi"));
            };
            if **major != t_applied {
                return Err(inv("motive slot 1 is not over the target type"));
            }
        }
        let motive_ty = Expr::arrow(t_applied.clone(), prop.clone());
        let (motive_id, motive_fv) = b.fresh_local(motive_ty.clone());
        ra.apply(motive_fv.clone()).map_err(inv)?;

        // Motive 2: the container motive, chosen as `λ x. C.All ā P̄ x`.
        let dom2 = ra.peek_domain().map_err(inv)?;
        let ExprKind::Pi(_, c_major, _) = &dom2.kind else {
            return Err(inv("motive slot 2 is not a Pi"));
        };
        let c_major = (**c_major).clone();
        let ExprKind::Const(container, c_levels) = &c_major.get_app_fn().kind else {
            return oos("container motive major is not constant-headed");
        };
        let container = container.clone();
        let c_levels: Vec<Level> = c_levels.to_vec();
        let c_args: Vec<Expr> = c_major.get_app_args().into_iter().cloned().collect();
        // Predicates: elementwise `motive` where the arg is T p̄; True-fill
        // where the arg mentions no block member; anything else declines.
        let mut preds = Vec::with_capacity(c_args.len());
        for a in &c_args {
            if *a == t_applied {
                preds.push(motive_fv.clone());
            } else if crate::inductive::mentions_name(a, ind) {
                return oos(format!(
                    "container argument mentions {ind} outside the elementwise position (v1)"
                ));
            } else {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (x_id, _x_fv) = cb.fresh_local(a.clone());
                let body = Expr::const_(Name::from_string("True"), Vec::new());
                let lam = cb.mk_lam(x_id, BinderInfo::Default, a.clone(), body);
                preds.push(cb.finish_child(lam));
            }
        }
        // The All family for the container.
        let plan = match self.all_family_decl(&container) {
            Ok(p) => p,
            Err(reason) => return oos(reason),
        };
        let all_applied = |target: Expr| {
            Expr::apps(
                Expr::const_(plan.all_name.clone(), c_levels.clone()),
                c_args
                    .iter()
                    .cloned()
                    .chain(preds.iter().cloned())
                    .chain(std::iter::once(target)),
            )
        };
        {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let (x_id, x_fv) = cb.fresh_local(c_major.clone());
            let body = all_applied(x_fv);
            let motive2 =
                cb.finish_child(cb.mk_lam(x_id, BinderInfo::Default, c_major.clone(), body));
            ra.apply(motive2).map_err(inv)?;
        }

        // Minor slots: T-ctors become bound hypotheses; container ctors are
        // discharged by the All constructors.
        let mut hyp_locals = Vec::new();
        for _ in 0..rec.num_minors {
            let dom = ra.peek_domain().map_err(inv)?;
            let minor = self.build_deep_minor(
                &mut b,
                ind,
                &container,
                &c_levels,
                &c_args,
                &preds,
                &motive_fv,
                &all_applied,
                &dom,
                &mut hyp_locals,
            )?;
            ra.apply(minor).map_err(inv)?;
        }

        // Major.
        let (t_id, t_fv) = b.fresh_local(t_applied.clone());
        ra.apply(t_fv.clone()).map_err(inv)?;
        let expected = Expr::app(motive_fv.clone(), t_fv.clone());
        if ra.cursor != expected {
            return Err(inv(format!(
                "residual recursor type is not `motive t` for {ind}"
            )));
        }

        // ── Close statement and proof ──────────────────────────────────────
        let mut binders = Vec::new();
        for (id, fv, ty) in &p_locals {
            binders.push((*id, fv.clone(), ty.clone(), BinderInfo::Implicit));
        }
        binders.push((motive_id, motive_fv.clone(), motive_ty, BinderInfo::Default));
        for (id, fv, ty) in &hyp_locals {
            binders.push((*id, fv.clone(), ty.clone(), BinderInfo::Default));
        }
        binders.push((t_id, t_fv, t_applied, BinderInfo::Default));

        let mut type_ = expected;
        let mut value = ra.term;
        for (id, _, ty, bi) in binders.iter().rev() {
            type_ = b.mk_pi(*id, *bi, ty.clone(), type_);
            value = b.mk_lam(*id, *bi, ty.clone(), value);
        }
        let type_ = b.finish(type_);
        let value = b.finish(value);
        // Anti-vacuity firewall: the statement must use the elementwise
        // vocabulary (the All family) whenever T has container hypotheses,
        // and must never leak internal machinery names.
        if !hyp_locals.is_empty() && !crate::inductive::mentions_name(&type_, &plan.all_name) {
            return Err(inv(format!(
                "deep_ind statement for {ind} never mentions {} — vacuous synthesis",
                plan.all_name
            )));
        }

        let theorem = Declaration::Theorem {
            name: deep_name,
            level_params: tv.level_params.clone(),
            type_,
            value,
        };
        let all_families = if plan.reuse {
            Vec::new()
        } else {
            vec![plan.decl]
        };
        Ok(DeepIndOutcome::Decls {
            all_families,
            theorems: vec![theorem],
        })
    }

    /// Build one minor: a bound hypothesis for a T-ctor slot, an
    /// All-constructor application for a container-ctor slot.
    #[allow(clippy::too_many_arguments)]
    fn build_deep_minor(
        &self,
        b: &mut EnvDeclBuilder,
        ind: &Name,
        container: &Name,
        c_levels: &[Level],
        c_args: &[Expr],
        preds: &[Expr],
        motive_fv: &Expr,
        all_applied: &dyn Fn(Expr) -> Expr,
        dom: &Expr,
        hyp_locals: &mut Vec<(crate::expr::FVarId, Expr, Expr)>,
    ) -> Result<Expr, DeepIndError> {
        // Classify by the ctor application in the slot codomain.
        let mut probe = EnvDeclBuilder::child_of(b);
        let (_probe_locals, cod) = walk_telescope(&mut probe, dom);
        let ctor_app = cod
            .get_app_args()
            .last()
            .cloned()
            .ok_or_else(|| inv("minor slot codomain is not a motive application"))?;
        let ExprKind::Const(ctor, _) = &ctor_app.get_app_fn().kind else {
            return Err(inv(
                "minor slot codomain does not end in a ctor application",
            ));
        };
        let ctor = ctor.clone();
        let cv = self
            .constructors
            .get(&ctor)
            .ok_or_else(|| inv(format!("minor ctor {ctor} is not registered")))?;

        if cv.inductive_name == *ind {
            // T-ctor: the hypothesis IS the (beta-normal) slot domain.
            let hyp_ty = dom.beta_normalize();
            let (id, fv) = b.fresh_local(hyp_ty.clone());
            hyp_locals.push((id, fv.clone(), hyp_ty));
            return Ok(fv);
        }
        if cv.inductive_name != *container {
            return Err(inv(format!(
                "minor ctor {ctor} belongs to neither {ind} nor {container}"
            )));
        }

        // Container ctor: λ (walked locals). C.All.c' ā P̄ f̄ q̄.
        let mut cb = EnvDeclBuilder::child_of(b);
        let (locals, _cod) = walk_telescope(&mut cb, dom);
        let nf = cv.num_fields as usize;
        if locals.len() < nf {
            return Err(inv(format!(
                "minor telescope for {ctor} shorter than its field count"
            )));
        }
        let (fields, ihs) = locals.split_at(nf);
        let suffix = ctor
            .to_string()
            .rsplit_once('.')
            .map(|(_, s)| s.to_string())
            .unwrap_or_else(|| ctor.to_string());
        let all_ctor = Name::from_string(&format!("{container}.All.{suffix}"));
        let mut args: Vec<Expr> = c_args.to_vec();
        args.extend(preds.iter().cloned());
        args.extend(fields.iter().map(|(_, fv, _)| fv.clone()));
        // Premises: identified BY TYPE among the IH locals — `motive f` for
        // elementwise fields, `C.All … f` for self-recursive fields,
        // `True.intro` for True-fill fields (no IH exists for those).
        for (_, f_fv, f_ty) in fields {
            if *f_ty == c_major_of(c_args, container, c_levels) {
                // Self-recursive container field: find the IH typed at the
                // container motive applied to this field.
                let want = all_applied(f_fv.clone());
                let ih = ihs
                    .iter()
                    .find(|(_, _, ty)| ty.beta_normalize() == want)
                    .ok_or_else(|| inv(format!("no IH found for a container field of {ctor}")))?;
                args.push(ih.1.clone());
            } else if let Some(j) = c_args.iter().position(|a| a == f_ty) {
                if preds[j] == *motive_fv {
                    let want = Expr::app(motive_fv.clone(), f_fv.clone());
                    let ih = ihs
                        .iter()
                        .find(|(_, _, ty)| ty.beta_normalize() == want)
                        .ok_or_else(|| {
                            inv(format!("no IH found for an elementwise field of {ctor}"))
                        })?;
                    args.push(ih.1.clone());
                } else {
                    args.push(Expr::const_(Name::from_string("True.intro"), Vec::new()));
                }
            } else {
                return Err(inv(format!(
                    "field of {ctor} is neither elementwise nor self-recursive"
                )));
            }
        }
        let body = Expr::apps(Expr::const_(all_ctor, c_levels.to_vec()), args);
        Ok(cb.finish_child(close_lams(&cb, &locals, body)))
    }
}

/// The uniform container application `C ā` (helper for field matching).
fn c_major_of(c_args: &[Expr], container: &Name, c_levels: &[Level]) -> Expr {
    Expr::apps(
        Expr::const_(container.clone(), c_levels.to_vec()),
        c_args.iter().cloned(),
    )
}
