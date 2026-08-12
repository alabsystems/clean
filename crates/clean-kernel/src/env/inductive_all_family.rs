// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic per-container `C.All` families for deep induction (rung P4,
//! `designs/2026-08-06-deep-induction-scheme-all.md` §All-family).
//!
//! For a container `C` with level params `v̄` and `m` Sort-typed params,
//! `C.All` is the elementwise predicate lifting:
//!
//! ```text
//! C.All      : Π {A₁:S₁}…{A_m:S_m} (P₁:A₁→Prop)…(P_m:A_m→Prop), C Ā → Prop
//! C.All.cᵢ   : Π {Ā} (P̄) (f̄ : ctor fields) (q̄), C.All Ā P̄ (cᵢ Ā f̄)
//!    where q_t : P_j f_t       when field t's type is exactly param A_j
//!          q_t : C.All Ā P̄ f_t when field t's type is exactly C Ā
//! ```
//!
//! Generated ONCE per container from its registered `InductiveVal` —
//! deterministic bytes — and instantiated per use by the deep-induction
//! generator. Registration goes through the caller's fully CHECKED
//! `add_inductive` (positivity, universes, ctor checks re-earned);
//! byte-identical re-generation against an existing `C.All` is the
//! idempotence/collision probe.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

use super::decl_builder::EnvDeclBuilder;
use super::Environment;

/// Plan for one container's All family.
#[derive(Debug, Clone)]
pub(crate) struct AllFamilyPlan {
    /// The family name (`C.All`).
    pub(crate) all_name: Name,
    /// The declaration to register (ignored when `reuse` is set).
    pub(crate) decl: InductiveDecl,
    /// True when a byte-identical `C.All` is already registered.
    pub(crate) reuse: bool,
}

impl Environment {
    /// Build (or match) the `C.All` family for `container`.
    ///
    /// Returns `Err(reason)` when the container is outside the v1 class or
    /// the `C.All` name is taken by something else — the caller maps this
    /// to an additive `OutOfScope` decline.
    pub(crate) fn all_family_decl(&self, container: &Name) -> Result<AllFamilyPlan, String> {
        let cv = self
            .inductives
            .get(container)
            .ok_or_else(|| format!("container {container} is not a registered inductive"))?;
        if cv.num_indices != 0 {
            return Err(format!(
                "container {container} is indexed (v1 supports non-indexed)"
            ));
        }
        if cv.all_names.len() != 1 {
            return Err(format!(
                "container {container} is mutual (v1 supports single)"
            ));
        }
        let m = cv.num_params as usize;
        if m == 0 {
            return Err(format!("container {container} has no params to lift over"));
        }

        // Param telescope: every domain must be a Sort.
        let mut param_tys = Vec::with_capacity(m);
        let mut cursor = &cv.type_;
        for i in 0..m {
            let ExprKind::Pi(_, dom, body) = &cursor.kind else {
                return Err(format!(
                    "container {container} type shorter than num_params"
                ));
            };
            if !matches!(&dom.kind, ExprKind::Sort(_)) {
                return Err(format!(
                    "container {container} param {i} is not Sort-typed (v1 class)"
                ));
            }
            param_tys.push((**dom).clone());
            cursor = body;
        }

        let levels: Vec<Level> = cv
            .level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let all_name = Name::from_string(&format!("{container}.All"));

        // ── Build with the FVar builder, close at the end ──────────────────
        let mut b = EnvDeclBuilder::new();
        let mut a_locals = Vec::with_capacity(m);
        for ty in &param_tys {
            a_locals.push(b.fresh_local(ty.clone()));
        }
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let mut p_locals = Vec::with_capacity(m);
        for (_, a_fv) in &a_locals {
            p_locals.push(b.fresh_local(Expr::arrow(a_fv.clone(), prop.clone())));
        }
        let c_applied = Expr::apps(
            Expr::const_(container.clone(), levels.clone()),
            a_locals.iter().map(|(_, fv)| fv.clone()),
        );
        let all_applied = |target: Expr| {
            Expr::apps(
                Expr::const_(all_name.clone(), levels.clone()),
                a_locals
                    .iter()
                    .map(|(_, fv)| fv.clone())
                    .chain(p_locals.iter().map(|(_, fv)| fv.clone()))
                    .chain(std::iter::once(target)),
            )
        };

        // Family former: Π {Ā} (P̄) (x : C Ā), Prop.
        let former = {
            let (x_id, _x_fv) = b.fresh_local(c_applied.clone());
            let mut t = b.mk_pi(x_id, BinderInfo::Default, c_applied.clone(), prop.clone());
            for ((p_id, p_fv), (_, a_fv)) in p_locals.iter().zip(&a_locals).rev() {
                let _ = p_fv;
                t = b.mk_pi(
                    *p_id,
                    BinderInfo::Default,
                    Expr::arrow(a_fv.clone(), prop.clone()),
                    t,
                );
            }
            for ((a_id, _), ty) in a_locals.iter().zip(&param_tys).rev() {
                t = b.mk_pi(*a_id, BinderInfo::Implicit, ty.clone(), t);
            }
            t
        };

        // Constructors.
        let mut ctors = Vec::with_capacity(cv.constructor_names.len());
        for ctor_name in &cv.constructor_names {
            let ctor = self
                .constructors
                .get(ctor_name)
                .ok_or_else(|| format!("constructor {ctor_name} is not registered"))?;
            // Strip C's param binders, instantiating with the Ā locals.
            let mut cty = ctor
                .type_
                .instantiate_level_params_direct(&ctor.level_params, &levels);
            for (_, a_fv) in &a_locals {
                let ExprKind::Pi(_, _, body) = &cty.kind else {
                    return Err(format!("constructor {ctor_name} shorter than num_params"));
                };
                cty = body.instantiate(a_fv);
            }
            // Fields: each must be exactly a param Ā_j or exactly C Ā.
            let mut cb = EnvDeclBuilder::child_of(&b);
            let mut f_locals = Vec::new();
            let mut q_specs = Vec::new(); // (field fvar, premise type)
            while let ExprKind::Pi(_, fdom, body) = &cty.kind {
                let fdom = (**fdom).clone();
                let premise = if let Some(j) = a_locals.iter().position(|(_, a_fv)| *a_fv == fdom) {
                    Some(PremiseKind::Param(j))
                } else if fdom == c_applied {
                    Some(PremiseKind::SelfRec)
                } else {
                    return Err(format!(
                        "constructor {ctor_name} field is neither a param nor a uniform \
                         self-application (v1 container class)"
                    ));
                };
                let (f_id, f_fv) = cb.fresh_local(fdom.clone());
                cty = body.instantiate(&f_fv);
                f_locals.push((f_id, f_fv.clone(), fdom));
                q_specs.push((f_fv, premise));
            }
            // Result must be C Ā.
            if cty != c_applied {
                return Err(format!(
                    "constructor {ctor_name} does not return the uniform container application"
                ));
            }
            // Premise locals q̄.
            let mut q_locals = Vec::new();
            for (f_fv, premise) in &q_specs {
                let q_ty = match premise {
                    Some(PremiseKind::Param(j)) => Expr::app(p_locals[*j].1.clone(), f_fv.clone()),
                    Some(PremiseKind::SelfRec) => all_applied(f_fv.clone()),
                    None => unreachable!("every v1 field has a premise kind"),
                };
                let (q_id, q_fv) = cb.fresh_local(q_ty.clone());
                let _ = q_fv;
                q_locals.push((q_id, q_ty));
            }
            // Codomain: C.All Ā P̄ (cᵢ Ā f̄).
            let ctor_app = Expr::apps(
                Expr::const_(ctor_name.clone(), levels.clone()),
                a_locals
                    .iter()
                    .map(|(_, fv)| fv.clone())
                    .chain(f_locals.iter().map(|(_, fv, _)| fv.clone())),
            );
            let mut ct = all_applied(ctor_app);
            for (q_id, q_ty) in q_locals.iter().rev() {
                ct = cb.mk_pi(*q_id, BinderInfo::Default, q_ty.clone(), ct);
            }
            for (f_id, _, fty) in f_locals.iter().rev() {
                ct = cb.mk_pi(*f_id, BinderInfo::Default, fty.clone(), ct);
            }
            let ct = cb.finish_child(ct);
            let mut ct_full = ct;
            for ((p_id, _), (_, a_fv)) in p_locals.iter().zip(&a_locals).rev() {
                ct_full = b.mk_pi(
                    *p_id,
                    BinderInfo::Default,
                    Expr::arrow(a_fv.clone(), prop.clone()),
                    ct_full,
                );
            }
            for ((a_id, _), ty) in a_locals.iter().zip(&param_tys).rev() {
                ct_full = b.mk_pi(*a_id, BinderInfo::Implicit, ty.clone(), ct_full);
            }
            let suffix = ctor_name
                .to_string()
                .rsplit_once('.')
                .map(|(_, s)| s.to_string())
                .unwrap_or_else(|| ctor_name.to_string());
            ctors.push(Constructor {
                name: Name::from_string(&format!("{all_name}.{suffix}")),
                type_: b.finish(ct_full),
            });
        }

        let decl = InductiveDecl {
            level_params: cv.level_params.clone(),
            num_params: (2 * m) as u32,
            types: vec![InductiveType {
                name: all_name.clone(),
                type_: b.finish(former),
                constructors: ctors,
            }],
        };

        // ── Idempotence / collision probe ──────────────────────────────────
        if let Some(existing) = self.inductives.get(&all_name) {
            let byte_identical = existing.level_params == decl.level_params
                && existing.num_params == decl.num_params
                && existing.type_ == decl.types[0].type_
                && existing.constructor_names.len() == decl.types[0].constructors.len()
                && decl.types[0].constructors.iter().all(|c| {
                    self.constructors
                        .get(&c.name)
                        .is_some_and(|reg| reg.type_ == c.type_)
                });
            if byte_identical {
                return Ok(AllFamilyPlan {
                    all_name,
                    decl,
                    reuse: true,
                });
            }
            return Err(format!(
                "{all_name} already exists with a different shape (name collision)"
            ));
        }
        if self.constants.contains_key(&all_name) {
            return Err(format!(
                "{all_name} already exists as a non-inductive constant"
            ));
        }
        for c in &decl.types[0].constructors {
            if self.constants.contains_key(&c.name) {
                return Err(format!("{} already exists (name collision)", c.name));
            }
        }
        Ok(AllFamilyPlan {
            all_name,
            decl,
            reuse: false,
        })
    }
}

#[derive(Clone, Copy)]
enum PremiseKind {
    /// Field is exactly param `A_j` — premise `P_j f`.
    Param(usize),
    /// Field is exactly `C Ā` — premise `C.All Ā P̄ f`.
    SelfRec,
}
