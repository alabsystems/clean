// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic per-container `C.map` — the functorial map over a container's
//! ELEMENT positions (rung P4 sibling of `inductive_all_family.rs`).
//!
//! For a container `C` with level params `v̄` and `m` Sort-typed params,
//! `C.map` transports every element position along a family of functions:
//!
//! ```text
//! C.map : Π {A₁:S₁}…{A_m:S_m} {B₁:S₁}…{B_m:S_m}
//!           (f₁:A₁→B₁)…(f_m:A_m→B_m), C Ā → C B̄
//! C.map Ā B̄ f̄ (cᵢ Ā ḡ) ≡ cᵢ B̄ ḡ'
//!    where g'_t = f_j g_t              when field t's type is exactly param A_j
//!          g'_t = C.map Ā B̄ f̄ g_t     when field t's type is exactly C Ā
//! ```
//!
//! The value is ONE application of `C.rec` with the motive CHOSEN as the
//! constant family `λ _ : C Ā. C B̄`; each minor then rebuilds its own
//! constructor at `B̄`, pushing element fields through `f̄` and taking the
//! recursor's own induction hypothesis for self-recursive fields. Every
//! defeq obligation is pure beta, closed by the kernel at `add_decl`.
//!
//! ## Accepted container class (v1) — fail-closed
//!
//! Exactly the class `inductive_all_family.rs` accepts for `C.All`: a
//! non-indexed, non-mutual, non-nested inductive with `m ≥ 1` Sort-typed
//! parameters whose every constructor field is EITHER exactly a parameter
//! `A_j` (an element position) OR exactly the uniform self-application
//! `C Ā`, and whose every constructor returns `C Ā`. Higher-order
//! positions, nested containers, dependent fields and indexed families are
//! declined as [`ContainerMapOutcome::OutOfScope`] — never approximated.
//!
//! ## Why the IH-to-field correspondence is safe
//!
//! A container with two self-recursive fields (`node : C Ā → C Ā → C Ā`)
//! has two induction hypotheses of the SAME type `C B̄`, so they cannot be
//! told apart by type the way `C.All`'s premises can. The correspondence
//! used here is positional — the k-th IH belongs to the k-th self-recursive
//! field — and it is CHECKED against the kernel's own
//! `RecursorRule::recursive_fields` before use: a disagreement aborts
//! synthesis rather than emitting a well-typed but scrambled map.
//!
//! Non-trust-bearing: the caller registers the definition through the
//! ordinary CHECKED `add_decl`, so the kernel referees the term.

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::inductive::{RecursorArgOrder, RecursorRule};
use crate::level::Level;
use crate::name::Name;

use super::decl_builder::EnvDeclBuilder;
use super::rec_apply::{close_lams, walk_telescope, RecApply};
use super::types::Declaration;
use super::Environment;

/// Result of container-map synthesis.
#[derive(Debug)]
#[non_exhaustive]
pub enum ContainerMapOutcome {
    /// Declarations to register through the checked `add_decl` path.
    /// Empty when a byte-identical `C.map` is already registered.
    Decls {
        /// The `C.map` definition(s).
        definitions: Vec<Declaration>,
    },
    /// A declared v1 limitation; callers skip additively.
    OutOfScope {
        /// Stable human-readable reason.
        reason: String,
    },
}

/// Synthesis invariant violations (caller must not register anything).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ContainerMapError {
    /// The synthesizer's own coherence checks failed.
    #[error("container-map synthesis invariant violated: {0}")]
    Invariant(String),
}

fn inv(msg: impl Into<String>) -> ContainerMapError {
    ContainerMapError::Invariant(msg.into())
}

fn oos(reason: impl Into<String>) -> Result<ContainerMapOutcome, ContainerMapError> {
    Ok(ContainerMapOutcome::OutOfScope {
        reason: reason.into(),
    })
}

/// Element-position classification of one constructor field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FieldPos {
    /// Exactly param `A_j` — an element position, mapped by `f_j`.
    Element(usize),
    /// Exactly `C Ā` — a uniform self-application, mapped recursively.
    SelfRec,
}

impl FieldPos {
    fn is_self_rec(self) -> bool {
        matches!(self, FieldPos::SelfRec)
    }
}

/// Whether `e` mentions the free variable `id`.
fn mentions_fvar(e: &Expr, id: FVarId) -> bool {
    e.abstract_fvar(id) != *e
}

impl Environment {
    /// Synthesize `C.map` for a registered container inductive `C`.
    ///
    /// Read-only: returns the declaration for the caller to register
    /// through the checked `add_decl` path. Declared v1 limitations come
    /// back as [`ContainerMapOutcome::OutOfScope`]; coherence failures as
    /// [`ContainerMapError::Invariant`].
    ///
    /// # Errors
    ///
    /// [`ContainerMapError::Invariant`] when the synthesizer's own checks
    /// fail — the caller must register nothing.
    pub fn synthesize_container_map(
        &self,
        container: &Name,
    ) -> Result<ContainerMapOutcome, ContainerMapError> {
        // ── Container gates (the `C.All` v1 class) ─────────────────────────
        let Some(cv) = self.inductives.get(container) else {
            return oos(format!("{container} is not a registered inductive"));
        };
        if cv.num_indices != 0 {
            return oos(format!(
                "container {container} is indexed (v1 supports non-indexed)"
            ));
        }
        if cv.all_names.len() != 1 {
            return oos(format!(
                "container {container} is mutual (v1 supports single)"
            ));
        }
        if cv.is_nested {
            return oos(format!(
                "container {container} is nested (v1 supports plain containers)"
            ));
        }
        let m = cv.num_params as usize;
        if m == 0 {
            return oos(format!("container {container} has no params to map over"));
        }

        // Param telescope: every domain a Sort; the codomain is C's own Sort.
        let mut param_tys = Vec::with_capacity(m);
        let mut cursor = &cv.type_;
        for i in 0..m {
            let ExprKind::Pi(_, dom, body) = &cursor.kind else {
                return oos(format!(
                    "container {container} type is shorter than num_params"
                ));
            };
            if !matches!(&dom.kind, ExprKind::Sort(_)) {
                return oos(format!(
                    "container {container} param {i} is not Sort-typed (v1 class)"
                ));
            }
            param_tys.push((**dom).clone());
            cursor = body;
        }
        let ExprKind::Sort(result_level) = &cursor.kind else {
            return oos(format!("container {container} does not land in a Sort"));
        };
        let result_level = result_level.clone();

        let map_name = Name::from_string(&format!("{container}.map"));

        // ── Recursor gates ────────────────────────────────────────────────
        let rec_name = Name::from_string(&format!("{container}.rec"));
        let Some(rec) = self.get_recursor(&rec_name).cloned() else {
            return oos(format!("{rec_name} is not registered"));
        };
        if rec.arg_order != RecursorArgOrder::MajorAfterMinors {
            return oos(format!("{rec_name} has a non-standard argument order"));
        }
        if rec.num_motives != 1 {
            return oos(format!(
                "{rec_name} has {} motives (v1 supports single)",
                rec.num_motives
            ));
        }
        if rec.num_indices != 0 || rec.num_params as usize != m {
            return oos(format!(
                "{rec_name} arity disagrees with {container}'s param/index counts"
            ));
        }
        // Elim level: rec must carry [elim] ++ C's own level params so the
        // motive can land in C's own sort. Restricted (Prop-only) elimination
        // declines here.
        if rec.level_params.len() != cv.level_params.len() + 1 {
            return oos(format!(
                "{rec_name} does not carry a free elimination level (restricted elimination)"
            ));
        }
        if rec.rules.len() != rec.num_minors as usize {
            return Err(inv(format!(
                "{rec_name} has {} rules for {} minors",
                rec.rules.len(),
                rec.num_minors
            )));
        }

        let c_levels: Vec<Level> = cv
            .level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let rec_levels: Vec<Level> = std::iter::once(result_level)
            .chain(c_levels.iter().cloned())
            .collect();
        let rec_ty = rec
            .type_
            .instantiate_level_params_direct(&rec.level_params, &rec_levels);
        let level_params = cv.level_params.clone();

        // ── Locals: Ā, B̄, f̄ ───────────────────────────────────────────────
        let mut b = EnvDeclBuilder::new();
        let mut a_locals = Vec::with_capacity(m);
        for ty in &param_tys {
            a_locals.push(b.fresh_local(ty.clone()));
        }
        let mut b_locals = Vec::with_capacity(m);
        for ty in &param_tys {
            b_locals.push(b.fresh_local(ty.clone()));
        }
        let mut f_locals = Vec::with_capacity(m);
        let mut f_tys = Vec::with_capacity(m);
        for ((_, a_fv), (_, b_fv)) in a_locals.iter().zip(&b_locals) {
            let f_ty = Expr::arrow(a_fv.clone(), b_fv.clone());
            f_tys.push(f_ty.clone());
            f_locals.push(b.fresh_local(f_ty));
        }
        let c_at = |args: &[(FVarId, Expr)]| {
            Expr::apps(
                Expr::const_(container.clone(), c_levels.clone()),
                args.iter().map(|(_, fv)| fv.clone()),
            )
        };
        let c_a = c_at(&a_locals);
        let c_b = c_at(&b_locals);

        // ── Element-position analysis (the `C.All` v1 field classification) ─
        let shapes = match self.classify_container_fields(&b, container, &c_levels, &a_locals, &c_a)
        {
            Ok(s) => s,
            Err(reason) => return oos(reason),
        };
        let mut element_hits = vec![0usize; m];
        for (_, poss) in &shapes {
            for p in poss {
                if let FieldPos::Element(j) = *p {
                    element_hits[j] += 1;
                }
            }
        }

        // ── Walk the recursor, building the value ─────────────────────────
        let mut ra = RecApply::new(Expr::const_(rec_name.clone(), rec_levels), rec_ty);
        for (j, (_, a_fv)) in a_locals.iter().enumerate() {
            let dom = ra.peek_domain().map_err(inv)?;
            if dom != param_tys[j] {
                return Err(inv(format!(
                    "{rec_name} param slot {j} does not match {container}'s param type"
                )));
            }
            ra.apply(a_fv.clone()).map_err(inv)?;
        }

        // Motive: the constant family `λ _ : C Ā. C B̄`.
        {
            let dom = ra.peek_domain().map_err(inv)?;
            let ExprKind::Pi(_, major, _) = &dom.kind else {
                return Err(inv("motive slot is not a Pi"));
            };
            if **major != c_a {
                return Err(inv("motive slot is not over the container application"));
            }
        }
        {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let (x_id, _x_fv) = cb.fresh_local(c_a.clone());
            let motive = cb.mk_lam(x_id, BinderInfo::Default, c_a.clone(), c_b.clone());
            ra.apply(cb.finish_child(motive)).map_err(inv)?;
        }

        // Minors: rebuild each constructor at B̄.
        for _ in 0..rec.num_minors {
            let dom = ra.peek_domain().map_err(inv)?;
            let minor = self.build_map_minor(
                &b, container, &c_levels, &c_a, &c_b, &a_locals, &b_locals, &f_locals, &shapes,
                &rec.rules, &dom,
            )?;
            ra.apply(minor).map_err(inv)?;
        }

        // Major.
        {
            let dom = ra.peek_domain().map_err(inv)?;
            if dom != c_a {
                return Err(inv("major slot is not the container application"));
            }
        }
        let (x_id, x_fv) = b.fresh_local(c_a.clone());
        ra.apply(x_fv).map_err(inv)?;
        if ra.cursor.beta_normalize() != c_b {
            return Err(inv(format!(
                "residual recursor type for {map_name} is not the mapped container application"
            )));
        }

        // Anti-vacuity firewall: every parameter that actually occurs in an
        // element position must have its transport function used in the body.
        for (j, hits) in element_hits.iter().enumerate() {
            if *hits > 0 && !mentions_fvar(&ra.term, f_locals[j].0) {
                return Err(inv(format!(
                    "{map_name} never applies the transport function for param {j} — \
                     vacuous synthesis"
                )));
            }
        }

        // ── Close statement and value ─────────────────────────────────────
        let mut binders: Vec<(FVarId, Expr, BinderInfo)> = Vec::with_capacity(3 * m + 1);
        for ((id, _), ty) in a_locals.iter().zip(&param_tys) {
            binders.push((*id, ty.clone(), BinderInfo::Implicit));
        }
        for ((id, _), ty) in b_locals.iter().zip(&param_tys) {
            binders.push((*id, ty.clone(), BinderInfo::Implicit));
        }
        for ((id, _), ty) in f_locals.iter().zip(&f_tys) {
            binders.push((*id, ty.clone(), BinderInfo::Default));
        }
        binders.push((x_id, c_a, BinderInfo::Default));

        let mut type_ = c_b;
        let mut value = ra.term;
        for (id, ty, bi) in binders.iter().rev() {
            type_ = b.mk_pi(*id, *bi, ty.clone(), type_);
            value = b.mk_lam(*id, *bi, ty.clone(), value);
        }
        let type_ = b.finish(type_);
        let value = b.finish(value);

        // ── Idempotence / collision probe ─────────────────────────────────
        if let Some(existing) = self.get_const(&map_name) {
            let byte_identical = existing.level_params == level_params
                && existing.type_ == type_
                && existing.value.as_ref() == Some(&value);
            if byte_identical {
                return Ok(ContainerMapOutcome::Decls {
                    definitions: Vec::new(),
                });
            }
            return oos(format!(
                "{map_name} already exists with a different shape (name collision)"
            ));
        }

        Ok(ContainerMapOutcome::Decls {
            definitions: vec![Declaration::Definition {
                name: map_name,
                level_params,
                type_,
                value,
                is_reducible: false,
            }],
        })
    }

    /// Classify every constructor field of `container` as an element
    /// position (exactly a param `A_j`) or a uniform self-application
    /// (exactly `C Ā`). Anything else puts the container outside the v1
    /// class — the same field discipline `C.All` requires.
    fn classify_container_fields(
        &self,
        scratch_parent: &EnvDeclBuilder,
        container: &Name,
        c_levels: &[Level],
        a_locals: &[(FVarId, Expr)],
        c_a: &Expr,
    ) -> Result<Vec<(Name, Vec<FieldPos>)>, String> {
        let cv = self
            .inductives
            .get(container)
            .ok_or_else(|| format!("container {container} is not a registered inductive"))?;
        let mut out = Vec::with_capacity(cv.constructor_names.len());
        for ctor_name in &cv.constructor_names {
            let ctor = self
                .constructors
                .get(ctor_name)
                .ok_or_else(|| format!("constructor {ctor_name} is not registered"))?;
            let mut cty = ctor
                .type_
                .instantiate_level_params_direct(&ctor.level_params, c_levels);
            for (_, a_fv) in a_locals {
                let ExprKind::Pi(_, _, body) = &cty.kind else {
                    return Err(format!(
                        "constructor {ctor_name} is shorter than num_params"
                    ));
                };
                cty = body.instantiate(a_fv);
            }
            // Placeholders for already-walked fields must not collide with
            // the Ā locals, or a dependent field could alias a parameter.
            let mut scratch = EnvDeclBuilder::child_of(scratch_parent);
            let mut positions = Vec::new();
            while let ExprKind::Pi(_, fdom, body) = &cty.kind {
                let fdom = (**fdom).clone();
                let pos = if let Some(j) = a_locals.iter().position(|(_, a_fv)| *a_fv == fdom) {
                    FieldPos::Element(j)
                } else if fdom == *c_a {
                    FieldPos::SelfRec
                } else {
                    return Err(format!(
                        "constructor {ctor_name} has a field that is neither an element position \
                         nor a uniform self-application (v1 container class)"
                    ));
                };
                let (_, f_fv) = scratch.fresh_local(fdom);
                cty = body.instantiate(&f_fv);
                positions.push(pos);
            }
            if cty != *c_a {
                return Err(format!(
                    "constructor {ctor_name} does not return the uniform container application"
                ));
            }
            out.push((ctor_name.clone(), positions));
        }
        Ok(out)
    }

    /// Build one minor: `λ (fields) (IHs). cᵢ B̄ ḡ'`, transporting element
    /// fields through `f̄` and taking the recursor's own IH for
    /// self-recursive fields.
    #[allow(clippy::too_many_arguments)]
    fn build_map_minor(
        &self,
        b: &EnvDeclBuilder,
        container: &Name,
        c_levels: &[Level],
        c_a: &Expr,
        c_b: &Expr,
        a_locals: &[(FVarId, Expr)],
        b_locals: &[(FVarId, Expr)],
        f_locals: &[(FVarId, Expr)],
        shapes: &[(Name, Vec<FieldPos>)],
        rules: &[RecursorRule],
        dom: &Expr,
    ) -> Result<Expr, ContainerMapError> {
        let mut cb = EnvDeclBuilder::child_of(b);
        let (locals, cod) = walk_telescope(&mut cb, dom);

        // The codomain is `motive (cᵢ Ā f̄)` — read the constructor off it.
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
        let cvc = self
            .constructors
            .get(&ctor)
            .ok_or_else(|| inv(format!("minor ctor {ctor} is not registered")))?;
        if cvc.inductive_name != *container {
            return Err(inv(format!(
                "minor ctor {ctor} does not belong to {container}"
            )));
        }
        if cod.beta_normalize() != *c_b {
            return Err(inv(format!(
                "minor codomain for {ctor} does not beta-reduce to the mapped container"
            )));
        }

        let positions = shapes
            .iter()
            .find(|(n, _)| *n == ctor)
            .map(|(_, p)| p.as_slice())
            .ok_or_else(|| inv(format!("no field classification for {ctor}")))?;
        let nf = cvc.num_fields as usize;
        if positions.len() != nf {
            return Err(inv(format!(
                "field classification for {ctor} has {} entries for {nf} fields",
                positions.len()
            )));
        }
        // The kernel's own recursive-field record must agree with the
        // classification — that is what licenses the positional IH match.
        let rule = rules
            .iter()
            .find(|r| r.constructor_name == ctor)
            .ok_or_else(|| inv(format!("no recursor rule for {ctor}")))?;
        let recursive: Vec<bool> = positions.iter().map(|p| p.is_self_rec()).collect();
        if rule.recursive_fields != recursive {
            return Err(inv(format!(
                "recursor rule for {ctor} disagrees with the element-position analysis \
                 about which fields are recursive"
            )));
        }
        let num_ihs = recursive.iter().filter(|r| **r).count();
        if locals.len() != nf + num_ihs {
            return Err(inv(format!(
                "minor telescope for {ctor} has {} binders, expected {}",
                locals.len(),
                nf + num_ihs
            )));
        }
        let (fields, ihs) = locals.split_at(nf);

        // Rebuild the constructor at B̄.
        let mut args: Vec<Expr> = b_locals.iter().map(|(_, fv)| fv.clone()).collect();
        let mut next_ih = 0usize;
        for ((_, f_fv, f_ty), pos) in fields.iter().zip(positions) {
            match *pos {
                FieldPos::Element(j) => {
                    let f = f_locals
                        .get(j)
                        .ok_or_else(|| inv(format!("{ctor} references param {j} out of range")))?;
                    // The minor's own binder must really carry `A_j`, or the
                    // transport would be applied to the wrong field.
                    if a_locals.get(j).map(|(_, a_fv)| a_fv) != Some(f_ty) {
                        return Err(inv(format!(
                            "minor field of {ctor} is not at the classified param {j}"
                        )));
                    }
                    args.push(Expr::app(f.1.clone(), f_fv.clone()));
                }
                FieldPos::SelfRec => {
                    if f_ty != c_a {
                        return Err(inv(format!(
                            "minor field of {ctor} is not the uniform self-application"
                        )));
                    }
                    let (_, ih_fv, ih_ty) = ihs.get(next_ih).ok_or_else(|| {
                        inv(format!(
                            "minor for {ctor} has fewer IHs than recursive fields"
                        ))
                    })?;
                    if ih_ty.beta_normalize() != *c_b {
                        return Err(inv(format!(
                            "IH {next_ih} of {ctor} is not at the mapped container type"
                        )));
                    }
                    args.push(ih_fv.clone());
                    next_ih += 1;
                }
            }
        }
        let body = Expr::apps(Expr::const_(ctor, c_levels.to_vec()), args);
        Ok(cb.finish_child(close_lams(&cb, &locals, body)))
    }
}
