// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic per-container `C.rel` — the two-container RELATIONAL LIFTING
//! (rung P4 sibling of `inductive_all_family.rs` and
//! `inductive_container_map.rs`).
//!
//! For a container `C` with level params `v̄` and `m` Sort-typed params,
//! `C.rel` lifts a family of element relations to the container:
//!
//! ```text
//! C.rel : Π {A₁:S₁}…{A_m:S_m} {B₁:S₁}…{B_m:S_m}
//!           (R₁:A₁→B₁→Prop)…(R_m:A_m→B_m→Prop), C Ā → C B̄ → Prop
//!
//! C.rel.cᵢ : Π {Ā} {B̄} (R̄) (f̄ : cᵢ's fields at Ā) (ḡ : cᵢ's fields at B̄) (q̄),
//!              C.rel Ā B̄ R̄ (cᵢ Ā f̄) (cᵢ B̄ ḡ)
//!    where q_t : R_j f_t g_t         when field t's type is exactly param A_j
//!          q_t : C.rel Ā B̄ R̄ f_t g_t when field t's type is exactly C Ā
//! ```
//!
//! Like `C.All` this is an inductive FAMILY, not a definition: the two
//! container arguments are INDICES (`num_params = 3m`, `num_indices = 2`),
//! because each constructor pins them to its own constructor applications.
//!
//! The lifting relates values built with the SAME constructor — one
//! generated constructor per original constructor, no cross-constructor
//! cases. That is what makes it the standard relational lifting and NOT an
//! equality: `C.rel R̄` is as coarse as `R̄` is at element positions and as
//! rigid as `C`'s own shape everywhere else.
//!
//! ## Accepted container class (v1) — fail-closed
//!
//! Exactly the class `inductive_container_map.rs` vetted for `C.map`: a
//! non-indexed, non-mutual, non-nested inductive with `m ≥ 1` Sort-typed
//! parameters whose every constructor field is EITHER exactly a parameter
//! `A_j` (an element position) OR exactly the uniform self-application
//! `C Ā`, and whose every constructor returns `C Ā`. Higher-order
//! positions, nested containers, dependent fields and indexed families are
//! declined as [`ContainerRelOutcome::OutOfScope`] — never approximated.
//! (The classification is duplicated rather than shared because `C.map`'s
//! copy is module-private; the two must be kept in step.)
//!
//! No recursor is consulted: unlike `C.map`, `C.rel` is not built by
//! eliminating `C`, so `C`'s elimination restrictions are irrelevant here.
//!
//! Non-trust-bearing: the caller registers the family through the ordinary
//! CHECKED `add_inductive`, so positivity, universes and constructor checks
//! are re-earned by the kernel exactly as they are for `C.All`.

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::inductive::{count_pi_args, Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

use super::decl_builder::EnvDeclBuilder;
use super::Environment;

/// Result of relational-lifting synthesis.
#[derive(Debug)]
#[non_exhaustive]
pub enum ContainerRelOutcome {
    /// Families to register through the checked `add_inductive` path.
    /// Empty when a byte-identical `C.rel` is already registered.
    Decls {
        /// The `C.rel` family (at most one).
        families: Vec<InductiveDecl>,
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
pub enum ContainerRelError {
    /// The synthesizer's own coherence checks failed.
    #[error("container-rel synthesis invariant violated: {0}")]
    Invariant(String),
}

fn inv(msg: impl Into<String>) -> ContainerRelError {
    ContainerRelError::Invariant(msg.into())
}

fn oos(reason: impl Into<String>) -> Result<ContainerRelOutcome, ContainerRelError> {
    Ok(ContainerRelOutcome::OutOfScope {
        reason: reason.into(),
    })
}

/// Element-position classification of one constructor field (the `C.map`
/// v1 class).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FieldPos {
    /// Exactly param `A_j` — an element position, related by `R_j`.
    Element(usize),
    /// Exactly `C Ā` — a uniform self-application, related recursively.
    SelfRec,
}

impl Environment {
    /// Synthesize the relational lifting `C.rel` for a registered container.
    ///
    /// Read-only: returns the family for the caller to register through the
    /// checked `add_inductive` path. Declared v1 limitations come back as
    /// [`ContainerRelOutcome::OutOfScope`]; coherence failures as
    /// [`ContainerRelError::Invariant`].
    ///
    /// # Errors
    ///
    /// [`ContainerRelError::Invariant`] when the synthesizer's own checks
    /// fail — the caller must register nothing.
    pub fn synthesize_container_rel(
        &self,
        container: &Name,
    ) -> Result<ContainerRelOutcome, ContainerRelError> {
        // ── Container gates (the vetted `C.map` v1 class) ──────────────────
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
            return oos(format!(
                "container {container} has no params to relate over"
            ));
        }

        // Param telescope: every domain a Sort, and `C` itself lands in a Sort.
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
        if !matches!(&cursor.kind, ExprKind::Sort(_)) {
            return oos(format!("container {container} does not land in a Sort"));
        }

        let c_levels: Vec<Level> = cv
            .level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let level_params = cv.level_params.clone();
        let rel_name = container.clone().str("rel");
        let constructor_names = cv.constructor_names.clone();

        // ── Locals: Ā, B̄, R̄ ───────────────────────────────────────────────
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let mut b = EnvDeclBuilder::new();
        let mut a_locals = Vec::with_capacity(m);
        for ty in &param_tys {
            a_locals.push(b.fresh_local(ty.clone()));
        }
        let mut b_locals = Vec::with_capacity(m);
        for ty in &param_tys {
            b_locals.push(b.fresh_local(ty.clone()));
        }
        let mut r_tys = Vec::with_capacity(m);
        let mut r_locals = Vec::with_capacity(m);
        for ((_, a_fv), (_, b_fv)) in a_locals.iter().zip(&b_locals) {
            let r_ty = Expr::arrow(a_fv.clone(), Expr::arrow(b_fv.clone(), prop.clone()));
            r_tys.push(r_ty.clone());
            r_locals.push(b.fresh_local(r_ty));
        }
        let c_at = |args: &[(FVarId, Expr)]| {
            Expr::apps(
                Expr::const_(container.clone(), c_levels.clone()),
                args.iter().map(|(_, fv)| fv.clone()),
            )
        };
        let c_a = c_at(&a_locals);
        let c_b = c_at(&b_locals);
        let rel_applied = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(rel_name.clone(), c_levels.clone()),
                a_locals
                    .iter()
                    .map(|(_, fv)| fv.clone())
                    .chain(b_locals.iter().map(|(_, fv)| fv.clone()))
                    .chain(r_locals.iter().map(|(_, fv)| fv.clone()))
                    .chain([x, y]),
            )
        };

        // ── Family former: Π {Ā} {B̄} (R̄) (x : C Ā) (y : C B̄), Prop ────────
        let former = {
            let (x_id, _x_fv) = b.fresh_local(c_a.clone());
            let (y_id, _y_fv) = b.fresh_local(c_b.clone());
            let mut t = b.mk_pi(y_id, BinderInfo::Default, c_b.clone(), prop.clone());
            t = b.mk_pi(x_id, BinderInfo::Default, c_a.clone(), t);
            close_rel_params(&b, &a_locals, &b_locals, &r_locals, &param_tys, &r_tys, t)
        };

        // ── Constructors ──────────────────────────────────────────────────
        let mut ctors = Vec::with_capacity(constructor_names.len());
        for ctor_name in &constructor_names {
            let ctor = self
                .constructors
                .get(ctor_name)
                .ok_or_else(|| inv(format!("constructor {ctor_name} is not registered")))?;
            // Strip C's param binders, instantiating with the Ā locals.
            let mut cty = ctor
                .type_
                .instantiate_level_params_direct(&ctor.level_params, &c_levels);
            for (_, a_fv) in &a_locals {
                let ExprKind::Pi(_, _, body) = &cty.kind else {
                    return oos(format!(
                        "constructor {ctor_name} is shorter than num_params"
                    ));
                };
                cty = body.instantiate(a_fv);
            }

            // Fields at Ā, classified into element / self-recursive positions.
            let mut cb = EnvDeclBuilder::child_of(&b);
            let mut f_locals: Vec<(FVarId, Expr, Expr)> = Vec::new();
            let mut positions: Vec<FieldPos> = Vec::new();
            while let ExprKind::Pi(_, fdom, body) = &cty.kind {
                let fdom = (**fdom).clone();
                let pos = if let Some(j) = a_locals.iter().position(|(_, a_fv)| *a_fv == fdom) {
                    FieldPos::Element(j)
                } else if fdom == c_a {
                    FieldPos::SelfRec
                } else {
                    return oos(format!(
                        "constructor {ctor_name} has a field that is neither an element position \
                         nor a uniform self-application (v1 container class)"
                    ));
                };
                let (f_id, f_fv) = cb.fresh_local(fdom.clone());
                cty = body.instantiate(&f_fv);
                f_locals.push((f_id, f_fv, fdom));
                positions.push(pos);
            }
            if cty != c_a {
                return oos(format!(
                    "constructor {ctor_name} does not return the uniform container application"
                ));
            }
            if f_locals.len() != ctor.num_fields as usize {
                return Err(inv(format!(
                    "constructor {ctor_name} walked {} fields, the environment records {}",
                    f_locals.len(),
                    ctor.num_fields
                )));
            }

            // The same fields again, at B̄.
            let mut g_locals: Vec<(FVarId, Expr, Expr)> = Vec::with_capacity(f_locals.len());
            for pos in &positions {
                let gty = match *pos {
                    FieldPos::Element(j) => {
                        b_locals.get(j).map(|(_, fv)| fv.clone()).ok_or_else(|| {
                            inv(format!("{ctor_name} references param {j} out of range"))
                        })?
                    }
                    FieldPos::SelfRec => c_b.clone(),
                };
                let (g_id, g_fv) = cb.fresh_local(gty.clone());
                g_locals.push((g_id, g_fv, gty));
            }

            // Relatedness premises q̄ — one per field, no field ignored.
            let mut q_locals: Vec<(FVarId, Expr)> = Vec::with_capacity(f_locals.len());
            // Which element params actually received a relatedness premise.
            let mut element_premises: Vec<usize> = Vec::with_capacity(f_locals.len());
            for ((pos, (_, f_fv, _)), (_, g_fv, _)) in
                positions.iter().zip(&f_locals).zip(&g_locals)
            {
                let q_ty = match *pos {
                    FieldPos::Element(j) => {
                        let r = r_locals.get(j).ok_or_else(|| {
                            inv(format!("{ctor_name} references param {j} out of range"))
                        })?;
                        element_premises.push(j);
                        Expr::apps(r.1.clone(), [f_fv.clone(), g_fv.clone()])
                    }
                    FieldPos::SelfRec => rel_applied(f_fv.clone(), g_fv.clone()),
                };
                let (q_id, _q_fv) = cb.fresh_local(q_ty.clone());
                q_locals.push((q_id, q_ty));
            }

            // Codomain: C.rel Ā B̄ R̄ (cᵢ Ā f̄) (cᵢ B̄ ḡ).
            let ctor_at = |ps: &[(FVarId, Expr)], fields: &[(FVarId, Expr, Expr)]| {
                Expr::apps(
                    Expr::const_(ctor_name.clone(), c_levels.clone()),
                    ps.iter()
                        .map(|(_, fv)| fv.clone())
                        .chain(fields.iter().map(|(_, fv, _)| fv.clone())),
                )
            };
            let mut ct = rel_applied(ctor_at(&a_locals, &f_locals), ctor_at(&b_locals, &g_locals));
            for (q_id, q_ty) in q_locals.iter().rev() {
                ct = cb.mk_pi(*q_id, BinderInfo::Default, q_ty.clone(), ct);
            }
            for (g_id, _, gty) in g_locals.iter().rev() {
                ct = cb.mk_pi(*g_id, BinderInfo::Default, gty.clone(), ct);
            }
            for (f_id, _, fty) in f_locals.iter().rev() {
                ct = cb.mk_pi(*f_id, BinderInfo::Default, fty.clone(), ct);
            }
            let ct = cb.finish_child(ct);

            // Anti-vacuity firewall: a lifting that forgot an element relation
            // would relate values it must not. Every parameter this constructor
            // actually stores must be demanded through its own `R_j`.
            //
            // STRUCTURAL, NOT SYNTACTIC — and that is the whole subtlety.
            //
            // This originally ran `mentions_fvar(&ct, r_j)` over the constructor
            // type. DEAD CODE: `ct` wraps the codomain `C.rel Ā B̄ R̄ x y`, which
            // mentions every `R_j` by construction, so with the R̄ binders free
            // the test was unconditionally true and the guard unconditionally
            // false. Measured: dropping the element premise with the firewall
            // "intact" produced ZERO hits (only the binder-count firewall below
            // caught it), and inverting the condition made it fire for EVERY
            // container.
            //
            // Narrowing the scan to the premises q̄ is ALSO insufficient, for the
            // same reason one level down: a `SelfRec` premise is itself
            // `C.rel Ā B̄ R̄ f g`. Any syntactic `R_j` test is satisfied for free
            // by the recursive premise of a container storing a recursive field
            // — i.e. by nearly every container of interest. That second attempt
            // was measured too, and it still did not fire.
            //
            // So record it structurally: `element_premises` lists the params for
            // which an ELEMENT premise was actually emitted. Nothing else can
            // satisfy that.
            for j in 0..r_locals.len() {
                let stores_j = positions.contains(&FieldPos::Element(j));
                let demanded = element_premises.contains(&j);
                if stores_j && !demanded {
                    return Err(inv(format!(
                        "{rel_name} constructor for {ctor_name} never demands the element \
                         relation for param {j} — vacuous synthesis"
                    )));
                }
            }

            let ct_full =
                close_rel_params(&b, &a_locals, &b_locals, &r_locals, &param_tys, &r_tys, ct);
            // Shape firewall: {Ā} {B̄} (R̄) (f̄) (ḡ) (q̄) and nothing else.
            let expected_binders = 3 * m + 3 * f_locals.len();
            if count_pi_args(&ct_full) as usize != expected_binders {
                return Err(inv(format!(
                    "{rel_name} constructor for {ctor_name} has {} binders, expected {}",
                    count_pi_args(&ct_full),
                    expected_binders
                )));
            }
            ctors.push(Constructor {
                name: ctor_name
                    .with_parent(rel_name.clone())
                    .ok_or_else(|| inv(format!("anonymous constructor in {container}")))?,
                type_: b.finish(ct_full),
            });
        }

        let decl = InductiveDecl {
            level_params,
            num_params: (3 * m) as u32,
            types: vec![InductiveType {
                name: rel_name.clone(),
                type_: b.finish(former),
                constructors: ctors,
            }],
        };

        // ── Idempotence / collision probe ─────────────────────────────────
        if let Some(existing) = self.inductives.get(&rel_name) {
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
                return Ok(ContainerRelOutcome::Decls {
                    families: Vec::new(),
                });
            }
            return oos(format!(
                "{rel_name} already exists with a different shape (name collision)"
            ));
        }
        if self.constants.contains_key(&rel_name) {
            return oos(format!(
                "{rel_name} already exists as a non-inductive constant"
            ));
        }
        for c in &decl.types[0].constructors {
            if self.constants.contains_key(&c.name) {
                return oos(format!("{} already exists (name collision)", c.name));
            }
        }

        Ok(ContainerRelOutcome::Decls {
            families: vec![decl],
        })
    }
}

/// Close `body` under the shared parameter telescope `{Ā} {B̄} (R̄)`.
/// The former and every constructor MUST agree on it, so they share one
/// closer rather than two copies that could drift apart.
fn close_rel_params(
    b: &EnvDeclBuilder,
    a_locals: &[(FVarId, Expr)],
    b_locals: &[(FVarId, Expr)],
    r_locals: &[(FVarId, Expr)],
    param_tys: &[Expr],
    r_tys: &[Expr],
    body: Expr,
) -> Expr {
    let mut t = body;
    for ((r_id, _), r_ty) in r_locals.iter().zip(r_tys).rev() {
        t = b.mk_pi(*r_id, BinderInfo::Default, r_ty.clone(), t);
    }
    for ((b_id, _), ty) in b_locals.iter().zip(param_tys).rev() {
        t = b.mk_pi(*b_id, BinderInfo::Implicit, ty.clone(), t);
    }
    for ((a_id, _), ty) in a_locals.iter().zip(param_tys).rev() {
        t = b.mk_pi(*a_id, BinderInfo::Implicit, ty.clone(), t);
    }
    t
}
