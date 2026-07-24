// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Template-inductive cumulativity for the Coq verification lane.
//!
//! Extends `is_le` (see `def_eq/mod.rs`) with Coq-faithful subtyping between two
//! universe instances of the SAME template-polymorphic inductive:
//!
//! ```text
//! I.{u₁ … uₙ} a₁ … aₖ   ≤   I.{v₁ … vₙ} a₁ … aₖ
//! ```
//!
//! accepted iff every `uᵢ ≤ vᵢ` and the parameters `aⱼ` are pairwise
//! definitionally equal (INVARIANT arguments — Coq's template polymorphism keeps
//! the parameters fixed and only floats the universe instance).
//!
//! This is the last rung of the Coq prod-poly program: a value can mix a
//! `Type`-level `prod.{1,1} A B` (an external definition floored monomorphic at
//! its own import) with a `Prop`-level `prod.{0,0} A B` (a transparent Prop-prod
//! definition), meeting where the kernel must accept `prod.{0,0} A B ≤
//! prod.{1,1} A B`. `is_le`'s Sort and Pi rules do not relate inductive
//! instances, so this rule closes the gap (`mathcomp … Num.Theory.real_maxrN`).

use crate::expr::{Expr, ExprKind};
use crate::inductive::InductiveVal;
use crate::level::Level;
use crate::tc::TypeChecker;

impl TypeChecker<'_> {
    /// Coq template-inductive cumulativity: `a_w ≤ b_w` when both are full
    /// applications of the SAME template-polymorphic inductive whose universe
    /// instances are pointwise `≤` and whose parameters are pairwise def-eq.
    ///
    /// `a_w` and `b_w` MUST already be in weak-head normal form (the caller,
    /// `is_le`, whnf's both sides). Returns `false` outside the Coq lane, so the
    /// Lean-faithful non-cumulative path is provably untouched.
    ///
    /// # Soundness
    ///
    /// The rule fires only for a **template-polymorphic singleton** inductive
    /// `I` (see [`Self::is_template_poly_singleton_inductive`]): a single,
    /// non-mutual, index-free inductive with exactly one universe parameter per
    /// type parameter, one constructor, arity
    /// `Π (p₁ : Sort l₁) … (pₖ : Sort lₖ). Sort _` (each `lᵢ` appearing ONLY as
    /// the `i`-th parameter's sort), and every constructor field typed by a bare
    /// de-Bruijn reference to an earlier binder. `prod.{u,v} : Sort u → Sort v →
    /// Sort (max u v)` with `pair : (A : Sort u)(B : Sort v)(a : A)(b : B) →
    /// prod A B` is exactly this shape.
    ///
    /// For such an `I`, no constructor field type mentions a universe parameter
    /// (a `BVar` cannot), so instantiating the constructor at `{u}` or at `{v}`
    /// (with the parameters `a₁ … aₖ` held fixed) yields the SAME field types and
    /// hence admits the SAME inhabitants. The parameter sorts embed by sort
    /// cumulativity (`Sort uᵢ ≤ Sort vᵢ` since `uᵢ ≤ vᵢ`), and the result sort
    /// `max l` is monotone in each `lᵢ`. Therefore every inhabitant of
    /// `I.{u} a` is an inhabitant of `I.{v} a`: the subtyping is a sound rule of
    /// Coq's (cumulative / template) pCIC, and it is exactly Coq's
    /// template-polymorphism subtyping restricted to identical parameters.
    ///
    /// Requiring the parameters to be *invariant* (def-eq, not `is_le`) and the
    /// application to be *saturated* (`argc == num_params`, so both sides are
    /// genuine `Sort`s rather than partially-applied type formers) keeps the rule
    /// strictly conservative: it never accepts a pair that Coq would reject.
    ///
    /// # Negative controls (kept sound by construction)
    ///
    /// * Different inductive heads, or heads that are not template-poly
    ///   singletons (e.g. a two-constructor type), are rejected.
    /// * Instances that are not pointwise `≤` are rejected.
    /// * Different parameters are rejected (invariant args).
    /// * Outside the Coq lane (`self.cumulative == false`) the rule is inert.
    pub(super) fn is_le_template_inductive(&self, a_w: &Expr, b_w: &Expr) -> bool {
        // Defense in depth: only ever active in the Coq cumulative lane. The sole
        // caller (`is_le`) already guarantees this; guarding here keeps the helper
        // sound in isolation and the Lean lane provably unreachable.
        if !self.cumulative {
            return false;
        }

        let (ExprKind::Const(a_name, a_levels), ExprKind::Const(b_name, b_levels)) =
            (a_w.get_app_fn().kind(), b_w.get_app_fn().kind())
        else {
            return false;
        };
        // SAME inductive head.
        if a_name != b_name {
            return false;
        }
        let Some(ind) = self.env.get_inductive(a_name) else {
            return false;
        };
        // (a) `I` must be a template-polymorphic singleton inductive.
        if !self.is_template_poly_singleton_inductive(ind) {
            return false;
        }
        // Both instances carry exactly the inductive's universe parameters.
        let n_lvl = ind.level_params.len();
        if a_levels.len() != n_lvl || b_levels.len() != n_lvl {
            return false;
        }
        // Saturated at the parameters (index-free class ⇒ both sides are Sorts).
        let a_args = a_w.get_app_args();
        let b_args = b_w.get_app_args();
        let k = ind.num_params as usize;
        if a_args.len() != k || b_args.len() != k {
            return false;
        }
        // (c) INVARIANT arguments: the parameters must be the SAME terms.
        for (x, y) in a_args.iter().zip(b_args.iter()) {
            if !self.is_def_eq(x, y) {
                return false;
            }
        }
        // (b) Pointwise universe cumulativity: `uᵢ ≤ vᵢ` for every parameter.
        a_levels
            .iter()
            .zip(b_levels.iter())
            .all(|(u, v)| Level::leq(u, v))
    }

    /// Structural predicate: is `ind` a template-polymorphic singleton inductive
    /// (the `prod`-class), for which per-parameter universe cumulativity is a
    /// sound subtyping rule?
    ///
    /// The check is deliberately conservative — it inspects only the stored
    /// (already kernel-checked) inductive and constructor declarations, so the
    /// kernel itself decides template-polymorphism rather than trusting any
    /// external marker. Today exactly `Coq.Init.Datatypes.prod.0` matches; the
    /// predicate generalises to any inductive of the same provably-safe shape.
    ///
    /// Sufficient conditions (each strengthening soundness; see
    /// [`Self::is_le_template_inductive`] for the argument):
    /// 1. non-mutual (`all_names.len() == 1`), index-free, `num_params ≥ 1`;
    /// 2. one universe parameter per type parameter; exactly one constructor;
    /// 3. arity `Π (p₁ : Sort l₁) … (pₖ : Sort lₖ). Sort _`, each `lᵢ` being the
    ///    `i`-th universe parameter (so a universe parameter appears ONLY as a
    ///    parameter sort in the type former);
    /// 4. every constructor field is typed by a bare `BVar` — no field type can
    ///    mention a universe parameter, so raising the instance never changes a
    ///    field type; and the constructor returns `I p₁ … pₖ`.
    fn is_template_poly_singleton_inductive(&self, ind: &InductiveVal) -> bool {
        // (1)/(2) shape counts.
        if ind.all_names.len() != 1 || ind.num_indices != 0 || ind.num_params == 0 {
            return false;
        }
        let k = ind.num_params as usize;
        if ind.level_params.len() != k || ind.constructor_names.len() != 1 {
            return false;
        }

        // (3) ARITY: Π (pᵢ : Sort lᵢ). … . Sort _, with lᵢ the i-th univ param.
        let mut ty: &Expr = &ind.type_;
        for level_param in &ind.level_params {
            let ExprKind::Pi(_, dom, cod) = ty.kind() else {
                return false;
            };
            let ExprKind::Sort(Level::Param(name)) = dom.kind() else {
                return false;
            };
            if name != level_param {
                return false;
            }
            ty = cod.as_ref();
        }
        // Fully applied to the parameters ⇒ the type former yields a genuine Sort.
        if !matches!(ty.kind(), ExprKind::Sort(_)) {
            return false;
        }

        // (4) CONSTRUCTOR: after k parameter binders, every field binder's type
        // is a bare BVar, and the result head is the inductive itself.
        let Some(ctor) = self.env.get_constructor(&ind.constructor_names[0]) else {
            return false;
        };
        if ctor.num_params as usize != k || ctor.num_fields == 0 {
            return false;
        }
        let mut cty: &Expr = &ctor.type_;
        for _ in 0..k {
            let ExprKind::Pi(_, _, cod) = cty.kind() else {
                return false;
            };
            cty = cod.as_ref();
        }
        for _ in 0..ctor.num_fields {
            let ExprKind::Pi(_, dom, cod) = cty.kind() else {
                return false;
            };
            if !matches!(dom.kind(), ExprKind::BVar(_)) {
                return false;
            }
            cty = cod.as_ref();
        }
        matches!(cty.get_app_fn().kind(), ExprKind::Const(n, _) if n == &ind.name)
    }
}
