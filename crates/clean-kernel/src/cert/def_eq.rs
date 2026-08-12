// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Definitional equality for `CertVerifier`.
//!
//! Thin wrappers that delegate to the shared `CertExprEqContext` trait
//! defined in `expr_eq.rs`. The verifier supplies its own full WHNF
//! (beta, zeta, delta, projection, iota, quotient) via `reduction.rs`.
//!
//! On top of the shared structural engine, the verifier implements the two
//! TYPE-DIRECTED kernel def-eq rules (`try_type_directed_eq`):
//!
//! - **Proof irrelevance** — `a ≡ b` when both inhabit the same `Prop`
//!   (mirrors `tc/def_eq/proof_irrel.rs`).
//! - **Structure eta** — `S.mk t₁ … tₙ ≡ s` fieldwise via projections when
//!   `s`'s type is the structure-like inductive `S` (mirrors the kernel's
//!   `try_structure_eta_core` in `tc/def_eq/structural.rs`).
//!
//! Both rules are PART of the kernel's definitional equality, so a faithful
//! implementation keeps the cert engine's acceptance a strict SUBSET of
//! kernel def-eq. Everything here is fail-closed: type inference is a
//! deliberately partial `infer_for_eq` (modeled on the kernel's
//! `try_infer_type_quick`) and any `None` means "the rule does not apply"
//! — never "equal".
//!
//! Extracted per design `designs/2026-03-10-2485-cert-builder-equality-extraction-and-module-split.md`.

use std::sync::LazyLock;

use crate::expr::{stack_safe, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;

use super::expr_eq::CertExprEqContext;
use super::verifier::CertVerifier;

static NAME_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static NAME_STRING: LazyLock<Name> = LazyLock::new(|| Name::from_string("String"));

/// Implement the shared equality trait for CertVerifier.
/// The verifier provides full WHNF from `reduction.rs` and the
/// type-directed rules (proof irrelevance + structure eta).
impl<'env> CertExprEqContext for CertVerifier<'env> {
    fn whnf_for_eq(&self, e: &Expr) -> Expr {
        // Delegates to the verifier's full WHNF in reduction.rs
        self.whnf_impl(e)
    }

    fn try_type_directed_eq(&self, ctx: &mut Vec<Expr>, a: &Expr, b: &Expr) -> bool {
        self.try_proof_irrel_eq(ctx, a, b)
            || self.try_struct_eta_eq(ctx, a, b)
            || self.try_unit_like_eq(ctx, a, b)
            || self.try_k_step_eq(ctx, a, b)
    }
}

impl<'env> CertVerifier<'env> {
    /// Check definitional equality (stack-safe entry point).
    pub(super) fn def_eq(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_impl(a, b)
    }

    /// Structural equality after WHNF (stack-safe entry point, test-only).
    #[cfg(test)]
    pub(super) fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        CertExprEqContext::structural_eq_impl(self, a, b)
    }

    /// Level equality — normalizes both sides before comparison.
    pub(super) fn level_eq(&self, l1: &Level, l2: &Level) -> bool {
        CertExprEqContext::level_eq(self, l1, l2)
    }

    /// Internal def_eq_impl — delegates to the shared trait engine.
    /// Called extensively from `verifier.rs` for type checking.
    ///
    /// Seeds the equality binder context from the verifier's own local
    /// context (`self.context`, same de-Bruijn-level convention as
    /// `verify_bvar`) so loose BVars in the compared expressions can be
    /// typed by the type-directed rules.
    pub(super) fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        let mut ctx = self.context.clone();
        CertExprEqContext::def_eq_impl(self, &mut ctx, a, b)
    }

    // ------------------------------------------------------------------
    // Type-directed definitional equality (proof irrelevance, struct eta)
    // ------------------------------------------------------------------

    /// Proof irrelevance: `a ≡ b` when `a : P`, `P : Prop`, and
    /// `typeof(b) ≡ P`.
    ///
    /// Mirrors `TypeChecker::is_def_eq_proof_irrel` (tc/def_eq/proof_irrel.rs):
    /// - Disabled in Cubical/Directed modes exactly as in the kernel
    ///   (definitional UIP is inconsistent with univalence; skipping is
    ///   strictly conservative).
    /// - The Prop test is a genuine Sort-0 inference on `typeof(a)`,
    ///   fail-closed on any inference failure.
    /// - Stricter than the kernel in one direction: the kernel also grants
    ///   irrelevance for `SProp`-sorted types; we do not (subset — sound).
    ///
    /// SOUNDNESS: for well-typed inputs, `infer_for_eq` returns (when it
    /// returns at all) the same type the kernel's inference computes, so
    /// every equation admitted here is admitted by kernel def-eq.
    fn try_proof_irrel_eq(&self, ctx: &mut Vec<Expr>, a: &Expr, b: &Expr) -> bool {
        if self.mode == CleanMode::Cubical || self.mode == CleanMode::Directed {
            return false;
        }
        let Some(ty_a) = self.infer_for_eq(ctx, a) else {
            return false;
        };
        if !self.type_is_prop_for_eq(ctx, &ty_a) {
            return false;
        }
        let Some(ty_b) = self.infer_for_eq(ctx, b) else {
            return false;
        };
        CertExprEqContext::def_eq_impl(self, ctx, &ty_a, &ty_b)
    }

    /// `ty` is a proposition: `whnf(ty)`'s inferred type is literally
    /// `Sort 0`. Fail-closed on any inference failure.
    ///
    /// The Sort quick-rejection is load-bearing: `Sort l : Sort (l+1)` is
    /// never a Prop, and rejecting it here is what stops proof irrelevance
    /// from ever identifying two propositions (rather than two proofs).
    fn type_is_prop_for_eq(&self, ctx: &mut Vec<Expr>, ty: &Expr) -> bool {
        let ty_whnf = self.whnf_impl(ty);
        if matches!(&ty_whnf.kind, ExprKind::Sort(_)) {
            return false;
        }
        // Kernel parity (tc/def_eq/proof_irrel.rs type_is_quickly_not_in_prop):
        // `Nat`/`String` are NEVER treated as propositions, even in a
        // malicious environment that re-declares them Prop-sorted. Without
        // this, a crafted .cleancert carrying `axiom Nat : Prop` would let
        // literal-typed proof irrelevance fire where the kernel's def-eq
        // refuses — the adversarial-env differential regression below pins
        // this exact divergence closed.
        if matches!(&ty_whnf.kind, ExprKind::Const(name, levels)
            if levels.is_empty() && (*name == *NAME_NAT || *name == *NAME_STRING))
        {
            return false;
        }
        let Some(ty_of_ty) = self.infer_for_eq(ctx, &ty_whnf) else {
            return false;
        };
        matches!(&self.whnf_impl(&ty_of_ty).kind, ExprKind::Sort(l) if l.is_zero())
    }

    /// Structure eta, both orientations (kernel `try_structure_eta_expansion`).
    fn try_struct_eta_eq(&self, ctx: &mut Vec<Expr>, a: &Expr, b: &Expr) -> bool {
        self.try_struct_eta_core(ctx, a, b) || self.try_struct_eta_core(ctx, b, a)
    }

    /// Lean 4's exact def-eq structure eta, mirrored from the kernel's
    /// `try_structure_eta_core` (tc/def_eq/structural.rs; Lean 4
    /// `type_checker.cpp:786-811 try_eta_struct_core(t, s)`):
    ///
    /// Fires ONLY when `t` is a saturated constructor application of a
    /// structure-like inductive (single constructor, no indices,
    /// non-recursive). `s`'s inferred type must be the same structure; the
    /// sides are then compared FIELDWISE via projections:
    /// `Proj i s ≡ t.field_i`. The ctor-app trigger keeps the recursion
    /// structural in `t` (termination) — never expand an arbitrary
    /// structure-typed term.
    ///
    /// SOUNDNESS: identical trigger + fieldwise decomposition as the
    /// kernel rule, with the type-of-`s` step fail-closed; every equation
    /// admitted here is admitted by kernel def-eq.
    fn try_struct_eta_core(&self, ctx: &mut Vec<Expr>, t: &Expr, s: &Expr) -> bool {
        let t_head = t.get_app_fn();
        let ExprKind::Const(head_name, _) = &t_head.kind else {
            return false;
        };
        let Some(ctor) = self.env.get_constructor(head_name) else {
            return false;
        };
        let Some(ind) = self.env.get_inductive(&ctor.inductive_name) else {
            return false;
        };
        // Kernel `is_structure_like`: one constructor, no indices, not recursive.
        if ind.constructor_names.len() != 1 || ind.num_indices != 0 || ind.is_recursive {
            return false;
        }
        let num_params = ctor.num_params as usize;
        let num_fields = ctor.num_fields as usize;
        let args = t.get_app_args();
        if args.len() != num_params + num_fields {
            return false;
        }
        // `s`'s type must be the same structure — fail-closed inference.
        let Some(s_ty) = self.infer_for_eq(ctx, s) else {
            return false;
        };
        let s_ty_whnf = self.whnf_impl(&s_ty);
        let s_ty_head = s_ty_whnf.get_app_fn();
        let ExprKind::Const(s_ind, _) = &s_ty_head.kind else {
            return false;
        };
        if *s_ind != ctor.inductive_name {
            return false;
        }
        // Fieldwise: Proj i s ≡ t.field_i.
        (0..ctor.num_fields).all(|i| {
            let proj = Expr::proj(ctor.inductive_name.clone(), i, s.clone());
            CertExprEqContext::def_eq_impl(self, ctx, &proj, args[num_params + i as usize])
        })
    }

    /// Unit-like collapse: `t ≡ s` when `t`'s type is a structure-like
    /// inductive whose single constructor has ZERO fields (`PUnit`, `Unit`,
    /// `True`-like data carriers) and `s`'s type is def-eq to it.
    ///
    /// Mirrors `TypeChecker::is_def_eq_unit_like` (tc/def_eq/structural.rs;
    /// Lean 4 `type_checker.cpp:1129-1130`): a zero-field structure has
    /// exactly one inhabitant up to definitional equality (0-ary structure
    /// eta), so any two terms of that type are equal.
    ///
    /// SOUNDNESS: same trigger conditions as the kernel rule with the two
    /// type inferences fail-closed; every equation admitted here is
    /// admitted by kernel def-eq.
    fn try_unit_like_eq(&self, ctx: &mut Vec<Expr>, t: &Expr, s: &Expr) -> bool {
        let Some(t_ty) = self.infer_for_eq(ctx, t) else {
            return false;
        };
        let t_ty_whnf = self.whnf_impl(&t_ty);
        let t_ty_head = t_ty_whnf.get_app_fn();
        let ExprKind::Const(ind_name, _) = &t_ty_head.kind else {
            return false;
        };
        let Some(ind) = self.env.get_inductive(ind_name) else {
            return false;
        };
        // Kernel `is_structure_like` + zero-field single constructor.
        if ind.constructor_names.len() != 1 || ind.num_indices != 0 || ind.is_recursive {
            return false;
        }
        let Some(ctor) = self.env.get_constructor(&ind.constructor_names[0]) else {
            return false;
        };
        if ctor.num_fields != 0 {
            return false;
        }
        let Some(s_ty) = self.infer_for_eq(ctx, s) else {
            return false;
        };
        CertExprEqContext::def_eq_impl(self, ctx, &t_ty_whnf, &self.whnf_impl(&s_ty))
    }

    /// K-like recursor step: if either side is a stuck application of a
    /// K-like recursor (`is_k`, e.g. `Eq.rec`) whose major premise can be
    /// K-converted to the unique nullary constructor, reduce that side and
    /// re-compare.
    ///
    /// This is the def-eq-level home of the kernel's `to_cnstr_when_K`
    /// (tc/reduction/mod.rs `try_to_cnstr_when_k`; Lean 4 inductive.h:31-49).
    /// It lives HERE rather than in the verifier's context-free WHNF because
    /// the conversion needs type inference of the major premise, which may
    /// mention loose BVars — only the equality recursion carries their
    /// binder types (`ctx`). Running inference against a misaligned context
    /// would be unsound; here the context is exact by construction.
    fn try_k_step_eq(&self, ctx: &mut Vec<Expr>, a: &Expr, b: &Expr) -> bool {
        if let Some(a_red) = self.k_convert_for_eq(ctx, a) {
            if CertExprEqContext::def_eq_impl(self, ctx, &a_red, b) {
                return true;
            }
        }
        if let Some(b_red) = self.k_convert_for_eq(ctx, b) {
            return CertExprEqContext::def_eq_impl(self, ctx, a, &b_red);
        }
        false
    }

    /// Mirror of the kernel's `try_to_cnstr_when_k`, fail-closed:
    /// for `Rec … major` with `rec.is_k`, when `typeof(major)` WHNFs to
    /// `I params indices` of the recursor's own inductive AND the unique
    /// nullary constructor applied to those params/indices has a def-eq
    /// type (the index-agreement check — e.g. `h : a = a`), rebuild the
    /// application with the constructor as major and WHNF (letting the
    /// ordinary iota rule fire).
    ///
    /// SOUNDNESS: identical firing conditions to the kernel rule; both
    /// inferences are fail-closed and the index agreement is checked with
    /// this engine's own (subset) def-eq. Any `None` leaves the old
    /// "not equal" answer in place.
    fn k_convert_for_eq(&self, ctx: &mut Vec<Expr>, e: &Expr) -> Option<Expr> {
        use crate::inductive::RecursorArgOrder;
        let head = e.get_app_fn();
        let ExprKind::Const(rec_name, rec_levels) = &head.kind else {
            return None;
        };
        let rec_val = self.env.get_recursor(rec_name)?;
        if !rec_val.is_k {
            return None;
        }
        let args = e.get_app_args();
        let major_pos = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_minors as usize
                    + rec_val.num_indices as usize
            }
            RecursorArgOrder::MajorAfterMotive => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_indices as usize
            }
        };
        if args.len() <= major_pos {
            return None;
        }
        let major = args[major_pos];
        // Already a constructor application — nothing to convert.
        if let ExprKind::Const(n, _) = &major.get_app_fn().kind {
            if self.env.get_constructor(n).is_some() {
                return None;
            }
        }
        // Fail-closed inference of the major's type: `I params indices`.
        let major_ty = self.infer_for_eq(ctx, major)?;
        let major_ty_whnf = self.whnf_impl(&major_ty);
        let ty_head = major_ty_whnf.get_app_fn();
        let ExprKind::Const(type_name, type_levels) = &ty_head.kind else {
            return None;
        };
        if *type_name != rec_val.inductive_name {
            return None;
        }
        // K-like types have a single nullary constructor.
        if rec_val.rules.len() != 1 {
            return None;
        }
        let ctor_name = &rec_val.rules[0].constructor_name;
        let ctor_val = self.env.get_constructor(ctor_name)?;
        let ctor_arity =
            (ctor_val.num_params as usize).checked_add(ctor_val.num_fields as usize)?;
        let num_params = rec_val.num_params as usize;
        // Constructor levels from recursor levels (rec_levels = [motive, inds…]),
        // falling back to the type's own levels — kernel parity.
        let ctor_levels: Vec<Level> = if rec_levels.len() > 1 {
            rec_levels[1..].to_vec()
        } else {
            type_levels.iter().cloned().collect()
        };
        let type_args = major_ty_whnf.get_app_args();
        if num_params > ctor_arity || type_args.len() < num_params {
            return None;
        }
        let mut ctor_app = Expr::const_(ctor_name.clone(), ctor_levels);
        for arg in type_args.iter().take(num_params) {
            ctor_app = Expr::app(ctor_app, (*arg).clone());
        }
        // Extra constructor args (fixed-index promotion case).
        let extra_ctor_args = ctor_arity - num_params;
        if type_args.len() < num_params + extra_ctor_args {
            return None;
        }
        for arg in type_args.iter().skip(num_params).take(extra_ctor_args) {
            ctor_app = Expr::app(ctor_app, (*arg).clone());
        }
        // Index agreement: the constructed constructor's type must be def-eq
        // to the major's type (this is what makes `h : a = a` K-firable and
        // `h : a = b` with `a ≢ b` NOT firable).
        let ctor_ty = self.infer_for_eq(ctx, &ctor_app)?;
        if !CertExprEqContext::def_eq_impl(self, ctx, &major_ty_whnf, &ctor_ty) {
            return None;
        }
        // Rebuild with the K-converted major and let ordinary iota fire.
        let mut result = head.clone();
        for (i, arg) in args.iter().enumerate() {
            result = Expr::app(
                result,
                if i == major_pos {
                    ctor_app.clone()
                } else {
                    (*arg).clone()
                },
            );
        }
        Some(self.whnf_impl(&result))
    }

    // ------------------------------------------------------------------
    // Fail-closed partial type inference for the equality engine
    // ------------------------------------------------------------------

    /// Infer the type of `e` under the equality binder context `ctx`
    /// (entry `i` expressed under `i` binders — the same convention as
    /// `CertVerifier::context` / `verify_bvar`).
    ///
    /// Deliberately PARTIAL, modeled on the kernel's `try_infer_type_quick`
    /// (tc/def_eq/proof_irrel.rs): returns `None` on ANY doubt, and callers
    /// treat `None` as "type-directed rule does not apply" — the old,
    /// conservative answer. For well-typed input this computes the same
    /// type (up to def-eq) as kernel inference; it is never consulted to
    /// certify a type, only to enable kernel-supported def-eq equations.
    fn infer_for_eq(&self, ctx: &mut Vec<Expr>, e: &Expr) -> Option<Expr> {
        stack_safe(|| self.infer_for_eq_inner(ctx, e))
    }

    fn infer_for_eq_inner(&self, ctx: &mut Vec<Expr>, e: &Expr) -> Option<Expr> {
        match &e.kind {
            ExprKind::BVar(i) => {
                let depth = ctx.len();
                let idx = *i as usize;
                if idx >= depth {
                    return None;
                }
                // Stored at depth (depth-1-idx); lift over the idx+1 binders
                // between there and here (same arithmetic as `verify_bvar`).
                Some(ctx[depth - 1 - idx].lift(i.checked_add(1)?))
            }
            ExprKind::FVar(id) => {
                let ty = self.fvar_types.get(id)?;
                // FVar types must be BVar-closed to be valid at any depth.
                if ty.has_loose_bvars() {
                    return None;
                }
                Some(ty.clone())
            }
            ExprKind::Const(name, levels) => self.env.instantiate_type(name, levels),
            ExprKind::Sort(l) => Some(Expr::from_kind(ExprKind::Sort(Level::succ(l.clone())))),
            ExprKind::App(f, a) => {
                let f_ty = self.infer_for_eq(ctx, f)?;
                let f_ty_whnf = self.whnf_impl(&f_ty);
                match &f_ty_whnf.kind {
                    ExprKind::Pi(_, _, result_type) => Some(result_type.instantiate(a)),
                    _ => None,
                }
            }
            ExprKind::Lam(bi, ty, body) => {
                ctx.push(ty.as_ref().clone());
                let body_ty = self.infer_for_eq(ctx, body);
                ctx.pop();
                Some(Expr::pi(*bi, ty.as_ref().clone(), body_ty?))
            }
            ExprKind::Lit(Literal::Nat(_)) => Some(Expr::const_(NAME_NAT.clone(), vec![])),
            ExprKind::Lit(Literal::String(_)) => Some(Expr::const_(NAME_STRING.clone(), vec![])),
            ExprKind::MData(_, inner) => self.infer_for_eq(ctx, inner),
            ExprKind::Proj(struct_name, idx, inner) => {
                let inner_ty = self.infer_for_eq(ctx, inner)?;
                // Independent environment-derived field type (soundness-
                // critical helper shared with `verify_proj`, #2064).
                self.derive_proj_field_type(struct_name, *idx, inner, &inner_ty)
                    .ok()
            }
            // Pi, Let, cubical, ZFC, Squash, …: not needed by the current
            // type-directed rules — fail closed.
            _ => None,
        }
    }
}
