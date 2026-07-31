// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! General `Rat.min_le_max` lattice lemma (Part of #3615 — C004 Phase 2
//! γ-scale prerequisite).
//!
//! Registers the constructive Mathlib-canonical theorem
//!
//! ```text
//! Rat.min_le_max : ∀ a b : Rat, Rat.le (Rat.min a b) (Rat.max a b)
//! ```
//!
//! as a sorry-free `Declaration::Theorem` with a kernel-checked proof term
//! composed from foundational axioms only. Closure:
//! `Rat.le_total`, `Rat.min_def`, `Rat.min_def'`, `Rat.max_def`,
//! `Rat.max_def'`, `Eq.subst`, `Eq.symm`, `Or.rec` — all entries of
//! `FOUNDATIONAL_AXIOMS` / constructive theorems.
//!
//! ## Proof sketch
//!
//! Dispatch on `Rat.le_total a b : Or (Rat.le a b) (Rat.le b a)` via
//! `Or.rec` against the constant motive `fun _ => Rat.le (min a b) (max a b)`.
//!
//! - **Case `inl (h : a ≤ b)`.**  `min_def a b h : min a b = a` and
//!   `max_def a b h : max a b = b`.  Starting from `h : a ≤ b`, two
//!   `Eq.subst`s transport the endpoints:
//!
//!     motive_L := fun z => Rat.le z b
//!     step_L   := Eq.subst @Rat motive_L a (min a b) (symm (min_def a b h)) h
//!              : Rat.le (min a b) b
//!
//!     motive_R := fun z => Rat.le (min a b) z
//!     result   := Eq.subst @Rat motive_R b (max a b) (symm (max_def a b h)) step_L
//!              : Rat.le (min a b) (max a b).
//!
//! - **Case `inr (h : b ≤ a)`.**  Symmetric: `min_def' a b h : min a b = b`
//!   and `max_def' a b h : max a b = a`.  From `h : b ≤ a`, transport via
//!
//!     step_L   := Eq.subst @Rat (fun z => Rat.le z a) b (min a b)
//!                   (symm (min_def' a b h)) h
//!     result   := Eq.subst @Rat (fun z => Rat.le (min a b) z) a (max a b)
//!                   (symm (max_def' a b h)) step_L.
//!
//! Each transport step is a textbook `Eq.subst` applied to the identity
//! produced by the corresponding `min_def` / `max_def` axiom; no new
//! domain axioms or trust envelopes are introduced.
//!
//! ## Part of
//!
//! - #3615 (C004 carrier infrastructure — unblocks Phase 2 γ-scale body)
//! - #3373 (C004 demoted equalities)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the canonical `Rat.min_le_max` lemma (#3615 prerequisite).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.rat_min_le_max_init == true`
    /// ENSURES: Idempotent — re-invocations short-circuit on the init flag.
    /// ENSURES: Registers `Rat.min_le_max` as `Declaration::Theorem` with a
    /// kernel type-checked proof term whose transitive closure contains only
    /// foundational axioms.
    pub fn init_rat_min_le_max(&mut self) -> Result<(), EnvError> {
        if self.rat_min_le_max_init {
            return Ok(());
        }
        // Dependencies:
        //   init_rat_linear_order → Rat.le, Rat.le_refl, Rat.le_total
        //   init_rat_minmax      → Rat.min, Rat.max, Rat.min_def/',
        //                          Rat.max_def/'
        //   init_or              → Or, Or.rec
        //   init_eq              → Eq, Eq.symm, Eq.subst
        self.init_rat_linear_order()?;
        self.init_rat_minmax()?;
        self.init_or()?;
        self.init_eq()?;

        self.register_rat_min_le_max()?;

        self.rat_min_le_max_init = true;
        Ok(())
    }

    /// Check whether the canonical `Rat.min_le_max` has been registered.
    #[cfg(test)]
    pub(crate) fn has_rat_min_le_max(&self) -> bool {
        self.rat_min_le_max_init
    }

    /// Register `Rat.min_le_max` with its constructive proof term.
    fn register_rat_min_le_max(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.min_le_max");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let consts = MinLeMaxConsts::new();
        let ty = build_min_le_max_type(&consts);
        let value = build_min_le_max_proof(&consts);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Shared constant `Expr`s used by the `Rat.min_le_max` proof builders.
struct MinLeMaxConsts {
    rat: Expr,
    rat_le: Expr,
    rat_min: Expr,
    rat_max: Expr,
    le_total: Expr,
    min_def: Expr,
    min_def_alt: Expr,
    max_def: Expr,
    max_def_alt: Expr,
    or_: Expr,
    or_rec: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
}

impl MinLeMaxConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_le: Expr::const_(Name::from_string("Rat.le"), vec![]),
            rat_min: Expr::const_(Name::from_string("Rat.min"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
            le_total: Expr::const_(Name::from_string("Rat.le_total"), vec![]),
            min_def: Expr::const_(Name::from_string("Rat.min_def"), vec![]),
            min_def_alt: Expr::const_(Name::from_string("Rat.min_def'"), vec![]),
            max_def: Expr::const_(Name::from_string("Rat.max_def"), vec![]),
            max_def_alt: Expr::const_(Name::from_string("Rat.max_def'"), vec![]),
            or_: Expr::const_(Name::from_string("Or"), vec![]),
            // `Or` is declared in `logic_or.rs` with `level_params: vec![]` —
            // `Or.rec` takes zero universe parameters.  The motive monomorphises
            // to Prop, so no additional level argument is required.  Mirrors
            // the pattern used in `nn_verify_relu_proofs::T81Consts`.
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![u1]),
        }
    }

    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_le.clone(), a), b)
    }

    fn min(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_min.clone(), a), b)
    }

    fn max(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_max.clone(), a), b)
    }

    /// `Rat.le_total a b`
    fn le_total_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.le_total.clone(), a), b)
    }

    /// `@Eq.symm.{1} Rat a b h`
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }

    /// `@Eq.subst.{1} Rat motive a b h_eq h_ma`
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_ma],
        )
    }

    /// `@Or.rec.{0} a_prop b_prop motive case_inl case_inr major`
    fn or_rec_app(
        &self,
        a_prop: Expr,
        b_prop: Expr,
        motive: Expr,
        case_inl: Expr,
        case_inr: Expr,
        major: Expr,
    ) -> Expr {
        Expr::apps(
            self.or_rec.clone(),
            [a_prop, b_prop, motive, case_inl, case_inr, major],
        )
    }
}

/// Type:  `∀ a b : Rat, Rat.le (Rat.min a b) (Rat.max a b)`.
fn build_min_le_max_type(c: &MinLeMaxConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let body = c.le(c.min(a.clone(), bv.clone()), c.max(a.clone(), bv.clone()));
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Constant `Or`-motive: `fun (_ : Or a_prop b_prop) => goal`.
fn or_const_motive(outer: &EnvDeclBuilder, or_ab: &Expr, goal: &Expr) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (h_id, _) = ch.fresh_local(or_ab.clone());
    let r = ch.mk_lam(h_id, BinderInfo::Default, or_ab.clone(), goal.clone());
    ch.finish_child(r)
}

/// Proof:
/// ```text
/// fun a b =>
///   Or.rec.{0}
///     (Rat.le a b)                   -- a_prop
///     (Rat.le b a)                   -- b_prop
///     (fun _ : Or _ _ => Rat.le (min a b) (max a b))
///     (case_inl : Rat.le a b   → Rat.le (min a b) (max a b))
///     (case_inr : Rat.le b a   → Rat.le (min a b) (max a b))
///     (Rat.le_total a b)
/// ```
fn build_min_le_max_proof(c: &MinLeMaxConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let min_ab = c.min(a.clone(), bv.clone());
    let max_ab = c.max(a.clone(), bv.clone());
    let goal = c.le(min_ab.clone(), max_ab.clone());

    let a_prop = c.le(a.clone(), bv.clone());
    let b_prop = c.le(bv.clone(), a.clone());
    let or_ab = Expr::app(Expr::app(c.or_.clone(), a_prop.clone()), b_prop.clone());

    let motive = or_const_motive(&b, &or_ab, &goal);
    let major = c.le_total_app(a.clone(), bv.clone());

    let case_inl = build_case_inl(c, &b, &a, &bv, &min_ab, &max_ab, &a_prop);
    let case_inr = build_case_inr(c, &b, &a, &bv, &min_ab, &max_ab, &b_prop);

    let body = c.or_rec_app(a_prop, b_prop, motive, case_inl, case_inr, major);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `case_inl : Rat.le a b → Rat.le (min a b) (max a b)`.
///
/// Given `h : a ≤ b`:
///   e_min : min a b = a      := Rat.min_def  a b h
///   e_max : max a b = b      := Rat.max_def  a b h
///   step₁ : Rat.le (min a b) b
///         := Eq.subst (fun z => Rat.le z b) a (min a b) (symm e_min) h
///   result : Rat.le (min a b) (max a b)
///         := Eq.subst (fun z => Rat.le (min a b) z) b (max a b)
///                     (symm e_max) step₁
fn build_case_inl(
    c: &MinLeMaxConsts,
    outer: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    min_ab: &Expr,
    max_ab: &Expr,
    a_prop: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (h_id, h) = ch.fresh_local(a_prop.clone());

    // e_min : Eq Rat (Rat.min a b) a
    let e_min = Expr::apps(c.min_def.clone(), [a.clone(), bv.clone(), h.clone()]);
    // e_max : Eq Rat (Rat.max a b) b
    let e_max = Expr::apps(c.max_def.clone(), [a.clone(), bv.clone(), h.clone()]);

    // motive_L : Rat → Prop  :=  fun z => Rat.le z b
    let motive_l = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let (z_id, z) = ch2.fresh_local(c.rat.clone());
        let body = c.le(z, bv.clone());
        let r = ch2.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body);
        ch2.finish_child(r)
    };

    // symm e_min : Eq Rat a (Rat.min a b)
    let symm_min = c.symm(min_ab.clone(), a.clone(), e_min);
    // step_l : Rat.le (Rat.min a b) b
    //        := Eq.subst @Rat motive_L a (min a b) (symm e_min) h
    let step_l = c.subst(motive_l, a.clone(), min_ab.clone(), symm_min, h.clone());

    // motive_R : Rat → Prop := fun z => Rat.le (min a b) z
    let motive_r = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let (z_id, z) = ch2.fresh_local(c.rat.clone());
        let body = c.le(min_ab.clone(), z);
        let r = ch2.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body);
        ch2.finish_child(r)
    };

    // symm e_max : Eq Rat b (Rat.max a b)
    let symm_max = c.symm(max_ab.clone(), bv.clone(), e_max);
    // result : Rat.le (min a b) (max a b)
    //        := Eq.subst @Rat motive_R b (max a b) (symm e_max) step_l
    let result = c.subst(motive_r, bv.clone(), max_ab.clone(), symm_max, step_l);

    let r = ch.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), result);
    ch.finish_child(r)
}

/// `case_inr : Rat.le b a → Rat.le (min a b) (max a b)`.
///
/// Given `h : b ≤ a`:
///   e_min : min a b = b      := Rat.min_def' a b h
///   e_max : max a b = a      := Rat.max_def' a b h
///   step₁ : Rat.le (min a b) a
///         := Eq.subst (fun z => Rat.le z a) b (min a b) (symm e_min) h
///   result : Rat.le (min a b) (max a b)
///         := Eq.subst (fun z => Rat.le (min a b) z) a (max a b)
///                     (symm e_max) step₁
fn build_case_inr(
    c: &MinLeMaxConsts,
    outer: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    min_ab: &Expr,
    max_ab: &Expr,
    b_prop: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (h_id, h) = ch.fresh_local(b_prop.clone());

    // e_min : Eq Rat (Rat.min a b) b
    let e_min = Expr::apps(c.min_def_alt.clone(), [a.clone(), bv.clone(), h.clone()]);
    // e_max : Eq Rat (Rat.max a b) a
    let e_max = Expr::apps(c.max_def_alt.clone(), [a.clone(), bv.clone(), h.clone()]);

    // motive_L : fun z => Rat.le z a
    let motive_l = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let (z_id, z) = ch2.fresh_local(c.rat.clone());
        let body = c.le(z, a.clone());
        let r = ch2.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body);
        ch2.finish_child(r)
    };

    // symm e_min : Eq Rat b (min a b)
    let symm_min = c.symm(min_ab.clone(), bv.clone(), e_min);
    // step_l : Rat.le (min a b) a
    let step_l = c.subst(motive_l, bv.clone(), min_ab.clone(), symm_min, h.clone());

    // motive_R : fun z => Rat.le (min a b) z
    let motive_r = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let (z_id, z) = ch2.fresh_local(c.rat.clone());
        let body = c.le(min_ab.clone(), z);
        let r = ch2.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body);
        ch2.finish_child(r)
    };

    // symm e_max : Eq Rat a (max a b)
    let symm_max = c.symm(max_ab.clone(), a.clone(), e_max);
    // result : Rat.le (min a b) (max a b)
    let result = c.subst(motive_r, a.clone(), max_ab.clone(), symm_max, step_l);

    let r = ch.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), result);
    ch.finish_child(r)
}
