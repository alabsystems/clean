// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-summand bound proof terms for T12 `to_ibp_sound`, plus the two atomic
//! abs lemmas it needs over the faithful `Rat.abs = max a (-a)` carrier:
//!
//! * `Rat.le_abs_self : ∀ a, a ≤ Rat.abs a`     (= `Rat.le_max_left a (-a)`)
//! * `Rat.neg_abs_le  : ∀ a, Rat.neg (Rat.abs a) ≤ a`
//!     (from `Rat.le_max_right a (-a) : -a ≤ |a|`, `Rat.neg_le_neg` and
//!      `Rat.neg_neg a : -(-a) = a`).
//!
//! The per-summand facts (for `g := G i j`, `e := ε j`, `t := Rat.mul g e`)
//! `upper_summand : t ≤ Rat.abs g` and `lower_summand : Rat.neg (Rat.abs g) ≤ t`
//! are both routed through `h_abs_t_le : Rat.abs t ≤ Rat.abs g`, itself
//! `|t| = |g|·|e| ≤ |g|·1 = |g|` via `Rat.abs_mul`, `NNVerify.mul_nonneg_le_left`
//! (with `Rat.abs_nonneg g` and `|e| ≤ 1`), and `Rat.mul_one`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants for the per-summand abs bound proofs.
pub(super) struct SummandConsts {
    pub(super) rat: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_neg: Expr,
    pub(super) rat_abs: Expr,
    pub(super) rat_mul: Expr,
    pub(super) abs_nonneg: Expr,
    pub(super) abs_mul: Expr,
    pub(super) mul_nonneg_le_left: Expr,
    pub(super) mul_one: Expr,
    pub(super) max_le: Expr,
    pub(super) neg_le_neg: Expr,
    pub(super) neg_neg: Expr,
    pub(super) le_abs_self: Expr,
    pub(super) neg_abs_le: Expr,
    pub(super) le_trans: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_subst: Expr,
    pub(super) and_right: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
}

impl SummandConsts {
    pub(super) fn new() -> Self {
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        Self {
            rat: c("Rat"),
            rat_one: c("Rat.one"),
            rat_neg: c("Rat.neg"),
            rat_abs: c("Rat.abs"),
            rat_mul: c("Rat.mul"),
            abs_nonneg: c("Rat.abs_nonneg"),
            abs_mul: c("Rat.abs_mul"),
            mul_nonneg_le_left: c("NNVerify.mul_nonneg_le_left"),
            mul_one: c("Rat.mul_one"),
            max_le: c("Rat.max_le"),
            neg_le_neg: c("Rat.neg_le_neg"),
            neg_neg: c("Rat.neg_neg"),
            le_abs_self: c("Rat.le_abs_self"),
            neg_abs_le: c("Rat.neg_abs_le"),
            le_trans: c("Rat.le_trans"),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
            and_right: c("And.right"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: c("instLERat"),
        }
    }

    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn abs(&self, a: Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), a)
    }
    fn neg(&self, a: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), a)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    /// Transport `h : Rat.le lhs a` to `Rat.le lhs b` along `h_eq : a = b`.
    fn transport_le_rhs(
        &self,
        parent: &EnvDeclBuilder,
        lhs: Expr,
        a: Expr,
        b: Expr,
        h: Expr,
        h_eq: Expr,
    ) -> Expr {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = d.fresh_local(self.rat.clone());
            let body = self.rat_le(lhs.clone(), x);
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }

    /// `h_e_le1 : Rat.abs e ≤ Rat.one`, from `hbound_j : (-1 ≤ e) ∧ (e ≤ 1)`.
    ///
    /// `Rat.max_le e (-e) 1 h_e_le1' h_neg_e_le1` where `h_e_le1' = And.right …`
    /// (`e ≤ 1`) and `h_neg_e_le1 = transport (Rat.neg_le_neg (-1) e h_neg1_le_e)`
    /// (`-e ≤ -(-1)`) along `Rat.neg_neg 1 : -(-1) = 1`. `Rat.abs e ≡ max e (-e)`.
    fn abs_e_le_one(&self, parent: &EnvDeclBuilder, e: Expr, hbound_j: Expr) -> Expr {
        let one = self.rat_one.clone();
        let neg_one = self.neg(one.clone());
        // le_e1 : e ≤ 1   = And.right (-1≤e) (e≤1) hbound_j.
        let p_neg1_le_e = self.rat_le(neg_one.clone(), e.clone());
        let p_e_le1 = self.rat_le(e.clone(), one.clone());
        let le_e1 = Expr::apps(
            self.and_right.clone(),
            [p_neg1_le_e.clone(), p_e_le1.clone(), hbound_j.clone()],
        );
        // h_neg1_le_e : -1 ≤ e   = And.left (-1≤e)(e≤1) hbound_j.
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let h_neg1_le_e = Expr::apps(and_left, [p_neg1_le_e, p_e_le1, hbound_j]);
        // neg_le_neg (-1) e h_neg1_le_e : Rat.neg e ≤ Rat.neg (Rat.neg 1).
        let nn = Expr::apps(
            self.neg_le_neg.clone(),
            [neg_one.clone(), e.clone(), h_neg1_le_e],
        );
        // transport RHS Rat.neg(Rat.neg 1) → 1 via Rat.neg_neg 1.
        let neg_neg_one = self.neg(neg_one.clone());
        let h_negneg = Expr::app(self.neg_neg.clone(), one.clone());
        let neg_e = self.neg(e.clone());
        let h_neg_e_le1 =
            self.transport_le_rhs(parent, neg_e, neg_neg_one, one.clone(), nn, h_negneg);
        // Rat.max_le e (-e) 1 le_e1 h_neg_e_le1 : max e (-e) ≤ 1 ≡ |e| ≤ 1.
        Expr::apps(
            self.max_le.clone(),
            [e.clone(), self.neg(e), one, le_e1, h_neg_e_le1],
        )
    }

    /// `h_abs_t_le : Rat.abs t ≤ Rat.abs g`  where `t = Rat.mul g e`.
    ///
    /// `|t| = |g|·|e|`  (Rat.abs_mul g e) ;
    /// `|g|·|e| ≤ |g|·1` (mul_nonneg_le_left |g| |e| 1 (abs_nonneg g) h_e_le1) ;
    /// `|g|·1 = |g|`     (Rat.mul_one |g|).
    /// Chain by transporting the middle ≤ on both ends.
    fn abs_t_le_abs_g(&self, parent: &EnvDeclBuilder, g: Expr, e: Expr, h_e_le1: Expr) -> Expr {
        let abs_g = self.abs(g.clone());
        let abs_e = self.abs(e.clone());
        let t = self.mul(g.clone(), e.clone());
        let abs_t = self.abs(t);
        // h_mid : |g|·|e| ≤ |g|·1.
        let abs_nonneg_g = Expr::app(self.abs_nonneg.clone(), g.clone());
        let h_mid = Expr::apps(
            self.mul_nonneg_le_left.clone(),
            [
                abs_g.clone(),
                abs_e.clone(),
                self.rat_one.clone(),
                abs_nonneg_g,
                h_e_le1,
            ],
        );
        // transport LHS: |g|·|e| → |t|  via Eq.symm (Rat.abs_mul g e) : |g|·|e| = |t|.
        // Rat.abs_mul g e : |g·e| = |g|·|e|  ⇒  symm : |g|·|e| = |t|.
        let abs_mul_ge = Expr::apps(self.abs_mul.clone(), [g.clone(), e.clone()]);
        let gmul_e = self.mul(abs_g.clone(), abs_e);
        let h_absmul_symm = Expr::apps(
            self.eq_symm.clone(),
            [self.rat.clone(), abs_t.clone(), gmul_e.clone(), abs_mul_ge],
        );
        // After transporting the LHS of h_mid from |g|·|e| to |t|:
        //   h_mid' : |t| ≤ |g|·1.
        // transport_le_lhs(rhs = |g|·1, a = |g|·|e|, b = |t|, h_mid, h_eq : |g|·|e| = |t|).
        let abs_g1 = self.mul(abs_g.clone(), self.rat_one.clone());
        let h_mid_lhs = self.transport_le_lhs(
            parent,
            abs_g1.clone(),
            gmul_e,
            abs_t.clone(),
            h_mid,
            h_absmul_symm,
        );
        // transport RHS: |g|·1 → |g|  via Rat.mul_one |g| : |g|·1 = |g|.
        let h_mul_one = Expr::app(self.mul_one.clone(), abs_g.clone());
        self.transport_le_rhs(parent, abs_t, abs_g1, abs_g, h_mid_lhs, h_mul_one)
    }

    /// Transport `h : Rat.le a rhs` to `Rat.le b rhs` along `h_eq : a = b`.
    fn transport_le_lhs(
        &self,
        parent: &EnvDeclBuilder,
        rhs: Expr,
        a: Expr,
        b: Expr,
        h: Expr,
        h_eq: Expr,
    ) -> Expr {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = d.fresh_local(self.rat.clone());
            let body = self.rat_le(x, rhs.clone());
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }

    /// `upper_summand : Rat.mul g e ≤ Rat.abs g`.
    /// `le_abs_self t : t ≤ |t|`, then `le_trans t |t| |g| (le_abs_self t) h_abs_t_le`.
    pub(super) fn upper_summand(
        &self,
        parent: &EnvDeclBuilder,
        g: Expr,
        e: Expr,
        hbound_j: Expr,
    ) -> Expr {
        let t = self.mul(g.clone(), e.clone());
        let abs_t = self.abs(t.clone());
        let abs_g = self.abs(g.clone());
        let h_e_le1 = self.abs_e_le_one(parent, e.clone(), hbound_j);
        let h_abs_t_le = self.abs_t_le_abs_g(parent, g, e, h_e_le1);
        let h_t_le_abst = Expr::app(self.le_abs_self.clone(), t.clone());
        Expr::apps(
            self.le_trans.clone(),
            [t, abs_t, abs_g, h_t_le_abst, h_abs_t_le],
        )
    }

    /// `lower_summand : Rat.neg (Rat.abs g) ≤ Rat.mul g e`.
    /// `neg_le_neg |t| |g| h_abs_t_le : -|g| ≤ -|t|`, `neg_abs_le t : -|t| ≤ t`,
    /// then `le_trans -|g| -|t| t`.
    pub(super) fn lower_summand(
        &self,
        parent: &EnvDeclBuilder,
        g: Expr,
        e: Expr,
        hbound_j: Expr,
    ) -> Expr {
        let t = self.mul(g.clone(), e.clone());
        let abs_t = self.abs(t.clone());
        let abs_g = self.abs(g.clone());
        let h_e_le1 = self.abs_e_le_one(parent, e.clone(), hbound_j);
        let h_abs_t_le = self.abs_t_le_abs_g(parent, g, e, h_e_le1);
        // neg_le_neg |t| |g| h_abs_t_le : -|g| ≤ -|t|.
        let h_neg = Expr::apps(
            self.neg_le_neg.clone(),
            [abs_t.clone(), abs_g.clone(), h_abs_t_le],
        );
        let neg_abs_g = self.neg(abs_g);
        let neg_abs_t = self.neg(abs_t);
        // neg_abs_le t : -|t| ≤ t.
        let h_negabs_le = Expr::app(self.neg_abs_le.clone(), t.clone());
        Expr::apps(
            self.le_trans.clone(),
            [neg_abs_g, neg_abs_t, t, h_neg, h_negabs_le],
        )
    }
}

impl Environment {
    /// Register `Rat.le_abs_self` and `Rat.neg_abs_le` over the faithful
    /// `Rat.abs = max a (-a)` carrier. Idempotent.
    pub(crate) fn register_rat_abs_self_bounds(&mut self) -> Result<(), EnvError> {
        self.register_rat_le_abs_self()?;
        self.register_rat_neg_abs_le()
    }

    /// `Rat.le_abs_self : ∀ a, Rat.le a (Rat.abs a)`.
    /// Value: `fun a => Rat.le_max_left a (Rat.neg a)` — retypes at
    /// `a ≤ Rat.abs a` because `Rat.abs a ≡ Rat.max a (Rat.neg a)` (reducible).
    fn register_rat_le_abs_self(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_abs_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let s = SummandConsts::new();
        let le_max_left = Expr::const_(Name::from_string("Rat.le_max_left"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(s.rat.clone());
            let body = s.rat_le(a.clone(), s.abs(a));
            b.finish(b.mk_pi(a_id, BinderInfo::Default, s.rat.clone(), body))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(s.rat.clone());
            let proof = Expr::apps(le_max_left, [a.clone(), s.neg(a.clone())]);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, s.rat.clone(), proof))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.neg_abs_le : ∀ a, Rat.le (Rat.neg (Rat.abs a)) a`.
    /// `Rat.le_max_right a (-a) : -a ≤ max a (-a) ≡ -a ≤ |a|`;
    /// `Rat.neg_le_neg (-a) |a| (…) : Rat.neg |a| ≤ Rat.neg (Rat.neg a)`;
    /// transport RHS `Rat.neg (Rat.neg a) → a` via `Rat.neg_neg a`.
    fn register_rat_neg_abs_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.neg_abs_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let s = SummandConsts::new();
        let le_max_right = Expr::const_(Name::from_string("Rat.le_max_right"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(s.rat.clone());
            let body = s.rat_le(s.neg(s.abs(a.clone())), a);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, s.rat.clone(), body))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(s.rat.clone());
            let neg_a = s.neg(a.clone());
            let abs_a = s.abs(a.clone());
            // h1 : -a ≤ |a|   (Rat.le_max_right a (-a), |a| ≡ max a (-a)).
            let h1 = Expr::apps(le_max_right, [a.clone(), neg_a.clone()]);
            // neg_le_neg (-a) |a| h1 : Rat.neg |a| ≤ Rat.neg (Rat.neg a).
            let nn = Expr::apps(s.neg_le_neg.clone(), [neg_a.clone(), abs_a.clone(), h1]);
            // transport RHS Rat.neg(Rat.neg a) → a via Rat.neg_neg a.
            let neg_neg_a = s.neg(neg_a);
            let h_negneg = Expr::app(s.neg_neg.clone(), a.clone());
            let neg_abs_a = s.neg(abs_a);
            let proof = s.transport_le_rhs(&b, neg_abs_a, neg_neg_a, a.clone(), nn, h_negneg);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, s.rat.clone(), proof))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
