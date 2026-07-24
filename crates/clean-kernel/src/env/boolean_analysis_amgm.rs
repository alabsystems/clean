// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **AM-GM-from-Cauchy-Schwarz** order helper.
//!
//! The keystone the `hc24` operator-induction step needs to combine the
//! Cauchy-Schwarz cross-term bound without taking square roots. Cauchy-Schwarz
//! gives `t² ≤ u·v` (with `t := E[A²B²]`, `u := E[A⁴]`, `v := E[B⁴]`); the
//! induction wants `2·t ≤ u + v`. The textbook route through `2√(uv) ≤ u+v`
//! drags in square roots; the root-free route is pure AM-GM:
//!
//! ```text
//! BoolAnalysis.two_mul_le_add_of_sq_le_mul :
//!   ∀ (t u v : Rat),
//!     Rat.le 0 t → Rat.le 0 u → Rat.le 0 v → Rat.le (t·t) (u·v) →
//!       Rat.le ((1+1)·t) (u + v)
//! ```
//!
//! ## Proof route (no square roots)
//!
//! From `t·t ≤ u·v` and `0 ≤ t, u, v`, derive `(2t)² ≤ (u+v)²` and invert with
//! `Rat.le_of_sq_le_sq`:
//!
//! 1. `((1+1)·t)·((1+1)·t) = ((1+1)·(1+1))·(t·t)`  [`Rat.mul_mul_mul_comm`]
//! 2. `((1+1)·(1+1))·(t·t) ≤ ((1+1)·(1+1))·(u·v)`  [`mul_le_mul_of_nonneg_left`,
//!    `0 ≤ (1+1)·(1+1)`]
//! 3. `((1+1)·(1+1))·(u·v) ≤ (u+v)·(u+v)`           [`four_mul_le_add_sq`, below]
//! 4. chain 1–3 (`subst` + `le_trans`):  `(2t)² ≤ (u+v)²`
//! 5. `0 ≤ 2t` (`mul_nonneg`), `0 ≤ u+v` (`le_trans` through `u ≤ u+v`)
//! 6. `Rat.le_of_sq_le_sq (2t) (u+v) (0≤2t) (0≤u+v) step4 : 2t ≤ u+v`.
//!
//! The sublemma `four_mul_le_add_sq : (2·2)·(u·v) ≤ (u+v)·(u+v)` is the AM-GM
//! core: `(u+v)·(u+v) = (u·u + v·v) + 2·(u·v)` [`Rat.add_sq_regroup`], and
//! `2·(u·v) ≤ u·u + v·v` from `0 ≤ (u−v)·(u−v)` [`Rat.sq_nonneg`] +
//! `Rat.sub_sq_regroup`; adding `2·(u·v)` to both sides of the latter and folding
//! `2·(u·v) + 2·(u·v) = (2·2)·(u·v)` closes it.
//!
//! Constructive (empty domain-axiom closure): leaves are
//! `Rat.le_of_sq_le_sq` / `Rat.mul_mul_mul_comm` / `Rat.add_sq_regroup` /
//! `Rat.sub_sq_regroup` / `Rat.sq_nonneg` / `Rat.mul_nonneg` /
//! `Rat.mul_le_mul_of_nonneg_left` / `Rat.add_le_add` / `Rat.le_trans`, all
//! already `Constructive`, plus `Eq`/`subst` built-ins.

use super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;
use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Initialize the AM-GM-from-Cauchy-Schwarz helper layer.
    ///
    /// Registers `BoolAnalysis.two_mul_le_add_of_sq_le_mul` as a kernel-checked
    /// `Declaration::Theorem`. Idempotent.
    ///
    /// Depends on `init_boolean_analysis_order_toolkit_b1d` (`Rat.le_of_sq_le_sq`)
    /// and `init_boolean_analysis_fourth_power` (`Rat.add_sq_regroup` /
    /// `Rat.sub_sq_regroup` / `Rat.mul_mul_mul_comm` + the constructive `Rat`
    /// ring/order surface). No axiom is added or removed.
    pub fn init_boolean_analysis_amgm(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_order_toolkit_b1d()?;
        self.init_boolean_analysis_fourth_power()?;
        // `Rat.add_le_add` and `Rat.le_of_sub_nonneg` are registered by the
        // interval-arith / rat-ordering layers the order toolkit transitively
        // pulls in; `Rat.mul_nonneg` likewise. Ensure they are present.
        self.register_rat_add_le_add()?;

        let name = Name::from_string("BoolAnalysis.two_mul_le_add_of_sq_le_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = AmGmConsts::new();
        let ty = build_amgm_type(&c);
        let value = build_amgm_proof(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Constants + smart-constructors for the AM-GM helper. Bundles the `RingConsts`
/// ring surface and the `HcBoundsConsts` order surface (both wrap an
/// `OrderConsts`, so atoms agree byte-for-byte).
struct AmGmConsts {
    r: RingConsts,
    o: HcBoundsConsts,
    mul_nonneg: Expr,
    add_le_add: Expr,
    le_of_sq_le_sq: Expr,
    add_sq_regroup: Expr,
    sub_sq_regroup: Expr,
    mul_mul_mul_comm: Expr,
}

impl AmGmConsts {
    fn new() -> Self {
        Self {
            r: RingConsts::new(),
            o: HcBoundsConsts::new(),
            mul_nonneg: Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            add_le_add: Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
            le_of_sq_le_sq: Expr::const_(Name::from_string("Rat.le_of_sq_le_sq"), vec![]),
            add_sq_regroup: Expr::const_(Name::from_string("Rat.add_sq_regroup"), vec![]),
            sub_sq_regroup: Expr::const_(Name::from_string("Rat.sub_sq_regroup"), vec![]),
            mul_mul_mul_comm: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.r.rat()
    }
    fn one(&self) -> Expr {
        self.r.one()
    }
    fn two(&self) -> Expr {
        self.r.two()
    }
    /// `(1+1)·(1+1)` — the literal `4` the squares expand to.
    fn four(&self) -> Expr {
        self.r.mul(self.two(), self.two())
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.r.add(a, b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.r.mul(a, b)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.r.sub(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.le(a, b)
    }
    fn zero(&self) -> Expr {
        self.o.zero()
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.r.trans(a, b, cc, h1, h2)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.r.symm(a, b, h)
    }

    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nn(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.add_le_add a b c d hab hcd : a+c ≤ b+d`.
    fn add_le(&self, a: Expr, b: Expr, cc: Expr, dd: Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a, b, cc, dd, hab, hcd])
    }
    /// `Rat.le_of_sq_le_sq a b ha hb h : a ≤ b`.
    fn le_of_sq(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_of_sq_le_sq.clone(), [a, b, ha, hb, h])
    }
    /// `Rat.add_sq_regroup u v : (u+v)·(u+v) = (u·u + v·v) + (1+1)·(u·v)`.
    fn add_sq_regroup(&self, u: Expr, v: Expr) -> Expr {
        Expr::apps(self.add_sq_regroup.clone(), [u, v])
    }
    /// `Rat.sub_sq_regroup u v : (u−v)·(u−v) = (u·u + v·v) + (1+1)·(u·(−v))`.
    fn sub_sq_regroup(&self, u: Expr, v: Expr) -> Expr {
        Expr::apps(self.sub_sq_regroup.clone(), [u, v])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, dd: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, cc, dd])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nn(&self, a: Expr) -> Expr {
        self.o.sqnn(a)
    }
}

/// Type: `∀ t u v, 0 ≤ t → 0 ≤ u → 0 ≤ v → t·t ≤ u·v → (1+1)·t ≤ u+v`.
fn build_amgm_type(c: &AmGmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (t_id, t) = b.fresh_local(c.rat());
    let (u_id, u) = b.fresh_local(c.rat());
    let (v_id, v) = b.fresh_local(c.rat());
    let h_t_ty = c.le(c.zero(), t.clone());
    let h_u_ty = c.le(c.zero(), u.clone());
    let h_v_ty = c.le(c.zero(), v.clone());
    let h_sq_ty = c.le(c.mul(t.clone(), t.clone()), c.mul(u.clone(), v.clone()));
    let concl = c.le(c.mul(c.two(), t.clone()), c.add(u.clone(), v.clone()));
    let (ht_id, _) = b.fresh_local(h_t_ty.clone());
    let (hu_id, _) = b.fresh_local(h_u_ty.clone());
    let (hv_id, _) = b.fresh_local(h_v_ty.clone());
    let (hsq_id, _) = b.fresh_local(h_sq_ty.clone());
    let e = b.mk_pi(hsq_id, BinderInfo::Default, h_sq_ty, concl);
    let e = b.mk_pi(hv_id, BinderInfo::Default, h_v_ty, e);
    let e = b.mk_pi(hu_id, BinderInfo::Default, h_u_ty, e);
    let e = b.mk_pi(ht_id, BinderInfo::Default, h_t_ty, e);
    let e = b.mk_pi(v_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(u_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(t_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// `0 ≤ (1+1)·(1+1)` via `mul_nonneg (1+1) (1+1) (0≤2) (0≤2)`.
fn zero_le_four(c: &AmGmConsts) -> Expr {
    let z2 = c.o.zero_le_two();
    c.mul_nn(c.two(), c.two(), z2.clone(), z2)
}

/// `(2·2)·(u·v) ≤ (u+v)·(u+v)`  — the AM-GM core.
///
/// `add_sq_regroup u v : (u+v)² = (u·u + v·v) + 2·(u·v)`.
/// `h_2uv : 2·(u·v) ≤ (u·u + v·v)` from `sub_sq_regroup` + `sq_nonneg`.
/// Then `(2·2)·(u·v) = 2·(u·v) + 2·(u·v)` and
/// `add_le_add (2uv) (u²+v²) (2uv) (2uv) h_2uv (le_refl 2uv)` gives
/// `2uv + 2uv ≤ (u²+v²) + 2uv = (u+v)²`.
fn four_mul_le_add_sq(c: &AmGmConsts, parent: &EnvDeclBuilder, u: &Expr, v: &Expr) -> Expr {
    let uu = c.mul(u.clone(), u.clone());
    let vv = c.mul(v.clone(), v.clone());
    let uv = c.mul(u.clone(), v.clone());
    let u2_v2 = c.add(uu.clone(), vv.clone());
    let two_uv = c.mul(c.two(), uv.clone()); // 2·(u·v)
    let usq_plus = c.add(u2_v2.clone(), two_uv.clone()); // (u²+v²) + 2·(u·v)
    let uv_sq = c.mul(c.add(u.clone(), v.clone()), c.add(u.clone(), v.clone())); // (u+v)²

    // h_2uv : 2·(u·v) ≤ (u·u + v·v).
    let h_2uv = build_two_uv_le(c, parent, u, v);

    // h_le_refl : 2uv ≤ 2uv.
    let le_refl = Expr::app(
        Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        two_uv.clone(),
    );
    // add_le_add (2uv) (u²+v²) (2uv) (2uv) h_2uv h_le_refl
    //   : 2uv + 2uv ≤ (u²+v²) + 2uv.
    let sum_le = c.add_le(
        two_uv.clone(),
        u2_v2.clone(),
        two_uv.clone(),
        two_uv.clone(),
        h_2uv,
        le_refl,
    );
    let lhs_sum = c.add(two_uv.clone(), two_uv.clone()); // 2uv + 2uv

    // eq_four : (2·2)·(u·v) = 2·(u·v) + 2·(u·v).
    //   right_distrib 2 2 (u·v) : (2+2)·(u·v) = 2·(u·v) + 2·(u·v); but we want
    //   (2·2)·(u·v) on the left. Build it the other way: fold lhs_sum to four_uv
    //   via mmmc? No — use: four_uv = (2·2)·(u·v); right side needs (2·2)·uv.
    //   We prove eq_four : (2·2)·(u·v) = 2·(u·v) + 2·(u·v) below.
    let four_uv = c.mul(c.four(), uv.clone());
    let eq_four = build_four_uv_eq(c, parent, &uv);

    // subst lhs of sum_le: rewrite (2uv + 2uv) ⇐ (2·2)·(u·v).
    //   sum_le : lhs_sum ≤ usq_plus; want four_uv ≤ usq_plus.
    let h_four_le_usq = c.o.subst_le_left(
        parent,
        usq_plus.clone(),
        lhs_sum.clone(),
        four_uv.clone(),
        c.symm(four_uv.clone(), lhs_sum.clone(), eq_four),
        sum_le,
    );
    // subst rhs: rewrite usq_plus ⇒ (u+v)² via add_sq_regroup.symm.
    //   add_sq_regroup u v : (u+v)² = usq_plus  ⇒ symm : usq_plus = (u+v)².
    let h_eq_usq = c.symm(
        uv_sq.clone(),
        usq_plus.clone(),
        c.add_sq_regroup(u.clone(), v.clone()),
    );
    c.o.subst_le_right(parent, four_uv, usq_plus, uv_sq, h_eq_usq, h_four_le_usq)
}

/// `(2·2)·(u·v) = 2·(u·v) + 2·(u·v)`.
///
/// `right_distrib 2 2 (u·v) : (2+2)·(u·v) = 2·(u·v) + 2·(u·v)`, and
/// `(2·2) = (2+2)` via `Rat.two_mul`-shape... built here directly:
/// `(2·2)·uv = (2+2)·uv` [cong_left on `2·2 = 2+2`] then `right_distrib`.
fn build_four_uv_eq(c: &AmGmConsts, parent: &EnvDeclBuilder, uv: &Expr) -> Expr {
    let two = c.two();
    let four_mul = c.mul(two.clone(), two.clone()); // 2·2
    let four_add = c.add(two.clone(), two.clone()); // 2+2
    let two_uv = c.mul(two.clone(), uv.clone());
    let sum = c.add(two_uv.clone(), two_uv.clone());

    // eq_22 : 2·2 = 2+2  (Rat.two_mul applied at t := 2: (1+1)·2 = 2 + 2).
    let eq_22 = c.r.two_mul(parent, two.clone());
    // cong_left: (2·2)·uv = (2+2)·uv.
    let mul_c = c.r.mul_const();
    let c1 = c.r.cong_left(
        parent,
        &mul_c,
        four_mul.clone(),
        four_add.clone(),
        uv.clone(),
        eq_22,
    );
    let four_add_uv = c.mul(four_add.clone(), uv.clone());
    // right_distrib 2 2 uv : (2+2)·uv = 2·uv + 2·uv.
    let c2 = c.r.rdist(two.clone(), two, uv.clone());
    c.trans(c.mul(four_mul, uv.clone()), four_add_uv, sum, c1, c2)
}

/// `2·(u·v) ≤ (u·u + v·v)`.
///
/// `sub_sq_regroup u v : (u−v)·(u−v) = (u·u + v·v) + 2·(u·(−v))`.
/// `sq_nonneg (u−v) : 0 ≤ (u−v)·(u−v)`, so `0 ≤ (u²+v²) + 2·(u·(−v))`.
/// `2·(u·(−v)) = −(2·(u·v))` [`mul_neg` lifts], so the RHS is `(u²+v²) − 2uv`;
/// `0 ≤ (u²+v²) − 2uv` ⟺ `2uv ≤ u²+v²` by `le_of_sub_nonneg`.
fn build_two_uv_le(c: &AmGmConsts, parent: &EnvDeclBuilder, u: &Expr, v: &Expr) -> Expr {
    let uu = c.mul(u.clone(), u.clone());
    let vv = c.mul(v.clone(), v.clone());
    let u2_v2 = c.add(uu.clone(), vv.clone());
    let uv = c.mul(u.clone(), v.clone());
    let two_uv = c.mul(c.two(), uv.clone());
    let neg_v = c.r.neg(v.clone());
    let u_negv = c.mul(u.clone(), neg_v.clone()); // u·(−v)
    let two_u_negv = c.mul(c.two(), u_negv.clone()); // 2·(u·(−v))
    let sub_sq = c.mul(c.sub(u.clone(), v.clone()), c.sub(u.clone(), v.clone())); // (u−v)²
    let regroup_rhs = c.add(u2_v2.clone(), two_u_negv.clone()); // (u²+v²) + 2·(u·(−v))

    // h0 : 0 ≤ (u−v)².
    let h0_sq = c.sq_nn(c.sub(u.clone(), v.clone()));
    // h0 : 0 ≤ (u²+v²) + 2·(u·(−v))  via subst_le_right along sub_sq_regroup.
    let h0 = c.o.subst_le_right(
        parent,
        c.zero(),
        sub_sq.clone(),
        regroup_rhs.clone(),
        c.sub_sq_regroup(u.clone(), v.clone()),
        h0_sq,
    );

    // eq_neg : 2·(u·(−v)) = −(2·(u·v)).
    //   u·(−v) = −(u·v)  [Rat.mul_neg u v]; lift over (2·_): 2·(u·(−v)) = 2·(−(u·v));
    //   2·(−(u·v)) = −(2·(u·v))  [Rat.mul_neg 2 (u·v)].
    let mneg_uv = c.r.mneg(u.clone(), v.clone()); // u·(−v) = −(u·v)
    let neg_uv = c.r.neg(uv.clone());
    let mul_c = c.r.mul_const();
    let c_lift = c.r.cong_right(
        parent,
        &mul_c,
        u_negv.clone(),
        neg_uv.clone(),
        c.two(),
        mneg_uv,
    );
    let two_neg_uv = c.mul(c.two(), neg_uv.clone()); // 2·(−(u·v))
    let mneg_2uv = c.r.mneg(c.two(), uv.clone()); // 2·(−(u·v)) = −(2·(u·v))
    let neg_two_uv = c.r.neg(two_uv.clone());
    let eq_neg = c.trans(
        two_u_negv.clone(),
        two_neg_uv,
        neg_two_uv.clone(),
        c_lift,
        mneg_2uv,
    );

    // rewrite h0's RHS cross term: (u²+v²) + 2·(u·(−v)) ⇒ (u²+v²) + (−(2uv)).
    let add_c = c.r.add_const();
    let c_rhs = c.r.cong_right(
        parent,
        &add_c,
        two_u_negv,
        neg_two_uv.clone(),
        u2_v2.clone(),
        eq_neg,
    );
    let u2v2_minus = c.add(u2_v2.clone(), neg_two_uv.clone()); // (u²+v²) + (−(2uv))
                                                               // h1 : 0 ≤ (u²+v²) + (−(2uv)).
    let h1 =
        c.o.subst_le_right(parent, c.zero(), regroup_rhs, u2v2_minus, c_rhs, h0);

    // (u²+v²) + (−(2uv)) is defeq to (u²+v²) − (2uv)  [Rat.sub reducible].
    //   le_of_sub_nonneg (2uv) (u²+v²) h1 : 2uv ≤ (u²+v²).
    let le_of_sub = Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]);
    Expr::apps(le_of_sub, [two_uv, u2_v2, h1])
}

/// Build the proof term for `BoolAnalysis.two_mul_le_add_of_sq_le_mul`.
fn build_amgm_proof(c: &AmGmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (t_id, t) = b.fresh_local(c.rat());
    let (u_id, u) = b.fresh_local(c.rat());
    let (v_id, v) = b.fresh_local(c.rat());
    let h_t_ty = c.le(c.zero(), t.clone());
    let h_u_ty = c.le(c.zero(), u.clone());
    let h_v_ty = c.le(c.zero(), v.clone());
    let h_sq_ty = c.le(c.mul(t.clone(), t.clone()), c.mul(u.clone(), v.clone()));
    let (ht_id, h_t) = b.fresh_local(h_t_ty.clone());
    let (hu_id, h_u) = b.fresh_local(h_u_ty.clone());
    let (hv_id, h_v) = b.fresh_local(h_v_ty.clone());
    let (hsq_id, h_sq) = b.fresh_local(h_sq_ty.clone());

    let two = c.two();
    let two_t = c.mul(two.clone(), t.clone()); // 2t
    let tt = c.mul(t.clone(), t.clone());
    let uv = c.mul(u.clone(), v.clone());
    let four = c.four();
    let u_plus_v = c.add(u.clone(), v.clone());
    let uv_sq = c.mul(u_plus_v.clone(), u_plus_v.clone()); // (u+v)²
    let two_t_sq = c.mul(two_t.clone(), two_t.clone()); // (2t)²

    // step1 : (2t)·(2t) = (2·2)·(t·t)   [mul_mul_mul_comm 2 t 2 t].
    let step1 = c.mmmc(two.clone(), t.clone(), two.clone(), t.clone());
    let four_tt = c.mul(four.clone(), tt.clone()); // (2·2)·(t·t)

    // step2 : (2·2)·(t·t) ≤ (2·2)·(u·v)   [mul_le_left four (t·t) (u·v) h_sq (0≤four)].
    let four_uv = c.mul(four.clone(), uv.clone());
    let z4 = zero_le_four(c);
    let step2 = c.o.mll(four.clone(), tt.clone(), uv.clone(), h_sq, z4);

    // step3 : (2·2)·(u·v) ≤ (u+v)·(u+v)   [four_mul_le_add_sq].
    let step3 = four_mul_le_add_sq(c, &b, &u, &v);

    // chain23 : (2·2)·(t·t) ≤ (u+v)²   [le_trans four_tt four_uv uv_sq step2 step3].
    let chain23 =
        c.o.ltrans(four_tt.clone(), four_uv, uv_sq.clone(), step2, step3);

    // sq_le : (2t)·(2t) ≤ (u+v)²   [subst_le_left along step1.symm].
    let sq_le = c.o.subst_le_left(
        &b,
        uv_sq.clone(),
        four_tt.clone(),
        two_t_sq.clone(),
        c.symm(two_t_sq.clone(), four_tt, step1),
        chain23,
    );

    // h_2t_nn : 0 ≤ 2t   [mul_nonneg 2 t (0≤2) h_t].
    let z2 = c.o.zero_le_two();
    let h_2t_nn = c.mul_nn(two.clone(), t.clone(), z2, h_t);
    // h_uv_nn : 0 ≤ u+v   [le_trans 0 u (u+v) h_u (u ≤ u+v)].
    let u_le_sum = c.o.le_add_nn(u.clone(), v.clone(), h_v);
    let h_uv_nn =
        c.o.ltrans(c.zero(), u.clone(), u_plus_v.clone(), h_u, u_le_sum);

    // le_of_sq_le_sq (2t) (u+v) h_2t_nn h_uv_nn sq_le : 2t ≤ u+v.
    let proof = c.le_of_sq(two_t, u_plus_v, h_2t_nn, h_uv_nn, sq_le);

    let e = b.mk_lam(hsq_id, BinderInfo::Default, h_sq_ty, proof);
    let e = b.mk_lam(hv_id, BinderInfo::Default, h_v_ty, e);
    let e = b.mk_lam(hu_id, BinderInfo::Default, h_u_ty, e);
    let e = b.mk_lam(ht_id, BinderInfo::Default, h_t_ty, e);
    let e = b.mk_lam(v_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(u_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(t_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_two_mul_le_add_of_sq_le_mul_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_amgm()
            .expect("init_boolean_analysis_amgm");
        let name = Name::from_string("BoolAnalysis.two_mul_le_add_of_sq_le_mul");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("amgm proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
