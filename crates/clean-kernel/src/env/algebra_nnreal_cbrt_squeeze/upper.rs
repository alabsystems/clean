// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 2 (`cbrtDyadicApprox_le_one`) and rung 3 (the UPPER cube squeeze
//! `x < a_n³ + 7·inv(2^n)`) on `0 ≤ x < 1`.
//!
//! - **Rung 2** `Rat.cbrtDyadicApprox_le_one : ∀ x, 0≤x → x<1 → ∀ n, a_n ≤ 1`.
//!   From the LOWER squeeze `a_n³ ≤ x` (`cbrtDyadicApprox_cube_le`) and `x < 1`,
//!   `a_n³ < 1`, hence `a_n³ ≤ 1`. Transport `1 = 1³` (two `mul_one`) to
//!   `a_n³ ≤ 1³`, then `Rat.le_of_cube_le_cube a_n 1 (0≤a_n)(0≤1)(a_n³≤1³)`.
//!
//! - **Rung 3** `Rat.x_lt_cbrtDyadicApprox_cube_add_seven_inv :
//!     ∀ x, 0≤x → x<1 → ∀ n,
//!       x < a_n³ + ((((((iv+iv)+iv)+iv)+iv)+iv)+iv)`  (`iv := inv(2^n)`).
//!   Mirrors the sqrt UPPER bound one cubic degree up: divide
//!   `cbrtDyadicNum_cube_lt_succ` by `8^n`, expand `b_n³ = (a_n+iv)³` via
//!   `Rat.add_cube`, and bound the three error summands `3·a_n²iv`, `3·a_n·iv²`,
//!   `iv³` each by `≤ 3iv`, `≤ 3iv`, `≤ iv` using `a_n ≤ 1` (rung 2) and
//!   `iv ≤ 1` (`Rat.inv_two_pow_le_one`).

use super::CbrtSqueezeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl CbrtSqueezeConsts {
    /// `3·t = (t+t)+t` where `3 = (1+1)+1`. `right_distrib (1+1) 1 t`,
    /// then `(1+1)·t → t+t` (`right_distrib 1 1 t` + two `one_mul`) and `1·t → t`.
    fn three_mul_eq(&self, parent: &EnvDeclBuilder, t: &Expr) -> Expr {
        let one = self.rat_one.clone();
        let two = self.add(one.clone(), one.clone());
        let three = self.add(two.clone(), one.clone());
        let three_t = self.mul(three.clone(), t.clone());
        let two_t = self.mul(two.clone(), t.clone());
        let one_t = self.mul(one.clone(), t.clone());
        let t_plus_t = self.add(t.clone(), t.clone());
        // d : 3·t = (1+1)·t + 1·t
        let d = self.right_distrib(two.clone(), one.clone(), t.clone());
        let two_t_plus_one_t = self.add(two_t.clone(), one_t.clone());
        // (1+1)·t = t+t :  right_distrib 1 1 t + two one_mul
        let two_mul = {
            let dd = self.right_distrib(one.clone(), one.clone(), t.clone()); // (1+1)·t = 1·t+1·t
            let one_t_plus_one_t = self.add(one_t.clone(), one_t.clone());
            // left 1·t → t
            let f_l = self.f_add_right(parent, one_t.clone());
            let c1 = self.congr_arg(one_t.clone(), t.clone(), f_l, self.one_mul(t.clone()));
            let t_plus_one_t = self.add(t.clone(), one_t.clone());
            // right 1·t → t
            let f_r = self.f_add_left(parent, t.clone());
            let c2 = self.congr_arg(one_t.clone(), t.clone(), f_r, self.one_mul(t.clone()));
            let s1 = self.trans(
                two_t.clone(),
                one_t_plus_one_t.clone(),
                t_plus_one_t.clone(),
                dd,
                c1,
            );
            self.trans(two_t.clone(), t_plus_one_t, t_plus_t.clone(), s1, c2)
        };
        // congr (·+1·t) two_mul : (1+1)·t + 1·t = (t+t) + 1·t
        let f_l2 = self.f_add_right(parent, one_t.clone());
        let c_l = self.congr_arg(two_t.clone(), t_plus_t.clone(), f_l2, two_mul);
        let tt_plus_one_t = self.add(t_plus_t.clone(), one_t.clone());
        // congr ((t+t)+·) one_mul : (t+t)+1·t = (t+t)+t
        let f_r2 = self.f_add_left(parent, t_plus_t.clone());
        let c_r = self.congr_arg(one_t.clone(), t.clone(), f_r2, self.one_mul(t.clone()));
        let tt_plus_t = self.add(t_plus_t.clone(), t.clone());
        // chain: 3·t = two_t+one_t = (t+t)+1·t = (t+t)+t
        let s1 = self.trans(
            three_t.clone(),
            two_t_plus_one_t.clone(),
            tt_plus_one_t.clone(),
            d,
            c_l,
        );
        self.trans(three_t, tt_plus_one_t, tt_plus_t, s1, c_r)
    }

    /// `congrArg` of `fun t => t + r`.
    fn f_add_right(&self, parent: &EnvDeclBuilder, r: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.add(w, r);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `congrArg` of `fun t => l + t`.
    fn f_add_left(&self, parent: &EnvDeclBuilder, l: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.add(l, w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `congrArg` of `fun t => t · r`.
    fn f_mul_right(&self, parent: &EnvDeclBuilder, r: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.mul(w, r);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `congrArg` of `fun t => l · t`.
    fn f_mul_left(&self, parent: &EnvDeclBuilder, l: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.mul(l, w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `3 := (1+1)+1` over `Rat`.
    fn three_const(&self) -> Expr {
        let one = self.rat_one.clone();
        self.add(self.add(one.clone(), one.clone()), one)
    }
    /// `0 ≤ (1+1)+1`. `0 ≤ 1` (`zero_le_one`); `0 ≤ 1+1` (`add_le_add 0 1 0 1`
    /// transported along `0+0 = 0`); `0 ≤ (1+1)+1` (`le_trans` via `1+1 ≤ (1+1)+1`?
    /// simpler: `add_le_add 0 (1+1) 0 1` transported along `0+0 = 0`).
    fn zero_le_three(&self, parent: &EnvDeclBuilder) -> Expr {
        let one = self.rat_one.clone();
        let two = self.add(one.clone(), one.clone());
        let three = self.three_const();
        let zero = self.rat_zero.clone();
        let zle1 = self.zero_le_one();
        let add_zero0 = Expr::app(
            Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            zero.clone(),
        ); // 0+0 = 0
        let zero_zero = self.add(zero.clone(), zero.clone());
        // 0 ≤ 1+1:  add_le_add 0 1 0 1 (0≤1)(0≤1) : 0+0 ≤ 1+1, transport 0+0 → 0.
        let h00_le_two = self.add_le_add(
            zero.clone(),
            one.clone(),
            zero.clone(),
            one.clone(),
            zle1.clone(),
            zle1.clone(),
        );
        let motive2 = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(t, two.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let h0_two = self.subst(
            motive2,
            zero_zero.clone(),
            zero.clone(),
            add_zero0.clone(),
            h00_le_two,
        ); // 0 ≤ 1+1
           // 0 ≤ (1+1)+1:  add_le_add 0 (1+1) 0 1 (0≤1+1)(0≤1) : 0+0 ≤ (1+1)+1, transport.
        let h00_le_three = self.add_le_add(
            zero.clone(),
            two.clone(),
            zero.clone(),
            one.clone(),
            h0_two,
            zle1,
        );
        let motive3 = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(t, three.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive3, zero_zero, zero, add_zero0, h00_le_three) // 0 ≤ (1+1)+1
    }
    /// `t·u ≤ u` from `t ≤ 1` and `0 ≤ u`:  `mul_le_right u t 1 (t≤1)(0≤u)`
    /// gives `t·u ≤ 1·u`; `one_mul u` rewrites RHS to `u`.
    fn mul_le_of_le_one_right(
        &self,
        parent: &EnvDeclBuilder,
        t: &Expr,
        u: &Expr,
        h_t1: Expr,
        h_0u: Expr,
    ) -> Expr {
        let one = self.rat_one.clone();
        let tu = self.mul(t.clone(), u.clone());
        let one_u = self.mul(one.clone(), u.clone());
        let h = self.mul_le_right(u.clone(), t.clone(), one.clone(), h_t1, h_0u); // t·u ≤ 1·u
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.le(tu.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, one_u, u.clone(), self.one_mul(u.clone()), h)
    }
}

impl Environment {
    /// `Rat.cbrtDyadicApprox_le_one : ∀ x, 0≤x → x<1 → ∀ n, a_n ≤ 1`.
    pub(crate) fn register_cbrt_dyadic_approx_le_one(
        &mut self,
        c: &CbrtSqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicApprox_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let cube_le = Expr::const_(Name::from_string("Rat.cbrtDyadicApprox_cube_le"), vec![]);
        let zero_le_approx =
            Expr::const_(Name::from_string("Rat.zero_le_cbrtDyadicApprox"), vec![]);
        let le_of_cube = Expr::const_(Name::from_string("Rat.le_of_cube_le_cube"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let a = c.approx(&x, n.clone());
                let concl = c.le(a, c.rat_one.clone());
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
            };
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, inner);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());

                let a = c.approx(&x, n.clone());
                let one = c.rat_one.clone();
                let a3 = c.cube(a.clone());
                let one3 = c.cube(one.clone()); // (1·1)·1

                // a_n³ ≤ x  (lower).
                let h_a3_le_x = Expr::apps(cube_le.clone(), [x.clone(), h0.clone(), n.clone()]);
                // a_n³ < 1  (lt_of_le_of_lt a³ x 1).
                let h_a3_lt_1 =
                    c.lt_of_le_of_lt(a3.clone(), x.clone(), one.clone(), h_a3_le_x, h1.clone());
                // a_n³ ≤ 1.
                let h_a3_le_1 = c.le_of_lt_generic(a3.clone(), one.clone(), h_a3_lt_1);

                // 1³ = 1:  (1·1)·1 = (1·1) (mul_one (1·1)) = 1 (mul_one 1).
                let one_one = c.mul(one.clone(), one.clone());
                let e1 = c.mul_one(one_one.clone()); // (1·1)·1 = (1·1)
                let e2 = c.mul_one(one.clone()); // (1·1) = 1
                let one3_eq_1 = c.trans(one3.clone(), one_one.clone(), one.clone(), e1, e2);
                let one_eq_one3 = c.symm(one3.clone(), one.clone(), one3_eq_1); // 1 = 1³

                // transport a_n³ ≤ 1 along (1 = 1³) → a_n³ ≤ 1³.
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(a3.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h_a3_le_13 = c.subst(motive, one.clone(), one3.clone(), one_eq_one3, h_a3_le_1);

                // 0 ≤ a_n ; 0 ≤ 1.
                let h_0a = Expr::apps(zero_le_approx.clone(), [x.clone(), n.clone()]);
                let h_01 = c.zero_le_one();

                // le_of_cube_le_cube a_n 1 (0≤a_n)(0≤1)(a_n³≤1³) : a_n ≤ 1.
                let body = Expr::apps(
                    le_of_cube.clone(),
                    [a.clone(), one.clone(), h_0a, h_01, h_a3_le_13],
                );
                ib.finish_child(ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, inner);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.x_lt_cbrtDyadicApprox_cube_add_seven_inv :
    ///   ∀ x, 0≤x → x<1 → ∀ n, x < a_n³ + (3iv + (3iv + iv))`
    /// where `iv := inv(2^n)`, `3iv := (iv+iv)+iv` (so the tail is 7 copies of
    /// `iv`, bracketed `3+3+1` to match the `add_cube` error bracketing).
    pub(crate) fn register_x_lt_cbrt_dyadic_approx_cube_add(
        &mut self,
        c: &CbrtSqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.x_lt_cbrtDyadicApprox_cube_add_seven_inv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let a = c.approx(&x, n.clone());
                let iv = c.inv_two_pow(n.clone());
                let three_iv = c.add(c.add(iv.clone(), iv.clone()), iv.clone());
                let tail = c.add(three_iv.clone(), c.add(three_iv.clone(), iv.clone()));
                let concl = c.lt(x.clone(), c.add(c.cube(a), tail));
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
            };
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, inner);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_cube_upper_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The proof term for `x_lt_cbrtDyadicApprox_cube_add_seven_inv`.
fn build_cube_upper_value(c: &CbrtSqueezeConsts) -> Expr {
    let cnum_cube_lt = Expr::const_(Name::from_string("Rat.cbrtDyadicNum_cube_lt_succ"), vec![]);
    let inv_cube_bridge = Expr::const_(
        Name::from_string("Rat.inv_two_pow_cube_eq_inv_pow8"),
        vec![],
    );
    let le_one = Expr::const_(Name::from_string("Rat.cbrtDyadicApprox_le_one"), vec![]);
    let add_cube = Expr::const_(Name::from_string("Rat.add_cube"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let h0_ty = c.le(c.rat_zero.clone(), x.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.lt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    let inner = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ib.fresh_local(c.nat.clone());

        let one = c.rat_one.clone();
        let kn = c.ofnat(c.cnum(&x, n.clone())); // ofNat k_n
        let succ_kn_nat = c.succ(c.cnum(&x, n.clone())); // Nat.succ k_n
        let s_kn = c.ofnat(succ_kn_nat.clone()); // ofNat(succ k_n) = s_k
        let iv = c.inv_two_pow(n.clone());
        let pow8 = c.pow8(n.clone());
        let inv8 = c.inv(pow8.clone());
        // a_n surface form (defeq cbrtDyadicApprox): kn·iv.
        let a = c.mul(kn.clone(), iv.clone());
        let a3 = c.cube(a.clone()); // (a·a)·a
                                    // b_n := s_k·iv ; b_n³ := (b·b)·b ; s_k³ := (s_k·s_k)·s_k.
        let bb = c.mul(s_kn.clone(), iv.clone());
        let b3 = c.cube(bb.clone());
        let sk3 = c.cube(s_kn.clone());
        let x_pow8 = c.mul(x.clone(), pow8.clone());

        // ── Step A: x < b_n³ ───────────────────────────────────────────────
        // h_inv : x·8^n < s_k³   (cbrtDyadicNum_cube_lt_succ x h0 h1 n).
        let h_inv = Expr::apps(
            cnum_cube_lt.clone(),
            [x.clone(), h0.clone(), h1.clone(), n.clone()],
        );
        // inv8 > 0.
        let inv8_pos = {
            let h_pos = Expr::app(
                Expr::const_(Name::from_string("Rat.zero_lt_cbrtDyadicPow8"), vec![]),
                n.clone(),
            );
            Expr::apps(
                Expr::const_(Name::from_string("Rat.inv_pos"), vec![]),
                [pow8.clone(), h_pos],
            )
        };
        // h_mul : inv8·(x·8^n) < inv8·s_k³.
        let h_mul = c.mul_lt_left(inv8.clone(), x_pow8.clone(), sk3.clone(), h_inv, inv8_pos);

        // LHS: inv8·(x·8^n) = x.  inv8·(x·8^n) = inv8·(8^n·x) = (inv8·8^n)·x = 1·x = x.
        let pow8_x = c.mul(pow8.clone(), x.clone());
        let inv8_pow8_x = c.mul(inv8.clone(), pow8_x.clone());
        let inv8_x_pow8 = c.mul(inv8.clone(), x_pow8.clone());
        let f_inv8 = c.f_mul_left(&ib, inv8.clone());
        let e_a1 = c.congr_arg(
            x_pow8.clone(),
            pow8_x.clone(),
            f_inv8,
            c.mul_comm(x.clone(), pow8.clone()),
        );
        let inv8_pow8 = c.mul(inv8.clone(), pow8.clone());
        let inv8_pow8_times_x = c.mul(inv8_pow8.clone(), x.clone());
        let e_assoc = c.mul_assoc(inv8.clone(), pow8.clone(), x.clone()); // (inv8·8^n)·x = inv8·(8^n·x)
        let e_a2 = c.symm(inv8_pow8_times_x.clone(), inv8_pow8_x.clone(), e_assoc);
        // inv8·8^n = 1:  inv8·8^n = 8^n·inv8 (mul_comm) = 1 (mul_inv_cancel).
        let cancel8 = {
            let e_comm = c.mul_comm(inv8.clone(), pow8.clone()); // inv8·8^n = 8^n·inv8
            let pow8_inv8 = c.mul(pow8.clone(), inv8.clone());
            let e_cancel = c.mul_inv_cancel(pow8.clone(), c.pow8_ne_zero(&n)); // 8^n·inv8 = 1
            c.trans(inv8_pow8.clone(), pow8_inv8, one.clone(), e_comm, e_cancel)
        };
        let f_x = c.f_mul_right(&ib, x.clone());
        let one_x = c.mul(one.clone(), x.clone());
        let e_a3 = c.congr_arg(inv8_pow8.clone(), one.clone(), f_x, cancel8); // (inv8·8^n)·x = 1·x
        let e_a4 = c.one_mul(x.clone());
        let t_a1 = c.trans(
            inv8_x_pow8.clone(),
            inv8_pow8_x.clone(),
            inv8_pow8_times_x.clone(),
            e_a1,
            e_a2,
        );
        let t_a2 = c.trans(
            inv8_x_pow8.clone(),
            inv8_pow8_times_x.clone(),
            one_x.clone(),
            t_a1,
            e_a3,
        );
        let lhs_eq_x = c.trans(inv8_x_pow8.clone(), one_x.clone(), x.clone(), t_a2, e_a4); // inv8·(x·8^n) = x

        // RHS: inv8·s_k³ = b_n³.
        //   b_n³ = s_k³·iv³  (cube_regroup s_k iv) = s_k³·inv8 (congr inv_cube_bridge)
        //        = inv8·s_k³ (mul_comm). So inv8·s_k³ = b_n³ by symm of the chain.
        let iv3 = c.cube(iv.clone());
        let regroup = c.cube_regroup(&ib, &s_kn, &iv); // b_n³ = s_k³·iv³
        let sk3_iv3 = c.mul(sk3.clone(), iv3.clone());
        let h_iv3 = Expr::app(inv_cube_bridge.clone(), n.clone()); // iv³ = inv8
        let f_sk3 = c.f_mul_left(&ib, sk3.clone());
        let step_iv3 = c.congr_arg(iv3.clone(), inv8.clone(), f_sk3, h_iv3); // s_k³·iv³ = s_k³·inv8
        let sk3_inv8 = c.mul(sk3.clone(), inv8.clone());
        let b3_eq_sk3inv8 = c.trans(
            b3.clone(),
            sk3_iv3.clone(),
            sk3_inv8.clone(),
            regroup,
            step_iv3,
        ); // b_n³ = s_k³·inv8
        let e_comm_sk3 = c.mul_comm(sk3.clone(), inv8.clone()); // s_k³·inv8 = inv8·s_k³
        let inv8_sk3 = c.mul(inv8.clone(), sk3.clone());
        let b3_eq_inv8sk3 = c.trans(
            b3.clone(),
            sk3_inv8.clone(),
            inv8_sk3.clone(),
            b3_eq_sk3inv8,
            e_comm_sk3,
        ); // b_n³ = inv8·s_k³
        let inv8sk3_eq_b3 = c.symm(b3.clone(), inv8_sk3.clone(), b3_eq_inv8sk3); // inv8·s_k³ = b_n³

        // transport h_mul (inv8·(x·8^n) < inv8·s_k³): LHS → x, RHS → b_n³.
        let motive_l = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.lt(t, inv8_sk3.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_x_lt_inv8sk3 = c.subst(motive_l, inv8_x_pow8.clone(), x.clone(), lhs_eq_x, h_mul); // x < inv8·s_k³
        let motive_r = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.lt(x.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_x_lt_b3 = c.subst(
            motive_r,
            inv8_sk3.clone(),
            b3.clone(),
            inv8sk3_eq_b3,
            h_x_lt_inv8sk3,
        ); // x < b_n³

        // ── Step B: b_n = a_n + iv ─────────────────────────────────────────
        let kn_plus_1 = c.add(kn.clone(), one.clone());
        let e_skn = c.add_natcast_one(c.cnum(&x, n.clone())); // ofNat k_n + 1 = ofNat(succ k_n)
        let rd = c.right_distrib(kn.clone(), one.clone(), iv.clone()); // (kn+1)·iv = kn·iv + 1·iv
        let one_iv = c.mul(one.clone(), iv.clone());
        let f_add_a = c.f_add_left(&ib, a.clone());
        let a_plus_oneiv = c.add(a.clone(), one_iv.clone());
        let a_plus_iv = c.add(a.clone(), iv.clone());
        let e_fix = c.congr_arg(one_iv.clone(), iv.clone(), f_add_a, c.one_mul(iv.clone())); // a+1·iv = a+iv
        let kn1_iv = c.mul(kn_plus_1.clone(), iv.clone());
        let rd_chain = c.trans(
            kn1_iv.clone(),
            a_plus_oneiv.clone(),
            a_plus_iv.clone(),
            rd,
            e_fix,
        ); // (kn+1)·iv = a+iv
        let f_iv = c.f_mul_right(&ib, iv.clone());
        let e_kn1iv_eq_b = c.congr_arg(kn_plus_1.clone(), s_kn.clone(), f_iv, e_skn); // (kn+1)·iv = b_n
        let e_b_eq_kn1iv = c.symm(kn1_iv.clone(), bb.clone(), e_kn1iv_eq_b); // b_n = (kn+1)·iv
        let b_eq_a_iv = c.trans(
            bb.clone(),
            kn1_iv.clone(),
            a_plus_iv.clone(),
            e_b_eq_kn1iv,
            rd_chain,
        ); // b_n = a+iv

        // ── Step C: b_n³ = a³ + E   (add_cube a iv, transported b_n = a+iv) ──
        // add_cube a iv : ((a+iv)·(a+iv))·(a+iv) = a³ + (3·(a²iv) + (3·(a·iv²) + iv³)).
        let three = c.three_const();
        let a2iv = c.mul(c.mul(a.clone(), a.clone()), iv.clone()); // (a·a)·iv
        let aiv2 = c.mul(c.mul(a.clone(), iv.clone()), iv.clone()); // (a·iv)·iv
        let three_a2iv = c.mul(three.clone(), a2iv.clone());
        let three_aiv2 = c.mul(three.clone(), aiv2.clone());
        let err_tail = c.add(three_aiv2.clone(), iv3.clone());
        let err = c.add(three_a2iv.clone(), err_tail.clone());
        let a3_plus_err = c.add(a3.clone(), err.clone());
        let h_add_cube = Expr::apps(add_cube.clone(), [a.clone(), iv.clone()]); // (a+iv)³ = a³ + E
                                                                                // subst (a+iv) → b_n along symm b_eq_a_iv in motive (fun t => t³ = a³+E).
        let motive_cube = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.eq(c.cube(t.clone()), a3_plus_err.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let e_aiv_eq_b = c.symm(bb.clone(), a_plus_iv.clone(), b_eq_a_iv); // (a+iv) = b_n
        let h_b3_eq_expand = c.subst(
            motive_cube,
            a_plus_iv.clone(),
            bb.clone(),
            e_aiv_eq_b,
            h_add_cube,
        ); // b_n³ = a³+E

        // x < a³ + E  (transport h_x_lt_b3 along h_b3_eq_expand).
        let motive_xb3 = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.lt(x.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_x_lt_expand = c.subst(
            motive_xb3,
            b3.clone(),
            a3_plus_err.clone(),
            h_b3_eq_expand,
            h_x_lt_b3,
        ); // x < a³+E

        // ── Step D: E ≤ (3iv + (3iv + iv)) ─────────────────────────────────
        // a_n ≤ 1 ; iv ≤ 1 ; 0 ≤ iv ; 0 ≤ a_n.
        let h_a_le_1 = Expr::apps(
            le_one.clone(),
            [x.clone(), h0.clone(), h1.clone(), n.clone()],
        );
        let h_iv_le_1 = c.inv_two_pow_le_one(n.clone());
        let h0_iv = c.le_of_lt(iv.clone(), c.zero_lt_inv_two_pow(n.clone()));
        let h0_a = Expr::apps(
            Expr::const_(Name::from_string("Rat.zero_le_cbrtDyadicApprox"), vec![]),
            [x.clone(), n.clone()],
        );

        // a²iv = (a·a)·iv ≤ iv:  a·a ≤ 1 then (a·a)·iv ≤ 1·iv = iv.
        //   a·a ≤ a (mul_le_of_le_one_right a a (a≤1)(0≤a)); a ≤ 1; le_trans.
        let aa = c.mul(a.clone(), a.clone());
        let h_aa_le_a = c.mul_le_of_le_one_right(&ib, &a, &a, h_a_le_1.clone(), h0_a.clone()); // a·a ≤ a
        let h_aa_le_1 = c.le_trans(
            aa.clone(),
            a.clone(),
            one.clone(),
            h_aa_le_a,
            h_a_le_1.clone(),
        ); // a·a ≤ 1
        let h_a2iv_le_iv = c.mul_le_of_le_one_right(&ib, &aa, &iv, h_aa_le_1, h0_iv.clone()); // (a·a)·iv ≤ iv

        // a·iv ≤ iv (mul_le_of_le_one_right a iv (a≤1)(0≤iv)); aiv2 = (a·iv)·iv.
        let a_iv = c.mul(a.clone(), iv.clone());
        let h_aiv_le_iv = c.mul_le_of_le_one_right(&ib, &a, &iv, h_a_le_1.clone(), h0_iv.clone()); // a·iv ≤ iv
        let h_aiv_le_1 = c.le_trans(
            a_iv.clone(),
            iv.clone(),
            one.clone(),
            h_aiv_le_iv,
            h_iv_le_1.clone(),
        ); // a·iv ≤ 1
        let h_aiv2_le_iv = c.mul_le_of_le_one_right(&ib, &a_iv, &iv, h_aiv_le_1, h0_iv.clone()); // (a·iv)·iv ≤ iv

        // iv³ = (iv·iv)·iv ≤ iv:  iv·iv ≤ 1 then (iv·iv)·iv ≤ iv.
        let iviv = c.mul(iv.clone(), iv.clone());
        let h_iviv_le_iv =
            c.mul_le_of_le_one_right(&ib, &iv, &iv, h_iv_le_1.clone(), h0_iv.clone()); // iv·iv ≤ iv
        let h_iviv_le_1 = c.le_trans(
            iviv.clone(),
            iv.clone(),
            one.clone(),
            h_iviv_le_iv,
            h_iv_le_1.clone(),
        ); // iv·iv ≤ 1
        let h_iv3_le_iv = c.mul_le_of_le_one_right(&ib, &iviv, &iv, h_iviv_le_1, h0_iv.clone()); // (iv·iv)·iv ≤ iv

        // 0 ≤ 3:  3 = (1+1)+1.  0 ≤ 1 (zero_le_one); 0 ≤ 1+1 via add_le_add then add_zero;
        //   0 ≤ (1+1)+1 again.
        let h0_three = c.zero_le_three(&ib);

        // 3·a²iv ≤ 3·iv  (mul_le_left 3 (a²iv) iv (a²iv≤iv)(0≤3)); 3·iv = 3iv (= (iv+iv)+iv).
        let three_iv = c.mul(three.clone(), iv.clone());
        let three_iv_sum = c.add(c.add(iv.clone(), iv.clone()), iv.clone()); // (iv+iv)+iv
        let e_3iv = c.three_mul_eq(&ib, &iv); // 3·iv = (iv+iv)+iv
        let h_3a2iv_le_3iv = c.mul_le_left(
            three.clone(),
            a2iv.clone(),
            iv.clone(),
            h_a2iv_le_iv,
            h0_three.clone(),
        ); // 3·a²iv ≤ 3·iv
           // transport RHS 3·iv → 3iv_sum.
        let motive_31 = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.le(three_a2iv.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_3a2iv_le_3sum = c.subst(
            motive_31,
            three_iv.clone(),
            three_iv_sum.clone(),
            e_3iv.clone(),
            h_3a2iv_le_3iv,
        ); // 3·a²iv ≤ 3iv_sum

        // 3·aiv² ≤ 3iv_sum similarly.
        let h_3aiv2_le_3iv = c.mul_le_left(
            three.clone(),
            aiv2.clone(),
            iv.clone(),
            h_aiv2_le_iv,
            h0_three,
        ); // 3·aiv² ≤ 3·iv
        let motive_32 = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.le(three_aiv2.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_3aiv2_le_3sum = c.subst(
            motive_32,
            three_iv.clone(),
            three_iv_sum.clone(),
            e_3iv,
            h_3aiv2_le_3iv,
        ); // 3·aiv² ≤ 3iv_sum

        // err_tail = 3·aiv² + iv³ ≤ 3iv_sum + iv  (add_le_add).
        let tail_bound = c.add(three_iv_sum.clone(), iv.clone());
        let h_tail_le = c.add_le_add(
            three_aiv2.clone(),
            three_iv_sum.clone(),
            iv3.clone(),
            iv.clone(),
            h_3aiv2_le_3sum,
            h_iv3_le_iv,
        ); // err_tail ≤ 3iv_sum + iv
           // err = 3·a²iv + err_tail ≤ 3iv_sum + (3iv_sum + iv)  (add_le_add).
        let target_tail = c.add(three_iv_sum.clone(), tail_bound.clone()); // 3iv_sum + (3iv_sum+iv)
        let h_err_le = c.add_le_add(
            three_a2iv.clone(),
            three_iv_sum.clone(),
            err_tail.clone(),
            tail_bound.clone(),
            h_3a2iv_le_3sum,
            h_tail_le,
        ); // err ≤ target_tail

        // ── Step E: combine ────────────────────────────────────────────────
        // a³ + err ≤ a³ + target_tail  (add_le_add (a³)(a³) err target_tail (le_refl)(h_err_le)).
        let a3_plus_target = c.add(a3.clone(), target_tail.clone());
        let h_a3err_le = c.add_le_add(
            a3.clone(),
            a3.clone(),
            err.clone(),
            target_tail.clone(),
            c.le_refl(a3.clone()),
            h_err_le,
        ); // a³+err ≤ a³+target_tail
           // x < a³+err ≤ a³+target_tail  (lt_of_lt_of_le).
        let body = c.lt_of_lt_of_le(
            x.clone(),
            a3_plus_err.clone(),
            a3_plus_target.clone(),
            h_x_lt_expand,
            h_a3err_le,
        );
        ib.finish_child(ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
    };

    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, inner);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
}
