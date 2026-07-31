// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Genuine, kernel-checked proof of
//! `Rat.le_trans : ∀ a b c : Rat, Rat.le a b → Rat.le b c → Rat.le a c`.
//!
//! # The soundness bug this closes
//!
//! `Rat` is the *free* inductive `Rat.mk : Int -> Nat` with NO `denom > 0`
//! invariant. The naive cross-multiplication order
//! `Rat.le a b := Int.le (num a · ofNat (denom b)) (num b · ofNat (denom a))`
//! is therefore NOT transitive: with `a = mk 5 1`, `b = mk 0 0`, `c = mk (-5) 1`
//! both `le a b` (`Int.le (5·0) (0·1) = Int.le 0 0`) and `le b c`
//! (`Int.le 0 0`) hold, yet `le a c = Int.le 5 (-5)` is FALSE. Registering
//! `Rat.le_trans` as a `Declaration::Axiom` was thus a FALSE axiom (exploitable
//! to derive `False`).
//!
//! # The fix
//!
//! `Rat.le` / `Rat.lt` are redefined (in `algebra.rs::init_rat_ord`) over the
//! EFFECTIVE denominator `Rat.effDenom x := Nat.succ (Nat.pred (Rat.denom x))`,
//! which is never `0`:
//!   - for a well-formed `denom = Nat.succ k` it is DEFINITIONALLY `denom`
//!     (so every existing well-formed proof reduces identically), and
//!   - for the pathological `denom = 0` it is `1`.
//!
//! The order is now a genuine preorder and `Rat.le_trans` is TRUE — and proven
//! here as a kernel-checked `Declaration::Theorem`.
//!
//! # Proof architecture
//!
//! Writing `na = Rat.num a`, `ea = Int.ofNat (Rat.effDenom a)` (and similarly
//! for `b`, `c`), the redefined `Rat.le` delta-reduces:
//!
//! ```text
//! Rat.le a b  ≡  Int.le (na · eb) (nb · ea)
//! Rat.le b c  ≡  Int.le (nb · ec) (nc · eb)
//! Rat.le a c  ≡  Int.le (na · ec) (nc · ea)
//! ```
//!
//! Crucially `Rat.effDenom x` is SYNTACTICALLY `Nat.succ (Nat.pred (Rat.denom x))`,
//! so every effective denominator is `Int.ofNat (Nat.succ _)` — manifestly
//! positive AND cancellable by the constructive `Int.mul_left_cancel_ofNat_succ`.
//!
//! Two constructive Int helpers carry the work (both registered here):
//!
//! 1. `Int.le_of_mul_le_mul_left_succ : ∀ (n : Nat) (x y : Int),
//!        Int.le (k · x) (k · y) → Int.le x y` with `k := Int.ofNat (Nat.succ n)`.
//!    Proof: `Int.le_total x y`; the `x ≤ y` case is immediate, and the `y ≤ x`
//!    case multiplies through by the nonneg `k` (`Int.mul_le_mul_of_nonneg_left`),
//!    derives `k·x = k·y` by `Int.le_antisymm`, cancels `k` with
//!    `Int.mul_left_cancel_ofNat_succ` to get `x = y`, and transports
//!    `Int.le_refl x` along it. Constructive (no `Declaration::Axiom` in closure).
//!
//! 2. `Int.le_cross_trans : ∀ (na nb nc : Int) (da db dc : Nat),
//!        Int.le (na · ofNat (succ db)) (nb · ofNat (succ da)) →
//!        Int.le (nb · ofNat (succ dc)) (nc · ofNat (succ db)) →
//!        Int.le (na · ofNat (succ dc)) (nc · ofNat (succ da))`.
//!    The standard positive-denominator transitivity argument: multiply the two
//!    hypotheses by the nonneg `ec` / `ea` (`Int.mul_le_mul_of_nonneg_right`),
//!    bridge through `Int.le_trans`, regroup the common middle factor
//!    `k = ofNat (succ db)` to the left with the `Int.mul_assoc` / `Int.mul_comm`
//!    helper `mul_rearrange (x*y)*z = y*(x*z)`, then cancel `k` with helper (1).
//!    Constructive.
//!
//! `Rat.le_trans` is then `λ a b c h1 h2 => Int.le_cross_trans na nb nc
//! (pred (denom a)) (pred (denom b)) (pred (denom c)) h1 h2`, accepted because
//! `Int.ofNat (Nat.succ (Nat.pred (Rat.denom x))) ≡ Int.ofNat (Rat.effDenom x)`
//! definitionally, so the Int-helper's type matches the delta-reduced Rat goal.
//!
//! # Honest classification
//!
//! Every delegate (`Int.le_total`, `Int.le_trans`, `Int.le_refl`,
//! `Int.le_antisymm`, `Int.mul_le_mul_of_nonneg_left/right`,
//! `Int.mul_left_cancel_ofNat_succ`, `Int.ofNat_zero_le`, `Int.mul_assoc`,
//! `Int.mul_comm`) is a constructive `Declaration::Theorem`. So `Rat.le_trans`
//! is genuinely `Constructive` (empty domain-axiom closure) — NOT an axiom,
//! NOT a `sorry`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the `Rat.le_trans` / Int-helper proof terms.
struct LeTransConsts {
    int: Expr,
    nat: Expr,
    rat: Expr,
    rat_le: Expr,
    rat_num: Expr,
    rat_denom: Expr,
    int_le: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    nat_succ: Expr,
    nat_pred: Expr,
    int_le_refl: Expr,
    int_le_trans: Expr,
    int_le_total: Expr,
    int_le_antisymm: Expr,
    int_mul_le_mul_left: Expr,
    int_mul_le_mul_right: Expr,
    int_mul_left_cancel: Expr,
    int_ofnat_zero_le: Expr,
    int_mul_assoc: Expr,
    int_mul_comm: Expr,
    or_rec: Expr,
    eq_subst: Expr,
    #[cfg(test)]
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl LeTransConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int: Expr::const_(Name::from_string("Int"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_le: Expr::const_(Name::from_string("Rat.le"), vec![]),
            rat_num: Expr::const_(Name::from_string("Rat.num"), vec![]),
            rat_denom: Expr::const_(Name::from_string("Rat.denom"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
            int_le_refl: Expr::const_(Name::from_string("Int.le_refl"), vec![]),
            int_le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            int_le_total: Expr::const_(Name::from_string("Int.le_total"), vec![]),
            int_le_antisymm: Expr::const_(Name::from_string("Int.le_antisymm"), vec![]),
            int_mul_le_mul_left: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_left"),
                vec![],
            ),
            int_mul_le_mul_right: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_right"),
                vec![],
            ),
            int_mul_left_cancel: Expr::const_(
                Name::from_string("Int.mul_left_cancel_ofNat_succ"),
                vec![],
            ),
            int_ofnat_zero_le: Expr::const_(Name::from_string("Int.ofNat_zero_le"), vec![]),
            int_mul_assoc: Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
            int_mul_comm: Expr::const_(Name::from_string("Int.mul_comm"), vec![]),
            // `Or.rec` eliminating into Prop carries empty universe params here
            // (matching the established Nat-cancellation idiom).
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            #[cfg(test)]
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    /// `Int.mul x y`.
    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [x, y])
    }

    /// `Int.le x y`.
    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }

    /// `Int.ofNat n`.
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    /// `Int.ofNat (Nat.succ n)`.
    fn of_succ(&self, n: Expr) -> Expr {
        self.of_nat(Expr::app(self.nat_succ.clone(), n))
    }

    /// `Int.le 0 (Int.ofNat (Nat.succ n))` via `Int.ofNat_zero_le (Nat.succ n)`.
    /// (`Int.le 0 x ≡ Int.le (Int.ofNat Nat.zero) x` definitionally.)
    fn nonneg_of_succ(&self, n: Expr) -> Expr {
        Expr::app(
            self.int_ofnat_zero_le.clone(),
            Expr::app(self.nat_succ.clone(), n),
        )
    }

    /// `@Eq.subst.{1} Int motive x y h_eq h_mx : motive y`.
    fn subst(&self, motive: Expr, x: Expr, y: Expr, h_eq: Expr, h_mx: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.int.clone(), motive, x, y, h_eq, h_mx],
        )
    }

    /// `@Eq.symm.{1} Int x y h : Eq Int y x`.
    #[cfg(test)]
    fn symm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int.clone(), x, y, h])
    }

    /// `@Eq.trans.{1} Int x y z h1 h2 : Eq Int x z`.
    fn trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.int.clone(), x, y, z, h1, h2])
    }

    /// `@congrArg.{1,1} Int Int x y f h : Eq (f x) (f y)`.
    fn congr_arg(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int.clone(), self.int.clone(), x, y, f, h],
        )
    }

    /// `Int.le_trans a b c h1 h2 : Int.le a c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.int_le_trans.clone(), [a, b, cc, h1, h2])
    }

    /// `Int.mul_assoc x y z : Eq ((x*y)*z) (x*(y*z))`.
    fn mul_assoc(&self, x: Expr, y: Expr, z: Expr) -> Expr {
        Expr::apps(self.int_mul_assoc.clone(), [x, y, z])
    }

    /// `Int.mul_comm x y : Eq (x*y) (y*x)`.
    fn mul_comm(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul_comm.clone(), [x, y])
    }
}

impl Environment {
    /// Ensure the Int / Eq machinery needed by the `Rat.le_trans` proof is
    /// registered (each call idempotent / skip-if-present).
    fn ensure_le_trans_deps(&mut self) -> Result<(), EnvError> {
        self.init_int_linear_order()?; // Int.le_total, Int.le_trans, Int.le_refl, Int.le_antisymm
        self.init_eq()?;
        self.init_or()?;
        self.register_int_mul_le_mul_of_nonneg_left_proof()?;
        self.register_int_mul_le_mul_of_nonneg_right_proof()?;
        self.register_int_mul_left_cancel_ofnat_succ_proof()?;
        self.register_int_ofnat_zero_le_proof()?;
        self.register_int_mul_assoc_proof()?;
        self.register_int_mul_comm_proof()?;
        Ok(())
    }

    /// `Int.mul_rearrange : ∀ x y z : Int, Eq ((x*y)*z) (y*(x*z))`.
    ///
    /// Proof: `(x*y)*z = (y*x)*z` [`congrArg (·*z) (mul_comm x y)`]
    ///                 `= y*(x*z)` [`mul_assoc y x z`].
    fn register_int_mul_rearrange(&mut self, c: &LeTransConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Int.mul_rearrange");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.int.clone());
            let (y_id, y) = b.fresh_local(c.int.clone());
            let (z_id, z) = b.fresh_local(c.int.clone());
            let lhs = c.mul(c.mul(x.clone(), y.clone()), z.clone());
            let rhs = c.mul(y.clone(), c.mul(x.clone(), z.clone()));
            let eq = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [c.int.clone(), lhs, rhs],
            );
            let e = b.mk_pi(z_id, BinderInfo::Default, c.int.clone(), eq);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.int.clone());
            let (y_id, y) = b.fresh_local(c.int.clone());
            let (z_id, z) = b.fresh_local(c.int.clone());

            let xy = c.mul(x.clone(), y.clone());
            let yx = c.mul(y.clone(), x.clone());
            // f := fun w => w * z
            let f_mul_z = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = ch.fresh_local(c.int.clone());
                let body = c.mul(w, z.clone());
                let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(lam)
            };
            // step1 : (x*y)*z = (y*x)*z
            let step1 = c.congr_arg(
                xy.clone(),
                yx.clone(),
                f_mul_z,
                c.mul_comm(x.clone(), y.clone()),
            );
            // step2 : (y*x)*z = y*(x*z)
            let step2 = c.mul_assoc(y.clone(), x.clone(), z.clone());
            let xy_z = c.mul(xy, z.clone());
            let yx_z = c.mul(yx, z.clone());
            let y_xz = c.mul(y.clone(), c.mul(x.clone(), z.clone()));
            let body = c.trans(xy_z, yx_z, y_xz, step1, step2);

            let e = b.mk_lam(z_id, BinderInfo::Default, c.int.clone(), body);
            let e = b.mk_lam(y_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Int.le_of_mul_le_mul_left_succ : ∀ (n : Nat) (x y : Int),
    ///     Int.le (Int.mul (Int.ofNat (Nat.succ n)) x)
    ///            (Int.mul (Int.ofNat (Nat.succ n)) y) → Int.le x y`.
    fn register_int_le_of_mul_le_mul_left_succ(
        &mut self,
        c: &LeTransConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.le_of_mul_le_mul_left_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (x_id, x) = b.fresh_local(c.int.clone());
            let (y_id, y) = b.fresh_local(c.int.clone());
            let k = c.of_succ(n.clone());
            let hyp = c.le(c.mul(k.clone(), x.clone()), c.mul(k.clone(), y.clone()));
            let goal = c.le(x.clone(), y.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, goal);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (x_id, x) = b.fresh_local(c.int.clone());
            let (y_id, y) = b.fresh_local(c.int.clone());
            let k = c.of_succ(n.clone());
            let hyp = c.le(c.mul(k.clone(), x.clone()), c.mul(k.clone(), y.clone()));
            let (h_id, h) = b.fresh_local(hyp.clone());

            let le_xy = c.le(x.clone(), y.clone());
            let le_yx = c.le(y.clone(), x.clone());
            let goal = le_xy.clone();

            // const motive for Or.rec: fun (_ : Or (x≤y) (y≤x)) => Int.le x y
            let or_motive = {
                let mut om = EnvDeclBuilder::child_of(&b);
                let or_ty = Expr::apps(
                    Expr::const_(Name::from_string("Or"), vec![]),
                    [le_xy.clone(), le_yx.clone()],
                );
                let (hh_id, _hh) = om.fresh_local(or_ty.clone());
                let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ty, goal.clone());
                om.finish_child(lam)
            };

            // inl: fun (hxy : x≤y) => hxy
            let case_inl = {
                let mut ic = EnvDeclBuilder::child_of(&b);
                let (hxy_id, hxy) = ic.fresh_local(le_xy.clone());
                let lam = ic.mk_lam(hxy_id, BinderInfo::Default, le_xy.clone(), hxy);
                ic.finish_child(lam)
            };

            // inr: fun (hyx : y≤x) => <derive x≤y by cancellation>
            let case_inr = {
                let mut rc = EnvDeclBuilder::child_of(&b);
                let (hyx_id, hyx) = rc.fresh_local(le_yx.clone());

                // hk : Int.le 0 k  (k = ofNat (succ n)).
                let hk = c.nonneg_of_succ(n.clone());
                // k*y ≤ k*x  via mul_le_mul_of_nonneg_left y x k hyx hk
                let kmul_yx = Expr::apps(
                    c.int_mul_le_mul_left.clone(),
                    [y.clone(), x.clone(), k.clone(), hyx.clone(), hk],
                );
                let kx = c.mul(k.clone(), x.clone());
                let ky = c.mul(k.clone(), y.clone());
                // h : k*x ≤ k*y ; kmul_yx : k*y ≤ k*x ; antisymm => Eq (k*x) (k*y)
                let eq_kx_ky = Expr::apps(
                    c.int_le_antisymm.clone(),
                    [kx.clone(), ky.clone(), h.clone(), kmul_yx],
                );
                // cancel: Int.mul_left_cancel_ofNat_succ n x y eq_kx_ky : Eq x y
                let eq_xy = Expr::apps(
                    c.int_mul_left_cancel.clone(),
                    [n.clone(), x.clone(), y.clone(), eq_kx_ky],
                );
                // transport Int.le_refl x along Eq x y:
                //   @Eq.subst Int (fun z => Int.le x z) x y eq_xy (Int.le_refl x) : Int.le x y
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&rc);
                    let (z_id, z) = mb.fresh_local(c.int.clone());
                    let body = c.le(x.clone(), z);
                    let lam = mb.mk_lam(z_id, BinderInfo::Default, c.int.clone(), body);
                    mb.finish_child(lam)
                };
                let le_refl_x = Expr::app(c.int_le_refl.clone(), x.clone());
                let body = c.subst(motive, x.clone(), y.clone(), eq_xy, le_refl_x);
                let lam = rc.mk_lam(hyx_id, BinderInfo::Default, le_yx.clone(), body);
                rc.finish_child(lam)
            };

            // major : Or (x≤y) (y≤x) := Int.le_total x y
            let major = Expr::apps(c.int_le_total.clone(), [x.clone(), y.clone()]);
            let or_rec_app = Expr::apps(
                c.or_rec.clone(),
                [le_xy, le_yx, or_motive, case_inl, case_inr, major],
            );

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, or_rec_app);
            let e = b.mk_lam(y_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Int.le_cross_trans : ∀ (na nb nc : Int) (da db dc : Nat),
    ///     Int.le (na · ofNat (succ db)) (nb · ofNat (succ da)) →
    ///     Int.le (nb · ofNat (succ dc)) (nc · ofNat (succ db)) →
    ///     Int.le (na · ofNat (succ dc)) (nc · ofNat (succ da))`.
    fn register_int_le_cross_trans(&mut self, c: &LeTransConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Int.le_cross_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_int_mul_rearrange(c)?;
        self.register_int_le_of_mul_le_mul_left_succ(c)?;

        // Shared type/value skeleton builder.
        let build = |is_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (na_id, na) = b.fresh_local(c.int.clone());
            let (nb_id, nb) = b.fresh_local(c.int.clone());
            let (nc_id, nc) = b.fresh_local(c.int.clone());
            let (da_id, da) = b.fresh_local(c.nat.clone());
            let (db_id, db) = b.fresh_local(c.nat.clone());
            let (dc_id, dc) = b.fresh_local(c.nat.clone());
            let ea = c.of_succ(da.clone());
            let eb = c.of_succ(db.clone());
            let ec = c.of_succ(dc.clone());

            // h1 : na·eb ≤ nb·ea ; h2 : nb·ec ≤ nc·eb ; goal : na·ec ≤ nc·ea
            let h1_ty = c.le(c.mul(na.clone(), eb.clone()), c.mul(nb.clone(), ea.clone()));
            let h2_ty = c.le(c.mul(nb.clone(), ec.clone()), c.mul(nc.clone(), eb.clone()));
            let goal = c.le(c.mul(na.clone(), ec.clone()), c.mul(nc.clone(), ea.clone()));

            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, h2) = b.fresh_local(h2_ty.clone());

            let result = if !is_value {
                goal.clone()
            } else {
                // ---- nonneg witnesses for ea, ec ----
                let hea = c.nonneg_of_succ(da.clone()); // 0 ≤ ea
                let hec = c.nonneg_of_succ(dc.clone()); // 0 ≤ ec

                // s1 : (na·eb)·ec ≤ (nb·ea)·ec
                let na_eb = c.mul(na.clone(), eb.clone());
                let nb_ea = c.mul(nb.clone(), ea.clone());
                let s1 = Expr::apps(
                    c.int_mul_le_mul_right.clone(),
                    [
                        na_eb.clone(),
                        nb_ea.clone(),
                        ec.clone(),
                        h1.clone(),
                        hec.clone(),
                    ],
                );
                // s2 : (nb·ec)·ea ≤ (nc·eb)·ea
                let nb_ec = c.mul(nb.clone(), ec.clone());
                let nc_eb = c.mul(nc.clone(), eb.clone());
                let s2 = Expr::apps(
                    c.int_mul_le_mul_right.clone(),
                    [
                        nb_ec.clone(),
                        nc_eb.clone(),
                        ea.clone(),
                        h2.clone(),
                        hea.clone(),
                    ],
                );

                // bridge : (nb·ea)·ec = (nb·ec)·ea
                //   mr1 := mul_rearrange nb ea ec : (nb·ea)·ec = ea·(nb·ec)
                //   cm  := mul_comm ea (nb·ec)     : ea·(nb·ec) = (nb·ec)·ea
                let mr = Expr::const_(Name::from_string("Int.mul_rearrange"), vec![]);
                let nb_ea_ec = c.mul(nb_ea.clone(), ec.clone());
                let nb_ec_ea = c.mul(nb_ec.clone(), ea.clone());
                let ea_nbec = c.mul(ea.clone(), nb_ec.clone());
                let mr1 = Expr::apps(mr.clone(), [nb.clone(), ea.clone(), ec.clone()]); // (nb·ea)·ec = ea·(nb·ec)
                let cm = c.mul_comm(ea.clone(), nb_ec.clone()); // ea·(nb·ec) = (nb·ec)·ea
                let bridge = c.trans(nb_ea_ec.clone(), ea_nbec.clone(), nb_ec_ea.clone(), mr1, cm);
                // s1' : (na·eb)·ec ≤ (nb·ec)·ea  (rewrite s1's RHS along bridge)
                let na_eb_ec = c.mul(na_eb.clone(), ec.clone());
                let motive_rhs = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = mb.fresh_local(c.int.clone());
                    let body = c.le(na_eb_ec.clone(), w);
                    let lam = mb.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                    mb.finish_child(lam)
                };
                let s1p = c.subst(motive_rhs, nb_ea_ec.clone(), nb_ec_ea.clone(), bridge, s1);
                // chained : (na·eb)·ec ≤ (nc·eb)·ea  via Int.le_trans
                let nc_eb_ea = c.mul(nc_eb.clone(), ea.clone());
                let chained = c.le_trans(
                    na_eb_ec.clone(),
                    nb_ec_ea.clone(),
                    nc_eb_ea.clone(),
                    s1p,
                    s2,
                );

                // Regroup the common middle factor eb to the LEFT:
                //   (na·eb)·ec = eb·(na·ec)   [mul_rearrange na eb ec]
                //   (nc·eb)·ea = eb·(nc·ea)   [mul_rearrange nc eb ea]
                let na_ec = c.mul(na.clone(), ec.clone());
                let nc_ea = c.mul(nc.clone(), ea.clone());
                let eb_na_ec = c.mul(eb.clone(), na_ec.clone());
                let eb_nc_ea = c.mul(eb.clone(), nc_ea.clone());
                let mr_l = Expr::apps(mr.clone(), [na.clone(), eb.clone(), ec.clone()]); // (na·eb)·ec = eb·(na·ec)
                let mr_r = Expr::apps(mr.clone(), [nc.clone(), eb.clone(), ea.clone()]); // (nc·eb)·ea = eb·(nc·ea)

                // rewrite LHS of `chained`: (na·eb)·ec -> eb·(na·ec)
                let motive_l = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = mb.fresh_local(c.int.clone());
                    let body = c.le(w, nc_eb_ea.clone());
                    let lam = mb.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                    mb.finish_child(lam)
                };
                let step_l = c.subst(motive_l, na_eb_ec.clone(), eb_na_ec.clone(), mr_l, chained);
                // rewrite RHS: (nc·eb)·ea -> eb·(nc·ea)
                let motive_r = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = mb.fresh_local(c.int.clone());
                    let body = c.le(eb_na_ec.clone(), w);
                    let lam = mb.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                    mb.finish_child(lam)
                };
                // grouped : eb·(na·ec) ≤ eb·(nc·ea)
                let grouped = c.subst(motive_r, nc_eb_ea.clone(), eb_nc_ea.clone(), mr_r, step_l);

                // cancel eb = ofNat(succ db) on the left:
                //   Int.le_of_mul_le_mul_left_succ db (na·ec) (nc·ea) grouped : na·ec ≤ nc·ea
                Expr::apps(
                    Expr::const_(Name::from_string("Int.le_of_mul_le_mul_left_succ"), vec![]),
                    [db.clone(), na_ec.clone(), nc_ea.clone(), grouped],
                )
            };

            let mk = |b: &EnvDeclBuilder, id, bi, ty, body| {
                if is_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = mk(&b, h2_id, BinderInfo::Default, h2_ty, result);
            let e = mk(&b, h1_id, BinderInfo::Default, h1_ty, e);
            let e = mk(&b, dc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = mk(&b, db_id, BinderInfo::Default, c.nat.clone(), e);
            let e = mk(&b, da_id, BinderInfo::Default, c.nat.clone(), e);
            let e = mk(&b, nc_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, nb_id, BinderInfo::Default, c.int.clone(), e);
            let e = mk(&b, na_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// Register `Rat.le_trans` as a genuine kernel-checked `Declaration::Theorem`.
    ///
    /// `λ a b c h1 h2 => Int.le_cross_trans (num a) (num b) (num c)
    ///      (pred (denom a)) (pred (denom b)) (pred (denom c)) h1 h2`.
    ///
    /// Accepted because `Int.ofNat (Nat.succ (Nat.pred (Rat.denom x)))
    /// ≡ Int.ofNat (Rat.effDenom x)` definitionally, so the Int-helper's
    /// hypotheses / conclusion match the delta-reduced `Rat.le` propositions.
    pub(crate) fn register_rat_le_trans_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_trans");
        // If some earlier path already registered it as a genuine Theorem, keep
        // it. (A pre-existing Axiom is REPLACED — that is the whole point.)
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        // WS-A ATOMIC LIVE SWITCH: the live `Rat` is the quotient carrier and
        // `Rat.le` is a `Quot.lift` (no longer the free `Rat.num`/`Rat.effDenom`
        // cross-product that reduced by def-eq). `Rat.le_trans` is registered as
        // a genuine `Quot.ind` Theorem by the quotient order-lemma helper.
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.register_int_le_cross_trans_only()?;
        self.register_int_lt_cross_trans_only()?;
        let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
        self.register_rat_q_order_lemmas(&qc)
    }

    #[allow(dead_code)]
    fn register_rat_le_trans_proof_legacy_free_carrier(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_trans");
        self.ensure_le_trans_deps()?;

        let c = LeTransConsts::new();
        self.register_int_le_cross_trans(&c)?;

        let num = |x: &Expr| Expr::app(c.rat_num.clone(), x.clone());
        let pred_denom = |x: &Expr| {
            Expr::app(
                c.nat_pred.clone(),
                Expr::app(c.rat_denom.clone(), x.clone()),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let le_ab = Expr::apps(c.rat_le.clone(), [a.clone(), bv.clone()]);
            let le_bc = Expr::apps(c.rat_le.clone(), [bv.clone(), cv.clone()]);
            let le_ac = Expr::apps(c.rat_le.clone(), [a.clone(), cv.clone()]);
            let (h1_id, _h1) = b.fresh_local(le_ab.clone());
            let (h2_id, _h2) = b.fresh_local(le_bc.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, le_bc, le_ac);
            let e = b.mk_pi(h1_id, BinderInfo::Default, le_ab, e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let le_ab = Expr::apps(c.rat_le.clone(), [a.clone(), bv.clone()]);
            let le_bc = Expr::apps(c.rat_le.clone(), [bv.clone(), cv.clone()]);
            let (h1_id, h1) = b.fresh_local(le_ab.clone());
            let (h2_id, h2) = b.fresh_local(le_bc.clone());

            // Int.le_cross_trans (num a) (num b) (num c)
            //   (pred (denom a)) (pred (denom b)) (pred (denom c)) h1 h2
            let body = Expr::apps(
                Expr::const_(Name::from_string("Int.le_cross_trans"), vec![]),
                [
                    num(&a),
                    num(&bv),
                    num(&cv),
                    pred_denom(&a),
                    pred_denom(&bv),
                    pred_denom(&cv),
                    h1,
                    h2,
                ],
            );

            let e = b.mk_lam(h2_id, BinderInfo::Default, le_bc, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, le_ab, e);
            let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register ONLY `Int.le_cross_trans` (+ its pure-Int dependencies), without
    /// pulling in the live free-inductive `Rat` (which `register_rat_le_trans_proof`
    /// does via `init_rat` / `init_rat_ord`). Used by the quotient-`Rat` carrier
    /// swap, whose `Rat.le` order-respect proofs need the cross-multiply
    /// monotonicity lemma but must build the carrier themselves.
    pub(crate) fn register_int_le_cross_trans_only(&mut self) -> Result<(), EnvError> {
        self.ensure_le_trans_deps()?;
        let c = LeTransConsts::new();
        self.register_int_le_cross_trans(&c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::new();
        env.register_rat_le_trans_proof()
            .expect("register_rat_le_trans_proof should succeed");
        env
    }

    #[test]
    fn test_rat_le_trans_is_theorem_with_value() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.le_trans"))
            .expect("Rat.le_trans should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Rat.le_trans must be Declaration::Theorem (not Axiom), got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "Rat.le_trans Theorem must retain a value"
        );
    }

    #[test]
    fn test_rat_le_trans_kernel_type_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Rat.le_trans"), vec![]))
            .expect("Rat.le_trans should kernel-type-check at its stated type");
    }

    #[test]
    fn test_rat_le_trans_constructive() {
        let env = env();
        let q = env
            .proof_quality(&Name::from_string("Rat.le_trans"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.le_trans must be Constructive (no domain axiom in closure), got {q:?}"
        );
    }

    /// The two Int helpers also kernel-check and are constructive.
    #[test]
    fn test_int_helpers_constructive() {
        let env = env();
        for name in &[
            "Int.le_of_mul_le_mul_left_succ",
            "Int.le_cross_trans",
            "Int.mul_rearrange",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            let q = env
                .proof_quality(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} proof_quality"));
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{name} must be Constructive, got {q:?}"
            );
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.register_rat_le_trans_proof().expect("first");
        env.register_rat_le_trans_proof()
            .expect("second idempotent");
    }

    /// The original soundness counterexample is CLOSED under the redefined
    /// (effective-denominator) `Rat.le`: with `a = mk 5 1`, `b = mk 0 0`,
    /// `c = mk (-5) 1`, the naive order had `le a b` ≡ `Int.le (5·0) (0·1)` ≡
    /// `Int.le 0 0` (TRUE). Under the new `Rat.le`, `effDenom (mk 0 0) = 1`
    /// (not `0`), so `le a b` ≡ `Int.le (5·1) (0·1)` ≡ `Int.le 5 0` (FALSE).
    /// We pin this by showing `Rat.le a b` is def-eq to `Int.le (ofNat 5) 0`
    /// (the new, false premise) and NOT def-eq to `Int.le 0 0` (the old, true
    /// premise that made non-transitivity exploitable).
    #[test]
    fn test_counterexample_premise_now_false() {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.register_rat_le_trans_proof().expect("register");

        let tc = TypeChecker::with_mode(&env, env.mode());

        let of_nat = |n: u64| {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..n {
                e = Expr::app(succ.clone(), e);
            }
            Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), e)
        };
        let nat = |n: u64| {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..n {
                e = Expr::app(succ.clone(), e);
            }
            e
        };
        let mk = |num: Expr, denom: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Rat.mk"), vec![]),
                [num, denom],
            )
        };
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);

        // a = mk 5 1, b = mk 0 0
        let a = mk(of_nat(5), nat(1));
        let b = mk(of_nat(0), nat(0));
        let le_ab = Expr::apps(rat_le.clone(), [a.clone(), b.clone()]);

        // NEW premise (false): Int.le (ofNat 5) (ofNat 0)  [effDenom (mk 0 0) = 1]
        let new_false = Expr::apps(int_le.clone(), [of_nat(5), of_nat(0)]);
        // OLD premise (true): Int.le (ofNat 0) (ofNat 0)   [naive denom (mk 0 0) = 0]
        let old_true = Expr::apps(int_le.clone(), [of_nat(0), of_nat(0)]);

        assert!(
            tc.is_def_eq(&le_ab, &new_false),
            "under the effective-denominator Rat.le, `le (mk 5 1) (mk 0 0)` must \
             reduce to the FALSE `Int.le 5 0` (effDenom (mk 0 0) = 1)"
        );
        assert!(
            !tc.is_def_eq(&le_ab, &old_true),
            "the OLD true premise `Int.le 0 0` must NO LONGER be the meaning of \
             `le (mk 5 1) (mk 0 0)` — that was the exploitable non-transitivity gap"
        );
    }

    /// WS-A: the representative-level `Rat.Raw.effDenom` is definitionally the
    /// identity on well-formed (denom > 0) representatives and bumps the
    /// pathological `denom = 0` to a positive value — the property the quotient
    /// `Rat.le`/`Rat.lt` lifts rely on. (The free-carrier `Rat.effDenom` no
    /// longer exists; this exercises `Rat.Raw.effDenom` on `Rat.Raw.mk`.)
    #[test]
    fn test_eff_denom_transparent_on_wellformed() {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.register_rat_le_trans_proof().expect("register");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = |n: u64| {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..n {
                e = Expr::app(succ.clone(), e);
            }
            e
        };
        let raw_mk = |num: Expr, denom: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Rat.Raw.mk"), vec![]),
                [num, denom],
            )
        };
        let eff = Expr::const_(Name::from_string("Rat.Raw.effDenom"), vec![]);
        let int0 = Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(0));

        // effDenom (Raw.mk 0 3) ≡ 3 (well-formed: definitionally the denom).
        let eff_3 = Expr::app(eff.clone(), raw_mk(int0.clone(), nat(3)));
        assert!(
            tc.is_def_eq(&eff_3, &nat(3)),
            "Rat.Raw.effDenom (mk 0 3) must be definitionally 3"
        );
        // effDenom (Raw.mk 0 0) ≡ 1 (pathological: bumped to a positive value).
        let eff_0 = Expr::app(eff.clone(), raw_mk(int0, nat(0)));
        assert!(
            tc.is_def_eq(&eff_0, &nat(1)),
            "Rat.Raw.effDenom (mk 0 0) must be definitionally 1 (closes the denom=0 gap)"
        );
    }
}
