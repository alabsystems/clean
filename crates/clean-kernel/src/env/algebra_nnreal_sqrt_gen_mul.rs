// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.sqrtGen` MULTIPLICATIVITY (square level), the
//! `√(x·y) = √x·√y` content, axiom-free.
//!
//! # Why this module exists (the cross-term `√(NG³·NH³)`)
//!
//! The `(4/3, 4)` tensorization cross-term needs `√(NG³·NH³) = NG^{3/2}·NH^{3/2}`
//! — i.e. the square root of a PRODUCT splits as a product of square roots. The
//! substantive, antisymmetry-free content of that splitting is: **the product of
//! the two scaled square roots is itself a square root of the product**, i.e.
//! `(√x·√y)² = ofRat (x·y)`. Because the landed `NNReal.sqrtGen_sq_at` gives
//! `√x² = ofRat x` and `√y² = ofRat y`, the regrouped square
//! `(√x·√y)·(√x·√y) = (√x·√x)·(√y·√y)` (one `mul_mul_mul_comm`) lands on
//! `ofRat x · ofRat y = ofRat (x·y)` (`ofRat_mul`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.sqrtGen_mul_sq :`
//!     `∀ (x y sx rx sy ry : Rat)`
//!     `  (hx:0≤x)(hy:0≤y)(hsx:0≤sx)(hrx:0≤rx)(hrx1:rx<1)(heqx:x=(sx·sx)·rx)`
//!     `  (hsy:0≤sy)(hry:0≤ry)(hry1:ry<1)(heqy:y=(sy·sy)·ry),`
//!     `  NNReal.mul (NNReal.mul (sqrtGen sx rx hsx)(sqrtGen sy ry hsy))`
//!     `             (NNReal.mul (sqrtGen sx rx hsx)(sqrtGen sy ry hsy))`
//!     `  = NNReal.ofRat (Rat.mul x y) h`.
//!
//! This is "`√x·√y` is a square root of `x·y`". Together with
//! `NNReal.sqrtGen_sq_at` (which says `√(x·y)` is ALSO a square root of `x·y`) and
//! `NNReal.le_of_sq_le_sq` both ways, the genuine EQUALITY `√(x·y)=√x·√y` follows
//! — but that last antisymmetry step needs `NNReal.le_antisymm`, which is NOT yet
//! in the carrier (see the module-level NOTE below). The square-level statement
//! here is the antisymmetry-free part and is exactly the "both square to x·y"
//! premise the plan (`designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, line 97)
//! calls for.
//!
//! # NOTE — the full equality `sqrtGen_mul` is blocked on `NNReal.le_antisymm`
//!
//! `NNReal.le_of_sq_le_sq` gives `√x·√y ≤ √(x·y)` and `√(x·y) ≤ √x·√y` (both
//! squares are `ofRat (x·y)`, so `ofRat_le_ofRat` + the reverse-square keystone
//! both ways). Converting `(a≤b ∧ b≤a)` to `a=b` needs antisymmetry of
//! `NNReal.le`, which is a quotient-level `Quot.sound` proof not present in the
//! carrier today. The square-level `sqrtGen_mul_sq` carries the full algebraic
//! content modulo that one missing order lemma.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Real` / `Rat.dist`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for `sqrtGen` square-level multiplicativity.
struct SqrtGenMulConsts {
    nnreal: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul_nonneg: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt_gen: Expr,
    nnreal_sqrt_gen_sq_at: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_mmm_comm: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
}

impl SqrtGenMulConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt_gen: k("NNReal.sqrtGen"),
            nnreal_sqrt_gen_sq_at: k("NNReal.sqrtGen_sq_at"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_mmm_comm: k("NNReal.mul_mul_mul_comm"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
        }
    }

    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.rle(self.rat_zero.clone(), a)
    }
    /// `(s·s)·r`.
    fn ss_r(&self, s: &Expr, r: &Expr) -> Expr {
        let ss = self.rmul(s.clone(), s.clone());
        self.rmul(ss, r.clone())
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn rat_mul_nonneg(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_nonneg.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone()],
        )
    }
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    fn sqrt_gen(&self, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_sqrt_gen.clone(),
            [s.clone(), r.clone(), hs.clone()],
        )
    }
    /// `sqrtGen_sq_at x s r hx hs hr hr1 heq : mul a a = ofRat x hx`.
    #[allow(clippy::too_many_arguments)]
    fn sqrt_gen_sq_at(
        &self,
        x: &Expr,
        s: &Expr,
        r: &Expr,
        hx: &Expr,
        hs: &Expr,
        hr: &Expr,
        hr1: &Expr,
        heq: &Expr,
    ) -> Expr {
        Expr::apps(
            self.nnreal_sqrt_gen_sq_at.clone(),
            [
                x.clone(),
                s.clone(),
                r.clone(),
                hx.clone(),
                hs.clone(),
                hr.clone(),
                hr1.clone(),
                heq.clone(),
            ],
        )
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn refl_nn(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a.clone()])
    }
    fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                hab,
                hbc,
            ],
        )
    }
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `NNReal.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn nn_mmm(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mmm_comm.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `NNReal.ofRat_mul a b ha hb hab : mul (ofRat a ha)(ofRat b hb) = ofRat (a·b) hab`.
    fn nn_ofrat_mul(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_mul.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
}

/// `a·p = a·q` from `h : p = q` (congruence in the right factor).
fn congr_mul_right(
    c: &SqrtGenMulConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    p: &Expr,
    q: &Expr,
    h_pq: Expr,
) -> Expr {
    let ap = c.nnmul(a, p);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&ap, &c.nnmul(a, &t));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&ap))
}

/// `p·a = q·a` from `h : p = q` (congruence in the left factor).
fn congr_mul_left(
    c: &SqrtGenMulConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    a: &Expr,
    h_pq: Expr,
) -> Expr {
    let pa = c.nnmul(p, a);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&pa, &c.nnmul(&t, a));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&pa))
}

impl Environment {
    /// Register `NNReal.sqrtGen_mul_sq`. Idempotent.
    pub fn init_algebra_nnreal_sqrt_gen_mul(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_gen()?; // sqrtGen, sqrtGen_sq_at
        self.init_algebra_nnreal_reverse_square_algebra()?; // ofRat_mul
        self.init_algebra_nnreal_pow43_cubed()?; // mul_mul_mul_comm + Rat.mul_nonneg
        self.init_eq()?;

        let c = SqrtGenMulConsts::new();
        self.register_sqrt_gen_mul_sq(&c)?;
        Ok(())
    }

    fn register_sqrt_gen_mul_sq(&mut self, c: &SqrtGenMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtGen_mul_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_sqrt_gen_mul_sq_ty(c);
        let value = build_sqrt_gen_mul_sq_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The 16-binder telescope of `NNReal.sqrtGen_mul_sq`.
fn build_sqrt_gen_mul_sq_ty(c: &SqrtGenMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (sx_id, sx) = b.fresh_local(c.rat.clone());
    let (rx_id, rx) = b.fresh_local(c.rat.clone());
    let (sy_id, sy) = b.fresh_local(c.rat.clone());
    let (ry_id, ry) = b.fresh_local(c.rat.clone());
    let hx_ty = c.nonneg(x.clone());
    let (hx_id, hx) = b.fresh_local(hx_ty.clone());
    let hy_ty = c.nonneg(y.clone());
    let (hy_id, hy) = b.fresh_local(hy_ty.clone());
    let hsx_ty = c.nonneg(sx.clone());
    let (hsx_id, hsx) = b.fresh_local(hsx_ty.clone());
    let hrx_ty = c.nonneg(rx.clone());
    let (hrx_id, _) = b.fresh_local(hrx_ty.clone());
    let hrx1_ty = c.rlt(rx.clone(), c.rat_one.clone());
    let (hrx1_id, _) = b.fresh_local(hrx1_ty.clone());
    let heqx_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), c.ss_r(&sx, &rx)]);
    let (heqx_id, _) = b.fresh_local(heqx_ty.clone());
    let hsy_ty = c.nonneg(sy.clone());
    let (hsy_id, hsy) = b.fresh_local(hsy_ty.clone());
    let hry_ty = c.nonneg(ry.clone());
    let (hry_id, _) = b.fresh_local(hry_ty.clone());
    let hry1_ty = c.rlt(ry.clone(), c.rat_one.clone());
    let (hry1_id, _) = b.fresh_local(hry1_ty.clone());
    let heqy_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), y.clone(), c.ss_r(&sy, &ry)]);
    let (heqy_id, _) = b.fresh_local(heqy_ty.clone());

    let a = c.sqrt_gen(&sx, &rx, &hsx);
    let bb = c.sqrt_gen(&sy, &ry, &hsy);
    let prod = c.nnmul(&a, &bb);
    let lhs = c.nnmul(&prod, &prod);
    let xy = c.rmul(x.clone(), y.clone());
    let h_xy = c.rat_mul_nonneg(&x, &y, &hx, &hy);
    let rhs = c.ofrat(&xy, &h_xy);
    let concl = c.eq_nn(&lhs, &rhs);

    let mk_pi = |b: &mut EnvDeclBuilder, id, ty: Expr, body: Expr| {
        b.mk_pi(id, BinderInfo::Default, ty, body)
    };
    let e = mk_pi(&mut b, heqy_id, heqy_ty, concl);
    let e = mk_pi(&mut b, hry1_id, hry1_ty, e);
    let e = mk_pi(&mut b, hry_id, hry_ty, e);
    let e = mk_pi(&mut b, hsy_id, hsy_ty, e);
    let e = mk_pi(&mut b, heqx_id, heqx_ty, e);
    let e = mk_pi(&mut b, hrx1_id, hrx1_ty, e);
    let e = mk_pi(&mut b, hrx_id, hrx_ty, e);
    let e = mk_pi(&mut b, hsx_id, hsx_ty, e);
    let e = mk_pi(&mut b, hy_id, hy_ty, e);
    let e = mk_pi(&mut b, hx_id, hx_ty, e);
    let e = mk_pi(&mut b, ry_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, sy_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, rx_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, sx_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, y_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, x_id, c.rat.clone(), e);
    b.finish(e)
}

/// The proof term of `NNReal.sqrtGen_mul_sq`.
///
/// `A := sqrtGen sx rx hsx`, `B := sqrtGen sy ry hsy`, `P := A·B`.
/// `P·P = (A·B)·(A·B) =[mul_mul_mul_comm A B A B] (A·A)·(B·B)`
/// `=[congr right, sqB] (A·A)·ofRat y =[congr left, sqA] ofRat x · ofRat y`
/// `=[ofRat_mul x y] ofRat (x·y)`.
fn build_sqrt_gen_mul_sq_value(c: &SqrtGenMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (sx_id, sx) = b.fresh_local(c.rat.clone());
    let (rx_id, rx) = b.fresh_local(c.rat.clone());
    let (sy_id, sy) = b.fresh_local(c.rat.clone());
    let (ry_id, ry) = b.fresh_local(c.rat.clone());
    let hx_ty = c.nonneg(x.clone());
    let (hx_id, hx) = b.fresh_local(hx_ty.clone());
    let hy_ty = c.nonneg(y.clone());
    let (hy_id, hy) = b.fresh_local(hy_ty.clone());
    let hsx_ty = c.nonneg(sx.clone());
    let (hsx_id, hsx) = b.fresh_local(hsx_ty.clone());
    let hrx_ty = c.nonneg(rx.clone());
    let (hrx_id, hrx) = b.fresh_local(hrx_ty.clone());
    let hrx1_ty = c.rlt(rx.clone(), c.rat_one.clone());
    let (hrx1_id, hrx1) = b.fresh_local(hrx1_ty.clone());
    let heqx_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), c.ss_r(&sx, &rx)]);
    let (heqx_id, heqx) = b.fresh_local(heqx_ty.clone());
    let hsy_ty = c.nonneg(sy.clone());
    let (hsy_id, hsy) = b.fresh_local(hsy_ty.clone());
    let hry_ty = c.nonneg(ry.clone());
    let (hry_id, hry) = b.fresh_local(hry_ty.clone());
    let hry1_ty = c.rlt(ry.clone(), c.rat_one.clone());
    let (hry1_id, hry1) = b.fresh_local(hry1_ty.clone());
    let heqy_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), y.clone(), c.ss_r(&sy, &ry)]);
    let (heqy_id, heqy) = b.fresh_local(heqy_ty.clone());

    let a = c.sqrt_gen(&sx, &rx, &hsx);
    let bb = c.sqrt_gen(&sy, &ry, &hsy);
    let prod = c.nnmul(&a, &bb);
    let lhs = c.nnmul(&prod, &prod); // (A·B)·(A·B)

    let aa = c.nnmul(&a, &a);
    let bbb = c.nnmul(&bb, &bb);
    let aabb = c.nnmul(&aa, &bbb); // (A·A)·(B·B)
    let step_regroup = c.nn_mmm(&a, &bb, &a, &bb); // lhs = aabb

    let ofx = c.ofrat(&x, &hx);
    let ofy = c.ofrat(&y, &hy);
    // sqA : A·A = ofRat x ; sqB : B·B = ofRat y.
    let sq_a = c.sqrt_gen_sq_at(&x, &sx, &rx, &hx, &hsx, &hrx, &hrx1, &heqx);
    let sq_b = c.sqrt_gen_sq_at(&y, &sy, &ry, &hy, &hsy, &hry, &hry1, &heqy);

    // aabb = (A·A)·(B·B) →[congr right sqB] (A·A)·ofRat y
    //                    →[congr left  sqA] ofRat x · ofRat y
    //                    →[ofRat_mul]       ofRat (x·y)
    let aa_ofy = c.nnmul(&aa, &ofy); // (A·A)·ofRat y
    let bb_to_ofy = congr_mul_right(c, &b, &aa, &bbb, &ofy, sq_b); // aabb = aa·ofy
    let ofx_ofy = c.nnmul(&ofx, &ofy); // ofRat x · ofRat y
    let aa_ofy_to_ofx_ofy = congr_mul_left(c, &b, &aa, &ofx, &ofy, sq_a); // aa·ofy = ofx·ofy

    let xy = c.rmul(x.clone(), y.clone());
    let h_xy = c.rat_mul_nonneg(&x, &y, &hx, &hy);
    let of_xy = c.ofrat(&xy, &h_xy);
    let ofx_ofy_eq = c.nn_ofrat_mul(&x, &y, &hx, &hy, &h_xy); // ofx·ofy = ofRat(x·y)

    let comb1 = c.trans_nn(&aabb, &aa_ofy, &ofx_ofy, bb_to_ofy, aa_ofy_to_ofx_ofy);
    let comb = c.trans_nn(&aabb, &ofx_ofy, &of_xy, comb1, ofx_ofy_eq);

    // FULL: lhs = aabb (step_regroup) = ofRat(x·y) (comb).
    let proof = c.trans_nn(&lhs, &aabb, &of_xy, step_regroup, comb);

    let mk_lam = |b: &mut EnvDeclBuilder, id, ty: Expr, body: Expr| {
        b.mk_lam(id, BinderInfo::Default, ty, body)
    };
    let e = mk_lam(&mut b, heqy_id, heqy_ty, proof);
    let e = mk_lam(&mut b, hry1_id, hry1_ty, e);
    let e = mk_lam(&mut b, hry_id, hry_ty, e);
    let e = mk_lam(&mut b, hsy_id, hsy_ty, e);
    let e = mk_lam(&mut b, heqx_id, heqx_ty, e);
    let e = mk_lam(&mut b, hrx1_id, hrx1_ty, e);
    let e = mk_lam(&mut b, hrx_id, hrx_ty, e);
    let e = mk_lam(&mut b, hsx_id, hsx_ty, e);
    let e = mk_lam(&mut b, hy_id, hy_ty, e);
    let e = mk_lam(&mut b, hx_id, hx_ty, e);
    let e = mk_lam(&mut b, ry_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, sy_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, rx_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, sx_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, y_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, x_id, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.sqrtGen_mul_sq"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_gen_mul()
            .expect("init_algebra_nnreal_sqrt_gen_mul");
        env.init_algebra_nnreal_sqrt_gen_mul().expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_gen_mul_sq_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_sqrt_gen_mul_sq_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
