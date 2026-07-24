// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.sqrtGen` MONOTONICITY, derived from
//! `sqrtGen_sq_at` + the square-reflects-order keystone (no dyadic-floor work).
//!
//! # Why this module exists (the cheap monotonicity route)
//!
//! The `(4/3,4)` tensorization cross-term needs `sqrt` monotone on arbitrary
//! nonneg arguments (e.g. `NG·NH ≤ NG'·NH' ⟹ √(NG·NH) ≤ √(NG'·NH')`). The landed
//! `[0,1)` `NNReal.sqrtRat` monotonicity is a heavy dyadic-floor argument. For the
//! GENERAL scaled square root `sqrtGen` we get monotonicity ALGEBRAICALLY for
//! free: `sqrtGen` squares back to its argument (`NNReal.sqrtGen_sq_at`), so a `≤`
//! on arguments transports to a `≤` on squares, and the square-reflects-order
//! keystone (`NNReal.le_of_sq_le_sq`, `algebra_nnreal_reverse_square_sq.rs`) pulls
//! it back to a `≤` on the square roots.
//!
//! This is the EXACT square analog of `NNReal.cbrtGen_le_cbrtGen`
//! (`algebra_nnreal_cbrt_gen_mono.rs`): cube → square, `le_of_cube_le_cube` →
//! `le_of_sq_le_sq`, `cbrtGen_cubed_at` → `sqrtGen_sq_at`.
//!
//! # The keystone (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.sqrtGen_le_sqrtGen :
//!     ∀ (x y sx rx sy ry : Rat)
//!       (hx : 0≤x)(hy : 0≤y)
//!       (hsx : 0≤sx)(hrx : 0≤rx)(hrx1 : rx<1)(heqx : x = (sx·sx)·rx)
//!       (hsy : 0≤sy)(hry : 0≤ry)(hry1 : ry<1)(heqy : y = (sy·sy)·ry)
//!       (hxy : Rat.le x y),
//!       NNReal.le (NNReal.sqrtGen sx rx hsx) (NNReal.sqrtGen sy ry hsy)
//! ```
//!
//! Proof. Let `a := sqrtGen sx rx hsx`, `b := sqrtGen sy ry hsy`.
//!   * `a² = ofRat x`  (`sqrtGen_sq_at x sx rx … heqx`).
//!   * `b² = ofRat y`  (`sqrtGen_sq_at y sy ry … heqy`).
//!   * `ofRat x ≤ ofRat y`  (`ofRat_le_ofRat x y hx hy hxy`).
//!   * transport: `a² ≤ b²`  (subst the two square equations into the `ofRat`
//!     inequality, in two `Eq.subst`s over `NNReal.le`).
//!   * `a ≤ b`  (`le_of_sq_le_sq a b (a²≤b²)`).
//!
//! The square `mul a a` in `sqrtGen_sq_at` matches exactly the square
//! `le_of_sq_le_sq` consumes.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Real` / `Rat.dist`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for `sqrtGen` monotonicity.
struct SqrtGenMonoConsts {
    nnreal: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    nnreal_mul: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt_gen: Expr,
    nnreal_sqrt_gen_sq_at: Expr,
    nnreal_ofrat_le_ofrat: Expr,
    nnreal_le_of_sq_le_sq: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
}

impl SqrtGenMonoConsts {
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
            nnreal_mul: k("NNReal.mul"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt_gen: k("NNReal.sqrtGen"),
            nnreal_sqrt_gen_sq_at: k("NNReal.sqrtGen_sq_at"),
            nnreal_ofrat_le_ofrat: k("NNReal.ofRat_le_ofRat"),
            nnreal_le_of_sq_le_sq: k("NNReal.le_of_sq_le_sq"),
            eq1: kl("Eq"),
            eq_symm1: kl("Eq.symm"),
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
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    /// `mul a a`.
    fn nnsq(&self, a: &Expr) -> Expr {
        self.nnmul(a, a)
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
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
    /// `ofRat_le_ofRat a b ha hb (a≤b) : NNReal.le (ofRat a ha)(ofRat b hb)`.
    fn ofrat_le_ofrat(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hle: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_le_ofrat.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hle.clone()],
        )
    }
    /// `le_of_sq_le_sq a b (mul a a ≤ mul b b) : NNReal.le a b`.
    fn le_of_sq_le_sq(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_sq_le_sq.clone(),
            [a.clone(), b.clone(), h],
        )
    }
    fn symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
}

impl Environment {
    /// Register `NNReal.sqrtGen_le_sqrtGen`. Idempotent.
    pub fn init_algebra_nnreal_sqrt_gen_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_gen()?; // sqrtGen, sqrtGen_sq_at
        self.init_algebra_nnreal_le()?; // NNReal.ofRat_le_ofRat
        self.init_algebra_nnreal_reverse_square_sq()?; // NNReal.le_of_sq_le_sq
        self.init_eq()?;

        let c = SqrtGenMonoConsts::new();
        self.register_sqrt_gen_le_sqrt_gen(&c)?;
        Ok(())
    }

    fn register_sqrt_gen_le_sqrt_gen(&mut self, c: &SqrtGenMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtGen_le_sqrtGen");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_sqrt_gen_mono_ty(c);
        let value = build_sqrt_gen_mono_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The 17-binder telescope of `NNReal.sqrtGen_le_sqrtGen`.
fn build_sqrt_gen_mono_ty(c: &SqrtGenMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (sx_id, sx) = b.fresh_local(c.rat.clone());
    let (rx_id, rx) = b.fresh_local(c.rat.clone());
    let (sy_id, sy) = b.fresh_local(c.rat.clone());
    let (ry_id, ry) = b.fresh_local(c.rat.clone());
    let hx_ty = c.nonneg(x.clone());
    let (hx_id, _) = b.fresh_local(hx_ty.clone());
    let hy_ty = c.nonneg(y.clone());
    let (hy_id, _) = b.fresh_local(hy_ty.clone());
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
    let hxy_ty = c.rle(x.clone(), y.clone());
    let (hxy_id, _) = b.fresh_local(hxy_ty.clone());

    let a = c.sqrt_gen(&sx, &rx, &hsx);
    let bb = c.sqrt_gen(&sy, &ry, &hsy);
    let concl = c.nnle(&a, &bb);

    let mk_pi = |b: &mut EnvDeclBuilder, id, ty: Expr, body: Expr| {
        b.mk_pi(id, BinderInfo::Default, ty, body)
    };
    let e = mk_pi(&mut b, hxy_id, hxy_ty, concl);
    let e = mk_pi(&mut b, heqy_id, heqy_ty, e);
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

/// The proof term of `NNReal.sqrtGen_le_sqrtGen`.
fn build_sqrt_gen_mono_value(c: &SqrtGenMonoConsts) -> Expr {
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
    let hxy_ty = c.rle(x.clone(), y.clone());
    let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());

    let a = c.sqrt_gen(&sx, &rx, &hsx);
    let bb = c.sqrt_gen(&sy, &ry, &hsy);
    let sq_a = c.nnsq(&a);
    let sq_b = c.nnsq(&bb);
    let ofx = c.ofrat(&x, &hx);
    let ofy = c.ofrat(&y, &hy);

    // ca : sq_a = ofRat x ;  cb : sq_b = ofRat y.
    let ca = c.sqrt_gen_sq_at(&x, &sx, &rx, &hx, &hsx, &hrx, &hrx1, &heqx);
    let cb = c.sqrt_gen_sq_at(&y, &sy, &ry, &hy, &hsy, &hry, &hry1, &heqy);

    // base : NNReal.le (ofRat x)(ofRat y).
    let base = c.ofrat_le_ofrat(&x, &y, &hx, &hy, &hxy);

    // Step 1: rewrite ofRat y → sq_b in base, giving NNReal.le (ofRat x) sq_b.
    let cb_symm = c.symm(&sq_b, &ofy, cb); // ofRat y = sq_b
    let motive1 = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&ofx, &t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let step1 = c.subst(motive1, &ofy, &sq_b, cb_symm, base); // NNReal.le (ofRat x) sq_b

    // Step 2: rewrite ofRat x → sq_a, giving NNReal.le sq_a sq_b.
    let ca_symm = c.symm(&sq_a, &ofx, ca); // ofRat x = sq_a
    let motive2 = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&t, &sq_b);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let step2 = c.subst(motive2, &ofx, &sq_a, ca_symm, step1); // NNReal.le sq_a sq_b

    // Conclude: le_of_sq_le_sq a b step2 : NNReal.le a b.
    let proof = c.le_of_sq_le_sq(&a, &bb, step2);

    let mk_lam = |b: &mut EnvDeclBuilder, id, ty: Expr, body: Expr| {
        b.mk_lam(id, BinderInfo::Default, ty, body)
    };
    let e = mk_lam(&mut b, hxy_id, hxy_ty, proof);
    let e = mk_lam(&mut b, heqy_id, heqy_ty, e);
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

    const THEOREMS: &[&str] = &["NNReal.sqrtGen_le_sqrtGen"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_gen_mono()
            .expect("init_algebra_nnreal_sqrt_gen_mono");
        env.init_algebra_nnreal_sqrt_gen_mono().expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_gen_mono_kernel_check() {
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
    fn test_sqrt_gen_mono_constructive_empty_closure() {
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
