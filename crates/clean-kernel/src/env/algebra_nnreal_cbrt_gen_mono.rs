// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.cbrtGen` MONOTONICITY, derived from
//! `cbrtGen_cubed_at` + the cube-reflects-order keystone (no dyadic-floor work).
//!
//! # Why this module exists (the cheap monotonicity route)
//!
//! The `(4/3,4)` two-point base needs `cbrt` monotone on arbitrary nonneg
//! arguments. The landed `[0,1)` `NNReal.cbrt` monotonicity is a heavy
//! dyadic-floor argument (~hundreds of lines). For the GENERAL scaled cube root
//! `cbrtGen` we get monotonicity ALGEBRAICALLY for free: `cbrtGen` cubes back to
//! its argument (`NNReal.cbrtGen_cubed_at`), so a `≤` on arguments transports to
//! a `≤` on cubes, and the cube-reflects-order keystone
//! (`NNReal.le_of_cube_le_cube`, `algebra_nnreal_reverse_cube.rs`) pulls it back
//! to a `≤` on the cube roots.
//!
//! # The keystone (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.cbrtGen_le_cbrtGen :
//!     ∀ (x y sx rx sy ry : Rat)
//!       (hx : 0≤x)(hy : 0≤y)
//!       (hsx : 0≤sx)(hrx : 0≤rx)(hrx1 : rx<1)(heqx : x = ((sx·sx)·sx)·rx)
//!       (hsy : 0≤sy)(hry : 0≤ry)(hry1 : ry<1)(heqy : y = ((sy·sy)·sy)·ry)
//!       (hxy : Rat.le x y),
//!       NNReal.le (NNReal.cbrtGen sx rx hsx) (NNReal.cbrtGen sy ry hsy)
//! ```
//!
//! Proof. Let `a := cbrtGen sx rx hsx`, `b := cbrtGen sy ry hsy`.
//!   * `a³ = ofRat x`  (`cbrtGen_cubed_at x sx rx … heqx`).
//!   * `b³ = ofRat y`  (`cbrtGen_cubed_at y sy ry … heqy`).
//!   * `ofRat x ≤ ofRat y`  (`ofRat_le_ofRat x y hx hy hxy`).
//!   * transport: `a³ ≤ b³`  (subst the two cube equations into the `ofRat`
//!     inequality, in two `Eq.subst`s over `NNReal.le`).
//!   * `a ≤ b`  (`le_of_cube_le_cube a b (a³≤b³)`).
//!
//! The cube nesting `mul (mul a a) a` in `cbrtGen_cubed_at` matches exactly the
//! cube `le_of_cube_le_cube` consumes.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for `cbrtGen` monotonicity.
struct CbrtGenMonoConsts {
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
    nnreal_cbrt_gen: Expr,
    nnreal_cbrt_gen_cubed_at: Expr,
    nnreal_ofrat_le_ofrat: Expr,
    nnreal_le_of_cube_le_cube: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
}

impl CbrtGenMonoConsts {
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
            nnreal_cbrt_gen: k("NNReal.cbrtGen"),
            nnreal_cbrt_gen_cubed_at: k("NNReal.cbrtGen_cubed_at"),
            nnreal_ofrat_le_ofrat: k("NNReal.ofRat_le_ofRat"),
            nnreal_le_of_cube_le_cube: k("NNReal.le_of_cube_le_cube"),
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
    /// `((s·s)·s)·r`.
    fn sss_r(&self, s: &Expr, r: &Expr) -> Expr {
        let ss = self.rmul(s.clone(), s.clone());
        let sss = self.rmul(ss, s.clone());
        self.rmul(sss, r.clone())
    }
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    /// `mul (mul a a) a`.
    fn nncube(&self, a: &Expr) -> Expr {
        self.nnmul(&self.nnmul(a, a), a)
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    fn cbrt_gen(&self, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_cbrt_gen.clone(),
            [s.clone(), r.clone(), hs.clone()],
        )
    }
    /// `cbrtGen_cubed_at x s r hx hs hr hr1 heq : mul(mul a a)a = ofRat x hx`.
    #[allow(clippy::too_many_arguments)]
    fn cbrt_gen_cubed_at(
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
            self.nnreal_cbrt_gen_cubed_at.clone(),
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
    /// `le_of_cube_le_cube a b (cube a ≤ cube b) : NNReal.le a b`.
    fn le_of_cube_le_cube(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_cube_le_cube.clone(),
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
    /// Register `NNReal.cbrtGen_le_cbrtGen`. Idempotent.
    pub fn init_algebra_nnreal_cbrt_gen_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cbrt_gen()?; // cbrtGen, cbrtGen_cubed_at, pow43Gen
        self.init_algebra_nnreal_le()?; // NNReal.ofRat_le_ofRat
        self.init_algebra_nnreal_reverse_cube()?; // NNReal.le_of_cube_le_cube
        self.init_eq()?;

        let c = CbrtGenMonoConsts::new();
        self.register_cbrt_gen_le_cbrt_gen(&c)?;
        Ok(())
    }

    fn register_cbrt_gen_le_cbrt_gen(&mut self, c: &CbrtGenMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cbrtGen_le_cbrtGen");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_cbrt_gen_mono_ty(c);
        let value = build_cbrt_gen_mono_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The 17-binder telescope of `NNReal.cbrtGen_le_cbrtGen`.
fn build_cbrt_gen_mono_ty(c: &CbrtGenMonoConsts) -> Expr {
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
    let heqx_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), c.sss_r(&sx, &rx)]);
    let (heqx_id, _) = b.fresh_local(heqx_ty.clone());
    let hsy_ty = c.nonneg(sy.clone());
    let (hsy_id, hsy) = b.fresh_local(hsy_ty.clone());
    let hry_ty = c.nonneg(ry.clone());
    let (hry_id, _) = b.fresh_local(hry_ty.clone());
    let hry1_ty = c.rlt(ry.clone(), c.rat_one.clone());
    let (hry1_id, _) = b.fresh_local(hry1_ty.clone());
    let heqy_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), y.clone(), c.sss_r(&sy, &ry)]);
    let (heqy_id, _) = b.fresh_local(heqy_ty.clone());
    let hxy_ty = c.rle(x.clone(), y.clone());
    let (hxy_id, _) = b.fresh_local(hxy_ty.clone());

    let a = c.cbrt_gen(&sx, &rx, &hsx);
    let bb = c.cbrt_gen(&sy, &ry, &hsy);
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

/// The proof term of `NNReal.cbrtGen_le_cbrtGen`.
fn build_cbrt_gen_mono_value(c: &CbrtGenMonoConsts) -> Expr {
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
    let heqx_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), c.sss_r(&sx, &rx)]);
    let (heqx_id, heqx) = b.fresh_local(heqx_ty.clone());
    let hsy_ty = c.nonneg(sy.clone());
    let (hsy_id, hsy) = b.fresh_local(hsy_ty.clone());
    let hry_ty = c.nonneg(ry.clone());
    let (hry_id, hry) = b.fresh_local(hry_ty.clone());
    let hry1_ty = c.rlt(ry.clone(), c.rat_one.clone());
    let (hry1_id, hry1) = b.fresh_local(hry1_ty.clone());
    let heqy_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), y.clone(), c.sss_r(&sy, &ry)]);
    let (heqy_id, heqy) = b.fresh_local(heqy_ty.clone());
    let hxy_ty = c.rle(x.clone(), y.clone());
    let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());

    let a = c.cbrt_gen(&sx, &rx, &hsx);
    let bb = c.cbrt_gen(&sy, &ry, &hsy);
    let cube_a = c.nncube(&a);
    let cube_b = c.nncube(&bb);
    let ofx = c.ofrat(&x, &hx);
    let ofy = c.ofrat(&y, &hy);

    // ca : cube_a = ofRat x ;  cb : cube_b = ofRat y.
    let ca = c.cbrt_gen_cubed_at(&x, &sx, &rx, &hx, &hsx, &hrx, &hrx1, &heqx);
    let cb = c.cbrt_gen_cubed_at(&y, &sy, &ry, &hy, &hsy, &hry, &hry1, &heqy);

    // base : NNReal.le (ofRat x)(ofRat y).
    let base = c.ofrat_le_ofrat(&x, &y, &hx, &hy, &hxy);

    // Step 1: rewrite ofRat y → cube_b in base, giving NNReal.le (ofRat x) cube_b.
    //   subst over motive `fun t => NNReal.le (ofRat x) t`, eq `ofRat y = cube_b`
    //   (= symm cb), starting from base : NNReal.le (ofRat x)(ofRat y).
    let cb_symm = c.symm(&cube_b, &ofy, cb); // ofRat y = cube_b
    let motive1 = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&ofx, &t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let step1 = c.subst(motive1, &ofy, &cube_b, cb_symm, base); // NNReal.le (ofRat x) cube_b

    // Step 2: rewrite ofRat x → cube_a, giving NNReal.le cube_a cube_b.
    let ca_symm = c.symm(&cube_a, &ofx, ca); // ofRat x = cube_a
    let motive2 = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&t, &cube_b);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let step2 = c.subst(motive2, &ofx, &cube_a, ca_symm, step1); // NNReal.le cube_a cube_b

    // Conclude: le_of_cube_le_cube a b step2 : NNReal.le a b.
    let proof = c.le_of_cube_le_cube(&a, &bb, step2);

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

    const THEOREMS: &[&str] = &["NNReal.cbrtGen_le_cbrtGen"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_gen_mono()
            .expect("init_algebra_nnreal_cbrt_gen_mono");
        env.init_algebra_nnreal_cbrt_gen_mono().expect("idempotent");
        env
    }

    #[test]
    fn test_cbrt_gen_mono_kernel_check() {
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
    fn test_cbrt_gen_mono_constructive_empty_closure() {
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
