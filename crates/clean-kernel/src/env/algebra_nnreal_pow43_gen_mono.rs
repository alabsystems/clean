// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.pow43Gen` MONOTONICITY
//! (`x ≤ y → x^{4/3} ≤ y^{4/3}` for nonneg `x,y`), derived ALGEBRAICALLY from
//! the two component monotonicities already landed.
//!
//! # Why this module exists (the `(4/3,4)` base consumer)
//!
//! The two-point Hölder base raises a lower bound on a sum of `pow43Gen` legs.
//! Every such consumer first needs the legs themselves to be MONOTONE in their
//! argument: a larger nonneg argument has a larger `^{4/3}`. This is the forward
//! partner of the cube-root monotonicity `NNReal.cbrtGen_le_cbrtGen`.
//!
//! # The keystone (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.pow43Gen_le_pow43Gen :
//!     ∀ (x y sx rx sy ry : Rat)
//!       (hx : 0≤x)(hy : 0≤y)
//!       (hsx : 0≤sx)(hrx : 0≤rx)(hrx1 : rx<1)(heqx : x = ((sx·sx)·sx)·rx)
//!       (hsy : 0≤sy)(hry : 0≤ry)(hry1 : ry<1)(heqy : y = ((sy·sy)·sy)·ry)
//!       (hxy : Rat.le x y),
//!       NNReal.le (NNReal.pow43Gen x sx rx hx hsx)
//!                 (NNReal.pow43Gen y sy ry hy hsy)
//! ```
//!
//! Proof. `pow43Gen x sx rx hx hsx ≡ NNReal.mul (ofRat x hx)(cbrtGen sx rx hsx)`
//! (reducible defeq), and likewise for `y`. Then:
//!   * `ofRat x hx ≤ ofRat y hy`              (`NNReal.ofRat_le_ofRat x y hx hy hxy`)
//!   * `cbrtGen sx rx hsx ≤ cbrtGen sy ry hsy`(`NNReal.cbrtGen_le_cbrtGen …`)
//!   * `mul (ofRat x)(cbrtGen …) ≤ mul (ofRat y)(cbrtGen …)` (`NNReal.mul_le_mul`).
//!
//! The conclusion is that last `≤` up to the `pow43Gen` defeq.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::name::Name;

/// Pre-resolved handles for `pow43Gen` monotonicity.
struct Pow43GenMonoConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    nnreal_le: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_cbrt_gen: Expr,
    nnreal_pow43_gen: Expr,
    nnreal_ofrat_le_ofrat: Expr,
    nnreal_cbrt_gen_le: Expr,
    nnreal_mul_le_mul: Expr,
    eq: Expr,
}

impl Pow43GenMonoConsts {
    fn new() -> Self {
        let l1 = crate::level::Level::succ(crate::level::Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            nnreal_le: k("NNReal.le"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_cbrt_gen: k("NNReal.cbrtGen"),
            nnreal_pow43_gen: k("NNReal.pow43Gen"),
            nnreal_ofrat_le_ofrat: k("NNReal.ofRat_le_ofRat"),
            nnreal_cbrt_gen_le: k("NNReal.cbrtGen_le_cbrtGen"),
            nnreal_mul_le_mul: k("NNReal.mul_le_mul"),
            eq: Expr::const_(Name::from_string("Eq"), vec![l1]),
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
    /// `NNReal.pow43Gen x s r hx hs`.
    fn pow43_gen(&self, x: &Expr, s: &Expr, r: &Expr, hx: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_pow43_gen.clone(),
            [x.clone(), s.clone(), r.clone(), hx.clone(), hs.clone()],
        )
    }
    /// `ofRat_le_ofRat a b ha hb (a≤b) : NNReal.le (ofRat a ha)(ofRat b hb)`.
    fn ofrat_le_ofrat(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hle: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_le_ofrat.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hle.clone()],
        )
    }
    /// `mul_le_mul a b c d (a≤b)(c≤d) : NNReal.le (mul a c)(mul b d)`.
    #[allow(clippy::too_many_arguments)]
    fn mul_le_mul(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_le_mul.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `cbrtGen_le_cbrtGen` fully applied (17 args), giving
    /// `NNReal.le (cbrtGen sx rx hsx)(cbrtGen sy ry hsy)`.
    #[allow(clippy::too_many_arguments)]
    fn cbrt_gen_le(&self, args: &[Expr]) -> Expr {
        Expr::apps(self.nnreal_cbrt_gen_le.clone(), args.to_vec())
    }
}

impl Environment {
    /// Register `NNReal.pow43Gen_le_pow43Gen`. Idempotent.
    pub fn init_algebra_nnreal_pow43_gen_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cbrt_gen()?; // pow43Gen, cbrtGen
        self.init_algebra_nnreal_cbrt_gen_mono()?; // cbrtGen_le_cbrtGen
        self.init_algebra_nnreal_cube_mono()?; // NNReal.mul_le_mul
        self.init_algebra_nnreal_le()?; // NNReal.ofRat_le_ofRat, NNReal.le

        let c = Pow43GenMonoConsts::new();
        self.register_pow43_gen_le_pow43_gen(&c)?;
        Ok(())
    }

    fn register_pow43_gen_le_pow43_gen(&mut self, c: &Pow43GenMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.pow43Gen_le_pow43Gen");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_pow43_gen_mono_ty(c);
        let value = build_pow43_gen_mono_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Push the shared 16-binder telescope (everything before the final conclusion)
/// onto a builder, returning the bound locals needed downstream. The 17th binder
/// (`hxy`) and the conclusion/body are supplied by the caller, so this is shared
/// verbatim between the type and the value.
struct Telescope {
    x: Expr,
    y: Expr,
    sx: Expr,
    rx: Expr,
    sy: Expr,
    ry: Expr,
    hx: Expr,
    hy: Expr,
    hsx: Expr,
    hrx: Expr,
    hrx1: Expr,
    heqx: Expr,
    hsy: Expr,
    hry: Expr,
    hry1: Expr,
    heqy: Expr,
    ids: Vec<(FVarId, Expr)>,
}

/// Allocate all 16 leading binders + their types in order, returning the locals
/// and the `(id, ty)` list (outer-first) so the caller can wrap with `mk_pi` /
/// `mk_lam` uniformly.
fn telescope(c: &Pow43GenMonoConsts, b: &mut EnvDeclBuilder) -> Telescope {
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
    let heqx_ty = Expr::apps(c.eq.clone(), [c.rat.clone(), x.clone(), c.sss_r(&sx, &rx)]);
    let (heqx_id, heqx) = b.fresh_local(heqx_ty.clone());
    let hsy_ty = c.nonneg(sy.clone());
    let (hsy_id, hsy) = b.fresh_local(hsy_ty.clone());
    let hry_ty = c.nonneg(ry.clone());
    let (hry_id, hry) = b.fresh_local(hry_ty.clone());
    let hry1_ty = c.rlt(ry.clone(), c.rat_one.clone());
    let (hry1_id, hry1) = b.fresh_local(hry1_ty.clone());
    let heqy_ty = Expr::apps(c.eq.clone(), [c.rat.clone(), y.clone(), c.sss_r(&sy, &ry)]);
    let (heqy_id, heqy) = b.fresh_local(heqy_ty.clone());

    let ids = vec![
        (x_id, c.rat.clone()),
        (y_id, c.rat.clone()),
        (sx_id, c.rat.clone()),
        (rx_id, c.rat.clone()),
        (sy_id, c.rat.clone()),
        (ry_id, c.rat.clone()),
        (hx_id, hx_ty),
        (hy_id, hy_ty),
        (hsx_id, hsx_ty),
        (hrx_id, hrx_ty),
        (hrx1_id, hrx1_ty),
        (heqx_id, heqx_ty),
        (hsy_id, hsy_ty),
        (hry_id, hry_ty),
        (hry1_id, hry1_ty),
        (heqy_id, heqy_ty),
    ];
    Telescope {
        x,
        y,
        sx,
        rx,
        sy,
        ry,
        hx,
        hy,
        hsx,
        hrx,
        hrx1,
        heqx,
        hsy,
        hry,
        hry1,
        heqy,
        ids,
    }
}

/// The 17-binder type of `NNReal.pow43Gen_le_pow43Gen`.
fn build_pow43_gen_mono_ty(c: &Pow43GenMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let t = telescope(c, &mut b);
    let hxy_ty = c.rle(t.x.clone(), t.y.clone());
    let (hxy_id, _) = b.fresh_local(hxy_ty.clone());

    let lhs = c.pow43_gen(&t.x, &t.sx, &t.rx, &t.hx, &t.hsx);
    let rhs = c.pow43_gen(&t.y, &t.sy, &t.ry, &t.hy, &t.hsy);
    let concl = c.nnle(&lhs, &rhs);

    let mut e = b.mk_pi(hxy_id, BinderInfo::Default, hxy_ty, concl);
    for (id, ty) in t.ids.into_iter().rev() {
        e = b.mk_pi(id, BinderInfo::Default, ty, e);
    }
    b.finish(e)
}

/// The proof term of `NNReal.pow43Gen_le_pow43Gen`.
fn build_pow43_gen_mono_value(c: &Pow43GenMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let t = telescope(c, &mut b);
    let hxy_ty = c.rle(t.x.clone(), t.y.clone());
    let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());

    // h_of : ofRat x hx ≤ ofRat y hy.
    let h_of = c.ofrat_le_ofrat(&t.x, &t.y, &t.hx, &t.hy, &hxy);

    // h_cbrt : cbrtGen sx rx hsx ≤ cbrtGen sy ry hsy.
    let cbrt_args = [
        t.x.clone(),
        t.y.clone(),
        t.sx.clone(),
        t.rx.clone(),
        t.sy.clone(),
        t.ry.clone(),
        t.hx.clone(),
        t.hy.clone(),
        t.hsx.clone(),
        t.hrx.clone(),
        t.hrx1.clone(),
        t.heqx.clone(),
        t.hsy.clone(),
        t.hry.clone(),
        t.hry1.clone(),
        t.heqy.clone(),
        hxy.clone(),
    ];
    let h_cbrt = c.cbrt_gen_le(&cbrt_args);

    // combine via mul_le_mul:
    //   mul (ofRat x)(cbrtGen sx rx) ≤ mul (ofRat y)(cbrtGen sy ry)
    // which is defeq to pow43Gen x … ≤ pow43Gen y ….
    let of_x = c.ofrat(&t.x, &t.hx);
    let of_y = c.ofrat(&t.y, &t.hy);
    let cb_x = c.cbrt_gen(&t.sx, &t.rx, &t.hsx);
    let cb_y = c.cbrt_gen(&t.sy, &t.ry, &t.hsy);
    let proof = c.mul_le_mul(&of_x, &of_y, &cb_x, &cb_y, h_of, h_cbrt);

    let mut e = b.mk_lam(hxy_id, BinderInfo::Default, hxy_ty, proof);
    for (id, ty) in t.ids.into_iter().rev() {
        e = b.mk_lam(id, BinderInfo::Default, ty, e);
    }
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.pow43Gen_le_pow43Gen"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_pow43_gen_mono()
            .expect("init_algebra_nnreal_pow43_gen_mono");
        env.init_algebra_nnreal_pow43_gen_mono()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_pow43_gen_mono_kernel_check() {
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
    fn test_pow43_gen_mono_constructive_empty_closure() {
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
