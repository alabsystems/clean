// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.sqrtGen_mul` — the FULL multiplicativity
//! `√(x·y) = √x·√y`, axiom-free.
//!
//! # Why this module exists (the cross-term keystone `√(NG³·NH³)`)
//!
//! The `(4/3, 4)` tensorization cross-term needs the GENUINE EQUALITY
//! `√(x·y) = √x·√y` (e.g. `√(NG³·NH³) = NG^{3/2}·NH^{3/2}`). The square-level
//! splitting `NNReal.sqrtGen_mul_sq` already shows `√x·√y` and `√(x·y)` BOTH
//! square to `ofRat (x·y)`; with the now-landed antisymmetry
//! `NNReal.le_antisymm`, the equality follows by squeezing both ways through the
//! square-reflects-order keystone `NNReal.le_of_sq_le_sq`. This is the
//! antisymmetry step the NOTE in `algebra_nnreal_sqrt_gen_mul.rs` deferred.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.sqrtGen_mul :`
//!     `∀ (x y sx rx sy ry sxy rxy : Rat)`
//!     `  (hx:0≤x)(hy:0≤y)`
//!     `  (hsx:0≤sx)(hrx:0≤rx)(hrx1:rx<1)(heqx:x=(sx·sx)·rx)`
//!     `  (hsy:0≤sy)(hry:0≤ry)(hry1:ry<1)(heqy:y=(sy·sy)·ry)`
//!     `  (hsxy:0≤sxy)(hrxy:0≤rxy)(hrxy1:rxy<1)(heqxy:(x·y)=(sxy·sxy)·rxy),`
//!     `  @Eq NNReal (NNReal.sqrtGen sxy rxy hsxy)`
//!     `             (NNReal.mul (NNReal.sqrtGen sx rx hsx)(NNReal.sqrtGen sy ry hsy))`.
//!
//! i.e. `√(x·y) = √x·√y` (with the scaling witnesses the archimedean reduction
//! supplies for each of `x`, `y`, `x·y`).
//!
//! # Proof
//!
//! Let `Q := sqrtGen sxy rxy` (a square root of `x·y`) and `P := √x·√y`. By the
//! square keystone, `Q·Q = ofRat (x·y)` (`sqrtGen_sq_at (x·y) sxy rxy … heqxy`)
//! and `P·P = ofRat (x·y)` (`sqrtGen_mul_sq x y sx rx sy ry … heqx heqy`).
//! Hence `Q·Q = P·P` (`trans` + `symm`). Transporting that equation into the
//! reflexive `NNReal.le (Q·Q)(Q·Q)` gives both `Q·Q ≤ P·P` and `P·P ≤ Q·Q`, so
//! `NNReal.le_of_sq_le_sq` yields `Q ≤ P` and `P ≤ Q`, and `NNReal.le_antisymm`
//! closes `Q = P`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, closure foundational-only
//! (the only quotient-level step rides `NNReal.le_antisymm`, itself ⊆
//! {Quot.sound}). NO `sorry` / `add_decl_unchecked` / `add_decl_structural` /
//! `Real` / `Rat.dist`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for full sqrt multiplicativity.
struct MulEqConsts {
    nnreal: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul_nonneg: Expr,
    nnreal_mul: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt_gen: Expr,
    nnreal_sqrt_gen_sq_at: Expr,
    nnreal_sqrt_gen_mul_sq: Expr,
    nnreal_le_of_sq_le_sq: Expr,
    nnreal_le_antisymm: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
}

impl MulEqConsts {
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
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt_gen: k("NNReal.sqrtGen"),
            nnreal_sqrt_gen_sq_at: k("NNReal.sqrtGen_sq_at"),
            nnreal_sqrt_gen_mul_sq: k("NNReal.sqrtGen_mul_sq"),
            nnreal_le_of_sq_le_sq: k("NNReal.le_of_sq_le_sq"),
            nnreal_le_antisymm: k("NNReal.le_antisymm"),
            eq1: kl("Eq"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
        }
    }

    // ── Rat ──
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

    // ── NNReal ──
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
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
    /// `sqrtGen_mul_sq x y sx rx sy ry hx hy hsx hrx hrx1 heqx hsy hry hry1 heqy :
    ///   mul (mul A B)(mul A B) = ofRat (x·y) h`.
    fn sqrt_gen_mul_sq(&self, args: &[Expr; 16]) -> Expr {
        Expr::apps(self.nnreal_sqrt_gen_mul_sq.clone(), args.clone())
    }
    /// `le_of_sq_le_sq a b (mul a a ≤ mul b b) : NNReal.le a b`.
    fn le_of_sq_le_sq(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_sq_le_sq.clone(),
            [a.clone(), b.clone(), h],
        )
    }
    /// `le_antisymm a b (a≤b)(b≤a) : a = b`.
    fn le_antisymm(&self, a: &Expr, b: &Expr, hab: Expr, hba: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_antisymm.clone(),
            [a.clone(), b.clone(), hab, hba],
        )
    }

    // ── Eq.{1} over NNReal ──
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
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
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
}

impl Environment {
    /// Register `NNReal.sqrtGen_mul` (full multiplicativity `√(x·y)=√x·√y`).
    /// Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_sqrt_gen_mul_eq(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_gen()?; // sqrtGen, sqrtGen_sq_at
        self.init_algebra_nnreal_sqrt_gen_mul()?; // sqrtGen_mul_sq
        self.init_algebra_nnreal_reverse_square_sq()?; // NNReal.le_of_sq_le_sq
        self.init_algebra_nnreal_le_antisymm()?; // NNReal.le_antisymm
        self.init_algebra_nnreal_pow43_cubed()?; // Rat.mul_nonneg
        self.init_eq()?;

        let c = MulEqConsts::new();
        self.register_sqrt_gen_mul_eq(&c)?;
        Ok(())
    }

    fn register_sqrt_gen_mul_eq(&mut self, c: &MulEqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtGen_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_mul_eq_ty(c);
        let value = build_mul_eq_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// All 22 binders, in order, shared by the type and value builders. Returns the
/// fresh ids + locals via a closure-driven telescope to avoid duplicating the
/// long binder list.
struct Telescope {
    x: Expr,
    y: Expr,
    sx: Expr,
    rx: Expr,
    sy: Expr,
    ry: Expr,
    sxy: Expr,
    rxy: Expr,
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
    hsxy: Expr,
    hrxy: Expr,
    hrxy1: Expr,
    heqxy: Expr,
    // ids, in binder order (outermost first).
    ids: Vec<(FVarId, Expr)>,
}

/// Build the 22-binder telescope into `b`, returning all locals + a record of
/// `(id, ty)` in binder order for the final wrap.
fn telescope(c: &MulEqConsts, b: &mut EnvDeclBuilder) -> Telescope {
    let mut ids: Vec<(FVarId, Expr)> = Vec::new();
    let rat_binder = |b: &mut EnvDeclBuilder, ids: &mut Vec<(FVarId, Expr)>| {
        let (id, v) = b.fresh_local(c.rat.clone());
        ids.push((id, c.rat.clone()));
        v
    };
    let x = rat_binder(b, &mut ids);
    let y = rat_binder(b, &mut ids);
    let sx = rat_binder(b, &mut ids);
    let rx = rat_binder(b, &mut ids);
    let sy = rat_binder(b, &mut ids);
    let ry = rat_binder(b, &mut ids);
    let sxy = rat_binder(b, &mut ids);
    let rxy = rat_binder(b, &mut ids);

    let hyp_binder = |b: &mut EnvDeclBuilder, ids: &mut Vec<(FVarId, Expr)>, ty: Expr| {
        let (id, v) = b.fresh_local(ty.clone());
        ids.push((id, ty));
        v
    };
    let hx = hyp_binder(b, &mut ids, c.nonneg(x.clone()));
    let hy = hyp_binder(b, &mut ids, c.nonneg(y.clone()));
    let hsx = hyp_binder(b, &mut ids, c.nonneg(sx.clone()));
    let hrx = hyp_binder(b, &mut ids, c.nonneg(rx.clone()));
    let hrx1 = hyp_binder(b, &mut ids, c.rlt(rx.clone(), c.rat_one.clone()));
    let heqx = hyp_binder(
        b,
        &mut ids,
        Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), c.ss_r(&sx, &rx)]),
    );
    let hsy = hyp_binder(b, &mut ids, c.nonneg(sy.clone()));
    let hry = hyp_binder(b, &mut ids, c.nonneg(ry.clone()));
    let hry1 = hyp_binder(b, &mut ids, c.rlt(ry.clone(), c.rat_one.clone()));
    let heqy = hyp_binder(
        b,
        &mut ids,
        Expr::apps(c.eq1.clone(), [c.rat.clone(), y.clone(), c.ss_r(&sy, &ry)]),
    );
    let hsxy = hyp_binder(b, &mut ids, c.nonneg(sxy.clone()));
    let hrxy = hyp_binder(b, &mut ids, c.nonneg(rxy.clone()));
    let hrxy1 = hyp_binder(b, &mut ids, c.rlt(rxy.clone(), c.rat_one.clone()));
    let xy = c.rmul(x.clone(), y.clone());
    let heqxy = hyp_binder(
        b,
        &mut ids,
        Expr::apps(c.eq1.clone(), [c.rat.clone(), xy, c.ss_r(&sxy, &rxy)]),
    );

    Telescope {
        x,
        y,
        sx,
        rx,
        sy,
        ry,
        sxy,
        rxy,
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
        hsxy,
        hrxy,
        hrxy1,
        heqxy,
        ids,
    }
}

/// The conclusion `@Eq NNReal Q P` where `Q := sqrtGen sxy rxy`, `P := √x·√y`.
fn conclusion(c: &MulEqConsts, t: &Telescope) -> Expr {
    let big_q = c.sqrt_gen(&t.sxy, &t.rxy, &t.hsxy);
    let a = c.sqrt_gen(&t.sx, &t.rx, &t.hsx);
    let bb = c.sqrt_gen(&t.sy, &t.ry, &t.hsy);
    let big_p = c.nnmul(&a, &bb);
    c.eq_nn(&big_q, &big_p)
}

fn build_mul_eq_ty(c: &MulEqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let t = telescope(c, &mut b);
    let concl = conclusion(c, &t);
    let mut e = concl;
    for (id, ty) in t.ids.iter().rev() {
        e = b.mk_pi(*id, BinderInfo::Default, ty.clone(), e);
    }
    b.finish(e)
}

fn build_mul_eq_value(c: &MulEqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let t = telescope(c, &mut b);

    let big_q = c.sqrt_gen(&t.sxy, &t.rxy, &t.hsxy);
    let a = c.sqrt_gen(&t.sx, &t.rx, &t.hsx);
    let bb = c.sqrt_gen(&t.sy, &t.ry, &t.hsy);
    let big_p = c.nnmul(&a, &bb);

    let xy = c.rmul(t.x.clone(), t.y.clone());
    let h_xy = c.rat_mul_nonneg(&t.x, &t.y, &t.hx, &t.hy);
    let of_xy = c.ofrat(&xy, &h_xy);

    let qq = c.nnsq(&big_q);
    let pp = c.nnsq(&big_p);

    // sq_q : Q·Q = ofRat(x·y).
    let sq_q = c.sqrt_gen_sq_at(
        &xy, &t.sxy, &t.rxy, &h_xy, &t.hsxy, &t.hrxy, &t.hrxy1, &t.heqxy,
    );
    // sq_p : (√x·√y)·(√x·√y) = ofRat(x·y).
    let mul_sq_args: [Expr; 16] = [
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
    ];
    let sq_p = c.sqrt_gen_mul_sq(&mul_sq_args);

    // qq_eq_pp : Q·Q = P·P   (trans sq_q (symm sq_p)).
    let ofxy_eq_pp = c.symm_nn(&pp, &of_xy, sq_p); // ofRat(x·y) = P·P
    let qq_eq_pp = c.trans_nn(&qq, &of_xy, &pp, sq_q, ofxy_eq_pp); // Q·Q = P·P
    let pp_eq_qq = c.symm_nn(&qq, &pp, qq_eq_pp.clone()); // P·P = Q·Q

    // le_qq_pp : NNReal.le (Q·Q)(P·P)   — subst (Q·Q = P·P) into le (Q·Q)(Q·Q).
    let refl_le_qq = {
        // NNReal.le.refl (Q·Q) : le (Q·Q)(Q·Q).
        let refl = Expr::const_(Name::from_string("NNReal.le.refl"), vec![]);
        Expr::app(refl, qq.clone())
    };
    // rewrite RHS Q·Q → P·P : motive fun t => le (Q·Q) t.
    let motive_r = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&qq, &s);
        m.finish_child(m.mk_lam(s_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let le_qq_pp = c.subst_nn(motive_r, &qq, &pp, qq_eq_pp.clone(), refl_le_qq); // le (Q·Q)(P·P)

    // le_pp_qq : NNReal.le (P·P)(Q·Q)   — subst (P·P = Q·Q) into le (P·P)(P·P).
    let refl_le_pp = {
        let refl = Expr::const_(Name::from_string("NNReal.le.refl"), vec![]);
        Expr::app(refl, pp.clone())
    };
    let motive_r2 = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&pp, &s);
        m.finish_child(m.mk_lam(s_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let le_pp_qq = c.subst_nn(motive_r2, &pp, &qq, pp_eq_qq, refl_le_pp); // le (P·P)(Q·Q)

    // Q ≤ P : le_of_sq_le_sq Q P (le (Q·Q)(P·P)).
    let q_le_p = c.le_of_sq_le_sq(&big_q, &big_p, le_qq_pp);
    // P ≤ Q : le_of_sq_le_sq P Q (le (P·P)(Q·Q)).
    let p_le_q = c.le_of_sq_le_sq(&big_p, &big_q, le_pp_qq);

    // Q = P : le_antisymm Q P (Q≤P)(P≤Q).
    let proof = c.le_antisymm(&big_q, &big_p, q_le_p, p_le_q);

    let mut e = proof;
    for (id, ty) in t.ids.iter().rev() {
        e = b.mk_lam(*id, BinderInfo::Default, ty.clone(), e);
    }
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.sqrtGen_mul"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_gen_mul_eq()
            .expect("init_algebra_nnreal_sqrt_gen_mul_eq");
        env.init_algebra_nnreal_sqrt_gen_mul_eq()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_gen_mul_eq_kernel_check() {
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
    fn test_sqrt_gen_mul_eq_constructive_empty_closure() {
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
