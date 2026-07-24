// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner / noise campaign — `BoolAnalysis.noiseFn_add`: the ADDITIVITY
//! (operator linearity) of the un-normalized noise operator `noiseFn`.
//!
//! # Why this module exists (L7 of the sqrt-free dual route)
//!
//! The `(4/3,4)` dual-HC tensorization (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`) splits the last coordinate
//! into the even/odd legs `gPart = fL+fH`, `hPart = fL−fH`, and needs the noise
//! operator legs `G ± H = noiseFn(gPart) ± noiseFn(hPart)` to factor through
//! `2·noiseFn{fL,fH}`. The enabling fact is that `noiseFn` is ADDITIVE in its
//! function argument `F`:
//!
//! ```text
//!   BoolAnalysis.noiseFn_add : ∀ (ρ : Rat)(n : Nat)(u v : HCPoint n → Rat)(jx),
//!     noiseFn ρ n (fun x => u x + v x) jx
//!       = noiseFn ρ n u jx + noiseFn ρ n v jx
//! ```
//!
//! # Why it is genuinely buildable here (landed deps only)
//!
//! `noiseFn ρ n F jx ≡ Fin.sum (2^n) (fun jy => F(hcDecode n jy)·noiseDensityW …)`
//! is an AFFINE/ADDITIVE finSum kernel: each summand is `F(y)·dens` — LINEAR in
//! `F`. So with `F = u+v` the summand splits by RIGHT-distributivity
//! `(u(y)+v(y))·dens = u(y)·dens + v(y)·dens` (the landed `Rat.right_distrib`),
//! and the whole `Fin.sum` distributes over `+` by the landed `Fin.sum_add`. The
//! pointwise split is lifted under the sum by the landed `Fin.sum_congr`. No
//! `NNReal`, no new carrier, no axiom — only the landed Rat `Fin.sum` engine.
//!
//! Proof (at fixed `ρ n u v jx`, with `x := hcDecode n jx`, `dens jy :=
//! noiseDensityW ρ n x (hcDecode n jy)`):
//!   * `summand_uv jy := (u(decode jy)+v(decode jy))·dens jy`  (≡ noiseFn(u+v) jx)
//!   * `summand_u  jy := u(decode jy)·dens jy`                  (≡ summand of noiseFn u)
//!   * `summand_v  jy := v(decode jy)·dens jy`
//!   1. `Fin.sum_congr (2^n) summand_uv (fun jy => summand_u jy + summand_v jy)
//!         (fun jy => Rat.right_distrib (u(decode jy)) (v(decode jy)) (dens jy))`
//!      : `Fin.sum (2^n) summand_uv = Fin.sum (2^n) (fun jy => summand_u + summand_v)`.
//!   2. `Fin.sum_add (2^n) summand_u summand_v`
//!      : `Fin.sum (2^n) (fun jy => summand_u + summand_v)
//!          = Fin.sum (2^n) summand_u + Fin.sum (2^n) summand_v`
//!      ≡ `noiseFn ρ n u jx + noiseFn ρ n v jx`.
//!   * `Eq.trans` of (1),(2). The LHS `Fin.sum (2^n) summand_uv` is defeq to
//!     `noiseFn ρ n (fun x => u x + v x) jx` (δ on noiseFn + β), so the whole
//!     conclusion holds on the nose.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `noiseFn_add`.
struct NoiseFnAddConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nat_pow: Expr,
    two: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_right_distrib: Expr,
    fin_sum: Expr,
    fin_sum_add: Expr,
    fin_sum_congr: Expr,
    noise_fn: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    noise_density: Expr,
    eq1: Expr,
    eq_trans1: Expr,
}

impl NoiseFnAddConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat_zero = k("Nat.zero");
        let nat_succ = k("Nat.succ");
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            fin: k("Fin"),
            nat_pow: k("Nat.pow"),
            two: Expr::app(nat_succ, nat_one),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_right_distrib: k("Rat.right_distrib"),
            fin_sum: k("Fin.sum"),
            fin_sum_add: k("Fin.sum_add"),
            fin_sum_congr: k("Fin.sum_congr"),
            noise_fn: k("BoolAnalysis.noiseFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn fin_pow(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), self.pow2(n))
    }
    /// `HCPoint n → Rat`.
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()])
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a.clone(), b.clone()])
    }
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `Fin.sum (2^n) f`.
    fn sum(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [self.pow2(n), f.clone()])
    }
    /// `noiseFn ρ n F jx`.
    fn noise_at(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), n.clone(), f.clone(), jx.clone()],
        )
    }
    fn eq_rat(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a.clone(), b.clone()])
    }
    fn trans(&self, a: &Expr, b: &Expr, c: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.rat.clone(), a.clone(), b.clone(), c.clone(), h1, h2],
        )
    }

    /// The pointwise-added function `fun x : HCPoint n => u x + v x`.
    fn uv_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr, v: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = b.fresh_local(self.hcpoint_of(n));
        let body = self.add(&Expr::app(u.clone(), x.clone()), &Expr::app(v.clone(), x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, self.hcpoint_of(n), body))
    }

    /// `fun jy => F(decode jy)·dens(jx,jy)` — the noiseFn summand for `F`.
    fn summand_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (jy_id, jy) = b.fresh_local(self.fin_pow(n));
        let y = self.decode(n, &jy);
        let body = self.mul(
            &Expr::app(f.clone(), y.clone()),
            &self.density(rho, n, x, &y),
        );
        b.finish_child(b.mk_lam(jy_id, BinderInfo::Default, self.fin_pow(n), body))
    }

    /// `fun jy => (summand_u jy) + (summand_v jy)` (the split summand, the shape
    /// `Fin.sum_add` consumes literally).
    fn split_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        u: &Expr,
        v: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (jy_id, jy) = b.fresh_local(self.fin_pow(n));
        let y = self.decode(n, &jy);
        let dens = self.density(rho, n, x, &y);
        let su = self.mul(&Expr::app(u.clone(), y.clone()), &dens);
        let sv = self.mul(&Expr::app(v.clone(), y.clone()), &dens);
        let body = self.add(&su, &sv);
        b.finish_child(b.mk_lam(jy_id, BinderInfo::Default, self.fin_pow(n), body))
    }

    /// The pointwise hypothesis `fun jy => Rat.right_distrib (u(decode jy))
    /// (v(decode jy)) (dens jy) : summand_uv jy = (summand_u + summand_v) jy`.
    fn pointwise_distrib(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        u: &Expr,
        v: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (jy_id, jy) = b.fresh_local(self.fin_pow(n));
        let y = self.decode(n, &jy);
        let dens = self.density(rho, n, x, &y);
        let uy = Expr::app(u.clone(), y.clone());
        let vy = Expr::app(v.clone(), y.clone());
        // Rat.right_distrib (u y) (v y) dens : (u y + v y)·dens = u y·dens + v y·dens
        let body = Expr::apps(self.rat_right_distrib.clone(), [uy, vy, dens]);
        b.finish_child(b.mk_lam(jy_id, BinderInfo::Default, self.fin_pow(n), body))
    }
}

impl Environment {
    /// Register `BoolAnalysis.noiseFn_add`. Idempotent; foundational-only closure.
    pub fn register_noise_fn_add(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseFn_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.add, Rat.mul
        self.init_rat_field_inst()?; // Rat.right_distrib
        self.init_fin_sum()?; // Fin.sum, Fin.sum_add, Fin.sum_congr
        self.register_noise_fn()?; // BoolAnalysis.noiseFn, hcDecode, noiseDensityW
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = NoiseFnAddConsts::new();
        let (ty, value) = build_noise_fn_add(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `noiseFn_add`'s type + proof.
fn build_noise_fn_add(c: &NoiseFnAddConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (u_id, u) = b.fresh_local(c.f_type(&n));
        let (v_id, v) = b.fresh_local(c.f_type(&n));
        let (jx_id, jx) = b.fresh_local(c.fin_pow(&n));

        let uv = c.uv_fn(&b, &n, &u, &v);
        let lhs = c.noise_at(&rho, &n, &uv, &jx);
        let rhs = c.add(
            &c.noise_at(&rho, &n, &u, &jx),
            &c.noise_at(&rho, &n, &v, &jx),
        );
        let concl = c.eq_rat(&lhs, &rhs);

        let e = b.mk_pi(jx_id, BinderInfo::Default, c.fin_pow(&n), concl);
        let e = b.mk_pi(v_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_pi(u_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (u_id, u) = b.fresh_local(c.f_type(&n));
        let (v_id, v) = b.fresh_local(c.f_type(&n));
        let (jx_id, jx) = b.fresh_local(c.fin_pow(&n));

        let x = c.decode(&n, &jx);
        let summand_uv = {
            // summand for F = u+v: fun jy => (u(decode jy)+v(decode jy))·dens
            let uv = c.uv_fn(&b, &n, &u, &v);
            c.summand_fn(&b, &rho, &n, &uv, &x)
        };
        let summand_u = c.summand_fn(&b, &rho, &n, &u, &x);
        let summand_v = c.summand_fn(&b, &rho, &n, &v, &x);
        let split = c.split_fn(&b, &rho, &n, &u, &v, &x);

        let sum_uv = c.sum(&n, &summand_uv); // ≡ noiseFn (u+v) jx
        let sum_split = c.sum(&n, &split);
        let sum_u = c.sum(&n, &summand_u); // ≡ noiseFn u jx
        let sum_v = c.sum(&n, &summand_v); // ≡ noiseFn v jx
        let sum_u_plus_v = c.add(&sum_u, &sum_v);

        // step1 : sum_uv = sum_split  (Fin.sum_congr + pointwise right_distrib)
        let h_pw = c.pointwise_distrib(&b, &rho, &n, &u, &v, &x);
        let step1 = Expr::apps(
            c.fin_sum_congr.clone(),
            [c.pow2(&n), summand_uv.clone(), split.clone(), h_pw],
        );

        // step2 : sum_split = sum_u + sum_v  (Fin.sum_add (2^n) summand_u summand_v)
        let step2 = Expr::apps(
            c.fin_sum_add.clone(),
            [c.pow2(&n), summand_u.clone(), summand_v.clone()],
        );

        let proof = c.trans(&sum_uv, &sum_split, &sum_u_plus_v, step1, step2);

        let e = b.mk_lam(jx_id, BinderInfo::Default, c.fin_pow(&n), proof);
        let e = b.mk_lam(v_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_lam(u_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_noise_fn_add().expect("register_noise_fn_add");
        env.register_noise_fn_add().expect("idempotent");
        env
    }

    #[test]
    fn test_noise_fn_add_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("BoolAnalysis.noiseFn_add");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("BoolAnalysis.noiseFn_add must kernel-check: {e:?}"));
    }

    #[test]
    fn test_noise_fn_add_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.noiseFn_add");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
