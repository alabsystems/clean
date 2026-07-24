// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **rung 2 squared bricks** toward retiring `kkl_inequality`.
//!
//! This module owns standalone, kernel-checked, `Constructive`,
//! empty-admitted-axiom-closure bricks that connect the un-normalized
//! coefficient carrier `A_S` (level-restriction / double-count bands) to the
//! `Expect`-normalized Fourier carrier `f̂(S)`, all `2^n`/`4^n` bookkeeping
//! tracked EXACTLY:
//!
//! 1. [`Environment::register_subset_sum_pm_sq_eq_pow4_fourier`] — **step 1**
//!    (`step-1-squared`): the SQUARE of the Fourier-normalization bridge,
//!    ```text
//!    A_S(pm∘f)² = 4^n · f̂(S)²
//!    ```
//!    i.e. `(subsetSum n (fun x => pm(f x)·χ_S x))² = (powNat 4 n)·(f̂(S)·f̂(S))`.
//!
//! This is a `9^k`/`4^n`-bookkeeping brick that lets rung 2 reconcile the
//! un-normalized `A_S` carrier (level-restriction bridge `lowband_le_noise_sum`)
//! with the `Expect`-normalized `f̂(S)` carrier (double-count bridge
//! `lowband_double_count_le`) under R3a's `4^n·W_norm` normalization.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! ### step 1 — `subsetSum_pm_sq_eq_pow4_fourier`
//!
//! Let `Z := A_S = subsetSum n (fun x => pm(f x)·χ_S x)`, `F := f̂(S)`,
//! `P := powNat 2 n`. The landed bridge
//! `subsetSum_pm_eq_pow2_fourier : Z = P·F`. Then
//! ```text
//!   Z·Z = (P·F)·(P·F)       congrArg (·²) bridge
//!       = (P·P)·(F·F)        mul_mul_mul_comm P F P F
//!       = (4^n)·(F·F)        congrArg (·(F·F)) (P·P = 4^n)
//! ```
//! where `P·P = 4^n` is `symm (powNat_mul_base 2 2 n) : 2^n·2^n = (2·2)^n`
//! chained with `congrArg (fun b => powNat b n) (refl : 2·2 = 4) : (2·2)^n = 4^n`.
//! (`2·2 = 4` holds by `Eq.refl` — the literal `Rat.mul (mk 2 1)(mk 2 1)`
//! whnf-reduces to `mk 4 1`; the same `Eq.refl` already used in
//! `deriv_coeff_sq_eq`.)
//!
//! Every leaf is `Constructive` with empty admitted-axiom closure, so the brick
//! is too. No axiom is added or removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the squared / mask-collapse bricks. Carrier spellings
/// (`subsetSum`, `chi`, `pm`, `FourierCoefficient`, `powNat`, `setSize`,
/// `setSizeNat`, `ind`, the band masks) byte-match the consumed Definitions/lemmas.
struct SquaredConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    chi: Expr,
    pm: Expr,
    subset_sum: Expr,
    fourier: Expr,
    // landed leaves.
    pow_mul_base: Expr,
    mul_mul_mul_comm: Expr,
    // Eq.{1}.
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr_arg1: Expr,
}

impl SquaredConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            chi: k("BoolAnalysis.chi"),
            pm: k("BoolAnalysis.pm"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            pow_mul_base: k("Rat.powNat_mul_base"),
            mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── Nat / Int / Rat constructors ──────────────────────────────────────────
    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mk.clone(), [n, d])
    }
    /// `Rat.mk (Int.ofNat v) 1` — the rational natCast literal.
    fn rat_lit(&self, v: u64) -> Expr {
        self.mk(self.of_nat(self.nat_lit(v)), self.nat_one())
    }
    /// `(2 : Rat) := mk(ofNat 2) 1` (byte-match `FourierNormConsts`/`ComposeConsts`).
    fn rat_two(&self) -> Expr {
        self.rat_lit(2)
    }
    /// `(4 : Rat) := mk(ofNat 4) 1` (byte-match the `4^n` carrier base).
    fn rat_four(&self) -> Expr {
        self.rat_lit(4)
    }
    /// `Rat.powNat b k`.
    fn pow(&self, b: Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b, k.clone()])
    }
    /// `P := powNat 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        self.pow(self.rat_two(), n)
    }
    /// `4^n := powNat 4 n`.
    fn pow4(&self, n: &Expr) -> Expr {
        self.pow(self.rat_four(), n)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    // ── BoolAnalysis carriers ─────────────────────────────────────────────────
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `Z := subsetSum n (fun x => pm(f x)·χ_S x)` — the un-normalized coefficient
    /// `A_S(pm∘f)` (BYTE-IDENTICAL to the bridge's LHS).
    fn z_sum(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let pm_fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let body = self.mul(pm_fx, self.chi_(n, s, &x));
        let g = d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }

    // ── Eq.{1} plumbing ───────────────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `congrArg (fun z => z·z) h : a·a = b·b`.
    fn congr_sq(&self, parent: &EnvDeclBuilder, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `congrArg (fun z => z·right) h : a·right = b·right`.
    fn congr_r(&self, parent: &EnvDeclBuilder, right: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `congrArg (fun b => powNat b n) h : powNat a n = powNat b n`.
    fn congr_pow_base(&self, parent: &EnvDeclBuilder, n: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.pow(z, n);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `Rat.powNat_mul_base a b k : (a·b)^k = a^k·b^k`.
    fn pow_mul_base_at(&self, a: Expr, b: Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_mul_base.clone(), [a, b, k.clone()])
    }
}

// ───────────────────────── step 1: A_S² = 4^n · f̂² ──────────────────────────

/// `∀ n f S, A_S(pm∘f)² = 4^n · f̂(S)²`.
fn sq_type(c: &SquaredConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let z = c.z_sum(&b, &n, &f, &s); // A_S
    let lhs = c.mul(z.clone(), z); // A_S²
    let fhat = c.fourier_of(&n, &f, &s); // f̂(S)
    let f_sq = c.mul(fhat.clone(), fhat); // f̂²
    let rhs = c.mul(c.pow4(&n), f_sq); // 4^n·f̂²
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `λ n f S => <A_S² = (P·F)² = (P·P)·(F·F) = 4^n·(F·F)>`.
fn sq_value(c: &SquaredConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let z = c.z_sum(&b, &n, &f, &s); // A_S = Z
    let p = c.pow2(&n); // P = 2^n
    let fhat = c.fourier_of(&n, &f, &s); // F = f̂(S)
    let f_sq = c.mul(fhat.clone(), fhat.clone()); // F·F
    let pf = c.mul(p.clone(), fhat.clone()); // P·F

    // bridge : Z = P·F.
    let bridge = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_pm_eq_pow2_fourier"),
            vec![],
        ),
        [n.clone(), f.clone(), s.clone()],
    );

    // s1 : Z·Z = (P·F)·(P·F)   congrArg (·²) bridge.
    let z_sq = c.mul(z.clone(), z.clone());
    let pf_sq = c.mul(pf.clone(), pf.clone());
    let s1 = c.congr_sq(&b, z.clone(), pf.clone(), bridge);

    // s2 : (P·F)·(P·F) = (P·P)·(F·F)   mul_mul_mul_comm P F P F.
    let p_sq = c.mul(p.clone(), p.clone()); // P·P
    let s2 = c.mmmc(p.clone(), fhat.clone(), p.clone(), fhat.clone());
    let mid = c.mul(p_sq.clone(), f_sq.clone()); // (P·P)·(F·F)

    // pp_eq_4 : P·P = 4^n
    //   symm (powNat_mul_base 2 2 n) : 2^n·2^n = (2·2)^n
    //   chained with congrArg (powNat ·) (refl 2·2=4) : (2·2)^n = 4^n.
    let two = c.rat_two();
    let four = c.rat_four();
    let two_two = c.mul(two.clone(), two.clone()); // 2·2
    let pow_two_two = c.pow(two_two.clone(), &n); // (2·2)^n
                                                  // pmb : (2·2)^n = 2^n·2^n.
    let pmb = c.pow_mul_base_at(two.clone(), two.clone(), &n);
    // symm : 2^n·2^n = (2·2)^n.
    let pmb_symm = c.symm_rat(pow_two_two.clone(), p_sq.clone(), pmb);
    // refl 2·2 = 4 (whnf reduction of the literal product).
    let two_two_eq_four = c.refl_rat(four.clone());
    // congr : (2·2)^n = 4^n.
    let pow_base_eq = c.congr_pow_base(&b, &n, two_two.clone(), four.clone(), two_two_eq_four);
    // pp_eq_4 : 2^n·2^n = 4^n.
    let pp_eq_4 = c.trans_rat(
        p_sq.clone(),
        pow_two_two.clone(),
        c.pow4(&n),
        pmb_symm,
        pow_base_eq,
    );

    // s3 : (P·P)·(F·F) = (4^n)·(F·F)   congrArg (·(F·F)) pp_eq_4.
    let rhs = c.mul(c.pow4(&n), f_sq.clone());
    let s3 = c.congr_r(&b, &f_sq, p_sq.clone(), c.pow4(&n), pp_eq_4);

    // chain : Z·Z = (P·F)·(P·F) = (P·P)·(F·F) = 4^n·(F·F).
    let c1 = c.trans_rat(z_sq.clone(), pf_sq.clone(), mid.clone(), s1, s2);
    let proof = c.trans_rat(z_sq, mid, rhs, c1, s3);

    let e = b.mk_lam(s_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_pm_sq_eq_pow4_fourier` — step 1
    /// (`step-1-squared`): the SQUARE of the Fourier-normalization bridge,
    /// `∀ n f S, (subsetSum n (fun x => pm(f x)·χ_S x))² = (powNat 4 n)·(f̂(S)·f̂(S))`,
    /// i.e. `A_S(pm∘f)² = 4^n·f̂(S)²`. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_subset_sum_pm_sq_eq_pow4_fourier(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_pm_sq_eq_pow4_fourier");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, chi, BoolFn, HCPoint, FourierCoefficient
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?; // subsetSum
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_mul_base()?; // Rat.powNat_mul_base
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm
        self.register_subset_sum_pm_eq_pow2_fourier()?; // the bridge A_S = 2^n·f̂

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = SquaredConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sq_type(&c),
            value: sq_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_pm_sq_eq_pow4_fourier_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_pm_sq_eq_pow4_fourier()
            .expect("register_subset_sum_pm_sq_eq_pow4_fourier");
        let nm = Name::from_string("BoolAnalysis.subsetSum_pm_sq_eq_pow4_fourier");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("step-1-squared proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_step1_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_pm_sq_eq_pow4_fourier()
            .expect("first");
        env.register_subset_sum_pm_sq_eq_pow4_fourier()
            .expect("idempotent");
    }
}
