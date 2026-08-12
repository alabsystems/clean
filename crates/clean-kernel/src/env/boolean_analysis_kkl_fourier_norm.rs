// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — the **Fourier-normalization bridge** (R3b, the residual): the
//! un-normalized spectral coefficient `A_S` equals `2^n` times the
//! `Expect`-normalized Fourier coefficient `f̂(S)`.
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.subsetSum_pm_eq_pow2_fourier :
//!   ∀ (n : Nat) (f : BoolFn n) (S : HCPoint n),
//!     @Eq Rat
//!       (subsetSum n (fun x => Rat.mul (pm (f x)) (chi n S x)))      -- A_S(pm∘f)
//!       (Rat.mul (Rat.powNat 2 n) (FourierCoefficient n f S))        -- 2^n · f̂(S)
//! ```
//!
//! i.e. `A_S = 2^n · f̂(S)`, where the LHS `A_S := subsetSum n (fun x => pm(f x)·χ_S x)`
//! is the un-normalized Fourier coefficient carrier used by the level-restriction
//! bridge (`lowband_le_noise_sum`'s `A_S` at `a := pm∘f`), and the RHS
//! `f̂(S) := FourierCoefficient n f S` is the `Expect`-normalized coefficient used
//! by the double-count bridge (`lowband_double_count_le`). This is the precise
//! `2^n`-bookkeeping that reconciles the two carriers — the same family of
//! cancellation already closed for the support-count identity
//! (`dualhc_m_pow2_eq_4pow_influence`).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! By δ-unfolding the reducible Definitions:
//!
//! ```text
//!   f̂(S) := FourierCoefficient n f S
//!        ≡ Expect n (fun x => pm(f x)·χ_S x)                      (FourierCoefficient δ)
//!        ≡ Rat.div (subsetSum n (fun x => pm(f x)·χ_S x)) L       (Expect δ; subsetSum δ matches)
//!        ≡ Rat.mul Z (Rat.inv L)                                  (Rat.div δ)
//! ```
//!
//! where `Z := subsetSum n (fun x => pm(f x)·χ_S x)`, `L := mk(ofNat (Nat.pow 2 n)) 1`
//! (the `Expect` denominator), and `P := Rat.powNat 2 n`. So `2^n·f̂(S) ≡ P·(Z·inv L)`
//! DEFINITIONALLY. We then ring-cancel `P·(Z·inv L) = Z`:
//!
//! ```text
//!   P·(Z·inv L) →[congr P·_ (congr Z·_ (inv L = inv P))]  P·(Z·inv P)   (inv P = inv L via P = L)
//!               →[reassoc c·(b·d)=b·(c·d), c:=P b:=Z d:=inv P]  Z·(P·inv P)
//!               →[congr Z·_ (P·inv P = 1)]  Z·1                          (mul_inv_cancel; P>0)
//!               →[mul_one Z]  Z                                          = LHS
//! ```
//!
//! `symm` of this chain is `Z = P·(Z·inv L)`, which the kernel accepts against the
//! stated `Z = P·f̂(S)` because `P·(Z·inv L)` is def-eq to `P·f̂(S)`. The `P = L`
//! bridge is the landed `Rat.powNat_two_eq_natCast`; `P > 0` is
//! `Rat.powNat_pos 2 n (0<2)`; `P·inv P = 1` is `Rat.mul_inv_cancel`. Every leaf
//! (`Rat.powNat_two_eq_natCast`, `Rat.powNat_pos`, `Rat.ne_zero_of_pos`,
//! `Rat.mul_inv_cancel`, `Rat.mul_assoc`/`mul_comm`/`mul_one`, `congrArg`, `Eq.*`)
//! is `Constructive` with empty admitted-axiom closure, so this bridge is too. No
//! axiom is added or removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the Fourier-normalization bridge. All carrier spellings
/// (`subsetSum`, `chi`, `pm`, `FourierCoefficient`, `powNat 2`,
/// `mk(ofNat (Nat.pow 2 n)) 1`) byte-match the consumed Definitions/lemmas, so
/// every leaf instance is def-eq.
struct FourierNormConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    chi: Expr,
    pm: Expr,
    subset_sum: Expr,
    fourier: Expr,
    // landed leaves.
    pow_two_natcast: Expr,
    mul_inv_cancel: Expr,
    ne_zero_of_pos: Expr,
    pow_pos: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    mul_one: Expr,
    // Eq.{1}.
    eq1: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr_arg1: Expr,
}

impl FourierNormConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            chi: k("BoolAnalysis.chi"),
            pm: k("BoolAnalysis.pm"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            pow_two_natcast: k("Rat.powNat_two_eq_natCast"),
            mul_inv_cancel: k("Rat.mul_inv_cancel"),
            ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            pow_pos: k("Rat.powNat_pos"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            mul_one: k("Rat.mul_one"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            #[cfg(test)]
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
    fn nat_two(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_one())
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mk.clone(), [n, d])
    }
    /// `Rat.mk (Int.ofNat k) 1` — the rational natCast literal.
    fn natcast(&self, k: Expr) -> Expr {
        self.mk(self.of_nat(k), self.nat_one())
    }
    /// `(2 : Rat) := mk(ofNat 2) 1` — the `powNat` base (byte-match `MinflConsts`).
    fn rat_two(&self) -> Expr {
        self.natcast(self.nat_two())
    }
    /// `Nat.pow 2 n`.
    fn nat_pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_two(), n.clone()])
    }
    /// `L := mk(ofNat (Nat.pow 2 n)) 1` — the `Expect` denominator literal.
    fn lit_pow2(&self, n: &Expr) -> Expr {
        self.natcast(self.nat_pow2(n))
    }
    /// `P := Rat.powNat 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.rat_two(), n.clone()])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
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
    /// (BYTE-IDENTICAL to `FourierCoefficient`'s inner sum and to the LR bridge's
    /// `A_S` at `a := pm∘f`).
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
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one_at(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn congr_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `congrArg Rat.inv h : inv a = inv b`.
    fn congr_inv(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg1.clone(),
            [
                self.rat.clone(),
                self.rat.clone(),
                a,
                b,
                self.rat_inv.clone(),
                h,
            ],
        )
    }

    // ── landed-leaf applications ──────────────────────────────────────────────
    /// `Rat.powNat_two_eq_natCast n : Rat.powNat 2 n = mk(ofNat (Nat.pow 2 n)) 1`.
    fn pow_two_natcast_at(&self, n: &Expr) -> Expr {
        Expr::app(self.pow_two_natcast.clone(), n.clone())
    }
    /// `Rat.mul_inv_cancel a h : a·inv a = 1`.
    fn mul_inv_cancel_at(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.ne_zero_of_pos a h : a = 0 → False`.
    fn ne_at(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.ne_zero_of_pos.clone(), [a, h])
    }
    /// `0 < (2 : Rat)` := `@Int.NonNeg.mk 1` (byte-match `MinflConsts::two_pos`).
    fn two_pos(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_one(),
        )
    }
    /// `0 < Rat.powNat 2 n` := `Rat.powNat_pos 2 n (0<2)`.
    fn pow_two_pos(&self, n: &Expr) -> Expr {
        Expr::apps(
            self.pow_pos.clone(),
            [self.rat_two(), n.clone(), self.two_pos()],
        )
    }
    /// `Rat.one`.
    fn one(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.one"), vec![])
    }
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_pm_eq_pow2_fourier` — the
    /// Fourier-normalization bridge `A_S = 2^n·f̂(S)`
    /// (`subsetSum n (fun x => pm(f x)·χ_S x) = (powNat 2 n)·FourierCoefficient n f S`).
    /// Reconciles the un-normalized `A_S` carrier (level-restriction bridge) with
    /// the `Expect`-normalized `f̂(S)` carrier (double-count bridge). See module
    /// docs. Kernel-checked, `Constructive`, empty admitted-axiom closure.
    /// Idempotent; no axiom added/removed.
    pub fn register_subset_sum_pm_eq_pow2_fourier(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_pm_eq_pow2_fourier");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, chi, BoolFn, HCPoint, FourierCoefficient, Expect
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?; // subsetSum (matches Expect's inner Fin.sum)
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_mul_base()?; // Rat.powNat_pos (positivity)
        self.register_rat_pow_nat_two_eq_natcast()?; // P = L bridge
        self.init_algebra_rat_inv_dyadic()?; // mul_inv_cancel, ne_zero_of_pos
        {
            // Rat.mul_one / Rat.mul_comm / Rat.mul_assoc.
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = FourierNormConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: bridge_type(&c),
            value: bridge_value(&c),
        })
    }
}

include!("boolean_analysis_kkl_fourier_norm_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_pm_eq_pow2_fourier()
            .expect("register_subset_sum_pm_eq_pow2_fourier");
        env
    }

    #[test]
    fn test_subset_sum_pm_eq_pow2_fourier_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.subsetSum_pm_eq_pow2_fourier");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("Fourier-norm bridge proof must check: {e:?}"));
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
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_pm_eq_pow2_fourier().expect("first");
        env.register_subset_sum_pm_eq_pow2_fourier()
            .expect("idempotent");
    }
}
