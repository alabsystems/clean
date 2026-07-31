// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — the **support-count identity** that turns the per-coordinate
//! dual-HC's measure hypothesis into a proven leaf, making `dualhc_per_coord`
//! UNCONDITIONAL (modulo `0 ≤ Inf < 1`).
//!
//! ## The three rungs proved here
//!
//! 1. **`Rat.mul_natCast`** — `mk(ofNat a) 1 · mk(ofNat b) 1 = mk(ofNat (a·b)) 1`,
//!    the multiplicative natCast bridge (one `Quot.sound`; the Equiv side is
//!    def-eq because `Int.mul (ofNat a)(ofNat b) ≡ ofNat (Nat.mul a b)` and the
//!    effDenoms reduce to `ofNat 1`). The product analogue of `Rat.add_natCast`.
//!
//! 2. **`Rat.powNat_two_eq_natCast`** —
//!    `Rat.powNat 2 n = Rat.mk (Int.ofNat (Nat.pow 2 n)) 1`, bridging the two
//!    spellings of the rational `2^n`: the `Nat.rec`-based `Rat.powNat` (used by
//!    the `8^n = (2^n)³` bookkeeping) and the literal `Nat.pow`-cast (used by the
//!    `Expect` denominator and the `influence_bridge`). `Nat.rec` on `n`:
//!    base `n=0` is `1 = mk(ofNat 1) 1` (def-eq); step `n+1` chains the powNat /
//!    Nat.pow ι-steps with `mul_natCast` (note `Rat.powNat` multiplies on the
//!    LEFT, `Nat.pow` on the RIGHT, so a `mul_comm` swaps the factor order).
//!
//! 3. **`BoolAnalysis.dualhc_m_pow2_eq_4pow_influence`** —
//!    ```text
//!    ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
//!      Rat.mul m (Rat.powNat 2 n)
//!        = Rat.mul (Rat.mul (Rat.powNat 2 n)(Rat.powNat 2 n)) (Influence n f i)
//!    ```
//!    where `m := subsetSum n (fun x => (D_i f x · D_i f x)·(half·half))` is STEP
//!    2's support measure. This is the support-count identity `m·2^n = (2^n)²·Inf`
//!    (equivalently `m = 2^n·Inf_i`). PROOF, in four steps:
//!    `m = subsetSum n (ind∘disagree)` (`dualhc_step2_m_eq_disagree_mass`);
//!    `Influence n f i ≡ subsetSum n (ind∘disagree) · inv (mk(ofNat (2^n)) 1)`
//!    (def-unfold of `Influence = Expect (ind∘disagree)`,
//!    `Expect g = Rat.div (subsetSum n g)(mk(ofNat (2^n)) 1)`, `Rat.div a b ≡
//!    a·inv b`); `mk(ofNat (2^n)) 1 = Rat.powNat 2 n` (`powNat_two_eq_natCast`,
//!    symm); then `(2^n·2^n)·(m·inv(2^n)) = m·2^n` by `mul_inv_cancel`/ring laws.
//!
//! All leaves are `Constructive` empty-closure Theorems (or `Quot.sound`, a
//! FOUNDATIONAL axiom), so every decl here is `Constructive` with EMPTY
//! admitted-axiom closure. No axiom added or removed; domain count stays 4.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms + smart-constructors for the support-count identity. The `m` /
/// `half` / `D_i f` / `subsetSum` / `Influence` spellings byte-match
/// `dualhc_step2_m_eq_disagree_mass`, `BoolAnalysis.Influence`, and
/// `dualhc_per_coord` so every leaf instance is def-eq.
struct MinflConsts {
    nat: Expr,
    int: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_mul: Expr,
    int_of_nat: Expr,
    #[cfg(test)]
    int_mul_one: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_sub: Expr,
    rat_one: Expr,
    pow_nat: Expr,
    // Raw / Quot machinery.
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    // BoolAnalysis carriers.
    bool_fn: Expr,
    hcpoint: Expr,
    fin: Expr,
    hc_flip: Expr,
    pm: Expr,
    ind: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    subset_sum: Expr,
    influence: Expr,
    // landed leaves.
    m_eq_mass: Expr,
    pow_two_natcast: Expr,
    mul_natcast: Expr,
    mul_inv_cancel: Expr,
    ne_zero_of_pos: Expr,
    pow_pos: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    pow_mul_base: Expr,
    // Eq.{1}.
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr_arg1: Expr,
    nat_rec0: Expr,
}

impl MinflConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            int: k("Int"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_mul: k("Nat.mul"),
            int_of_nat: k("Int.ofNat"),
            #[cfg(test)]
            int_mul_one: k("Int.mul_one"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_sub: k("Rat.sub"),
            rat_one: k("Rat.one"),
            pow_nat: k("Rat.powNat"),
            raw: k("Rat.Raw"),
            raw_mk: k("Rat.Raw.mk"),
            raw_equiv: k("Rat.Raw.Equiv"),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1.clone()]),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            fin: k("Fin"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            bool_beq: k("Bool.beq"),
            bool_not: k("Bool.not"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            influence: k("BoolAnalysis.Influence"),
            m_eq_mass: k("BoolAnalysis.dualhc_step2_m_eq_disagree_mass"),
            pow_two_natcast: k("Rat.powNat_two_eq_natCast"),
            mul_natcast: k("Rat.mul_natCast"),
            mul_inv_cancel: k("Rat.mul_inv_cancel"),
            ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            pow_pos: k("Rat.powNat_pos"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            pow_mul_base: k("Rat.powNat_mul_base"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        }
    }

    // ── Nat constructors ──────────────────────────────────────────────────────
    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn nat_two(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_one())
    }
    #[cfg(test)]
    fn nsucc(&self, k: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), k.clone())
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    fn nat_pow_of(&self, base: Expr, k: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [base, k.clone()])
    }
    /// `k : Nat` as `Nat.succ^k Nat.zero`.
    fn nat_lit(&self, k: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        nat
    }

    // ── Int / Rat constructors ────────────────────────────────────────────────
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
    /// `mk(ofNat k) 1` for a small literal `k` — byte-matches `PerCoordConsts::lit`.
    fn lit(&self, k: usize) -> Expr {
        self.natcast(self.nat_lit(k))
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    /// `Rat.powNat base k`.
    fn pow(&self, base: Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [base, k.clone()])
    }
    /// `(2 : Rat) := Rat.mk (Int.ofNat 2) 1` — the `powNat` base used by
    /// `dualhc_per_coord` (`PerCoordConsts::lit 2`).
    fn rat_two(&self) -> Expr {
        self.natcast(self.nat_two())
    }

    // ── Raw / Quot ────────────────────────────────────────────────────────────
    fn raw_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.raw_mk.clone(), [n, d])
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), l],
        )
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), a, b, h],
        )
    }

    // ── Eq.{1} plumbing ───────────────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn eq_int(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.int.clone(), a, b])
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    fn refl_int(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.int.clone(), a])
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

    // ── BoolAnalysis term shapes (byte-match step2b / Influence) ──────────────
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn flip(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `half := Rat.inv (mk(ofNat 2) 1)` — byte-match `PerCoordConsts::half`
    /// (`Rat.inv Rat.two`, where `Rat.two ≡ mk(ofNat 2) 1` reducibly).
    fn half(&self) -> Expr {
        self.inv(self.rat_two())
    }
    /// `fun x => (D_i f x · D_i f x)·(half·half)` — STEP 2 / `dualhc_per_coord`'s
    /// support-measure integrand. `D_i f x := pm (f x) − pm (f (hcFlip n x i))`.
    fn m_integrand(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, &x, i));
        let g = self.sub(
            Expr::app(self.pm.clone(), fx),
            Expr::app(self.pm.clone(), fflip),
        );
        let half = self.half();
        let body = self.mul(self.mul(g.clone(), g), self.mul(half.clone(), half));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => ind (Bool.not (Bool.beq (f x)(f (hcFlip n x i))))` — the disagree
    /// indicator; byte-matches `Influence`'s summand and step2b's RHS integrand.
    fn ind_disagree_integrand(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        i: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, &x, i));
        let beq = Expr::apps(self.bool_beq.clone(), [fx, fflip]);
        let differ = Expr::app(self.bool_not.clone(), beq);
        let body = Expr::app(self.ind.clone(), differ);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    // ── landed-leaf applications ──────────────────────────────────────────────
    /// `Rat.mul_natCast a b : mk(ofNat a) 1 · mk(ofNat b) 1 = mk(ofNat (a·b)) 1`.
    fn mul_natcast_at(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_natcast.clone(), [a, b])
    }
    /// `Rat.powNat_two_eq_natCast n : Rat.powNat 2 n = mk(ofNat (Nat.pow 2 n)) 1`.
    fn pow_two_natcast_at(&self, n: &Expr) -> Expr {
        Expr::app(self.pow_two_natcast.clone(), n.clone())
    }
    /// `Rat.mul_inv_cancel a h : a·inv a = 1`.
    fn mul_inv_cancel_at(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.powNat_pos b k hb : 0 < b^k`.
    fn pow_pos_at(&self, base: Expr, k: &Expr, hb: Expr) -> Expr {
        Expr::apps(self.pow_pos.clone(), [base, k.clone(), hb])
    }
    /// `Rat.ne_zero_of_pos a h : a = 0 → False`.
    fn ne_at(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.ne_zero_of_pos.clone(), [a, h])
    }
}

impl Environment {
    /// Register the support-count identity rungs:
    /// `Rat.mul_natCast`, `Rat.powNat_two_eq_natCast`,
    /// `BoolAnalysis.dualhc_m_pow2_eq_4pow_influence`. Idempotent; each
    /// kernel-checked, `Constructive`, empty admitted-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_minfl(&mut self) -> Result<(), EnvError> {
        self.register_rat_mul_natcast()?;
        self.register_rat_pow_nat_two_eq_natcast()?;
        self.register_rat_pow_nat_eight_eq_two_cubed()?;
        self.register_dualhc_m_pow2_eq_4pow_influence()?;
        Ok(())
    }
}

include!("boolean_analysis_kkl_dualhc_minfl_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_minfl()
            .expect("init_boolean_analysis_kkl_dualhc_minfl");
        env.init_boolean_analysis_kkl_dualhc_minfl()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_rat_mul_natcast_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "Rat.mul_natCast");
    }

    #[test]
    fn test_rat_pow_nat_two_eq_natcast_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "Rat.powNat_two_eq_natCast");
    }

    #[test]
    fn test_rat_pow_nat_eight_eq_two_cubed_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "Rat.powNat_eight_eq_two_cubed");
    }

    #[test]
    fn test_dualhc_m_pow2_eq_4pow_influence_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "BoolAnalysis.dualhc_m_pow2_eq_4pow_influence");
    }
}
