// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **RUNG 5** (`conditional`): the CONDITIONAL sharp-KKL variance
//! bound `(k+1)·Var ≤ 2·I[f]` (`= I[f]+I[f]`) under small influences.
//!
//! Assembles the three landed rungs:
//! - rung 2 [`kkl_lowband_le_wnorm_sum`] `4·M ≤ 9^k·Σ_i W_norm_i`,
//! - rung 4c [`kkl_wnorm_sum_le_rat`]    `Σ_i W_norm_i ≤ 4·(δ·I[f])`,
//! - rung 3 [`kkl_variance_pinch_of_lowband_le`] `M ≤ t → (k+1)·(Var − t) ≤ I[f]`,
//!
//! into:
//!
//! ```text
//! BoolAnalysis.kkl_conditional_var_bound :
//!   ∀ (n k : Nat) (f : BoolFn n) (d : Rat)
//!     (hd   : Rat.le Rat.zero d)
//!     (hdd0 : Rat.le Rat.zero (Rat.mul d d))
//!     (hdd1 : Rat.lt (Rat.mul d d) Rat.one)
//!     (h0 : ∀ i, Rat.le Rat.zero (Influence n f i))
//!     (h1 : ∀ i, Rat.le (Influence n f i) (Rat.mul d d))   -- max influence ≤ δ²
//!     (hkt : Rat.le (Rat.mul (natCast (k+1))                -- (k+1)·t ≤ I[f]
//!                            (Rat.mul (9^k) (Rat.mul d (TotalInfluence n f))))
//!                   (TotalInfluence n f)),
//!     Rat.le (Rat.mul (natCast (k+1)) (Variance n f))       -- (k+1)·Var
//!            (Rat.add (TotalInfluence n f) (TotalInfluence n f))   -- ≤ I[f]+I[f]
//! ```
//!
//! with `t := 9^k·(δ·I[f])`. Under `max_i Inf_i ≤ δ² < 1`, this is exactly the
//! conditional sharp KKL (O'Donnell Thm 9.28): `I[f] ≥ ((k+1)/2)·Var`.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Write `P9 := 9^k`, `K := natCast(k+1)`, `V := Variance n f`, `M := M_{1..k}`,
//! `I := TotalInfluence n f`, `Σwn := Σ_i W_norm_i`, `dI := d·I`, `t := P9·dI`.
//!
//! 1. r2 : 4·M ≤ P9·Σwn            (kkl_lowband_le_wnorm_sum n k f).
//! 2. br : Σwn ≤ 4·dI              (kkl_wnorm_sum_le_rat n f d hd hdd0 hdd1 h0 h1).
//! 3. h9 : 0 ≤ P9                  (powNat_nonneg 9 k (0≤9)).
//! 4. mono : P9·Σwn ≤ P9·(4·dI)    (mul_le_mul_of_nonneg_left P9 Σwn (4·dI) br h9).
//! 5. r2' : 4·M ≤ P9·(4·dI)        (le_trans r2 mono).
//! 6. eR : P9·(4·dI) = 4·(P9·dI)   (assoc/comm reshape: P9·(4·dI)=(P9·4)·dI=(4·P9)·dI=4·(P9·dI)).
//! 7. r2'' : 4·M ≤ 4·t             (subst eR into r2', t := P9·dI).
//! 8. hMt : M ≤ t                  (le_of_mul_le_mul_left_pos M t 4 (0<4) r2'').
//! 9. r3 : K·(V − t) ≤ I           (kkl_variance_pinch_of_lowband_le n k f t hMt).
//! 10. eV : V = (V − t) + t        (symm (sub_add_cancel t V)).
//! 11. eKV : K·V = K·(V−t) + K·t   (congrArg (K·) eV ⬝ left_distrib K (V−t) t).
//! 12. add_le : K·(V−t) + K·t ≤ I + I   (add_le_add … r3 hkt).
//! 13. subst eKV into add_le ⟹ K·V ≤ I + I.
//!
//! Every leaf is a `Constructive` empty-closure Theorem, so this rung is too.
//! No axiom added/removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms. The `M`/`9^k`/`natCast`/`Var`/`I` spellings byte-match rung 2,
/// rung 3, and rung 4c so their instances apply directly.
struct CondConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_of_nat: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_add: Expr,
    pow_nat: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    ind: Expr,
    fourier: Expr,
    variance: Expr,
    total_influence: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    bool_: Expr,
    bool_true: Expr,
    u1: crate::level::Level,
}

impl CondConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_of_nat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            rat_add: k("Rat.add"),
            pow_nat: k("Rat.powNat"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            variance: k("BoolAnalysis.Variance"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            u1: crate::level::Level::succ(crate::level::Level::zero()),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rat_le(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [l, r])
    }
    fn rat_lt(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [l, r])
    }
    fn rat_one(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.one"), vec![])
    }
    fn rat_zero(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.zero"), vec![])
    }
    fn four(&self) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(4)),
                self.one_nat(),
            ],
        )
    }
    /// `9^k := powNat (Rat.ofNat 9) k` — byte-match rung 2's `pow9`.
    fn pow9(&self, k: &Expr) -> Expr {
        Expr::apps(
            self.pow_nat.clone(),
            [
                Expr::app(self.rat_of_nat.clone(), self.nat_lit(9)),
                k.clone(),
            ],
        )
    }
    /// `0 ≤ Rat.ofNat 9` via `Rat.le_of_ble_eq_true 0 (ofNat 9)(Eq.refl Bool true)`.
    fn zero_le_nine(&self) -> Expr {
        let nine = Expr::app(self.rat_of_nat.clone(), self.nat_lit(9));
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.u1.clone()]),
            [self.bool_.clone(), self.bool_true.clone()],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [self.rat_zero(), nine, refl],
        )
    }
    /// `0 < 4` := `@Int.NonNeg.mk 3` — byte-match rung 2's `four_pos`.
    fn four_pos(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_lit(3),
        )
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1` — byte-match rung 3's `natcast`.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.one_nat(),
            ],
        )
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let cc = self.fourier_of(n, f, s);
        self.mul(cc.clone(), cc)
    }
    fn ss_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    /// `M_{1..k}` — BYTE-IDENTICAL to rung 3's `m_lo` (and rung 2's `m_mass`).
    fn m_lo(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.ss_nat_of(n, &s);
        let band = Expr::apps(
            self.bool_and.clone(),
            [
                self.ble(self.one_nat(), ss.clone()),
                Expr::app(self.bool_not.clone(), self.ble(self.succ(k.clone()), ss)),
            ],
        );
        let body = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }

    // ── Eq.{1} plumbing over Rat ──────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
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
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
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
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
}

// Proof-term + hypothesis builders live in a sibling include to keep this
// file under the 500-line convention.
include!("boolean_analysis_kkl_conditional_build.rs");

impl Environment {
    /// Register `BoolAnalysis.kkl_conditional_var_bound` — **RUNG 5**: the
    /// conditional sharp-KKL variance bound `(k+1)·Var ≤ I[f]+I[f]` under
    /// `max_i Inf_i ≤ δ² < 1` and the threshold `(k+1)·t ≤ I[f]`. See module docs.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent;
    /// no axiom added/removed.
    pub fn register_kkl_conditional_var_bound(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_conditional_var_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.init_rat_field_inst()?; // Rat.left_distrib, mul_assoc, mul_comm
        self.register_kkl_lowband_le_wnorm_sum()?; // rung 2 (+ Σwn carriers, powNat, cancel)
        self.register_kkl_wnorm_sum_le_rat()?; // rung 4c
        self.register_kkl_variance_pinch_of_lowband_le()?; // rung 3
        self.register_rat_pow_nat_nonneg()?; // Rat.powNat_nonneg
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_le_of_mul_le_mul_left_pos()?; // Rat.le_of_mul_le_mul_left_pos
        self.init_boolean_analysis_order_toolkit_b1b()?; // Rat.sub_add_cancel
        self.register_rat_add_le_add()?; // Rat.add_le_add
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = CondConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_conditional(&c, false),
            value: build_conditional(&c, true),
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
    fn test_kkl_conditional_var_bound_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_conditional_var_bound()
            .expect("register_kkl_conditional_var_bound");
        let nm = Name::from_string("BoolAnalysis.kkl_conditional_var_bound");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("conditional proof must check: {e:?}"));
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
    fn test_conditional_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_conditional_var_bound().expect("first");
        env.register_kkl_conditional_var_bound()
            .expect("idempotent");
    }
}
