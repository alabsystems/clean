// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **RUNG 3 variance-split arithmetic** (`rung3-split`).
//!
//! The conditional-pinch ARITHMETIC of rung 3, isolated to its pure-`Rat`
//! variance-split core. Given an ABSTRACT low-band charge bound `M_{1..k} ≤ t`
//! (the rung-2 deliverable, instantiated at `t := 9^k·√ε·I[f]` once the
//! NNReal→Rat order bridge lands — see module-tail NOTE), it monotonically
//! transports the landed high-band charge
//! [`BoolAnalysis.variance_low_band_influence`]
//! (`(k+1)·(Var − M_{1..k}) ≤ I[f]`) down to the threshold `t`:
//!
//! ```text
//! BoolAnalysis.kkl_variance_pinch_of_lowband_le :
//!   ∀ (n k : Nat) (f : BoolFn n) (t : Rat),
//!     Rat.le
//!       (subsetSum n (fun S =>                                            -- M_{1..k}
//!           ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                         (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!             · (f̂ S · f̂ S)))
//!       t →
//!     Rat.le
//!       (Rat.mul (natCast (Nat.succ k)) (Rat.sub (Variance n f) t))       -- (k+1)·(Var − t)
//!       (TotalInfluence n f)                                               -- I[f]
//! ```
//!
//! i.e. **`M_{1..k} ≤ t  →  (k+1)·(Var − t) ≤ I[f]`**. This is the EXACT
//! conditional pinch of sharp KKL (O'Donnell Thm 9.28), with the only unresolved
//! input being the rung-2/aggregate low-band charge `t`.
//!
//! ## The conditional sharp-KKL closure (NOTE — the residual)
//!
//! With the rung-2 deliverable [`BoolAnalysis.kkl_lowband_le_wnorm_sum`]
//! (`4·M_{1..k} ≤ 9^k·Σ_i W_norm_i`) and the small-influence aggregate
//! [`BoolAnalysis.kkl_deriv_two_norm_sum_le`] (`Σ_i W_norm_i ≤ 4·√ε·I[f]`, in
//! `NNReal`), one gets `M_{1..k} ≤ 9^k·√ε·I[f]`. Instantiating `t` at this charge
//! and choosing the small-influence threshold
//!
//! ```text
//!   √ε ≤ 1/((k+1)·9^k)      ⟺      ε ≤ 1/((k+1)²·81^k)
//! ```
//! makes `(k+1)·9^k·√ε ≤ 1`, so `(k+1)·t = (k+1)·9^k·√ε·I[f] ≤ I[f]`, hence
//! `(k+1)·Var = (k+1)·(Var − t) + (k+1)·t ≤ I[f] + I[f] = 2·I[f]`, i.e.
//! **`I[f] ≥ ((k+1)/2)·Var`** — the conditional sharp KKL (under `max_i Inf_i ≤ ε`).
//!
//! The instantiation `t := 9^k·√ε·I[f]` is the SOLE remaining blocker: the
//! aggregate `Σ_i W_norm_i ≤ 4·√ε·I[f]` is stated in `NNReal` (`√ε` has no `Rat`
//! representative), and the branch has the FORWARD embedding
//! `NNReal.ofRat_le_ofRat : Rat.le a b → NNReal.le (ofRat a)(ofRat b)` but NOT its
//! order-REFLECTION `NNReal.le (ofRat a)(ofRat b) → Rat.le a b`. Without that
//! reflection the `NNReal` charge cannot be brought back into the `Rat` `Var`/`I[f]`
//! ledger. That reflection lemma (rung 4) is the precise next brick. This module
//! lands everything up to that boundary in pure `Rat`, axiom-free.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! Write `K := natCast (k+1)`, `V := Variance n f`, `M := M_{1..k}`, `I := I[f]`.
//! Given `h : M ≤ t`:
//! 1. `h_refl : V ≤ V`            — `Rat.le_refl V`.
//! 2. `h_sub : V − t ≤ V − M`     — `Rat.sub_le_sub V V t M h_refl h`
//!    (`∀ a b c d, a≤b → d≤c → a−c ≤ b−d` at `a=b:=V, c:=t, d:=M`).
//! 3. `h_K_nn : 0 ≤ K`            — `BoolAnalysis.natCast_nonneg (k+1)`.
//! 4. `h_scaled : K·(V − t) ≤ K·(V − M)` — `mul_le_mul_of_nonneg_left K (V−t)(V−M) h_sub h_K_nn`.
//! 5. `h_charge : K·(V − M) ≤ I`  — `variance_low_band_influence n k f`.
//! 6. `Rat.le_trans (K·(V−t)) (K·(V−M)) I h_scaled h_charge : K·(V − t) ≤ I`.
//!
//! Every leaf (`variance_low_band_influence`, `Rat.sub_le_sub`, `Rat.le_refl`,
//! `Rat.mul_le_mul_of_nonneg_left`, `BoolAnalysis.natCast_nonneg`, `Rat.le_trans`)
//! is `Constructive` with empty admitted-axiom closure, so this rung is too. No
//! axiom added/removed. Idempotent. Gated behind `cfg(any(test, feature =
//! "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the rung-3 variance-split. The `M_{1..k}` band integrand,
/// `Variance`, `TotalInfluence`, `natCast (k+1)` spellings byte-match
/// `variance_low_band_influence` so the high-band charge applies directly.
struct Rung3Consts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    ind: Expr,
    fourier: Expr,
    variance: Expr,
    total_influence: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
}

impl Rung3Consts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            variance: k("BoolAnalysis.Variance"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn ss_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.one_nat(), m)
    }
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    fn band(&self, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [b, c])
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1` — byte-match `LowBandConsts.natcast`.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.one_nat(),
            ],
        )
    }
    fn rat_le(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [l, r])
    }
    /// `M_{1..k} := subsetSum n (fun S => ind(and (ble 1 |S|)(not (ble (k+1) |S|)))·(f̂·f̂))`
    /// — BYTE-IDENTICAL to `variance_low_band_influence`'s `m_lo_fn`.
    fn m_lo(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.ss_nat_of(n, &s);
        let band = self.band(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)));
        let body = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.subset_sum_of(n, g)
    }
}

fn rung3_type(c: &Rung3Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (t_id, t) = b.fresh_local(c.rat.clone());

    let m = c.m_lo(&b, &n, &k, &f);
    let hyp = c.rat_le(m, t.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());

    let kcast = c.natcast(&c.succ(k.clone()));
    let var = c.variance_of(&n, &f);
    let lhs = c.mul(kcast, c.sub(var, t.clone()));
    let concl = c.rat_le(lhs, c.total_influence_of(&n, &f));

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(t_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn rung3_value(c: &Rung3Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (t_id, t) = b.fresh_local(c.rat.clone());

    let m = c.m_lo(&b, &n, &k, &f);
    let hyp = c.rat_le(m.clone(), t.clone());
    let (h_id, h) = b.fresh_local(hyp.clone());

    let kcast = c.natcast(&c.succ(k.clone()));
    let var = c.variance_of(&n, &f);
    let ti = c.total_influence_of(&n, &f);
    let v_sub_t = c.sub(var.clone(), t.clone()); // V − t
    let v_sub_m = c.sub(var.clone(), m.clone()); // V − M
    let k_v_sub_t = c.mul(kcast.clone(), v_sub_t.clone()); // K·(V − t)
    let k_v_sub_m = c.mul(kcast.clone(), v_sub_m.clone()); // K·(V − M)

    // h_refl : V ≤ V.
    let h_refl = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        [var.clone()],
    );
    // h_sub : V − t ≤ V − M
    //   Rat.sub_le_sub V V t M h_refl h : (V − t) ≤ (V − M).
    //   (∀ a b c d, a≤b → d≤c → a−c ≤ b−d ; a=b:=V, c:=t, d:=M, with h : M ≤ t.)
    let h_sub = Expr::apps(
        Expr::const_(Name::from_string("Rat.sub_le_sub"), vec![]),
        [
            var.clone(),
            var.clone(),
            t.clone(),
            m.clone(),
            h_refl,
            h.clone(),
        ],
    );
    // h_K_nn : 0 ≤ K   (natCast_nonneg (k+1)).
    let h_k_nn = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]),
        [c.succ(k.clone())],
    );
    // h_scaled : K·(V − t) ≤ K·(V − M)
    //   mul_le_mul_of_nonneg_left K (V−t) (V−M) h_sub h_K_nn.
    let h_scaled = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
        [
            kcast.clone(),
            v_sub_t.clone(),
            v_sub_m.clone(),
            h_sub,
            h_k_nn,
        ],
    );
    // h_charge : K·(V − M) ≤ I   (variance_low_band_influence n k f).
    let h_charge = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.variance_low_band_influence"),
            vec![],
        ),
        [n.clone(), k.clone(), f.clone()],
    );
    // proof : K·(V − t) ≤ I   Rat.le_trans (K·(V−t)) (K·(V−M)) I h_scaled h_charge.
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        [k_v_sub_t, k_v_sub_m, ti, h_scaled, h_charge],
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
    let e = b.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.kkl_variance_pinch_of_lowband_le` — **RUNG 3**
    /// variance-split arithmetic: `M_{1..k} ≤ t → (k+1)·(Var − t) ≤ I[f]`. See
    /// module docs (incl. the NNReal→Rat reflection NOTE / residual). Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_kkl_variance_pinch_of_lowband_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_variance_pinch_of_lowband_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Variance, TotalInfluence, FourierCoefficient, ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_rat_order_proofs()?; // Rat.le_refl
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_natcast_nonneg()?; // BoolAnalysis.natCast_nonneg
        self.register_rat_add_le_add()?; // (dep of sub_le_sub)
        self.register_rat_neg_le_neg()?; // (dep of sub_le_sub)
        self.register_rat_sub_le_sub()?; // Rat.sub_le_sub
        self.register_variance_low_band_influence()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Rung3Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: rung3_type(&c),
            value: rung3_value(&c),
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
    fn test_kkl_variance_pinch_of_lowband_le_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_variance_pinch_of_lowband_le()
            .expect("register_kkl_variance_pinch_of_lowband_le");
        let nm = Name::from_string("BoolAnalysis.kkl_variance_pinch_of_lowband_le");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("rung-3 pinch proof must check: {e:?}"));
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
    fn test_rung3_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_variance_pinch_of_lowband_le()
            .expect("first");
        env.register_kkl_variance_pinch_of_lowband_le()
            .expect("idempotent");
    }
}
