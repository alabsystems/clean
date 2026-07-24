// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — RUNG 5: `dyadic_level_mass_le`, the faithful linear-`k`-factor
//! level-mass counting bound.
//!
//! ## What this rung proves (and the honest correction to the stated target)
//!
//! The sharp-KKL roadmap names rung 5 "`dyadic_level_sum`": manufacture the
//! linear `k`-factor from the threshold-mass bound. The *stated* target spelled
//! that with the **level-`≥1`** mask (`Nat.ble 1 |S|`):
//!
//! ```text
//!   k · (Σ_S [|S| ≥ 1]·w S)  ≤  Σ_S |S|·w S          -- STATED, but FALSE for k ≥ 2
//! ```
//!
//! That inequality is **not true** for `k ≥ 2`. With `w := f̂²` it reads
//! `k·M_1 ≤ I[f]`, i.e. `k·Var ≤ I[f]` (since `M_1 = Σ_{|S|≥1} f̂² = Var`) — the
//! genuine sharp KKL `log n` bound `hc_dual_sharp`, which the roadmap pins as the
//! UNBUILT hypercontractive crux (it needs the `pow4_noisefn_spectral` +
//! `hc24_at_third` + `{0,±1}` 4-norm collapse + `2^k ≤ n` dyadic-pinch chain).
//! It is NOT a pointwise-monotonicity reduction: the per-`S` claim
//! `k·[|S| ≥ 1] ≤ |S|` fails whenever `|S| = 1 < k`. Proving the `≥1`-mask form
//! from on-branch bricks is impossible; faking it would be masquerade.
//!
//! The **faithful** linear-`k`-factor counting bound — the one that is genuinely
//! true and that the threshold count actually manufactures — uses the
//! level-`≥k` mask `Nat.ble k |S|`:
//!
//! ```text
//! BoolAnalysis.dyadic_level_mass_le :
//!   ∀ (n k : Nat) (w : HCPoint n → Rat),
//!     (∀ S, 0 ≤ w S) → Nat.le (Nat.pow 2 k) n →
//!       Rat.le
//!         (Rat.mul (natCast k)
//!                  (subsetSum n (fun S => Rat.mul (ind (Nat.ble k (setSizeNat n S))) (w S))))
//!         (subsetSum n (fun S => Rat.mul (setSize n S) (w S)))
//! ```
//!
//! i.e. `k · M_{≥k} ≤ Σ_S |S|·w S`, where `M_{≥k} := Σ_{|S| ≥ k} w S` is the
//! level-`≥k` masked mass. This IS the honest manufacturing of the linear
//! `k`-factor: every set surviving the `|S| ≥ k` mask contributes weight
//! `|S| ≥ k` on the right, so the masked sum can be scaled by `k`. It is the
//! `w`-generalized form of the on-branch `kkl_threshold_mass_le` (which fixes
//! `w := f̂²` and the RHS as `TotalInfluence`), exposing the raw
//! `ind`/`setSizeNat`/`setSize` carriers directly.
//!
//! The `2^k ≤ n` premise is carried to match the dyadic-admissible-level framing
//! of rung 5; the bound is in fact unconditionally true (the threshold mask makes
//! the per-`S` step hold without any `n`-side assumption), so including the
//! premise is a sound weakening, never a masquerade.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! The whole rung is an assembly of on-branch bricks:
//!
//! 1. `BoolAnalysis.subsetSum_threshold_le n (natCast k) w b` with the threshold
//!    function `b S := Nat.ble k (setSizeNat n S)` gives
//!    `Σ_S natCast k·(ind (b S)·w S) ≤ Σ_S setSize n S·w S`, once its three
//!    hypotheses are discharged:
//!    - `∀ S, 0 ≤ w S` — the lemma's own `hw` argument;
//!    - `∀ S, 0 ≤ setSize n S` — `BoolAnalysis.setSize_nonneg`;
//!    - `∀ S, b S = true → natCast k ≤ setSize n S` — from
//!      `Nat.cast_le_of_ble k (setSizeNat n S)` (`natCast k ≤ natCast |S|`)
//!      transported along `symm (setSize_eq_natCast n S)`
//!      (`setSize n S = natCast (setSizeNat n S)`).
//! 2. `BoolAnalysis.subsetSum_smul n (natCast k) (fun S => ind (b S)·w S)` pulls
//!    the scalar OUT: `Σ_S natCast k·(ind (b S)·w S) = natCast k · Σ_S ind(b S)·w S`.
//! 3. `Eq.subst` (motive `t ↦ t ≤ Σ_S |S|·w S`) transports (1) along (2) to the
//!    stated `natCast k · M_{≥k} ≤ Σ_S |S|·w S`.
//!
//! Every dependency (`subsetSum_threshold_le`, `setSize_nonneg`,
//! `Nat.cast_le_of_ble`, `setSize_eq_natCast`, `subsetSum_smul`, `Eq.subst`,
//! `Eq.symm`) is `Constructive` with empty closure, so this rung is too. No axiom
//! is added or removed. Idempotent.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the dyadic level-sum rung.
struct DyadicConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    hcpoint: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    nat_ble: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    u1: Level,
}

impl DyadicConsts {
    fn new() -> Self {
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            u1: Level::succ(Level::zero()),
        }
    }

    fn rat_ty(&self) -> Expr {
        self.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `Nat.ble k m`.
    fn ble(&self, k: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [k, m])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    /// `Nat.pow 2 k`.
    fn pow2(&self, k: &Expr) -> Expr {
        let two = self.succ(self.one_nat());
        Expr::apps(self.nat_pow.clone(), [two, k.clone()])
    }
    fn nat_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Rat.mk (Int.ofNat m) 1` — the `Nat → Rat` cast `natCast m`.
    fn natcast(&self, m: &Expr) -> Expr {
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(of_nat, m.clone()), self.one_nat()],
        )
    }
    /// `bit = Bool.true`.
    fn bit_eq_true(&self, bit: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), bit, self.bool_true.clone()],
        )
    }
    /// The threshold function `fun (S : HCPoint n) => Nat.ble k (setSizeNat n S)`.
    fn threshold_fn(&self, parent: &EnvDeclBuilder, n: &Expr, knat: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = self.ble(knat.clone(), self.set_size_nat_of(n, &s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The masked level-`≥k` integrand `fun S => ind (ble k |S|) · w S`.
    fn mask_fn(&self, parent: &EnvDeclBuilder, n: &Expr, knat: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = self.ble(knat.clone(), self.set_size_nat_of(n, &s));
        let body = self.mul(self.ind_of(bit), Expr::app(w.clone(), s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The RHS integrand `fun S => setSize n S · w S`.
    fn spectral_fn(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = self.mul(self.set_size_of(n, &s), Expr::app(w.clone(), s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the dyadic level-sum rung. Idempotent.
    pub fn init_boolean_analysis_dyadic_level_sum(&mut self) -> Result<(), EnvError> {
        self.register_dyadic_level_mass_le()?;
        Ok(())
    }

    /// `BoolAnalysis.dyadic_level_mass_le :
    ///   ∀ (n k : Nat) (w : HCPoint n → Rat),
    ///     (∀ S, 0 ≤ w S) → Nat.le (Nat.pow 2 k) n →
    ///       Rat.le (natCast k · subsetSum n (fun S => ind (ble k |S|) · w S))
    ///              (subsetSum n (fun S => setSize n S · w S))`.
    ///
    /// The faithful linear-`k`-factor level-mass counting bound `k·M_{≥k} ≤ Σ|S|w`.
    /// See module docs for the honest correction to the (false-for-`k≥2`)
    /// level-`≥1` form of the stated target.
    pub fn register_dyadic_level_mass_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dyadic_level_mass_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_kkl_k2b()?; // subsetSum_threshold_le
        self.register_set_size_nonneg()?; // setSize_nonneg
        self.register_nat_cast_le_of_ble()?; // Nat.cast_le_of_ble
        self.register_set_size_eq_natcast()?; // setSize_eq_natCast
        self.register_subset_sum_smul_theorem()?; // subsetSum_smul
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;

        let c = DyadicConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());
            let w_ty = c.hcpoint_to_rat(&n);
            let (w_id, w) = b.fresh_local(w_ty.clone());

            // hw : ∀ S, 0 ≤ w S
            let hw_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = c
                    .order
                    .rat_le(c.order.rat_zero.clone(), Expr::app(w.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };
            // hk : Nat.le (Nat.pow 2 k) n
            let hk_ty = c.nat_le_of(c.pow2(&knat), n.clone());

            let mass = c.subset_sum_of(&n, c.mask_fn(&b, &n, &knat, &w));
            let lhs = c.mul(c.natcast(&knat), mass);
            let rhs = c.subset_sum_of(&n, c.spectral_fn(&b, &n, &w));
            let concl = c.order.rat_le(lhs, rhs);

            let (hw_id, _) = b.fresh_local(hw_ty.clone());
            let (hk_id, _) = b.fresh_local(hk_ty.clone());
            let e = b.mk_pi(hk_id, BinderInfo::Default, hk_ty, concl);
            let e = b.mk_pi(hw_id, BinderInfo::Default, hw_ty, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, w_ty, e);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let threshold_le = Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_threshold_le"),
            vec![],
        );
        let set_size_nonneg =
            Expr::const_(Name::from_string("BoolAnalysis.setSize_nonneg"), vec![]);
        let cast_le_of_ble = Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]);
        let set_size_eq_natcast =
            Expr::const_(Name::from_string("BoolAnalysis.setSize_eq_natCast"), vec![]);
        let subset_sum_smul =
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());
            let w_ty = c.hcpoint_to_rat(&n);
            let (w_id, w) = b.fresh_local(w_ty.clone());

            let hw_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = c
                    .order
                    .rat_le(c.order.rat_zero.clone(), Expr::app(w.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };
            let hk_ty = c.nat_le_of(c.pow2(&knat), n.clone());
            let (hw_id, hw) = b.fresh_local(hw_ty.clone());
            let (hk_id, _hk) = b.fresh_local(hk_ty.clone());

            let kcast = c.natcast(&knat);
            let bf = c.threshold_fn(&b, &n, &knat);
            let mask = c.mask_fn(&b, &n, &knat, &w);
            let rhs = c.subset_sum_of(&n, c.spectral_fn(&b, &n, &w));

            // hyp2 : ∀ S, 0 ≤ setSize n S   := fun S => setSize_nonneg n S
            let hyp2 = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = Expr::apps(set_size_nonneg.clone(), [n.clone(), s.clone()]);
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };

            // hyp3 : ∀ S, (ble k |S| = true) → natCast k ≤ setSize n S
            //   := fun S (h : ble k |S| = true) =>
            //        subst (motive t => natCast k ≤ t)
            //              (a := natCast (setSizeNat n S)) (b := setSize n S)
            //              (symm (setSize_eq_natCast n S))
            //              (Nat.cast_le_of_ble k (setSizeNat n S) h)
            let hyp3 = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let size_nat = c.set_size_nat_of(&n, &s);
                let bit = c.ble(knat.clone(), size_nat.clone());
                let ante = c.bit_eq_true(bit);
                let (h_id, h) = ch.fresh_local(ante.clone());

                let cast_size = c.natcast(&size_nat); // natCast (setSizeNat n S)
                let set_size = c.set_size_of(&n, &s); // setSize n S

                // h_eq : setSize n S = natCast (setSizeNat n S)
                let h_eq = Expr::apps(set_size_eq_natcast.clone(), [n.clone(), s.clone()]);
                // symm : natCast (setSizeNat n S) = setSize n S
                let h_eq_symm = c.order.symm(set_size.clone(), cast_size.clone(), h_eq);
                // h_cast : natCast k ≤ natCast (setSizeNat n S)
                let h_cast = Expr::apps(
                    cast_le_of_ble.clone(),
                    [knat.clone(), size_nat.clone(), h.clone()],
                );
                // motive t => natCast k ≤ t
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&ch);
                    let (t_id, t) = m.fresh_local(c.rat_ty());
                    let mbody = c.order.rat_le(kcast.clone(), t);
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat_ty(), mbody))
                };
                let proof = c
                    .order
                    .subst(motive, cast_size, set_size, h_eq_symm, h_cast);
                let lam = ch.mk_lam(h_id, BinderInfo::Default, ante, proof);
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, lam))
            };

            // thr : Σ_S natCast k·(ind (b S)·w S) ≤ Σ_S setSize n S·w S
            //   := subsetSum_threshold_le n (natCast k) w b hw hyp2 hyp3
            let thr = Expr::apps(
                threshold_le.clone(),
                [
                    n.clone(),
                    kcast.clone(),
                    w.clone(),
                    bf.clone(),
                    hw.clone(),
                    hyp2,
                    hyp3,
                ],
            );

            // h_smul : Σ_S natCast k·(ind (b S)·w S) = natCast k · Σ_S ind (b S)·w S
            //   := subsetSum_smul n (natCast k) mask
            let scaled = c.subset_sum_of(&n, {
                // fun S => natCast k · (ind (b S) · w S) — the threshold LHS integrand,
                // which is exactly `fun S => natCast k · mask S`.
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let bit = c.ble(knat.clone(), c.set_size_nat_of(&n, &s));
                let body = c.mul(kcast.clone(), c.mul(c.ind_of(bit), Expr::app(w.clone(), s)));
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            });
            let pulled = c.mul(kcast.clone(), c.subset_sum_of(&n, mask.clone()));
            let h_smul = Expr::apps(
                subset_sum_smul.clone(),
                [n.clone(), kcast.clone(), mask.clone()],
            );

            // subst (motive t => t ≤ rhs) (a := scaled) (b := pulled) h_smul thr
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat_ty());
                let mbody = c.order.rat_le(t, rhs.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat_ty(), mbody))
            };
            let body = c.order.subst(motive, scaled, pulled, h_smul, thr);

            let e = b.mk_lam(hk_id, BinderInfo::Default, hk_ty, body);
            let e = b.mk_lam(hw_id, BinderInfo::Default, hw_ty, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, w_ty, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_dyadic_level_sum()
            .expect("init_boolean_analysis_dyadic_level_sum");
        env.init_boolean_analysis_dyadic_level_sum()
            .expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
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
            "{name} closure must be empty"
        );
    }

    #[test]
    fn test_dyadic_level_mass_le_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.dyadic_level_mass_le");
    }
}
