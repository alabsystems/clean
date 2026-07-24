// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — `hc_dual_total`: the `n`-scaled total-influence lower bound.
//!
//! This module lands `BoolAnalysis.hc_dual_total`, the dual-chain input the
//! `kkl_inequality` assembly (`designs/2026-06-12-kkl-endgame-worked-chain.md`,
//! §5B) consumes:
//!
//! ```text
//! BoolAnalysis.hc_dual_total : ∀ (n) (f : BoolFn n) (k : Nat),
//!   Nat.le (Nat.pow 2 k) n →
//!     Rat.le (Rat.mul (natCast 1) (Rat.mul (Variance n f) (natCast k)))
//!            (Rat.mul (natCast n) (TotalInfluence n f))
//! ```
//!
//! i.e. `1·(Var·k) ≤ n·I[f]` whenever `2^k ≤ n`. This is the **genuinely-true,
//! constant-clean** form of the KKL dual bound (the `n·` slack on the RHS
//! absorbs the hypercontractive constant the no-`n` `hc_dual_level_lower` would
//! need a fractional/irrational `C` to state). It is proven WITHOUT
//! hypercontractivity, from:
//!
//! - `variance_le_influence` (the Poincaré inequality `Var ≤ I[f]`, on branch);
//! - `Nat.le_two_pow_self` (`k ≤ 2^k`, built here) + the hypothesis `2^k ≤ n`
//!   ⟹ `k ≤ n` (`Nat.le_trans`) ⟹ `natCast k ≤ natCast n`
//!   (`Nat.cast_le_of_ble` + `Nat.ble_eq_true_of_le`);
//! - `total_influence_nonneg` (`0 ≤ I[f]`) + `variance_nonneg`/`natCast_nonneg`
//!   for the `mul_le_mul` monotonicity steps.
//!
//! The standard KKL `log n` rate is the SHARPER bound `Var·log₂n ≤ c·I[f]`;
//! this `Var·k ≤ n·I[f]` form deliberately weakens to stay constant-clean and
//! rational (the design §4 "dyadic counting loses a constant, which we
//! absorb"), but is exactly what the helper Definition / assembly needs:
//! maximising over `k = ⌊log₂ n⌋` recovers the dyadic-level KKL statement.
//!
//! All lemmas are kernel-checked, `ProofQuality::Constructive`, empty closure.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the `hc_dual_total` chain.
struct HcDualTotalConsts {
    order: OrderConsts,
    nat: Expr,
    bool_fn: Expr,
    variance: Expr,
    total_influence: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    nat_rec0: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_succ_le_succ: Expr,
    nat_zero_le: Expr,
    nat_add: Expr,
    nat_add_le_add: Expr,
    nat_le_trans: Expr,
    one_le_two_pow: Expr,
    pow_two_succ: Expr,
    eq_subst_nat: Expr,
}

impl HcDualTotalConsts {
    fn new() -> Self {
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            variance: Expr::const_(Name::from_string("BoolAnalysis.Variance"), vec![]),
            total_influence: Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_le_refl: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            nat_succ_le_succ: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            nat_zero_le: Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_add_le_add: Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
            nat_le_trans: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            one_le_two_pow: Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_subst_nat: Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
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
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn pow2(&self, k: &Expr) -> Expr {
        let two = self.succ(self.one_nat());
        Expr::apps(self.nat_pow.clone(), [two, k.clone()])
    }
    fn nat_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn nat_add_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    /// `Rat.mk (Int.ofNat m) 1` — the `Nat → Rat` cast.
    fn natcast(&self, m: &Expr) -> Expr {
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(of_nat, m.clone()), self.one_nat()],
        )
    }
}

impl Environment {
    /// Register the `hc_dual_total` chain. Idempotent.
    pub fn init_boolean_analysis_kkl_hcdualtotal(&mut self) -> Result<(), EnvError> {
        self.register_nat_le_two_pow_self()?;
        self.register_hc_dual_total()?;
        Ok(())
    }

    /// `Nat.le_two_pow_self : ∀ (k : Nat), Nat.le k (Nat.pow 2 k)`.
    ///
    /// `k ≤ 2^k`. Proof: `Nat.rec.{0}` on `k`, motive `λ k => k ≤ 2^k`.
    /// - **base** `0 ≤ 2^0 (≡ 1)`: `Nat.zero_le (2^0)`.
    /// - **step** given `k`, `ih : k ≤ 2^k`, goal `succ k ≤ 2^(succ k)`:
    ///   `Nat.succ_le_succ k (2^k) ih : succ k ≤ succ (2^k)`, and
    ///   `succ (2^k) ≡ Nat.add (2^k) 1` (def-eq: `add x 1 = succ x`), so
    ///   `Nat.add_le_add (2^k) (2^k) 1 (2^k) (le.refl) (one_le_two_pow k)
    ///     : add (2^k) 1 ≤ add (2^k) (2^k)`. `Nat.le_trans` chains them to
    ///   `succ k ≤ add (2^k) (2^k)`, then `Eq.subst` along
    ///   `symm (pow_two_succ k) : add (2^k) (2^k) = 2^(succ k)` lands the goal.
    pub fn register_nat_le_two_pow_self(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_two_pow_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.rec
        self.init_eq()?;
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.init_nat_top_level_ordering()?; // Nat.succ_le_succ
        self.register_nat_le_total_proof()?; // Nat.zero_le
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow
        self.register_nat_pow_two_succ_proof()?; // Nat.pow_two_succ
        self.register_nat_arith_order_proofs()?; // Nat.add_le_add

        let c = HcDualTotalConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let concl = c.nat_le_of(k.clone(), c.pow2(&k));
            b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl))
        };

        // motive : λ (k : Nat) => Nat.le k (Nat.pow 2 k)
        let motive = {
            let mut m = EnvDeclBuilder::new();
            let (k_id, k) = m.fresh_local(c.nat.clone());
            let body = c.nat_le_of(k.clone(), c.pow2(&k));
            m.finish(m.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // base : Nat.le 0 (2^0)   := Nat.zero_le (2^0)
        let base = {
            let pow2_zero = c.pow2(&c.nat_zero);
            Expr::app(c.nat_zero_le.clone(), pow2_zero)
        };

        // step : λ (k) (ih : k ≤ 2^k) => (proof : succ k ≤ 2^(succ k))
        let step = {
            let mut s = EnvDeclBuilder::new();
            let (k_id, k) = s.fresh_local(c.nat.clone());
            let ih_ty = c.nat_le_of(k.clone(), c.pow2(&k));
            let (ih_id, ih) = s.fresh_local(ih_ty.clone());

            let pow_k = c.pow2(&k);
            let sk = c.succ(k.clone());
            let add_pp = c.nat_add_of(pow_k.clone(), pow_k.clone()); // 2^k + 2^k

            // h_ss : succ k ≤ succ (2^k)   (≡ succ k ≤ add (2^k) 1 by def-eq)
            let h_ss = Expr::apps(
                c.nat_succ_le_succ.clone(),
                [k.clone(), pow_k.clone(), ih.clone()],
            );
            // h_one : Nat.le 1 (2^k)   (Nat.one_le_two_pow k)
            let h_one = Expr::app(c.one_le_two_pow.clone(), k.clone());
            // h_refl : Nat.le (2^k) (2^k)   (Nat.le.refl (2^k))
            let h_refl = Expr::app(c.nat_le_refl.clone(), pow_k.clone());
            // h_add : Nat.le (add (2^k) 1) (add (2^k) (2^k))
            //   Nat.add_le_add (2^k) (2^k) 1 (2^k) h_refl h_one
            let one = c.one_nat();
            let add_p1 = c.nat_add_of(pow_k.clone(), one.clone());
            let h_add = Expr::apps(
                c.nat_add_le_add.clone(),
                [
                    pow_k.clone(),
                    pow_k.clone(),
                    one.clone(),
                    pow_k.clone(),
                    h_refl,
                    h_one,
                ],
            );
            // h_chain : succ k ≤ add (2^k) (2^k)
            //   Nat.le_trans (succ k) (add (2^k) 1) (add (2^k) (2^k)) h_ss h_add
            //   (h_ss : succ k ≤ succ (2^k) ≡ succ k ≤ add (2^k) 1 by def-eq)
            let h_chain = Expr::apps(
                c.nat_le_trans.clone(),
                [sk.clone(), add_p1.clone(), add_pp.clone(), h_ss, h_add],
            );
            // h_pts : 2^(succ k) = add (2^k) (2^k)   (Nat.pow_two_succ k)
            let pow_sk = c.pow2(&sk);
            let h_pts = Expr::app(c.pow_two_succ.clone(), k.clone());
            // symm h_pts : add (2^k) (2^k) = 2^(succ k)
            let eq_symm = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            let h_pts_symm = Expr::apps(
                eq_symm,
                [c.nat.clone(), pow_sk.clone(), add_pp.clone(), h_pts],
            );
            // subst (motive z => succ k ≤ z) (a := add (2^k)(2^k)) (b := 2^(succ k))
            //       h_pts_symm h_chain : succ k ≤ 2^(succ k)
            let subst_motive = {
                let mut zb = EnvDeclBuilder::child_of(&s);
                let (z_id, z) = zb.fresh_local(c.nat.clone());
                let body = c.nat_le_of(sk.clone(), z);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let body = Expr::apps(
                c.eq_subst_nat.clone(),
                [
                    c.nat.clone(),
                    subst_motive,
                    add_pp,
                    pow_sk,
                    h_pts_symm,
                    h_chain,
                ],
            );

            let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            let e = s.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            s.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let rec_app = Expr::apps(c.nat_rec0.clone(), [motive, base, step, k.clone()]);
            b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app))
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

    /// `BoolAnalysis.hc_dual_total : ∀ (n) (f : BoolFn n) (k : Nat),
    ///   Nat.le (Nat.pow 2 k) n →
    ///     Rat.le (natCast 1 · (Variance n f · natCast k))
    ///            (natCast n · TotalInfluence n f)`.
    ///
    /// The `n`-scaled dual bound `1·(Var·k) ≤ n·I[f]`. See module docs.
    ///
    /// ## Proof (constructive, empty closure)
    ///
    /// Goal (after `1·x ≡ x`): `Var·k ≤ n·I[f]`.
    /// 1. `Var ≤ I[f]`  (`variance_le_influence n f`).
    /// 2. `k ≤ n`: `Nat.le_trans k (2^k) n (Nat.le_two_pow_self k) hk`.
    /// 3. `natCast k ≤ natCast n`: `Nat.cast_le_of_ble k n
    ///    (Nat.ble_eq_true_of_le k n (step 2))`.
    /// 4. `Var·k ≤ I[f]·k`  (`mul_le_mul_of_nonneg_right` on (1), `0 ≤ natCast k`).
    /// 5. `I[f]·k ≤ I[f]·n`  (`mul_le_mul_of_nonneg_left` on (3), `0 ≤ I[f]`).
    /// 6. `Var·k ≤ I[f]·n`  (`Rat.le_trans` of 4,5).
    /// 7. `I[f]·n = n·I[f]`  (`Rat.mul_comm`); `Eq.subst` lands `Var·k ≤ n·I[f]`.
    /// 8. `natCast 1 · (Var·k) ≡ Var·k`  (`natCast 1 ≡ Rat.one`, `Rat.one_mul`);
    ///    `Eq.subst` lands the stated LHS.
    pub fn register_hc_dual_total(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hc_dual_total");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_nat_le_two_pow_self()?;
        self.register_variance_le_influence()?; // Var ≤ I[f]
        self.register_total_influence_nonneg()?; // 0 ≤ I[f]
        self.register_natcast_nonneg()?; // 0 ≤ natCast k
        self.register_nat_cast_le_of_ble()?; // Nat.cast_le_of_ble
        self.register_nat_ble_le_lemmas()?; // Nat.ble_eq_true_of_le
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left/right
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_rat()?; // Rat.one_mul, Rat.mul_comm

        let c = HcDualTotalConsts::new();
        let one_nat = c.one_nat();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());
            let hk_ty = c.nat_le_of(c.pow2(&knat), n.clone());
            let (hk_id, _) = b.fresh_local(hk_ty.clone());

            let var = c.variance_of(&n, &f);
            let ti = c.total_influence_of(&n, &f);
            let lhs = c.mul(c.natcast(&one_nat), c.mul(var, c.natcast(&knat)));
            let rhs = c.mul(c.natcast(&n), ti);
            let concl = c.order.rat_le(lhs, rhs);

            let e = b.mk_pi(hk_id, BinderInfo::Default, hk_ty, concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let var_le_inf = Expr::const_(
            Name::from_string("BoolAnalysis.variance_le_influence"),
            vec![],
        );
        let ti_nonneg = Expr::const_(
            Name::from_string("BoolAnalysis.total_influence_nonneg"),
            vec![],
        );
        let natcast_nonneg = Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]);
        let cast_le_of_ble = Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]);
        let ble_of_le = Expr::const_(Name::from_string("Nat.ble_eq_true_of_le"), vec![]);
        let le_two_pow_self = Expr::const_(Name::from_string("Nat.le_two_pow_self"), vec![]);
        let nat_le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let mul_le_right =
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]);
        let mul_le_left = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]);
        let rat_le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
        let mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());
            let hk_ty = c.nat_le_of(c.pow2(&knat), n.clone());
            let (hk_id, hk) = b.fresh_local(hk_ty.clone());

            let var = c.variance_of(&n, &f);
            let ti = c.total_influence_of(&n, &f);
            let kcast = c.natcast(&knat);
            let ncast = c.natcast(&n);

            // (1) h_vi : Var ≤ I[f]
            let h_vi = Expr::apps(var_le_inf.clone(), [n.clone(), f.clone()]);
            // (2) h_kn : k ≤ n   := Nat.le_trans k (2^k) n (le_two_pow_self k) hk
            let h_kn = Expr::apps(
                nat_le_trans.clone(),
                [
                    knat.clone(),
                    c.pow2(&knat),
                    n.clone(),
                    Expr::app(le_two_pow_self.clone(), knat.clone()),
                    hk.clone(),
                ],
            );
            // (3) h_cast : natCast k ≤ natCast n
            //   := Nat.cast_le_of_ble k n (Nat.ble_eq_true_of_le k n h_kn)
            let h_ble = Expr::apps(ble_of_le.clone(), [knat.clone(), n.clone(), h_kn]);
            let h_cast = Expr::apps(cast_le_of_ble.clone(), [knat.clone(), n.clone(), h_ble]);
            // h_kpos : 0 ≤ natCast k ; h_tipos : 0 ≤ I[f]
            let h_kpos = Expr::app(natcast_nonneg.clone(), knat.clone());
            let h_tipos = Expr::apps(ti_nonneg.clone(), [n.clone(), f.clone()]);

            // (4) h4 : Var·k ≤ I[f]·k
            //   mul_le_mul_of_nonneg_right (natCast k) Var I[f] h_vi h_kpos
            let h4 = Expr::apps(
                mul_le_right.clone(),
                [kcast.clone(), var.clone(), ti.clone(), h_vi, h_kpos],
            );
            // (5) h5 : I[f]·k ≤ I[f]·n
            //   mul_le_mul_of_nonneg_left I[f] (natCast k) (natCast n) h_cast h_tipos
            let h5 = Expr::apps(
                mul_le_left.clone(),
                [ti.clone(), kcast.clone(), ncast.clone(), h_cast, h_tipos],
            );
            // (6) h6 : Var·k ≤ I[f]·n   (le_trans of h4, h5)
            let var_k = c.mul(var.clone(), kcast.clone());
            let ti_k = c.mul(ti.clone(), kcast.clone());
            let ti_n = c.mul(ti.clone(), ncast.clone());
            let h6 = Expr::apps(
                rat_le_trans.clone(),
                [var_k.clone(), ti_k, ti_n.clone(), h4, h5],
            );

            // (7) bridge I[f]·n → n·I[f]: mul_comm I[f] n ; subst.
            //   h_comm : I[f]·n = n·I[f]   (Rat.mul_comm I[f] (natCast n))
            let n_ti = c.mul(ncast.clone(), ti.clone());
            let h_comm = Expr::apps(mul_comm.clone(), [ti.clone(), ncast.clone()]);
            //   subst (motive t => var_k ≤ t) (a := I[f]·n) (b := n·I[f]) h_comm h6
            let motive7 = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let mbody = c.order.rat_le(var_k.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), mbody))
            };
            let h7 = c
                .order
                .subst(motive7, ti_n.clone(), n_ti.clone(), h_comm, h6);

            // (8) LHS bridge: 1·(Var·k) ≡ natCast 1 · var_k ; one_mul var_k.
            //   one_var_k := natCast 1 · var_k   (the stated LHS)
            let one_var_k = c.mul(c.natcast(&one_nat), var_k.clone());
            //   h_one : 1·var_k = var_k   (Rat.one_mul var_k)
            let h_one = Expr::app(one_mul.clone(), var_k.clone());
            //   subst (motive t => t ≤ n·I[f]) (a := var_k) (b := one_var_k)
            //         (symm h_one : var_k = 1·var_k ≡ var_k = one_var_k) (h7)
            let h_one_symm = c.order.symm(one_var_k.clone(), var_k.clone(), h_one);
            let motive8 = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let mbody = c.order.rat_le(t, n_ti.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), mbody))
            };
            let body = c
                .order
                .subst(motive8, var_k.clone(), one_var_k, h_one_symm, h7);

            let e = b.mk_lam(hk_id, BinderInfo::Default, hk_ty, body);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
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
        env.init_boolean_analysis_kkl_hcdualtotal()
            .expect("init_boolean_analysis_kkl_hcdualtotal");
        env.init_boolean_analysis_kkl_hcdualtotal()
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
    fn test_nat_le_two_pow_self_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "Nat.le_two_pow_self");
    }

    #[test]
    fn test_hc_dual_total_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.hc_dual_total");
    }
}
