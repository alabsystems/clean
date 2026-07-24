// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — STEP 1: the band-MASK reconciliation.
//!
//! ## What this proves
//!
//! The conditional KKL assembly (`kkl_lowband_mass_of_dual_hc`) consumes
//! `h_dual : Σ_i W^{≤k}[D_i f] ≤ B·Σ_i r_i`, where the per-coordinate band term
//! `W^{≤k}[D_i f]` is spelled with the assembly's mask
//! `ind (S i) · (ind (not (ble (k+1) |S|)) · (4 · f̂(S)²))`.
//!
//! The spectral side (`dualhc_W_eq_spectral` ∘ `deriv_coeff_sq_eq` ∘ RUNG A at
//! `b = 1/9`) produces the low-band-extracted mass with RUNG A's mask
//! `ind (ble |S| k) · (4 · ind (S i) · f̂(S)²)` (`|S| ≤ k`). The two masks agree
//! because `not (ble (k+1) |S|)` and `ble |S| k` are the SAME Bool (both compute
//! `|S| ≤ k`). This module supplies that Nat-boolean identity, which is the
//! load-bearing reconcile primitive:
//!
//! ```text
//! BoolAnalysis.not_ble_succ_eq_ble :
//!   ∀ (m k : Nat), @Eq Bool (Bool.not (Nat.ble (Nat.succ k) m)) (Nat.ble m k)
//! ```
//!
//! i.e. `¬(k+1 ≤ m) ↔ (m ≤ k)`, at the Bool level. Proven by `Nat.rec` on `m`
//! (universally-quantified-in-`k` motive) with `Nat.casesOn k` in each branch:
//!
//!   * `m = 0`: `ble (k+1) 0 ι→ false`, `not false ι→ true`; `ble 0 k ι→ true`.
//!     `Eq.refl` (both sides reduce to `Bool.true`).
//!   * `m = succ m'`, ih `∀ k, not(ble (k+1) m') = ble m' k`:
//!       - `k = 0`: `ble 1 (succ m') ι→ ble 0 m' ι→ true`, `not true ι→ false`;
//!         `ble (succ m') 0 ι→ false`. `Eq.refl Bool.false`.
//!       - `k = succ k'`: `not(ble (k+2) (succ m')) ι→ not(ble (k+1) m')`,
//!         `ble (succ m') (succ k') ι→ ble m' k'`; closed by `ih k'`.
//!
//! Every leaf (`Nat.rec`, `Nat.casesOn`, `Eq.refl`) is `Constructive` with empty
//! closure, so this is too. NO axiom is added or removed.
//!
//! NOTE: this file holds STEP-1 (mask primitive). The downstream per-`S`
//! integrand reconcile and the H1 collapse live in the sibling
//! `boolean_analysis_kkl_dualhc_h1.rs` once landed; STEP 1 is reusable in
//! isolation. NOT wired into the always-on `init_boolean_analysis` aggregate
//! (reachable via `init_boolean_analysis_kkl_band_reconcile`). Idempotent.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the band-mask reconcile.
struct BandReconcileConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_ble: Expr,
    bool_not: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    ind: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    u1: Level,
}

impl BandReconcileConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_ble: k("Nat.ble"),
            bool_not: k("Bool.not"),
            rat_mul: k("Rat.mul"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    /// `Nat.ble a b`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    /// `Bool.not b`.
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// `@Eq Bool a b`.
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), a, b],
        )
    }
    /// `@Eq.refl Bool a`.
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.u1.clone()]),
            [self.bool_.clone(), a],
        )
    }
    /// The reconcile goal at `(m, k)`:
    /// `Bool.not (Nat.ble (succ k) m) = Nat.ble m k`.
    fn goal_at(&self, m: &Expr, k: &Expr) -> Expr {
        self.eq_bool(
            self.bnot(self.ble(self.succ(k.clone()), m.clone())),
            self.ble(m.clone(), k.clone()),
        )
    }

    // ── mask-swap (subsetSum-level) helpers ──────────────────────────────────
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `@Eq Rat a b`.
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    /// `@Eq.symm.{1} Bool a b h : b = a`.
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.bool_.clone(), a, b, h],
        )
    }
    /// `@congrArg.{1,1} Bool Rat a b g h : g a = g b`.
    fn congr_bool_rat(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.bool_.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    /// `@congrArg.{1,1} Rat Rat a b g h : g a = g b`.
    fn congr_rat_rat(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
}

impl Environment {
    /// Register STEP-1's band-mask reconcile primitives. Idempotent;
    /// kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_band_reconcile(&mut self) -> Result<(), EnvError> {
        self.register_not_ble_succ_eq_ble()?;
        self.register_subset_sum_mask_ble_eq_not_ble()?;
        Ok(())
    }

    /// `BoolAnalysis.not_ble_succ_eq_ble :
    ///   ∀ (m k : Nat), Bool.not (Nat.ble (Nat.succ k) m) = Nat.ble m k`.
    /// See module docs. Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_not_ble_succ_eq_ble(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.not_ble_succ_eq_ble");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_nat_cmp()?; // Nat.ble (reducible def)

        let c = BandReconcileConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_reconcile(&c, false),
            value: build_reconcile(&c, true),
        })
    }

    /// `BoolAnalysis.subsetSum_mask_ble_eq_not_ble :
    ///   ∀ (n k : Nat) (w : HCPoint n → Rat),
    ///     @Eq Rat
    ///       (subsetSum n (fun S => ind (Nat.ble (setSizeNat n S) k) · w S))
    ///       (subsetSum n (fun S => ind (Bool.not (Nat.ble (succ k) (setSizeNat n S))) · w S))`.
    ///
    /// The low-band mask swap: RUNG A's `ble |S| k` mask equals the assembly's
    /// `not (ble (k+1) |S|)` mask under `subsetSum`, for ANY integrand `w`. The
    /// per-`S` equality is `congrArg (·w S) (congrArg ind (symm (not_ble_succ_eq_ble
    /// |S| k)))`, lifted by `subsetSum_congr`. Kernel-checked, `Constructive`,
    /// empty closure. Idempotent.
    pub fn register_subset_sum_mask_ble_eq_not_ble(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_mask_ble_eq_not_ble");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_nat_cmp()?;
        self.init_boolean_analysis()?; // ind
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_set_size_nat()?;
        self.register_not_ble_succ_eq_ble()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BandReconcileConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_mask_swap(&c, false),
            value: build_mask_swap(&c, true),
        })
    }
}

/// LHS integrand `fun S => ind (ble |S| k) · w S`.
fn ble_mask_fn(
    c: &BandReconcileConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    w: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let ss = c.set_size_nat_of(n, &s);
    let bit = c.ble(ss, k.clone());
    let body = c.mul(c.ind_of(bit), Expr::app(w.clone(), s));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// RHS integrand `fun S => ind (not (ble (k+1) |S|)) · w S`.
fn not_ble_mask_fn(
    c: &BandReconcileConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    w: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let ss = c.set_size_nat_of(n, &s);
    let bit = c.bnot(c.ble(c.succ(k.clone()), ss));
    let body = c.mul(c.ind_of(bit), Expr::app(w.clone(), s));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `subsetSum_mask_ble_eq_not_ble`.
fn build_mask_swap(c: &BandReconcileConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let w_ty = c.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());

    let lhs_fn = ble_mask_fn(c, &b, &n, &k, &w);
    let rhs_fn = not_ble_mask_fn(c, &b, &n, &k, &w);
    let lhs = c.subset_sum_of(&n, lhs_fn.clone());
    let rhs = c.subset_sum_of(&n, rhs_fn.clone());
    let concl = c.eq_rat(lhs, rhs);

    let tail = if for_value {
        // pointwise : ∀ S, ind(ble |S| k)·w S = ind(not(ble (k+1) |S|))·w S.
        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let ss = c.set_size_nat_of(&n, &s);
            let ble_lo = c.ble(ss.clone(), k.clone()); // ble |S| k
            let not_ble_hi = c.bnot(c.ble(c.succ(k.clone()), ss.clone())); // not(ble (k+1) |S|)
            let w_s = Expr::app(w.clone(), s.clone());

            // h_bool : ble |S| k = not(ble (k+1) |S|)   [symm (not_ble_succ_eq_ble |S| k)].
            let nbsb = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.not_ble_succ_eq_ble"),
                    vec![],
                ),
                [ss.clone(), k.clone()],
            ); // not(ble (succ k) |S|) = ble |S| k
            let h_bool = c.symm_bool(not_ble_hi.clone(), ble_lo.clone(), nbsb);

            // h_ind : ind(ble |S| k) = ind(not(ble (k+1) |S|))   [congrArg ind h_bool].
            let h_ind = c.congr_bool_rat(ble_lo.clone(), not_ble_hi.clone(), c.ind.clone(), h_bool);

            // h_term : ind(ble |S| k)·w S = ind(not(ble (k+1) |S|))·w S
            //   [congrArg (·w S) h_ind].
            let mul_w = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (z_id, z) = g.fresh_local(c.rat.clone());
                let body = c.mul(z, w_s.clone());
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let body = c.congr_rat_rat(c.ind_of(ble_lo), c.ind_of(not_ble_hi), mul_w, h_ind);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        // subsetSum_congr n lhs_fn rhs_fn pointwise.
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]),
            [n.clone(), lhs_fn, rhs_fn, pointwise],
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, w_id, w_ty, tail);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`).
fn build_reconcile(c: &BandReconcileConsts, for_value: bool) -> Expr {
    if !for_value {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let concl = c.goal_at(&m, &k);
        let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
        let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        return b.finish(e);
    }

    let mut b = EnvDeclBuilder::new();

    // Outer recursion on `m`: motive P m := ∀ k, goal_at m k.
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let nat_cases_on = Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]);

    // motive : fun (mm : Nat) => ∀ k, goal_at mm k
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mm_id, mm) = d.fresh_local(c.nat.clone());
        let inner = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (k_id, k) = g.fresh_local(c.nat.clone());
            let body = c.goal_at(&mm, &k);
            g.finish_child(g.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body))
        };
        d.finish_child(d.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), inner))
    };

    // BASE m=0: fun k => Eq.refl Bool (ble 0 k).
    //   LHS `not (ble (succ k) 0)` ι→ `not false` ι→ `true ≡ ble 0 k`.
    let base = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let rhs = c.ble(c.nat_zero.clone(), k);
        let body = c.refl_bool(rhs);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // STEP: fun (m')(ih : ∀ k, goal_at m' k) => fun k => Nat.casesOn k <k0> <kS>.
    //   At `succ m'` the goal is `∀ k, goal_at (succ m') k`.
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mp_id, mp) = d.fresh_local(c.nat.clone());
        // ih : ∀ k, goal_at m' k.
        let ih_ty = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (k_id, k) = g.fresh_local(c.nat.clone());
            let body = c.goal_at(&mp, &k);
            g.finish_child(g.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body))
        };
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());

        let succ_mp = c.succ(mp.clone());

        // inner : fun k => Nat.casesOn k <k0> <kS> : goal_at (succ m') k.
        let inner = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (k_id, k) = g.fresh_local(c.nat.clone());

            // casesOn motive : fun (kk : Nat) => goal_at (succ m') kk.
            let cmotive = {
                let mut e = EnvDeclBuilder::child_of(&g);
                let (kk_id, kk) = e.fresh_local(c.nat.clone());
                let body = c.goal_at(&succ_mp, &kk);
                e.finish_child(e.mk_lam(kk_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // k = 0 case: goal_at (succ m') 0.
            //   `not (ble 1 (succ m'))` ι→ `not (ble 0 m')` ι→ `not true` ι→ `false`
            //   `ble (succ m') 0` ι→ `false`.  Eq.refl Bool (ble (succ m') 0).
            let k0_case = {
                let rhs = c.ble(succ_mp.clone(), c.nat_zero.clone());
                c.refl_bool(rhs)
            };

            // k = succ k' case: fun (k' : Nat) => ih k' : goal_at (succ m') (succ k').
            //   goal `not(ble (succ(succ k'))(succ m')) = ble (succ m')(succ k')`
            //   ι→ `not(ble (succ k') m') = ble m' k'` = `ih k'`.
            let ks_case = {
                let mut e = EnvDeclBuilder::child_of(&g);
                let (kp_id, kp) = e.fresh_local(c.nat.clone());
                let body = Expr::app(ih.clone(), kp);
                e.finish_child(e.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // @Nat.casesOn.{0} cmotive k k0_case ks_case : goal_at (succ m') k.
            let body = Expr::apps(nat_cases_on.clone(), [cmotive, k, k0_case, ks_case]);
            g.finish_child(g.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
        };

        let e = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, inner);
        d.finish_child(d.mk_lam(mp_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // @Nat.rec.{0} motive base step m k.
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let rec = Expr::apps(nat_rec.clone(), [motive, base, step, m.clone()]);
    let applied = Expr::app(rec, k.clone());
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), applied);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_band_reconcile()
            .expect("init_boolean_analysis_kkl_band_reconcile");
        env.init_boolean_analysis_kkl_band_reconcile()
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
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_not_ble_succ_eq_ble_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.not_ble_succ_eq_ble");
    }

    #[test]
    fn test_subset_sum_mask_ble_eq_not_ble_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.subsetSum_mask_ble_eq_not_ble");
    }
}
