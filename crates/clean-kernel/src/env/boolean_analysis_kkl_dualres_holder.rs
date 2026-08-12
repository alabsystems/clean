// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3 residual, component **M-Hölder** proper:
//! the SUPPORT-restricted double Cauchy–Schwarz that discharges the `h_holder4`
//! hypothesis of `two_norm_sq_le_of_holder_chain`.
//!
//! # The theorem
//!
//! With `D x := pm(p x) − pm(q x)` (a `{0,±2}` discrete derivative),
//! `X x := ind(¬(p x == q x))` (the `{0,1}` indicator of its support, the
//! disagreement set), and `a : HCPoint n → Rat`:
//!
//! ```text
//! BoolAnalysis.deriv_holder_fourth_support :
//!   ∀ (n : Nat) (a : HCPoint n → Rat) (p q : HCPoint n → Bool),
//!     Rat.le (Rat.mul (Rat.mul l l) (Rat.mul l l))            -- ⟨a,D⟩⁴
//!            (Rat.mul f4 (Rat.mul (Rat.mul 16 cnt)            -- (Σ a⁴)·(16·cnt³)
//!                                  (Rat.mul cnt cnt)))
//! ```
//!
//! where `l := Σ_x a x · D x` (`= ⟨T_{1/9}g, g⟩` at the consumer instance),
//! `f4 := Σ_x (a x·a x)·(a x·a x)` (`= Σ a⁴ = ‖T_{1/9}g‖₄⁴`), and
//! `cnt := Σ_x X x` (`= count`). This is EXACTLY the `h_holder4 : (l·l)·(l·l) ≤
//! f4·b43` shape consumed by `two_norm_sq_le_of_holder_chain`, at `b43 = 16·cnt³`.
//!
//! # Why the support restriction is the RIGHT inequality (design §10.6)
//!
//! The abstract double-CS `subsetSum_holder_fourth` carries the cube cardinal
//! `⟨1,1⟩ = 2^n` and yields only `Inf^{5/4}` (design §10.6 point 4). The SHARP
//! `Inf^{3/2}` constant comes from restricting BOTH Cauchy–Schwarz applications
//! to the SUPPORT of `D` (size `cnt`, NOT `2^n`): because `D` vanishes off the
//! disagreement set, `⟨a,D⟩` only sees `a` there, and each CS picks up `cnt`.
//! With `W := Σ (a²·X)`:
//!
//! ```text
//!   l²  =  (Σ (a·D)·X)²  ≤  (Σ (a·D)²)·(Σ X·X)  =  (4·W)·cnt   (CS-1)
//!   W²  =  (Σ (a²)·X)²   ≤  (Σ (a²)·(a²))·(Σ X·X)  =  f4·cnt    (CS-2)
//! ```
//!
//! and `l⁴ = (l²)² ≤ ((4W)cnt)² = 16·W²·cnt² ≤ f4·(16·cnt³)` by the landed
//! `holder_quad_combine`. The masking facts are landed:
//! `subsetSum_ind_sq_eq_ind` (`Σ X·X = cnt`), `deriv_mul_ind_self` (`D·X = D`),
//! `disagree_sq_bridge` (`D·D = 4·X`), composed through `subsetSum_congr` /
//! `subsetSum_smul` and the `Rat` ring lemmas.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! Build the two CS shadows (`cs1`/`cs2` instantiated with the indicator in the
//! `v`-slot), collapse `Σ X·X → cnt`, bridge `Σ (a·D)·X → Σ a·D` and
//! `Σ (a·D)² → 4·Σ(a²·X)`, supply the three nonnegativities (`Fin.sum_nonneg`),
//! and finish with `holder_quad_combine`. Every leaf is `Constructive` with empty
//! admitted-axiom closure, so the bound is too.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the support-restricted double-CS Hölder build.
pub(super) struct HolderResConsts {
    o: OrderConsts,
    nat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    hcpoint: Expr,
    bool_t: Expr,
    fin: Expr,
    hc_decode: Expr,
    pm: Expr,
    ind: Expr,
    ind_nonneg: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    subset_sum: Expr,
    cs: Expr,
    ind_sq: Expr,
    deriv_mask: Expr,
    disagree_sq: Expr,
    ssum_congr: Expr,
    ssum_smul: Expr,
    combine: Expr,
    fin_sum_nonneg: Expr,
    mmmc: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    congr_arg: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
}

impl HolderResConsts {
    pub(super) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            o: OrderConsts::new(),
            nat: k("Nat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_t: k("Bool"),
            fin: k("Fin"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            ind_nonneg: k("BoolAnalysis.ind_nonneg"),
            bool_beq: k("Bool.beq"),
            bool_not: k("Bool.not"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            cs: k("BoolAnalysis.subsetSum_cauchy_schwarz"),
            ind_sq: k("BoolAnalysis.subsetSum_ind_sq_eq_ind"),
            deriv_mask: k("BoolAnalysis.deriv_mul_ind_self"),
            disagree_sq: k("BoolAnalysis.disagree_sq_bridge"),
            ssum_congr: k("BoolAnalysis.subsetSum_congr"),
            ssum_smul: k("BoolAnalysis.subsetSum_smul"),
            combine: k("BoolAnalysis.holder_quad_combine"),
            fin_sum_nonneg: k("Fin.sum_nonneg"),
            mmmc: k("Rat.mul_mul_mul_comm"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
        }
    }

    // ── plumbing ────────────────────────────────────────────────────────────
    pub(super) fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    pub(super) fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }
    pub(super) fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    pub(super) fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    pub(super) fn hcpoint_to_bool(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.bool_t.clone())
    }
    pub(super) fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    pub(super) fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    pub(super) fn fin_pow2(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), self.pow2(n))
    }
    pub(super) fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `Rat.mk (Int.ofNat v) 1`.
    pub(super) fn lit(&self, v: u64) -> Expr {
        let mut nk = self.nat_zero.clone();
        for _ in 0..v {
            nk = Expr::app(self.nat_succ.clone(), nk);
        }
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), nk), one_nat],
        )
    }

    // ── const-atom accessors (for the split proof module) ──────────────────
    pub(super) fn nat(&self) -> Expr {
        self.nat.clone()
    }
    pub(super) fn cs_const(&self) -> Expr {
        self.cs.clone()
    }
    pub(super) fn ind_sq_const(&self) -> Expr {
        self.ind_sq.clone()
    }
    pub(super) fn combine_const(&self) -> Expr {
        self.combine.clone()
    }
    pub(super) fn mul_comm_const(&self) -> Expr {
        self.mul_comm.clone()
    }

    // ── pointwise terms (over a local `x : HCPoint n`) ──────────────────────
    pub(super) fn deriv_at(&self, p: &Expr, q: &Expr, x: &Expr) -> Expr {
        self.o.sub(
            Expr::app(self.pm.clone(), Expr::app(p.clone(), x.clone())),
            Expr::app(self.pm.clone(), Expr::app(q.clone(), x.clone())),
        )
    }
    pub(super) fn notbeq_at(&self, p: &Expr, q: &Expr, x: &Expr) -> Expr {
        let beq = Expr::apps(
            self.bool_beq.clone(),
            [
                Expr::app(p.clone(), x.clone()),
                Expr::app(q.clone(), x.clone()),
            ],
        );
        Expr::app(self.bool_not.clone(), beq)
    }
    pub(super) fn ind_at(&self, p: &Expr, q: &Expr, x: &Expr) -> Expr {
        Expr::app(self.ind.clone(), self.notbeq_at(p, q, x))
    }
    pub(super) fn aa_at(&self, a: &Expr, x: &Expr) -> Expr {
        self.mul(
            Expr::app(a.clone(), x.clone()),
            Expr::app(a.clone(), x.clone()),
        )
    }

    // ── lambdas (HCPoint n → Rat / Bool) ────────────────────────────────────
    pub(super) fn lam_rat<F: Fn(&Self, &Expr) -> Expr>(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        body: F,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let bd = body(self, &x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, bd))
    }
    /// `fun x => ¬(p x == q x)` — the Bool predicate fed to `subsetSum_ind_sq_eq_ind`.
    pub(super) fn notbeq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr, q: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let bd = self.notbeq_at(p, q, &x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, bd))
    }
    /// `fun x => a x · D x`.
    pub(super) fn a_d_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        p: &Expr,
        q: &Expr,
    ) -> Expr {
        self.lam_rat(parent, n, |c, x| {
            c.mul(Expr::app(a.clone(), x.clone()), c.deriv_at(p, q, x))
        })
    }
    /// `fun x => X x`.
    pub(super) fn x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr, q: &Expr) -> Expr {
        self.lam_rat(parent, n, |c, x| c.ind_at(p, q, x))
    }
    /// `fun x => a x · a x`.
    pub(super) fn aa_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        self.lam_rat(parent, n, |c, x| c.aa_at(a, x))
    }
    /// `fun x => (a x·a x) · X x` — the `W` summand.
    pub(super) fn aax_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        p: &Expr,
        q: &Expr,
    ) -> Expr {
        self.lam_rat(parent, n, |c, x| c.mul(c.aa_at(a, x), c.ind_at(p, q, x)))
    }
    /// `fun x => 4·((a x·a x)·X x)` — the `4·W` (smul) summand.
    pub(super) fn four_aax_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        p: &Expr,
        q: &Expr,
    ) -> Expr {
        self.lam_rat(parent, n, |c, x| {
            c.mul(c.lit(4), c.mul(c.aa_at(a, x), c.ind_at(p, q, x)))
        })
    }
    /// `fun x => (a x·a x)·(a x·a x)` — the `f4 = Σ a⁴` summand (CS-2's RHS form).
    pub(super) fn a4_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        self.lam_rat(parent, n, |c, x| {
            let aa = c.aa_at(a, x);
            c.mul(aa.clone(), aa)
        })
    }
    /// `fun x => (a x·D x)·(a x·D x)` — the `M = Σ (aD)²` summand (CS-1's RHS form).
    pub(super) fn ad_sq_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        p: &Expr,
        q: &Expr,
    ) -> Expr {
        self.lam_rat(parent, n, |c, x| {
            let ad = c.mul(Expr::app(a.clone(), x.clone()), c.deriv_at(p, q, x));
            c.mul(ad.clone(), ad)
        })
    }
    /// `fun x => (a x·D x)·X x` — the masked inner-product summand (`Pm_l`).
    pub(super) fn adx_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        p: &Expr,
        q: &Expr,
    ) -> Expr {
        self.lam_rat(parent, n, |c, x| {
            let ad = c.mul(Expr::app(a.clone(), x.clone()), c.deriv_at(p, q, x));
            c.mul(ad, c.ind_at(p, q, x))
        })
    }
    /// `fun x => X x · X x` — CS's `Σ v²` integrand (`cntXX`).
    pub(super) fn xx_fn(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr, q: &Expr) -> Expr {
        self.lam_rat(parent, n, |c, x| {
            c.mul(c.ind_at(p, q, x), c.ind_at(p, q, x))
        })
    }

    // ── leaf proof terms ────────────────────────────────────────────────────
    pub(super) fn sq_nonneg(&self, t: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), t)
    }
    pub(super) fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    pub(super) fn ind_nonneg(&self, b: Expr) -> Expr {
        Expr::app(self.ind_nonneg.clone(), b)
    }
    /// `congrArg @Rat @Rat a₁ a₂ f h : f a₁ = f a₂`.
    pub(super) fn congr_arg(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat(), self.rat(), a1, a2, f, h],
        )
    }
    pub(super) fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mmmc.clone(), [a, b, cc, d])
    }
    pub(super) fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    pub(super) fn disagree_sq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.disagree_sq.clone(), [a, b])
    }
    pub(super) fn deriv_mask(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.deriv_mask.clone(), [a, b])
    }
    pub(super) fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, hyp: Expr) -> Expr {
        Expr::apps(self.ssum_congr.clone(), [n.clone(), g, h, hyp])
    }
    pub(super) fn ssum_smul(&self, n: &Expr, c: Expr, f: Expr) -> Expr {
        Expr::apps(self.ssum_smul.clone(), [n.clone(), c, f])
    }
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.o.symm(a, b, h)
    }
    pub(super) fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.o.trans(a, b, cc, h1, h2)
    }
    pub(super) fn subst(&self, motive: Expr, a: Expr, b: Expr, h: Expr, hm: Expr) -> Expr {
        self.o.subst(motive, a, b, h, hm)
    }
    /// `fun (z : Rat) => left·z` — congr-motive used for the `D·X` mask bridge.
    pub(super) fn lam_mul_left(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat());
        let body = self.mul(left.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat(), body))
    }
    /// `fun (z : Rat) => z·right` — congr-motive.
    pub(super) fn lam_mul_right(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat());
        let body = self.mul(z, right.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat(), body))
    }
    /// `0 ≤ subsetSum n g` via `Fin.sum_nonneg (2^n) (decoded g) (per)` where
    /// `per j : 0 ≤ g (hcDecode n j)`. Builds the decoded integrand + per-summand.
    pub(super) fn ssum_nonneg<G, P>(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        body: G,
        per_body: P,
    ) -> Expr
    where
        G: Fn(&Self, &Expr) -> Expr,
        P: Fn(&Self, &Expr) -> Expr,
    {
        let fin_p = self.fin_pow2(n);
        let dec = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = d.fresh_local(fin_p.clone());
            let x = self.hc_decode(n, &j);
            let bd = body(self, &x);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), bd))
        };
        let per = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = d.fresh_local(fin_p.clone());
            let x = self.hc_decode(n, &j);
            let bd = per_body(self, &x);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), bd))
        };
        Expr::apps(self.fin_sum_nonneg.clone(), [self.pow2(n), dec, per])
    }
}

impl Environment {
    /// Register `BoolAnalysis.deriv_holder_fourth_support` — the §9.6 M-Hölder
    /// hypothesis `(l·l)·(l·l) ≤ f4·(16·cnt³)` for the support-supported discrete
    /// derivative. Kernel-checked, `ProofQuality::Constructive`, empty admitted-
    /// axiom closure. Idempotent.
    pub fn register_deriv_holder_fourth_support(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_holder_fourth_support");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_cauchy_schwarz()?; // + Fin.sum_nonneg transitively
        self.register_subset_sum_ind_sq_eq_ind()?;
        self.register_deriv_mul_ind_self()?;
        self.register_disagree_sq_bridge()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_holder_quad_combine()?;
        self.register_ind_nonneg()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_comm_proof()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.register_rat_order_proofs()?;

        let c = HolderResConsts::new();
        let (ty, value) = super::boolean_analysis_kkl_dualres_holder_proof::build_holder_res(&c);
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
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    pub(super) fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_deriv_holder_fourth_support()
            .expect("register_deriv_holder_fourth_support");
        env
    }

    #[test]
    pub(super) fn test_holder_res_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.deriv_holder_fourth_support");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty (foundational-only), got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    pub(super) fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_deriv_holder_fourth_support().expect("first");
        env.register_deriv_holder_fourth_support()
            .expect("idempotent");
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). The support-restricted Hölder
    /// fourth-power bound is TRUE; `refute_conjecture` must NOT find a
    /// counterexample. (By hand on tribes: the SHARP edge — the support count
    /// `cnt` is the disagreement-set size, and the double CS on the support is an
    /// equality only at the dictator/parity extremes.)
    #[test]
    pub(super) fn test_holder_res_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.deriv_holder_fourth_support",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the support-restricted Hölder fourth bound is TRUE; must NOT refute"
        );
    }
}
