// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `IsCauchy (dyadicApproxNN x)` (Stage B3, sqrt run #4,
//! rung 6 CAPSTONE).
//!
//! # Why this module exists
//!
//! This closes rung 6 of plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5: the scaled dyadic
//! approximation, lifted to a nonneg-rational sequence
//! `dyadicApproxNN x n := NNRat.ofRat (dyadicApprox x n) (zero_le_dyadicApprox x n)`,
//! is a genuine Cauchy sequence in the `NNReal.IsCauchy` sense. This is the
//! property `NNReal.CauSeq.mk` consumes to lift the dyadic approximation into
//! `NNReal.CauSeq` (rung 8).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.dyadicApproxNN : Rat → Nat → NNRat`   (reducible Def)
//! - `NNReal.dyadicApprox_isCauchy : ∀ x, NNReal.IsCauchy (Rat.dyadicApproxNN x)`
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof
//!
//! `NNRat.val (dyadicApproxNN x k) ≡ dyadicApprox x k =: a_k` (defeq: `NNRat.val`
//! / `NNRat.ofRat` are reducible `Subtype.val`/`Subtype.mk`, so the projection
//! ι-reduces). For `ε > 0`, `Rat.exists_inv_two_pow_lt ε` gives `N` with
//! `inv(2^N) < ε`. Witness `N`. For `m, n ≥ N`, each conjunct `a_i < a_j + ε`
//! (for `(i,j) ∈ {(m,n),(n,m)}`) is built ANCHORED AT N:
//!   `a_i ≤ a_N + inv(2^N)`  (`dyadicApprox_le_add_inv_of_le … N i`)
//!   `a_N + inv(2^N) ≤ a_j + inv(2^N)`  (`add_le_add_right` of `dyadicApprox_mono N j`)
//!   ⟹ `a_i ≤ a_j + inv(2^N)`  (`le_trans`)
//!   `a_j + inv(2^N) < a_j + ε`  (`add_lt_add_left` of `inv(2^N) < ε`)
//!   ⟹ `a_i < a_j + ε`  (`lt_of_le_of_lt`).
//!
//! # Universe note
//!
//! `Exists`/`Exists.intro`/`Exists.elim` over `Nat : Sort 1` are universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the dyadic `IsCauchy` capstone.
pub(crate) struct IsCauchyConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_inv: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    nnrat: Expr,
    nnrat_of_rat: Expr,
    rat_dyadic_approx: Expr,
    rat_zero_le_dyadic_approx: Expr,
    rat_dyadic_approxnn: Expr,
    nnreal_is_cauchy: Expr,
    rat_exists_inv_two_pow_lt: Expr,
    rat_dyadic_mono: Expr,
    rat_dyadic_le_add_inv_of_le: Expr,
    rat_add_le_add_right: Expr,
    rat_add_lt_add_left: Expr,
    rat_le_trans: Expr,
    rat_lt_of_le_of_lt: Expr,
    and_c: Expr,
    and_intro: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
}

impl IsCauchyConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_le: k("Nat.le"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_inv: k("Rat.inv"),
            #[cfg(test)]
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            nnrat: k("NNRat"),
            nnrat_of_rat: k("NNRat.ofRat"),
            rat_dyadic_approx: k("Rat.dyadicApprox"),
            rat_zero_le_dyadic_approx: k("Rat.zero_le_dyadicApprox"),
            rat_dyadic_approxnn: k("Rat.dyadicApproxNN"),
            nnreal_is_cauchy: k("NNReal.IsCauchy"),
            rat_exists_inv_two_pow_lt: k("Rat.exists_inv_two_pow_lt"),
            rat_dyadic_mono: k("Rat.dyadicApprox_mono"),
            rat_dyadic_le_add_inv_of_le: k("Rat.dyadicApprox_le_add_inv_of_le"),
            rat_add_le_add_right: k("Rat.add_le_add_right"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_le_trans: k("Rat.le_trans"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn iv(&self, n: Expr) -> Expr {
        self.inv(self.ofnat(self.npow2(n)))
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    fn add_le_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add_right.clone(), [a, b, cc, h])
    }
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, h1, h2])
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    /// `dyadicApprox_mono x p q h : a_p ≤ a_q`.
    fn mono(&self, x: &Expr, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_mono.clone(), [x.clone(), p, q, h])
    }
    /// `dyadicApprox_le_add_inv_of_le x p q h : a_q ≤ a_p + inv(2^p)`.
    fn le_add_inv_of_le(&self, x: &Expr, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.rat_dyadic_le_add_inv_of_le.clone(),
            [x.clone(), p, q, h],
        )
    }

    /// Build the conjunct `a_i < a_j + ε`, anchored at `cap` (= N), given the
    /// witnesses `hi : N ≤ i`, `hj : N ≤ j` and `hlt : inv(2^N) < ε`.
    #[allow(clippy::too_many_arguments)]
    fn conjunct(
        &self,
        x: &Expr,
        cap: &Expr,
        eps: &Expr,
        i: &Expr,
        j: &Expr,
        hi: Expr,
        hj: Expr,
        hlt: Expr,
    ) -> Expr {
        let a_i = self.approx(x, i.clone());
        let a_j = self.approx(x, j.clone());
        let a_cap = self.approx(x, cap.clone());
        let iv_cap = self.iv(cap.clone());
        // h1 : a_i ≤ a_N + inv(2^N).
        let h1 = self.le_add_inv_of_le(x, cap.clone(), i.clone(), hi);
        // hmono : a_N ≤ a_j.
        let hmono = self.mono(x, cap.clone(), j.clone(), hj);
        // h2 : a_N + inv(2^N) ≤ a_j + inv(2^N).
        let h2 = self.add_le_add_right(a_cap.clone(), a_j.clone(), iv_cap.clone(), hmono);
        // h3 : a_i ≤ a_j + inv(2^N).
        let a_cap_plus_iv = self.add(a_cap.clone(), iv_cap.clone());
        let a_j_plus_iv = self.add(a_j.clone(), iv_cap.clone());
        let h3 = self.le_trans(a_i.clone(), a_cap_plus_iv, a_j_plus_iv.clone(), h1, h2);
        // h4 : a_j + inv(2^N) < a_j + ε.
        let a_j_plus_eps = self.add(a_j.clone(), eps.clone());
        let h4 = self.add_lt_add_left(iv_cap.clone(), eps.clone(), a_j.clone(), hlt);
        // lt_of_le_of_lt a_i (a_j+inv(2^N)) (a_j+ε) h3 h4 : a_i < a_j + ε.
        self.lt_of_le_of_lt(a_i, a_j_plus_iv, a_j_plus_eps, h3, h4)
    }
}

impl Environment {
    /// Register `Rat.dyadicApproxNN` + `NNReal.dyadicApprox_isCauchy`.
    /// Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_iscauchy(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_exists()?;
        self.init_nat()?;
        self.init_algebra_nnreal_cauchy()?; // NNReal.IsCauchy, NNRat
        self.init_algebra_nnreal_sqrt_seq()?; // dyadicApprox, zero_le_dyadicApprox
        self.init_algebra_nnreal_sqrt_cauchy_le()?; // mono, le_add_inv_of_le
        self.init_algebra_rat_inv_dyadic_modulus()?; // exists_inv_two_pow_lt
        self.register_rat_add_lt_add_left()?; // add_lt_add_left
        self.register_rat_add_le_add_right()?;
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt
        self.init_rat_quotient_poc()?; // le_trans

        let c = IsCauchyConsts::new();
        self.register_dyadic_approxnn(&c)?;
        self.register_dyadic_approx_iscauchy(&c)?;
        Ok(())
    }

    /// `Rat.dyadicApproxNN : Rat → Nat → NNRat`
    ///   `:= fun x n => NNRat.ofRat (dyadicApprox x n) (zero_le_dyadicApprox x n)`.
    fn register_dyadic_approxnn(&mut self, c: &IsCauchyConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApproxNN");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.rat.clone(),
            Expr::pi(BinderInfo::Default, c.nat.clone(), c.nnrat.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ak = c.approx(&x, n.clone());
            let hk = Expr::apps(c.rat_zero_le_dyadic_approx.clone(), [x.clone(), n.clone()]);
            let body = Expr::apps(c.nnrat_of_rat.clone(), [ak, hk]);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.dyadicApprox_isCauchy : ∀ x, NNReal.IsCauchy (Rat.dyadicApproxNN x)`.
    fn register_dyadic_approx_iscauchy(&mut self, c: &IsCauchyConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.dyadicApprox_isCauchy");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let seq = Expr::app(c.rat_dyadic_approxnn.clone(), x.clone());
            let concl = Expr::app(c.nnreal_is_cauchy.clone(), seq);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
            let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

            // The target ∃-pred over N: fun N => ∀ m n, N≤m → N≤n →
            //   And (val(f m) < val(f n)+ε)(val(f n) < val(f m)+ε), where
            //   val(f k) ≡ a_k defeq. We build the predicate using a_k directly.
            let tgt_pred = |bb: &EnvDeclBuilder| -> Expr {
                let mut bn = EnvDeclBuilder::child_of(bb);
                let (cap_id, cap) = bn.fresh_local(c.nat.clone());
                let inner = {
                    let mut bi = EnvDeclBuilder::child_of(&bn);
                    let (m_id, m) = bi.fresh_local(c.nat.clone());
                    let (n_id, n) = bi.fresh_local(c.nat.clone());
                    let hm_ty = c.nat_le(cap.clone(), m.clone());
                    let (hm_id, _hm) = bi.fresh_local(hm_ty.clone());
                    let hn_ty = c.nat_le(cap.clone(), n.clone());
                    let (hn_id, _hn) = bi.fresh_local(hn_ty.clone());
                    let a_m = c.approx(&x, m.clone());
                    let a_n = c.approx(&x, n.clone());
                    let left = c.lt(a_m.clone(), c.add(a_n.clone(), eps.clone()));
                    let right = c.lt(a_n.clone(), c.add(a_m.clone(), eps.clone()));
                    let concl = c.and_ty(left, right);
                    let e = bi.mk_pi(hn_id, BinderInfo::Default, hn_ty, concl);
                    let e = bi.mk_pi(hm_id, BinderInfo::Default, hm_ty, e);
                    let e = bi.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
                    let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
                    bi.finish_child(e)
                };
                bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // ex_modulus : ∃ N, inv(2^N) < ε.
            let ex_mod = Expr::apps(c.rat_exists_inv_two_pow_lt.clone(), [eps.clone(), hpos]);
            // source pred: fun N => inv(2^N) < ε.
            let src_pred = {
                let mut sp = EnvDeclBuilder::child_of(&b);
                let (sn_id, sn) = sp.fresh_local(c.nat.clone());
                let body = c.lt(c.iv(sn.clone()), eps.clone());
                sp.finish_child(sp.mk_lam(sn_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let tgt_goal = Expr::apps(c.exists_c.clone(), [c.nat.clone(), tgt_pred(&b)]);

            // elim fn : (N:Nat) → (hN : inv(2^N) < ε) → ∃ N', <tgt_pred N'>.
            let elim_fn = {
                let mut eb = EnvDeclBuilder::child_of(&b);
                let (cap_id, cap) = eb.fresh_local(c.nat.clone());
                let hn_ty = c.lt(c.iv(cap.clone()), eps.clone());
                let (hn_id, h_n) = eb.fresh_local(hn_ty.clone());

                // witness proof : ∀ m n, N≤m → N≤n → And (...)(...).
                let witness = {
                    let mut wb = EnvDeclBuilder::child_of(&eb);
                    let (m_id, m) = wb.fresh_local(c.nat.clone());
                    let (n_id, n) = wb.fresh_local(c.nat.clone());
                    let hm_ty = c.nat_le(cap.clone(), m.clone());
                    let (hm_id, hm) = wb.fresh_local(hm_ty.clone());
                    let hn_ty = c.nat_le(cap.clone(), n.clone());
                    let (hn_id, hn) = wb.fresh_local(hn_ty.clone());

                    let a_m = c.approx(&x, m.clone());
                    let a_n = c.approx(&x, n.clone());
                    let left_ty = c.lt(a_m.clone(), c.add(a_n.clone(), eps.clone()));
                    let right_ty = c.lt(a_n.clone(), c.add(a_m.clone(), eps.clone()));
                    // LEFT conjunct: a_m < a_n + ε  (i=m, j=n).
                    let left =
                        c.conjunct(&x, &cap, &eps, &m, &n, hm.clone(), hn.clone(), h_n.clone());
                    // RIGHT conjunct: a_n < a_m + ε  (i=n, j=m).
                    let right = c.conjunct(&x, &cap, &eps, &n, &m, hn, hm, h_n.clone());
                    let proof = c.and_intro(left_ty, right_ty, left, right);

                    let e = wb.mk_lam(hn_id, BinderInfo::Default, hn_ty, proof);
                    let e = wb.mk_lam(hm_id, BinderInfo::Default, hm_ty, e);
                    let e = wb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
                    let e = wb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                    wb.finish_child(e)
                };

                let intro = Expr::apps(
                    c.exists_intro.clone(),
                    [c.nat.clone(), tgt_pred(&eb), cap.clone(), witness],
                );
                let e = eb.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
                let e = eb.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
                eb.finish_child(e)
            };

            // @Exists.elim Nat src_pred tgt_goal ex_mod elim_fn : tgt_goal.
            let elim = Expr::apps(
                c.exists_elim.clone(),
                [c.nat.clone(), src_pred, tgt_goal, ex_mod, elim_fn],
            );

            let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
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

    const DEFS: &[&str] = &["Rat.dyadicApproxNN"];
    const THEOREMS: &[&str] = &["NNReal.dyadicApprox_isCauchy"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_iscauchy()
            .expect("init_algebra_nnreal_sqrt_iscauchy");
        env.init_algebra_nnreal_sqrt_iscauchy().expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_iscauchy_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_dyadic_iscauchy_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
