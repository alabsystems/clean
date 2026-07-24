// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The FIXED-point inductive STEP of `Fin.sum_reindex_involution`, fully closed
//! modulo the size-`k` induction hypothesis (which strong induction supplies).
//!
//! ```text
//! Fin.sum_reindex_fixed_step :
//!   (k : Nat) (σ : Fin (k+1) → Fin (k+1))
//!   → (∀ jx, σ (σ jx) = jx)                                   -- σ involution
//!   → (σ (Fin.last k) = Fin.last k)                           -- σ fixes top
//!   → (∀ (τ : Fin k → Fin k), (∀ j, τ (τ j) = j)
//!        → ∀ (G : Fin k → Rat), Fin.sum k (fun j => G (τ j)) = Fin.sum k G) -- IH at k
//!   → ∀ (F : Fin (k+1) → Rat),
//!       Fin.sum (k+1) (fun jx => F (σ jx)) = Fin.sum (k+1) F
//! ```
//!
//! Proof (constructive, empty admitted-axiom closure):
//! 1. `Fin.sum_reindex_fixed_last k σ σ' coh hfix F`
//!    : `Σ_{k+1}(F∘σ) = Σ_k(fun j => F (castSucc (σ' j))) + F(last)`,
//!    where `σ' := Fin.sigmaRestrict k σ hinv hfix`, `coh :=
//!    Fin.sigmaRestrict_coherence …`.
//! 2. IH at `σ'` and `G := fun j => F (castSucc k j)`:
//!    `Σ_k(fun j => G (σ' j)) = Σ_k G`, i.e.
//!    `Σ_k(fun j => F (castSucc (σ' j))) = Σ_k(fun j => F (castSucc j))`.
//!    `σ'` is an involution by `Fin.sigmaRestrict_involutive`.
//! 3. `congrArg (· + F(last))` of (2).
//! 4. `Fin.sum_succ k F` : `Σ_{k+1} F = Σ_k(F∘castSucc) + F(last)`; symm.
//! 5. chain (1)·(3)·(4.symm).
//!
//! This closes the σ-fixes-top case of the keystone. The σ-moves-top (2-cycle)
//! case is the separate, deeper branch.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FixedStepConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    rat_add: Expr,
    sigma_restrict: Expr,
    sigma_coh: Expr,
    sigma_inv: Expr,
    fixed_last: Expr,
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl FixedStepConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_succ: k("Fin.sum_succ"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            rat_add: k("Rat.add"),
            sigma_restrict: k("Fin.sigmaRestrict"),
            sigma_coh: k("Fin.sigmaRestrict_coherence"),
            sigma_inv: k("Fin.sigmaRestrict_involutive"),
            fixed_last: k("Fin.sum_reindex_fixed_last"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn sum(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f.clone()])
    }
    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [x, y])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn cast_succ(&self, k: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [k.clone(), j.clone()])
    }
    fn last(&self, k: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), k.clone())
    }

    /// The IH type at `k`:
    /// `∀ (τ : Fin k → Fin k), (∀ j, τ (τ j) = j) → ∀ G, Σ_k (G∘τ) = Σ_k G`.
    fn ih_type(&self, parent: &EnvDeclBuilder, k: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_k = self.fin_of(k);
        let tau_ty = Expr::pi(BinderInfo::Default, fin_k.clone(), fin_k.clone());
        let (tau_id, tau) = d.fresh_local(tau_ty.clone());
        // hinv τ : ∀ j, τ (τ j) = j
        let hinv = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (j_id, j) = e.fresh_local(fin_k.clone());
            let ttj = Expr::app(tau.clone(), Expr::app(tau.clone(), j.clone()));
            let body = Expr::apps(self.eq1.clone(), [fin_k.clone(), ttj, j.clone()]);
            e.finish_child(e.mk_pi(j_id, BinderInfo::Default, fin_k.clone(), body))
        };
        let (hinv_id, _hinv) = d.fresh_local(hinv.clone());
        // ∀ G, Σ_k (fun j => G (τ j)) = Σ_k G
        let g_ty = self.fin_to_rat(k);
        let (g_id, g) = d.fresh_local(g_ty.clone());
        let reindexed = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (j_id, j) = e.fresh_local(fin_k.clone());
            let body = Expr::app(g.clone(), Expr::app(tau.clone(), j.clone()));
            e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
        };
        let concl = self.eq_rat(self.sum(k, &reindexed), self.sum(k, &g));
        let r = d.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
        let r = d.mk_pi(hinv_id, BinderInfo::Default, hinv, r);
        d.finish_child(d.mk_pi(tau_id, BinderInfo::Default, tau_ty, r))
    }
}

/// Shared prefix: `k, σ, hinv, hfix, ihk`. Returns builder + fvars/types.
struct StepPrefix {
    b: EnvDeclBuilder,
    k: Expr,
    k_id: crate::expr::FVarId,
    sigma: Expr,
    sigma_id: crate::expr::FVarId,
    sigma_ty: Expr,
    hinv: Expr,
    hinv_id: crate::expr::FVarId,
    hinv_ty: Expr,
    hfix: Expr,
    hfix_id: crate::expr::FVarId,
    hfix_ty: Expr,
    ihk: Expr,
    ihk_id: crate::expr::FVarId,
    ihk_ty: Expr,
    fin_succ: Expr,
    fin_k: Expr,
    nat: Expr,
}

fn make_step_prefix(c: &FixedStepConsts) -> StepPrefix {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);

    let sigma_ty = Expr::pi(BinderInfo::Default, fin_succ.clone(), fin_succ.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());

    let hinv_ty = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = hb.fresh_local(fin_succ.clone());
        let ssjx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), jx.clone()));
        let body = Expr::apps(c.eq1.clone(), [fin_succ.clone(), ssjx, jx.clone()]);
        hb.finish_child(hb.mk_pi(jx_id, BinderInfo::Default, fin_succ.clone(), body))
    };
    let (hinv_id, hinv) = b.fresh_local(hinv_ty.clone());

    let hfix_ty = Expr::apps(
        c.eq1.clone(),
        [
            fin_succ.clone(),
            Expr::app(sigma.clone(), c.last(&k)),
            c.last(&k),
        ],
    );
    let (hfix_id, hfix) = b.fresh_local(hfix_ty.clone());

    let ihk_ty = c.ih_type(&b, &k);
    let (ihk_id, ihk) = b.fresh_local(ihk_ty.clone());

    StepPrefix {
        b,
        k,
        k_id,
        sigma,
        sigma_id,
        sigma_ty,
        hinv,
        hinv_id,
        hinv_ty,
        hfix,
        hfix_id,
        hfix_ty,
        ihk,
        ihk_id,
        ihk_ty,
        fin_succ,
        fin_k,
        nat: c.nat.clone(),
    }
}

fn close_step_prefix(p: &StepPrefix, body: Expr, pi: bool) -> Expr {
    let bind = |id, ty: Expr, inner: Expr| -> Expr {
        if pi {
            p.b.mk_pi(id, BinderInfo::Default, ty, inner)
        } else {
            p.b.mk_lam(id, BinderInfo::Default, ty, inner)
        }
    };
    let e = bind(p.ihk_id, p.ihk_ty.clone(), body);
    let e = bind(p.hfix_id, p.hfix_ty.clone(), e);
    let e = bind(p.hinv_id, p.hinv_ty.clone(), e);
    let e = bind(p.sigma_id, p.sigma_ty.clone(), e);
    let e = bind(p.k_id, p.nat.clone(), e);
    p.b.finish(e)
}

fn fixed_step_type(c: &FixedStepConsts) -> Expr {
    let mut p = make_step_prefix(c);
    let succ_k = c.succ(&p.k);
    let f_ty = c.fin_to_rat(&succ_k);
    let (f_id, f) = p.b.fresh_local(f_ty.clone());
    let reindexed = {
        let mut d = EnvDeclBuilder::child_of(&p.b);
        let (jx_id, jx) = d.fresh_local(p.fin_succ.clone());
        let body = Expr::app(f.clone(), Expr::app(p.sigma.clone(), jx.clone()));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, p.fin_succ.clone(), body))
    };
    let concl = c.eq_rat(c.sum(&succ_k, &reindexed), c.sum(&succ_k, &f));
    let body = p.b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    close_step_prefix(&p, body, true)
}

fn fixed_step_value(c: &FixedStepConsts) -> Expr {
    let mut p = make_step_prefix(c);
    let succ_k = c.succ(&p.k);
    let f_ty = c.fin_to_rat(&succ_k);
    let (f_id, f) = p.b.fresh_local(f_ty.clone());

    // σ' := Fin.sigmaRestrict k σ hinv hfix
    let sigma_prime = Expr::apps(
        c.sigma_restrict.clone(),
        [p.k.clone(), p.sigma.clone(), p.hinv.clone(), p.hfix.clone()],
    );
    // coh := Fin.sigmaRestrict_coherence k σ hinv hfix : ∀ j, σ(castSucc j)=castSucc(σ' j)
    let coh = Expr::apps(
        c.sigma_coh.clone(),
        [p.k.clone(), p.sigma.clone(), p.hinv.clone(), p.hfix.clone()],
    );
    // hsp_inv := Fin.sigmaRestrict_involutive k σ hinv hfix : ∀ j, σ'(σ' j)=j
    let hsp_inv = Expr::apps(
        c.sigma_inv.clone(),
        [p.k.clone(), p.sigma.clone(), p.hinv.clone(), p.hfix.clone()],
    );

    // reindexed := fun jx => F (σ jx)
    let reindexed = {
        let mut d = EnvDeclBuilder::child_of(&p.b);
        let (jx_id, jx) = d.fresh_local(p.fin_succ.clone());
        let body = Expr::app(f.clone(), Expr::app(p.sigma.clone(), jx.clone()));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, p.fin_succ.clone(), body))
    };
    let lhs = c.sum(&succ_k, &reindexed);

    // prefix_fn := fun j : Fin k => F (castSucc k (σ' j))   [fixed_last's RHS prefix]
    let prefix_fn = {
        let mut d = EnvDeclBuilder::child_of(&p.b);
        let (j_id, j) = d.fresh_local(p.fin_k.clone());
        let body = Expr::app(
            f.clone(),
            c.cast_succ(&p.k, &Expr::app(sigma_prime.clone(), j.clone())),
        );
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, p.fin_k.clone(), body))
    };
    // cast_fn := fun j : Fin k => F (castSucc k j)   [= G in IH, and sum_succ's f∘castSucc]
    let cast_fn = {
        let mut d = EnvDeclBuilder::child_of(&p.b);
        let (j_id, j) = d.fresh_local(p.fin_k.clone());
        let body = Expr::app(f.clone(), c.cast_succ(&p.k, &j));
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, p.fin_k.clone(), body))
    };
    let f_last = Expr::app(f.clone(), c.last(&p.k));
    let sum_prefix = c.sum(&p.k, &prefix_fn);
    let sum_cast = c.sum(&p.k, &cast_fn);
    let mid_a = c.add(sum_prefix.clone(), f_last.clone()); // fixed_last's RHS

    // step1 : lhs = mid_a   [Fin.sum_reindex_fixed_last k σ σ' coh hfix F]
    let step1 = Expr::apps(
        c.fixed_last.clone(),
        [
            p.k.clone(),
            p.sigma.clone(),
            sigma_prime.clone(),
            coh,
            p.hfix.clone(),
            f.clone(),
        ],
    );

    // ih_app := ihk σ' hsp_inv cast_fn
    //   : Fin.sum k (fun j => cast_fn (σ' j)) = Fin.sum k cast_fn.
    //   `fun j => cast_fn (σ' j)` ≡ `fun j => F (castSucc (σ' j))` = prefix_fn (β/def-eq).
    let ih_app = Expr::apps(
        p.ihk.clone(),
        [sigma_prime.clone(), hsp_inv, cast_fn.clone()],
    );
    // ih_app : Fin.sum k (fun j => cast_fn (σ' j)) = sum_cast.
    // The LHS is def-eq to sum_prefix; we present it as sum_prefix via congrArg below.
    let reidx_cast = {
        let mut d = EnvDeclBuilder::child_of(&p.b);
        let (j_id, j) = d.fresh_local(p.fin_k.clone());
        let body = Expr::app(cast_fn.clone(), Expr::app(sigma_prime.clone(), j.clone()));
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, p.fin_k.clone(), body))
    };
    let sum_reidx_cast = c.sum(&p.k, &reidx_cast);

    // step2 : mid_a = Rat.add sum_cast f_last
    //   := congrArg (fun X => Rat.add X f_last) ih_app, but ih_app's LHS is
    //   sum_reidx_cast (def-eq to sum_prefix). We lift via congrArg (· + f_last).
    let add_flip = {
        let mut d = EnvDeclBuilder::child_of(&p.b);
        let (x_id, x) = d.fresh_local(c.rat.clone());
        let body = c.add(x.clone(), f_last.clone());
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // congrArg add_flip ih_app : Rat.add sum_reidx_cast f_last = Rat.add sum_cast f_last.
    // Rat.add sum_reidx_cast f_last ≡ mid_a (sum_reidx_cast ≡ sum_prefix def-eq).
    let mid_b = c.add(sum_cast.clone(), f_last.clone());
    let step2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            sum_reidx_cast.clone(),
            sum_cast.clone(),
            add_flip,
            ih_app,
        ],
    );
    // step2 : Rat.add sum_reidx_cast f_last = mid_b. By def-eq the LHS is mid_a.

    // step3 : Fin.sum (k+1) F = mid_b  [Fin.sum_succ k F]
    let rhs_total = c.sum(&succ_k, &f);
    let sum_succ = Expr::apps(c.fin_sum_succ.clone(), [p.k.clone(), f.clone()]);
    // sum_succ : rhs_total = Rat.add (Fin.sum k (f∘castSucc)) (F (last k)) = mid_b (def-eq).
    // symm : mid_b = rhs_total
    let sum_succ_sym = Expr::apps(
        c.eq_symm.clone(),
        [c.rat.clone(), rhs_total.clone(), mid_b.clone(), sum_succ],
    );

    // chain: lhs =(step1) mid_a ≡ (LHS of step2) ; step2 : … = mid_b ; sum_succ_sym : mid_b = rhs_total
    //   step1 : lhs = mid_a   (mid_a ≡ Rat.add sum_reidx_cast f_last, the LHS of step2)
    let t1 = Expr::apps(
        c.eq_trans.clone(),
        [
            c.rat.clone(),
            lhs.clone(),
            mid_a.clone(),
            mid_b.clone(),
            step1,
            step2,
        ],
    );
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.rat.clone(), lhs, mid_b, rhs_total, t1, sum_succ_sym],
    );

    let body = p.b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
    close_step_prefix(&p, body, false)
}

impl Environment {
    /// Register `Fin.sum_reindex_fixed_step` — the σ-fixes-top inductive step of
    /// the keystone, closed modulo the size-`k` IH. Constructive, empty axiom
    /// closure. Idempotent.
    pub(crate) fn register_fin_sum_reindex_fixed_step(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_reindex_fixed_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ
        self.register_fin_sum_reindex_fixed_last()?; // Fin.sum_reindex_fixed_last
        self.register_fin_sigma_restrict()?; // σ' restriction bundle

        let c = FixedStepConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: fixed_step_type(&c),
            value: fixed_step_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_reindex_fixed_step_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_reindex_fixed_step().expect("register");
        env.register_fin_sum_reindex_fixed_step()
            .expect("idempotent");

        let name = Name::from_string("Fin.sum_reindex_fixed_step");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("fixed_step must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
