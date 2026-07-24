// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Infrastructure toward `Fin.sum_reindex_involution` (the kkl keystone).
//!
//! The kernel has NO general `Fin.sum` permutation theory. The general
//! reindex-by-involution
//!
//! ```text
//! Fin.sum_reindex_involution :
//!   ∀ (m : Nat) (σ : Fin m → Fin m),
//!     (∀ jx, σ (σ jx) = jx) → ∀ (F : Fin m → Rat),
//!       Fin.sum m (fun jx => F (σ jx)) = Fin.sum m F
//! ```
//!
//! is approached by **Route B** (orbit / strong-induction on `m`): an
//! involution partitions `Fin m` into fixed points and 2-cycles. The natural
//! recursion follows the FAITHFUL `Fin.sum` carrier, which peels the TOP index
//! (`Fin.last`) via `Fin.sum_succ`. Case-split `σ (Fin.last k)` with
//! `Fin.lastCases`:
//!
//! - **σ fixes the top** (`σ (last k) = last k`): σ restricts to an involution
//!   `σ'` on `Fin k`, and the `(k+1)`-reindex reduces to a `k`-reindex. This
//!   reduction is THIS module's deliverable, `Fin.sum_reindex_fixed_last`
//!   (fully kernel-checked, constructive, empty axiom closure).
//! - **σ swaps the top with an interior `p`**: the harder branch — see the
//!   residual note below.
//!
//! ## `Fin.sum_reindex_fixed_last` (LANDED — constructive)
//!
//! ```text
//! Fin.sum_reindex_fixed_last :
//!   ∀ (k : Nat) (σ : Fin (k+1) → Fin (k+1)) (σ' : Fin k → Fin k),
//!     (∀ j : Fin k, σ (Fin.castSucc k j) = Fin.castSucc k (σ' j))   -- coherence
//!     → σ (Fin.last k) = Fin.last k                                  -- σ fixes top
//!     → ∀ (F : Fin (k+1) → Rat),
//!         Fin.sum (k+1) (fun jx => F (σ jx))
//!           = Rat.add (Fin.sum k (fun j => F (Fin.castSucc k (σ' j))))
//!                     (F (Fin.last k))
//! ```
//!
//! **Proof.** `Fin.sum_succ (k) (F ∘ σ)` peels the top:
//!
//! ```text
//!   Fin.sum (k+1) (F ∘ σ)
//!     = Rat.add (Fin.sum k (fun j => F (σ (Fin.castSucc k j))))
//!               (F (σ (Fin.last k)))
//! ```
//!
//! Then `congr`/`congrArg` combine:
//! - the prefix via `Fin.sum_congr` with the pointwise coherence rewrite
//!   `F (σ (castSucc j)) = F (castSucc (σ' j))` (`congrArg F` of the coherence
//!   hypothesis at `j`);
//! - the top term via `congrArg F` of `σ (last k) = last k`.
//!
//! Every leaf is `Fin.sum_succ` / `Fin.sum_congr` / `congrArg` / `congr` —
//! all constructive — so the closure is empty.
//!
//! This is the inductive STEP body of Route B's fixed-point branch: the RHS is
//! `Rat.add (k-reindex of (F ∘ castSucc) by σ') (F (last k))`, so an induction
//! hypothesis on `Fin k` (collapsing the σ'-reindex) plus a re-peel by
//! `Fin.sum_succ` would close the fixed-point case of the full keystone.
//!
//! ## Residual toward the full keystone (HONEST)
//!
//! Two pieces remain unbuilt; the keystone is NOT landed and
//! `Fin.sum_reindex_involution` is NOT registered (fail-closed — no Axiom):
//!
//! 1. **The restriction map** `σ' : Fin k → Fin k` together with its coherence
//!    `∀ j, σ (castSucc j) = castSucc (σ' j)` and involutivity, derived from
//!    `σ (last) = last` + injectivity-of-involution. Constructing `σ'` requires
//!    `σ' j := Fin.mk k (Fin.val (σ (castSucc j))) hlt` where `hlt :
//!    Fin.val (σ (castSucc j)) < k` follows from `σ (castSucc j) ≠ last`
//!    (else injectivity forces `castSucc j = last`, impossible by
//!    `Fin.castSucc_ne_last`). This is a `Fin.val`-arithmetic development.
//! 2. **The 2-cycle branch** `σ (last k) = Fin.castSucc k p` (σ moves the top):
//!    peel `last` and the partner `p` together, pairing `F(last) + F(σ(last))`,
//!    and recurse on the `Fin (k-1)` rest with `last`/`p` removed — needs a
//!    general "remove one index" reindex (itself reindex-flavored).
//!
//! `Fin.sum_reindex_fixed_last` is the largest tractable, fully-verified
//! sub-lemma; the residual is the σ'-construction + the 2-cycle branch.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the reindex sub-lemmas.
struct ReindexConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_succ: Expr,
    fin_sum_congr: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    rat_add: Expr,
    eq1: Expr,
    eq_trans: Expr,
    congr: Expr,
    congr_arg: Expr,
}

impl ReindexConsts {
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
            fin_sum_congr: k("Fin.sum_congr"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            rat_add: k("Rat.add"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr: Expr::const_(Name::from_string("congr"), vec![l1.clone(), l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, m: &Expr) -> Expr {
        Expr::app(self.fin.clone(), m.clone())
    }
    fn fin_to_rat(&self, m: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(m), self.rat.clone())
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
    fn cast_succ(&self, k: &Expr, j: Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [k.clone(), j])
    }
    fn last(&self, k: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), k.clone())
    }
}

// ===========================================================================
// Fin.sum_reindex_fixed_last — the fixed-point reduction step (constructive).
// ===========================================================================
fn fixed_last_type(c: &ReindexConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);

    // σ : Fin (k+1) → Fin (k+1)
    let sigma_ty = Expr::pi(BinderInfo::Default, fin_succ.clone(), fin_succ.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());
    // σ' : Fin k → Fin k
    let sigmap_ty = Expr::pi(BinderInfo::Default, fin_k.clone(), fin_k.clone());
    let (sigmap_id, sigmap) = b.fresh_local(sigmap_ty.clone());

    // coh : ∀ j : Fin k, σ (castSucc k j) = castSucc k (σ' j)
    let coh = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = hb.fresh_local(fin_k.clone());
        let lhs = Expr::app(sigma.clone(), c.cast_succ(&k, j.clone()));
        let rhs = c.cast_succ(&k, Expr::app(sigmap.clone(), j.clone()));
        let body = Expr::apps(c.eq1.clone(), [fin_succ.clone(), lhs, rhs]);
        hb.finish_child(hb.mk_pi(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let (coh_id, _coh) = b.fresh_local(coh.clone());

    // hfix : σ (last k) = last k
    let hfix = {
        let lhs = Expr::app(sigma.clone(), c.last(&k));
        Expr::apps(c.eq1.clone(), [fin_succ.clone(), lhs, c.last(&k)])
    };
    let (hfix_id, _hfix) = b.fresh_local(hfix.clone());

    // F : Fin (k+1) → Rat
    let f_ty = c.fin_to_rat(&succ_k);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    // lhs : Fin.sum (k+1) (fun jx => F (σ jx))
    let reindexed = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = rb.fresh_local(fin_succ.clone());
        let body = Expr::app(f.clone(), Expr::app(sigma.clone(), jx.clone()));
        rb.finish_child(rb.mk_lam(jx_id, BinderInfo::Default, fin_succ.clone(), body))
    };
    let lhs = c.sum(&succ_k, &reindexed);

    // rhs : Rat.add (Fin.sum k (fun j => F (castSucc k (σ' j)))) (F (last k))
    let prefix_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        let body = Expr::app(
            f.clone(),
            c.cast_succ(&k, Expr::app(sigmap.clone(), j.clone())),
        );
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let rhs = c.add(c.sum(&k, &prefix_fn), Expr::app(f.clone(), c.last(&k)));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    let e = b.mk_pi(hfix_id, BinderInfo::Default, hfix, e);
    let e = b.mk_pi(coh_id, BinderInfo::Default, coh, e);
    let e = b.mk_pi(sigmap_id, BinderInfo::Default, sigmap_ty, e);
    let e = b.mk_pi(sigma_id, BinderInfo::Default, sigma_ty, e);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e))
}

fn fixed_last_value(c: &ReindexConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);

    let sigma_ty = Expr::pi(BinderInfo::Default, fin_succ.clone(), fin_succ.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());
    let sigmap_ty = Expr::pi(BinderInfo::Default, fin_k.clone(), fin_k.clone());
    let (sigmap_id, sigmap) = b.fresh_local(sigmap_ty.clone());

    let coh = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = hb.fresh_local(fin_k.clone());
        let lhs = Expr::app(sigma.clone(), c.cast_succ(&k, j.clone()));
        let rhs = c.cast_succ(&k, Expr::app(sigmap.clone(), j.clone()));
        let body = Expr::apps(c.eq1.clone(), [fin_succ.clone(), lhs, rhs]);
        hb.finish_child(hb.mk_pi(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let (coh_id, coh_h) = b.fresh_local(coh.clone());

    let hfix_ty = {
        let lhs = Expr::app(sigma.clone(), c.last(&k));
        Expr::apps(c.eq1.clone(), [fin_succ.clone(), lhs, c.last(&k)])
    };
    let (hfix_id, hfix_h) = b.fresh_local(hfix_ty.clone());

    let f_ty = c.fin_to_rat(&succ_k);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    // The reindexed summand: fun jx => F (σ jx).
    let reindexed = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = rb.fresh_local(fin_succ.clone());
        let body = Expr::app(f.clone(), Expr::app(sigma.clone(), jx.clone()));
        rb.finish_child(rb.mk_lam(jx_id, BinderInfo::Default, fin_succ.clone(), body))
    };

    // ── step1 : Fin.sum (k+1) reindexed
    //              = Rat.add (Fin.sum k peeled) (reindexed (last k))
    //   via Fin.sum_succ k reindexed.
    //   peeled := fun j : Fin k => reindexed (castSucc k j)
    //           ≡ fun j => F (σ (castSucc k j))   (β)
    let peeled = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        let body = Expr::app(
            f.clone(),
            Expr::app(sigma.clone(), c.cast_succ(&k, j.clone())),
        );
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let reindexed_last = Expr::app(f.clone(), Expr::app(sigma.clone(), c.last(&k)));
    let mid = c.add(c.sum(&k, &peeled), reindexed_last.clone());
    // step1 : Fin.sum (k+1) reindexed = mid
    let step1 = Expr::apps(c.fin_sum_succ.clone(), [k.clone(), reindexed.clone()]);
    let lhs_top = c.sum(&succ_k, &reindexed);

    // target prefix function: fun j => F (castSucc k (σ' j))
    let prefix_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        let body = Expr::app(
            f.clone(),
            c.cast_succ(&k, Expr::app(sigmap.clone(), j.clone())),
        );
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };

    // ── leg_prefix : Fin.sum k peeled = Fin.sum k prefix_fn
    //   via Fin.sum_congr k peeled prefix_fn pw, where
    //     pw : ∀ j, peeled j = prefix_fn j
    //        := fun j => congrArg F (coh_h j)
    //   peeled j   ≡ F (σ (castSucc k j))         (β)
    //   prefix_fn j ≡ F (castSucc k (σ' j))        (β)
    //   coh_h j     : σ (castSucc k j) = castSucc k (σ' j)
    let pw = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        // arguments of congrArg.{1,1}: A=Fin(k+1), B=Rat, a, b, f=F, h
        let a_pt = Expr::app(sigma.clone(), c.cast_succ(&k, j.clone()));
        let b_pt = c.cast_succ(&k, Expr::app(sigmap.clone(), j.clone()));
        let h_pt = Expr::app(coh_h.clone(), j.clone());
        let body = Expr::apps(
            c.congr_arg.clone(),
            [fin_succ.clone(), c.rat.clone(), a_pt, b_pt, f.clone(), h_pt],
        );
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let leg_prefix = Expr::apps(
        c.fin_sum_congr.clone(),
        [k.clone(), peeled.clone(), prefix_fn.clone(), pw],
    );

    // ── leg_top : reindexed (last k) = F (last k)
    //   reindexed (last k) ≡ F (σ (last k))    (β)
    //   := congrArg F hfix_h
    let leg_top = {
        let a_pt = Expr::app(sigma.clone(), c.last(&k));
        let b_pt = c.last(&k);
        Expr::apps(
            c.congr_arg.clone(),
            [
                fin_succ.clone(),
                c.rat.clone(),
                a_pt,
                b_pt,
                f.clone(),
                hfix_h.clone(),
            ],
        )
    };

    // ── step2 : mid = Rat.add (Fin.sum k prefix_fn) (F (last k))
    //   via congr (congrArg Rat.add leg_prefix) leg_top.
    let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let sum_peeled = c.sum(&k, &peeled);
    let sum_prefix = c.sum(&k, &prefix_fn);
    let congr_add = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            rat_to_rat,
            sum_peeled.clone(),
            sum_prefix.clone(),
            c.rat_add.clone(),
            leg_prefix,
        ],
    );
    let f_last = Expr::app(f.clone(), c.last(&k));
    let step2 = Expr::apps(
        c.congr.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            Expr::app(c.rat_add.clone(), sum_peeled.clone()),
            Expr::app(c.rat_add.clone(), sum_prefix.clone()),
            reindexed_last.clone(),
            f_last.clone(),
            congr_add,
            leg_top,
        ],
    );
    let rhs_final = c.add(sum_prefix, f_last);

    // chain : lhs_top = mid = rhs_final
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.rat.clone(), lhs_top, mid, rhs_final, step1, step2],
    );

    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
    let e = b.mk_lam(hfix_id, BinderInfo::Default, hfix_ty, e);
    let e = b.mk_lam(coh_id, BinderInfo::Default, coh, e);
    let e = b.mk_lam(sigmap_id, BinderInfo::Default, sigmap_ty, e);
    let e = b.mk_lam(sigma_id, BinderInfo::Default, sigma_ty, e);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `Fin.sum_reindex_fixed_last` — the fixed-point reduction step of
    /// the Route-B involution-reindex induction (see module docs). A
    /// kernel-checked constructive Theorem with empty admitted-axiom closure.
    /// Idempotent.
    pub(crate) fn register_fin_sum_reindex_fixed_last(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_reindex_fixed_last");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ
        {
            use super::nn_verify_fin_sum::FinSumConsts;
            let fc = FinSumConsts::new();
            self.register_fin_sum_congr(&fc)?; // Fin.sum_congr
        }

        let c = ReindexConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: fixed_last_type(&c),
            value: fixed_last_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_reindex_fixed_last_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_reindex_fixed_last().expect("register");
        env.register_fin_sum_reindex_fixed_last()
            .expect("idempotent");

        let name = Name::from_string("Fin.sum_reindex_fixed_last");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);

        // Kernel-recheck the stored proof against its declared type.
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("fixed_last proof must kernel-check");

        // Empty admitted-axiom closure ⇒ Constructive.
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
