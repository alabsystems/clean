// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The remove-one-index sum `Fin.sum_remove` and its `skipNth` coherence
//! lemmas, the deep finite-sum infrastructure for `Fin.sum_reindex_involution`
//! (kkl retirement).
//!
//! ```text
//! Fin.sum_remove : ∀ (k : Nat) (p : Fin (k+1)) (F : Fin (k+1) → Rat),
//!   @Eq Rat (Fin.sum (k+1) F)
//!           (Rat.add (F p) (Fin.sum k (fun j => F (Fin.skipNth k p j))))
//! ```
//!
//! "Pull index `p` out of a `Fin (k+1)` sum": the remaining `k` terms are
//! `F` precomposed with the order-embedding `Fin.skipNth k p` whose image is
//! everything-but-`p`.
//!
//! ## Landed here (constructive, empty axiom closure)
//!
//! - `Fin.sum_remove_last` — the `p = Fin.last k` specialization. `Fin.sum_succ`
//!   peels `F (last)`, `Fin.skipNth_castSucc_of_last` folds `skipNth (last)` to
//!   `castSucc` under `Fin.sum_congr`, and `Rat.add_comm` swaps the two pieces.
//!
//! ## Residual toward the general `Fin.sum_remove` (HONEST)
//!
//! The general lemma is `Nat.rec` on `m` with `Fin.lastCases` on `p` at the
//! step. The `last` minor is `Fin.sum_remove_last`; the `castSucc p'` minor (the
//! genuine interior case) needs the two `skipNth` reindex coherences
//!
//! ```text
//!   skipNth (m+1) (castSucc p') (last m)      = last (m+1)               -- A
//!   skipNth (m+1) (castSucc p') (castSucc j)  = castSucc (skipNth m p' j) -- B
//! ```
//!
//! plus `Rat.add_assoc` to reassociate `(F p' + Σ) + F(last)`.  Coherences A/B
//! are `Fin.eq_of_val_eq` on a `Nat.decLt`-case-split feeding `skipNth_lt` /
//! `skipNth_ge` (see `boolean_analysis_fin_sum_skip.rs`).  They are the precise
//! unbuilt frontier.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct RemoveConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    fin: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_sum: Expr,
    fin_sum_succ: Expr,
    fin_sum_congr: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    fin_last_cases: Expr, // Fin.lastCases.{0} — lcMotive returns Prop (the Eq goal)
    skip_nth: Expr,
    skip_nth_last: Expr,
    coh_a: Expr, // Fin.skipNth_castSucc_last
    coh_b: Expr, // Fin.skipNth_castSucc_castSucc
    rat_add: Expr,
    rat_add_comm: Expr,
    rat_add_assoc: Expr,
    nat_rec1: Expr, // Nat.rec.{0} — motive M : Nat → Prop
    nat_not_succ_le_zero: Expr,
    false_elim: Expr, // False.elim.{0}
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl RemoveConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let l0 = Level::zero();
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            fin: k("Fin"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            fin_sum: k("Fin.sum"),
            fin_sum_succ: k("Fin.sum_succ"),
            fin_sum_congr: k("Fin.sum_congr"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            fin_last_cases: Expr::const_(Name::from_string("Fin.lastCases"), vec![l0.clone()]),
            skip_nth: k("Fin.skipNth"),
            skip_nth_last: k("Fin.skipNth_castSucc_of_last"),
            coh_a: k("Fin.skipNth_castSucc_last"),
            coh_b: k("Fin.skipNth_castSucc_castSucc"),
            rat_add: k("Rat.add"),
            rat_add_comm: k("Rat.add_comm"),
            rat_add_assoc: k("Rat.add_assoc"),
            nat_rec1: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            nat_not_succ_le_zero: k("Nat.not_succ_le_zero"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
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
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn val(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), x.clone()])
    }
    fn skip(&self, k: &Expr, p: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.skip_nth.clone(), [k.clone(), p.clone(), j.clone()])
    }

    /// `M m := ∀ (p : Fin (m+1)) (F : Fin (m+1) → Rat),
    ///   Fin.sum (m+1) F = Rat.add (F p) (Fin.sum m (fun j => F (skipNth m p j)))`
    /// — the `Nat.rec` motive for `Fin.sum_remove` (a `Prop`-valued Π).
    fn motive_body(&self, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let m1 = self.succ(m);
        let fin_m1 = self.fin_of(&m1);
        let fin_m = self.fin_of(m);
        let (p_id, p) = d.fresh_local(fin_m1.clone());
        let f_ty = self.fin_to_rat(&m1);
        let (f_id, f) = d.fresh_local(f_ty.clone());
        // skip-prefix fn: fun j : Fin m => F (skipNth m p j)
        let skip_fn = {
            let mut rb = EnvDeclBuilder::child_of(&d);
            let (j_id, j) = rb.fresh_local(fin_m.clone());
            let body = Expr::app(f.clone(), self.skip(m, &p, &j));
            rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body))
        };
        let lhs = self.sum(&m1, &f);
        let rhs = self.add(Expr::app(f.clone(), p.clone()), self.sum(m, &skip_fn));
        let concl = self.eq_rat(lhs, rhs);
        let r = d.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
        d.finish_child(d.mk_pi(p_id, BinderInfo::Default, fin_m1, r))
    }
}

// ===========================================================================
// Fin.sum_remove_last : (k)(F : Fin (k+1) → Rat) →
//   Fin.sum (k+1) F = Rat.add (F (last k)) (Fin.sum k (fun j => F (skipNth k (last k) j)))
// ===========================================================================
fn sum_remove_last_type(c: &RemoveConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);
    let f_ty = c.fin_to_rat(&succ_k);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    let lhs = c.sum(&succ_k, &f);
    // skip-prefix fn: fun j : Fin k => F (skipNth k (last k) j)
    let skip_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        let skipped = Expr::apps(c.skip_nth.clone(), [k.clone(), c.last(&k), j.clone()]);
        let body = Expr::app(f.clone(), skipped);
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let rhs = c.add(Expr::app(f.clone(), c.last(&k)), c.sum(&k, &skip_fn));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e))
}

fn sum_remove_last_value(c: &RemoveConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);
    let f_ty = c.fin_to_rat(&succ_k);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    let f_last = Expr::app(f.clone(), c.last(&k));

    // castSucc-prefix fn: fun j : Fin k => F (castSucc k j)
    let cast_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        let body = Expr::app(f.clone(), c.cast_succ(&k, &j));
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    // skip-prefix fn: fun j : Fin k => F (skipNth k (last k) j)
    let skip_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        let skipped = Expr::apps(c.skip_nth.clone(), [k.clone(), c.last(&k), j.clone()]);
        let body = Expr::app(f.clone(), skipped);
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };

    let sum_cast = c.sum(&k, &cast_fn);
    let sum_skip = c.sum(&k, &skip_fn);

    // step1 : Fin.sum (k+1) F = Rat.add (Fin.sum k cast_fn) (F last)   [Fin.sum_succ]
    let lhs = c.sum(&succ_k, &f);
    let mid1 = c.add(sum_cast.clone(), f_last.clone());
    let step1 = Expr::apps(c.fin_sum_succ.clone(), [k.clone(), f.clone()]);

    // step2 : Rat.add (Fin.sum k cast_fn) (F last) = Rat.add (F last) (Fin.sum k cast_fn)  [add_comm]
    let mid2 = c.add(f_last.clone(), sum_cast.clone());
    let step2 = Expr::apps(c.rat_add_comm.clone(), [sum_cast.clone(), f_last.clone()]);

    // leg_sum : Fin.sum k skip_fn = Fin.sum k cast_fn   [Fin.sum_congr]
    //   pw j : skip_fn j = cast_fn j := congrArg F (skipNth_castSucc_of_last k j)
    let pw = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = rb.fresh_local(fin_k.clone());
        let skipped = Expr::apps(c.skip_nth.clone(), [k.clone(), c.last(&k), j.clone()]);
        let casted = c.cast_succ(&k, &j);
        // skipNth_castSucc_of_last k j : skipNth k (last k) j = castSucc k j
        let h = Expr::apps(c.skip_nth_last.clone(), [k.clone(), j.clone()]);
        // congrArg.{1,1} (Fin (k+1)) Rat skipped casted F h : F skipped = F casted
        let body = Expr::apps(
            c.congr_arg.clone(),
            [
                fin_succ.clone(),
                c.rat.clone(),
                skipped,
                casted,
                f.clone(),
                h,
            ],
        );
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let leg_sum = Expr::apps(
        c.fin_sum_congr.clone(),
        [k.clone(), skip_fn.clone(), cast_fn.clone(), pw],
    );
    // leg_sum_sym : Fin.sum k cast_fn = Fin.sum k skip_fn
    let leg_sum_sym = Expr::apps(
        c.eq_symm.clone(),
        [c.rat.clone(), sum_skip.clone(), sum_cast.clone(), leg_sum],
    );

    // step3 : Rat.add (F last) (Fin.sum k cast_fn) = Rat.add (F last) (Fin.sum k skip_fn)
    //   := congrArg (Rat.add (F last)) leg_sum_sym
    let add_flast = Expr::app(c.rat_add.clone(), f_last.clone());
    let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let final_rhs = c.add(f_last.clone(), sum_skip.clone());
    let step3 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            sum_cast.clone(),
            sum_skip.clone(),
            add_flast,
            leg_sum_sym,
        ],
    );

    // chain: lhs = mid1 = mid2 = final_rhs
    let t12 = Expr::apps(
        c.eq_trans.clone(),
        [
            c.rat.clone(),
            lhs.clone(),
            mid1.clone(),
            mid2.clone(),
            step1,
            step2,
        ],
    );
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.rat.clone(), lhs, mid2, final_rhs, t12, step3],
    );

    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
}

include!("boolean_analysis_fin_sum_remove_general.rs");

impl Environment {
    /// Register `Fin.sum_remove_last` — the `p = Fin.last k` case of the
    /// remove-one-index sum (see module docs). Kernel-checked constructive
    /// Theorem, empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_fin_sum_remove_last(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_remove_last");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ
        self.register_rat_add_comm_proof()?; // Rat.add_comm
        self.register_fin_skip_nth_last()?; // skipNth + skipNth_castSucc_of_last
        {
            use super::nn_verify_fin_sum::FinSumConsts;
            let fc = FinSumConsts::new();
            self.register_fin_sum_congr(&fc)?; // Fin.sum_congr
        }

        let c = RemoveConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sum_remove_last_type(&c),
            value: sum_remove_last_value(&c),
        })
    }

    /// Register the GENERAL `Fin.sum_remove` (see module docs) — pull an
    /// arbitrary index `p` out of a `Fin (k+1)` sum. `Nat.rec` on the size with
    /// `Fin.lastCases` on `p`: `last` minor = `Fin.sum_remove_last`; `castSucc
    /// p'` minor = the interior assembly (IH + coherences A/B + `Fin.sum_succ` +
    /// `Rat.add_assoc`). Kernel-checked constructive Theorem, empty admitted-
    /// axiom closure. Idempotent.
    pub(crate) fn register_fin_sum_remove(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_remove");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ
        self.init_rat_field_inst()?; // Rat.add_assoc, Rat.add_zero
        self.register_rat_add_comm_proof()?; // Rat.add_comm (via sum_remove_last)
        self.register_fin_sum_remove_last()?; // Fin.sum_remove_last
        self.register_fin_last_cases()?; // Fin.lastCases
        self.register_fin_skip_coherence_a()?; // Fin.skipNth_castSucc_last
        self.register_fin_skip_coherence_b()?; // Fin.skipNth_castSucc_castSucc
        self.register_nat_not_succ_le_zero_theorem()?; // Nat.not_succ_le_zero (empty Fin 0)
        {
            use super::nn_verify_fin_sum::FinSumConsts;
            let fc = FinSumConsts::new();
            self.register_fin_sum_congr(&fc)?; // Fin.sum_congr
        }

        let c = RemoveConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sum_remove_type(&c),
            value: sum_remove_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_remove_last_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_remove_last().expect("register");
        env.register_fin_sum_remove_last().expect("idempotent");

        let name = Name::from_string("Fin.sum_remove_last");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("sum_remove_last proof must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }

    #[test]
    fn test_fin_sum_remove_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_remove().expect("register");
        env.register_fin_sum_remove().expect("idempotent");

        let name = Name::from_string("Fin.sum_remove");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("sum_remove proof must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
