// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **generic** `2^(n+1)`-cube `Fin.sum` split (S1
//! of the `hc24_core` operator induction).
//!
//! `BoolAnalysis.hcSumSplit` splits a sum whose summand is `g (hcDecode (n+1) k)`
//! — but the `hc24_core` LHS is `Fin.sum (2^(n+1)) (fun jx => pow4 (noiseFn ρ
//! (n+1) F jx))`, whose summand is a function of the *index* `jx`, NOT of a
//! decoded point. This lemma is the `hcSumSplit` route with the `hcDecode∘g`
//! wrapper stripped: it splits ANY `F : Fin (2^(n+1)) → Rat` into its `2^n`
//! low/high halves reindexed by `castP ∘ castAdd` / `castP ∘ addNat`:
//!
//! ```text
//! BoolAnalysis.finSumPow2SuccSplit : ∀ (n : Nat) (F : Fin (2^(n+1)) → Rat),
//!   @Eq Rat (Fin.sum (2^(n+1)) F)
//!           (Rat.add (Fin.sum (2^n) (fun i => F (castP (castAdd (2^n) (2^n) i))))
//!                    (Fin.sum (2^n) (fun j => F (castP (addNat  (2^n) (2^n) j)))))
//! ```
//!
//! where `castP : Fin (2^n + 2^n) → Fin (2^(n+1))` is the index transport
//! `@Eq.ndrec Nat (2^n+2^n) (fun m => Fin m) · (2^(n+1)) (Nat.pow_two_succ n).symm`.
//!
//! Route (identical to `hcSumSplit`, sans the outer `g∘hcDecode`):
//! `Fin.sum_cast` transports the `2^(n+1)` sum to a `2^n+2^n` sum along
//! `(Nat.pow_two_succ n).symm`, then `Fin.sum_split_add` splits the `2^n+2^n`
//! sum into the `castAdd` / `addNat` halves. The LOW/HIGH summands stated here
//! are δ-defeq to the split's reduced form, so `Eq.trans` of the two steps
//! inhabits the stated equality directly.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure):
//! leaves are `Fin.sum_cast`, `Fin.sum_split_add`, `Nat.pow_two_succ`, and the
//! `Eq` built-ins.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct Pc {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_add: Expr,
    two: Expr,
    fin_sum: Expr,
    rat_add: Expr,
    eq_const: Expr,     // Eq.{1}
    eq_symm1: Expr,     // Eq.symm.{1}
    eq_trans1: Expr,    // Eq.trans.{1}
    eq_ndrec_fin: Expr, // Eq.ndrec for `fun m => Fin m`
    cast_add: Expr,
    add_nat: Expr,
    fin_sum_cast: Expr,
    fin_sum_split: Expr,
    pow_two_succ: Expr,
}

impl Pc {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), nat_one);
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_succ,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            two,
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            fin_sum_cast: Expr::const_(Name::from_string("Fin.sum_cast"), vec![]),
            fin_sum_split: Expr::const_(Name::from_string("Fin.sum_split_add"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.rat.clone(), l, r])
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    /// `@Eq.ndrec Nat b (fun m => Fin m) i a e : Fin a` — transport `i : Fin b`
    /// to `Fin a` along `e : @Eq Nat b a`.
    fn cast_fin(&self, parent: &EnvDeclBuilder, b: &Expr, a: &Expr, i: &Expr, e: &Expr) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [
                self.nat.clone(),
                b.clone(),
                motive,
                i.clone(),
                a.clone(),
                e.clone(),
            ],
        )
    }
}

/// Build the type + proof of `BoolAnalysis.finSumPow2SuccSplit`.
fn build_pow2_succ_split(c: &Pc) -> (Expr, Expr) {
    // mk_half(F, idx_map): fun (i : Fin (2^n)) => F (castP (idx_map (2^n) (2^n) i))
    let mk_half =
        |parent: &EnvDeclBuilder, n: &Expr, sn: &Expr, f: &Expr, idx_map: &Expr| -> Expr {
            let mut hb = EnvDeclBuilder::child_of(parent);
            let p2n = c.pow2(n);
            let (i_id, i) = hb.fresh_local(c.fin_of(&p2n));
            let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
            let sum_pow = Expr::apps(c.nat_add.clone(), [p2n.clone(), p2n.clone()]);
            let p2sn = c.pow2(sn);
            let e_fwd = Expr::app(c.pow_two_succ.clone(), n.clone());
            let e = Expr::apps(
                c.eq_symm1.clone(),
                [c.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
            );
            let casted = c.cast_fin(&hb, &sum_pow, &p2sn, &mapped, &e);
            let body = Expr::app(f.clone(), casted);
            hb.finish_child(hb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
        };

    // concl(n, F): Fin.sum (2^(n+1)) F = Rat.add (Fin.sum (2^n) LOW) (Fin.sum (2^n) HIGH)
    let concl = |parent: &EnvDeclBuilder, n: &Expr, f: &Expr| -> (Expr, Expr) {
        let sn = c.succ(n.clone());
        let p2sn = c.pow2(&sn);
        let p2n = c.pow2(n);
        let lhs = c.sum(p2sn, f.clone());
        let low = c.sum(p2n.clone(), mk_half(parent, n, &sn, f, &c.cast_add));
        let high = c.sum(p2n, mk_half(parent, n, &sn, f, &c.add_nat));
        (lhs, c.add(low, high))
    };

    // Type: ∀ (n : Nat) (F : Fin (2^(n+1)) → Rat), Eq Rat lhs rhs
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let sn = c.succ(n.clone());
        let f_ty = c.fin_to_rat(&c.pow2(&sn));
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let (lhs, rhs) = concl(&b, &n, &f);
        let body = c.eq_rat(lhs, rhs);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, body);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    // Value: fun n F => Eq.trans (Fin.sum_cast …) (Fin.sum_split_add …)
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let sn = c.succ(n.clone());
        let p2sn = c.pow2(&sn);
        let p2n = c.pow2(&n);
        let sum_pow = Expr::apps(c.nat_add.clone(), [p2n.clone(), p2n.clone()]);
        let f_ty = c.fin_to_rat(&p2sn);
        let (f_id, f) = vb.fresh_local(f_ty.clone());

        // e_sym : 2^n+2^n = 2^(n+1)
        let e_fwd = Expr::app(c.pow_two_succ.clone(), n.clone());
        let e_sym = Expr::apps(
            c.eq_symm1.clone(),
            [c.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd.clone()],
        );

        // F' : Fin (2^n+2^n) → Rat := fun i => F (cast_fin (2^n+2^n) (2^(n+1)) i e_sym)
        let f_prime = {
            let mut fb = EnvDeclBuilder::child_of(&vb);
            let (i_id, i) = fb.fresh_local(c.fin_of(&sum_pow));
            let casted = c.cast_fin(&fb, &sum_pow, &p2sn, &i, &e_sym);
            let body = Expr::app(f.clone(), casted);
            fb.finish_child(fb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&sum_pow), body))
        };

        // step1 : Fin.sum (2^(n+1)) F = Fin.sum (2^n+2^n) F'
        let step1 = Expr::apps(
            c.fin_sum_cast.clone(),
            [p2sn.clone(), sum_pow.clone(), e_sym.clone(), f.clone()],
        );
        // step2 : Fin.sum (2^n+2^n) F' = Rat.add (Fin.sum (2^n) low') (Fin.sum (2^n) high')
        let step2 = Expr::apps(
            c.fin_sum_split.clone(),
            [p2n.clone(), p2n.clone(), f_prime.clone()],
        );

        let lhs = c.sum(p2sn.clone(), f.clone());
        let mid = c.sum(sum_pow.clone(), f_prime.clone());
        let low_prime = {
            let mut lb = EnvDeclBuilder::child_of(&vb);
            let (i_id, i) = lb.fresh_local(c.fin_of(&p2n));
            let ca = Expr::apps(c.cast_add.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
            let body = Expr::app(f_prime.clone(), ca);
            lb.finish_child(lb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2n), body))
        };
        let high_prime = {
            let mut hb = EnvDeclBuilder::child_of(&vb);
            let (j_id, j) = hb.fresh_local(c.fin_of(&p2n));
            let an = Expr::apps(c.add_nat.clone(), [p2n.clone(), p2n.clone(), j.clone()]);
            let body = Expr::app(f_prime.clone(), an);
            hb.finish_child(hb.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2n), body))
        };
        let rhs = c.add(
            c.sum(p2n.clone(), low_prime),
            c.sum(p2n.clone(), high_prime),
        );

        let composed = Expr::apps(
            c.eq_trans1.clone(),
            [c.rat.clone(), lhs, mid, rhs, step1, step2],
        );

        let lam = vb.mk_lam(f_id, BinderInfo::Default, f_ty, composed);
        let lam = vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        vb.finish(lam)
    };

    (type_, value)
}

impl Environment {
    /// Register `BoolAnalysis.finSumPow2SuccSplit` — the generic `2^(n+1)`-cube
    /// `Fin.sum` split (S1 of the `hc24_core` induction). Idempotent; axiom-free.
    pub(crate) fn register_fin_sum_pow2_succ_split(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_fin_sum()?;
        self.register_hc_sum_split_theorem()?; // Fin.sum_cast, Fin.castAdd/addNat, Fin.sum_split_add, Nat.pow_two_succ

        let name = Name::from_string("BoolAnalysis.finSumPow2SuccSplit");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pc::new();
        let (type_, value) = build_pow2_succ_split(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_pow2_succ_split_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_pow2_succ_split().expect("register");
        env.register_fin_sum_pow2_succ_split().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.finSumPow2SuccSplit");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("finSumPow2SuccSplit proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
