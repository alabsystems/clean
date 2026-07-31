// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Off-diagonal index lemmas for the FAITHFUL `Fin` carrier, used by the
//! `Fin.sum_single` proof. Real kernel-checked terms (NO `sorry`, NO axiom).
//!
//! - `Fin.castSucc_ne_last : (k : Nat) (j : Fin k) →
//!       @Eq (Fin (Nat.succ k)) (Fin.castSucc k j) (Fin.last k) → False`
//! - `Fin.last_ne_castSucc : (k : Nat) (j : Fin k) →
//!       @Eq (Fin (Nat.succ k)) (Fin.last k) (Fin.castSucc k j) → False`
//! - `Fin.castSucc_inj : (k : Nat) (a b : Fin k) →
//!       @Eq (Fin (Nat.succ k)) (Fin.castSucc k a) (Fin.castSucc k b)
//!       → @Eq (Fin k) a b`
//!
//! `Fin.castSucc k j` has `val ≡ Fin.val j < k` whereas `Fin.last k` has
//! `val ≡ k`; equating them forces `Fin.val j = k`, contradicting
//! `Fin.isLt j : Fin.val j < k` via `Nat.lt_irrefl`. Injectivity of
//! `Fin.castSucc` follows from equal `val`s + `Fin.eq_of_val_eq`.
//!
//! Axiom closure: `Fin`/`Fin.val`/`Fin.isLt`/`Fin.castSucc`/`Fin.last`/
//! `Fin.eq_of_val_eq`, `Nat`/`Nat.lt`/`Nat.lt_irrefl`, `Eq`(`.ndrec`/`.symm`),
//! `congrArg`, `False` — all axiom-free. Empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Fin.castSucc_ne_last`, `Fin.last_ne_castSucc`,
    /// `Fin.castSucc_inj`. Idempotent; axiom-free.
    pub(crate) fn register_fin_index_lemmas(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.castSucc_ne_last"))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }

        self.init_eq()?;
        self.init_nat()?;
        self.init_fin()?;
        self.init_lt()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_nat_lt_irrefl_theorem()?; // Nat.lt_irrefl (axiom-free thm)
                                                // `Fin.castSucc` / `Fin.last` via the LIGHTWEIGHT ensures (independent of
                                                // `Fin.sum`), NOT `init_fin_sum` — avoids the `Fin.sum_single`-proof
                                                // registration cycle (see `register_fin_last_cases`). Idempotent.
        {
            let c = super::nn_verify_fin_sum::FinSumConsts::new();
            self.ensure_fin_cast_succ(&c)?;
            self.ensure_fin_last(&c)?;
        }

        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let nat_lt_irrefl = Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]);

        let fin_c = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let fin_cast = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let _fin_eq_of_val = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);

        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
        // congrArg.{1,1} : {α β}{a₁ a₂ : α}(f : α → β) → a₁ = a₂ → f a₁ = f a₂
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
        // Eq.ndrec.{motive_u=0, alpha_v=1}: transport along Eq Nat, motive in Prop.
        let eq_ndrec = Expr::const_(Name::from_string("Eq.ndrec"), vec![l0.clone(), l1.clone()]);

        // helpers
        let fin_n = |n: Expr| Expr::app(fin_c.clone(), n);
        let succ = |n: Expr| Expr::app(nat_succ.clone(), n);
        let val = |n: Expr, x: Expr| Expr::apps(fin_val.clone(), [n, x]);
        let lt = |a: Expr, b: Expr| Expr::apps(nat_lt.clone(), [a, b]);
        let eq_fin = |n: Expr, l: Expr, r: Expr| Expr::apps(eq1.clone(), [fin_n(n), l, r]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [nat.clone(), l, r]);

        // ── shared core: given `ev : Fin.val (succ k) lhs = Fin.val (succ k) rhs`
        //    where one side is `castSucc k j` (val ≡ val j) and the other is
        //    `last k` (val ≡ k), produce `Nat.lt k k → False`. ──
        //
        // We build, for `castSucc_ne_last` / `last_ne_castSucc`, a proof of False
        // from the *Fin*-equality `e`. The internal val-equality is obtained by
        // `congrArg (Fin.val (succ k)) e`.

        // ─────────────────── Fin.castSucc_ne_last ───────────────────
        // (k)(j) → @Eq (Fin (succ k)) (castSucc k j) (last k) → False
        let cne_last = {
            // Type
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let (j_id, j) = b.fresh_local(fin_n(k.clone()));
                let cs = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
                let lk = Expr::app(fin_last.clone(), k.clone());
                let e_ty = eq_fin(succ(k.clone()), cs, lk);
                let (e_id, _e) = b.fresh_local(e_ty.clone());
                let r = b.mk_pi(e_id, BinderInfo::Default, e_ty, false_c.clone());
                let r = b.mk_pi(j_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };
            // Value: fun k j e =>
            //   let ev : Fin.val (succ k) (castSucc k j) = Fin.val (succ k) (last k)
            //          := congrArg (Fin.val (succ k)) e
            //        -- ≡ Eq Nat (Fin.val k j) k  (defeq)
            //   Nat.lt_irrefl k (@Eq.ndrec Nat (Fin.val k j) (fun w => Nat.lt w k)
            //                       (Fin.isLt k j) k ev)
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let (j_id, j) = b.fresh_local(fin_n(k.clone()));
                let sk = succ(k.clone());
                let cs = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
                let lk = Expr::app(fin_last.clone(), k.clone());
                let e_ty = eq_fin(sk.clone(), cs.clone(), lk.clone());
                let (e_id, e) = b.fresh_local(e_ty.clone());

                // fin_val_sk : Fin (succ k) → Nat := Fin.val (succ k)
                let fin_val_sk = Expr::app(fin_val.clone(), sk.clone());
                // ev := congrArg (Fin (succ k)) Nat cs lk (Fin.val (succ k)) e
                //     : Fin.val (succ k) cs = Fin.val (succ k) lk
                //     ≡ Eq Nat (Fin.val k j) k
                let ev = Expr::apps(
                    congr_arg.clone(),
                    [
                        fin_n(sk.clone()),
                        nat.clone(),
                        cs.clone(),
                        lk.clone(),
                        fin_val_sk,
                        e,
                    ],
                );

                // motive : Nat → Prop := fun w => Nat.lt w k
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = d.fresh_local(nat.clone());
                    let body = lt(w, k.clone());
                    d.finish_child(d.mk_lam(w_id, BinderInfo::Default, nat.clone(), body))
                };
                // base : motive (Fin.val k j) := Fin.isLt k j : Nat.lt (Fin.val k j) k
                let islt = Expr::apps(fin_islt.clone(), [k.clone(), j.clone()]);
                let val_j = val(k.clone(), j.clone());
                // @Eq.ndrec.{0,1} Nat (Fin.val k j) motive islt k ev : Nat.lt k k
                let lt_kk = Expr::apps(
                    eq_ndrec.clone(),
                    [nat.clone(), val_j, motive, islt, k.clone(), ev],
                );
                // Nat.lt_irrefl k lt_kk : False
                let body = Expr::apps(nat_lt_irrefl.clone(), [k.clone(), lt_kk]);

                let r = b.mk_lam(e_id, BinderInfo::Default, e_ty, body);
                let r = b.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };
            (ty, value)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.castSucc_ne_last"),
            level_params: vec![],
            type_: cne_last.0,
            value: cne_last.1,
        })?;

        // ─────────────────── Fin.last_ne_castSucc ───────────────────
        // (k)(j) → @Eq (Fin (succ k)) (last k) (castSucc k j) → False
        //   := fun k j e => Fin.castSucc_ne_last k j (Eq.symm e)
        let lne_cast = {
            let cne = Expr::const_(Name::from_string("Fin.castSucc_ne_last"), vec![]);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let (j_id, j) = b.fresh_local(fin_n(k.clone()));
                let cs = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
                let lk = Expr::app(fin_last.clone(), k.clone());
                let e_ty = eq_fin(succ(k.clone()), lk, cs);
                let (e_id, _e) = b.fresh_local(e_ty.clone());
                let r = b.mk_pi(e_id, BinderInfo::Default, e_ty, false_c.clone());
                let r = b.mk_pi(j_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let (j_id, j) = b.fresh_local(fin_n(k.clone()));
                let sk = succ(k.clone());
                let cs = Expr::apps(fin_cast.clone(), [k.clone(), j.clone()]);
                let lk = Expr::app(fin_last.clone(), k.clone());
                let e_ty = eq_fin(sk.clone(), lk.clone(), cs.clone());
                let (e_id, e) = b.fresh_local(e_ty.clone());
                // Eq.symm.{1} (Fin (succ k)) lk cs e : castSucc k j = last k
                let e_sym = Expr::apps(
                    eq_symm.clone(),
                    [fin_n(sk.clone()), lk.clone(), cs.clone(), e],
                );
                let body = Expr::apps(cne.clone(), [k.clone(), j.clone(), e_sym]);
                let r = b.mk_lam(e_id, BinderInfo::Default, e_ty, body);
                let r = b.mk_lam(j_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };
            (ty, value)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.last_ne_castSucc"),
            level_params: vec![],
            type_: lne_cast.0,
            value: lne_cast.1,
        })?;

        // ─────────────────── Fin.castSucc_inj ───────────────────
        // (k)(a b : Fin k) → @Eq (Fin (succ k)) (castSucc k a) (castSucc k b)
        //   → @Eq (Fin k) a b
        //   := fun k a b e =>
        //        Fin.eq_of_val_eq k a b
        //          (congrArg (Fin.val (succ k)) e : Fin.val k a = Fin.val k b)
        let cinj = {
            let eq_of_val = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let (a_id, a) = b.fresh_local(fin_n(k.clone()));
                let (bb_id, bb) = b.fresh_local(fin_n(k.clone()));
                let csa = Expr::apps(fin_cast.clone(), [k.clone(), a.clone()]);
                let csb = Expr::apps(fin_cast.clone(), [k.clone(), bb.clone()]);
                let e_ty = eq_fin(succ(k.clone()), csa, csb);
                let (e_id, _e) = b.fresh_local(e_ty.clone());
                let concl = eq_fin(k.clone(), a.clone(), bb.clone());
                let r = b.mk_pi(e_id, BinderInfo::Default, e_ty, concl);
                let r = b.mk_pi(bb_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_pi(a_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat.clone());
                let (a_id, a) = b.fresh_local(fin_n(k.clone()));
                let (bb_id, bb) = b.fresh_local(fin_n(k.clone()));
                let sk = succ(k.clone());
                let csa = Expr::apps(fin_cast.clone(), [k.clone(), a.clone()]);
                let csb = Expr::apps(fin_cast.clone(), [k.clone(), bb.clone()]);
                let e_ty = eq_fin(sk.clone(), csa.clone(), csb.clone());
                let (e_id, e) = b.fresh_local(e_ty.clone());
                let fin_val_sk = Expr::app(fin_val.clone(), sk.clone());
                // ev : Fin.val (succ k) (castSucc k a) = Fin.val (succ k) (castSucc k b)
                //    ≡ Eq Nat (Fin.val k a) (Fin.val k b)
                let ev = Expr::apps(
                    congr_arg.clone(),
                    [
                        fin_n(sk.clone()),
                        nat.clone(),
                        csa.clone(),
                        csb.clone(),
                        fin_val_sk,
                        e,
                    ],
                );
                // Annotate the expected val-equality (defeq target) for clarity.
                let _ = eq_nat(val(k.clone(), a.clone()), val(k.clone(), bb.clone()));
                // Fin.eq_of_val_eq k a b ev : Eq (Fin k) a b
                let body = Expr::apps(eq_of_val.clone(), [k.clone(), a.clone(), bb.clone(), ev]);
                let r = b.mk_lam(e_id, BinderInfo::Default, e_ty, body);
                let r = b.mk_lam(bb_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_lam(a_id, BinderInfo::Default, fin_n(k.clone()), r);
                let r = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), r);
                b.finish(r)
            };
            (ty, value)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.castSucc_inj"),
            level_params: vec![],
            type_: cinj.0,
            value: cinj.1,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_index_lemmas_type_check_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_index_lemmas().expect("register");
        env.register_fin_index_lemmas().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "Fin.castSucc_ne_last",
            "Fin.last_ne_castSucc",
            "Fin.castSucc_inj",
        ] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(n.clone(), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            assert_eq!(
                env.get_const(&n).expect("registered").kind,
                ConstantKind::Theorem
            );
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
            assert!(matches!(
                env.proof_quality(&n),
                Some(ProofQuality::Constructive)
            ));
        }
    }
}
