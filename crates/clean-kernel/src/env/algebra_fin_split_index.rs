// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Split index maps for the FAITHFUL `Fin` carrier, the first rung of the
//! Parseval infrastructure ladder. Real kernel-checked terms (NO `sorry`, NO
//! axiom in the proof terms themselves).
//!
//! - `Fin.castAdd : (a b : Nat) → Fin a → Fin (Nat.add a b)`
//!     low embedding `i ↦ i`, keeping the same `val`. The bound
//!     `Nat.lt (val i) (a + b)` is built from `Fin.isLt i : Nat.lt (val i) a`
//!     and `Nat.le_add_right a b : Nat.le a (a + b)` via `Nat.le_trans`
//!     (recall `Nat.lt p q ≡ Nat.le (Nat.succ p) q`).
//! - `Fin.addNat : (a b : Nat) → Fin b → Fin (Nat.add a b)`
//!     high embedding `j ↦ a + j`, `val = Nat.add a (val j)`. The bound
//!     `Nat.lt (a + val j) (a + b)` is `Nat.add_lt_add_left (val j) b
//!     (Fin.isLt j) a`.
//!
//! Both are registered as **reducible `Declaration::Definition`s** with the
//! exact `Fin.mk`-faithful shape, so they stay δ-transparent for the
//! downstream `Fin.sum_split_add` ι-steps.
//!
//! Axiom closure of the proof terms: `Fin`/`Fin.mk`/`Fin.val`/`Fin.isLt`,
//! `Nat`/`Nat.add`/`Nat.succ`/`Nat.lt`/`Nat.le`, `Nat.le_trans`,
//! `Nat.le_add_right`, `Nat.add_lt_add_left` — every one of which is itself a
//! constructive (axiom-free) `Declaration::Theorem`/`Definition`, so these
//! definitions are axiom-free too.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `Fin.castAdd` and `Fin.addNat` as reducible Definitions.
    /// Idempotent; the proof terms are axiom-free.
    pub(crate) fn register_fin_split_index(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.castAdd"))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Definition)
            && self
                .get_const(&Name::from_string("Fin.addNat"))
                .is_some_and(|c| c.kind == super::types::ConstantKind::Definition)
        {
            return Ok(());
        }

        self.init_nat()?;
        self.init_lt()?;
        self.init_fin()?;
        // `Nat.le_trans` (typeclass-form, reducible to raw `Nat.le`).
        self.register_nat_le_trans_proof()?;
        // `Nat.le_add_right` (raw `Nat.le`) — registered transitively.
        self.register_nat_mul_le_mul_left_proof()?;
        // `Nat.add_lt_add_left` (raw `Nat.lt`) — registered transitively.
        self.register_nat_arith_order_proofs()?;

        let c = FinSumConsts::new();

        let nat = c.nat.clone();
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let fin_c = c.fin.clone();
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let nat_le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let nat_le_add_right = Expr::const_(Name::from_string("Nat.le_add_right"), vec![]);
        let nat_add_lt_add_left = Expr::const_(Name::from_string("Nat.add_lt_add_left"), vec![]);

        let fin_n = |n: Expr| Expr::app(fin_c.clone(), n);
        let add = |x: Expr, y: Expr| Expr::apps(nat_add.clone(), [x, y]);
        let succ = |n: Expr| Expr::app(nat_succ.clone(), n);
        let val = |n: Expr, x: Expr| Expr::apps(fin_val.clone(), [n, x]);
        let islt = |n: Expr, x: Expr| Expr::apps(fin_islt.clone(), [n, x]);

        // ─────────────────── Fin.castAdd ───────────────────
        // (a b : Nat) → Fin a → Fin (Nat.add a b)
        //   := fun a b x =>
        //        @Fin.mk (a + b) (@Fin.val a x)
        //          (@Nat.le_trans (succ (val a x)) a (a + b)
        //             (@Fin.isLt a x)            -- : Nat.le (succ (val x)) a
        //             (@Nat.le_add_right a b))   -- : Nat.le a (a + b)
        let cast_add_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bb_id, bb) = b.fresh_local(nat.clone());
            let (x_id, _x) = b.fresh_local(fin_n(a.clone()));
            let r = b.mk_pi(
                x_id,
                BinderInfo::Default,
                fin_n(a.clone()),
                fin_n(add(a.clone(), bb.clone())),
            );
            let r = b.mk_pi(bb_id, BinderInfo::Default, nat.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };
        let cast_add_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bb_id, bb) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(fin_n(a.clone()));
            let v = val(a.clone(), x.clone());
            let ab = add(a.clone(), bb.clone());
            // bound : Nat.le (succ v) (a + b)
            let bound = Expr::apps(
                nat_le_trans.clone(),
                [
                    succ(v.clone()),
                    a.clone(),
                    ab.clone(),
                    islt(a.clone(), x.clone()),
                    Expr::apps(nat_le_add_right.clone(), [a.clone(), bb.clone()]),
                ],
            );
            // @Fin.mk (a + b) v bound : Fin (a + b)
            let body = Expr::apps(fin_mk.clone(), [ab, v, bound]);
            let r = b.mk_lam(x_id, BinderInfo::Default, fin_n(a.clone()), body);
            let r = b.mk_lam(bb_id, BinderInfo::Default, nat.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.castAdd"),
            level_params: vec![],
            type_: cast_add_type,
            value: cast_add_value,
            is_reducible: true,
        })?;

        // ─────────────────── Fin.addNat ───────────────────
        // (a b : Nat) → Fin b → Fin (Nat.add a b)
        //   := fun a b x =>
        //        @Fin.mk (a + b) (Nat.add a (@Fin.val b x))
        //          (@Nat.add_lt_add_left (val b x) b (@Fin.isLt b x) a)
        //            -- : Nat.lt (a + val x) (a + b) ≡ Nat.le (succ (a + val x)) (a + b)
        let add_nat_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bb_id, bb) = b.fresh_local(nat.clone());
            let (x_id, _x) = b.fresh_local(fin_n(bb.clone()));
            let r = b.mk_pi(
                x_id,
                BinderInfo::Default,
                fin_n(bb.clone()),
                fin_n(add(a.clone(), bb.clone())),
            );
            let r = b.mk_pi(bb_id, BinderInfo::Default, nat.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };
        let add_nat_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bb_id, bb) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(fin_n(bb.clone()));
            let v = val(bb.clone(), x.clone());
            let new_val = add(a.clone(), v.clone());
            let ab = add(a.clone(), bb.clone());
            // bound : Nat.lt (a + val x) (a + b)  ≡  Nat.le (succ (a + val x)) (a + b)
            //   = @Nat.add_lt_add_left (val x) b (isLt x) a
            let bound = Expr::apps(
                nat_add_lt_add_left.clone(),
                [
                    v.clone(),
                    bb.clone(),
                    islt(bb.clone(), x.clone()),
                    a.clone(),
                ],
            );
            // @Fin.mk (a + b) (a + val x) bound : Fin (a + b)
            let body = Expr::apps(fin_mk.clone(), [ab, new_val, bound]);
            let r = b.mk_lam(x_id, BinderInfo::Default, fin_n(bb.clone()), body);
            let r = b.mk_lam(bb_id, BinderInfo::Default, nat.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.addNat"),
            level_params: vec![],
            type_: add_nat_type,
            value: add_nat_value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_split_index_type_checks() {
        let mut env = Environment::with_prelude();
        env.register_fin_split_index().expect("register");
        env.register_fin_split_index().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["Fin.castAdd", "Fin.addNat"] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(n.clone(), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            assert_eq!(
                env.get_const(&n).expect("registered").kind,
                ConstantKind::Definition
            );
            // Defends the soundness posture: the split-index maps must not
            // smuggle in any axiom via their bound proofs.
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        }
    }

    /// Ground sanity: `Fin.castAdd 1 1 (Fin.last 0)` and `Fin.addNat 1 1
    /// (Fin.last 0)` are well-typed closed terms in `Fin 2`, and their `val`s
    /// reduce as expected (`0` and `1` respectively) under `Eq.refl`.
    #[test]
    fn test_fin_split_index_ground_vals() {
        let mut env = Environment::with_prelude();
        env.register_fin_split_index().expect("register");
        // Bring `Fin.last` into scope for the ground witnesses.
        {
            let c = FinSumConsts::new();
            env.ensure_fin_last(&c).expect("ensure Fin.last");
        }
        // Fin.last 0 : Fin 1, val 0
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            zero.clone(),
        );
        let two = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            one.clone(),
        );
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let cast_add = Expr::const_(Name::from_string("Fin.castAdd"), vec![]);
        let add_nat = Expr::const_(Name::from_string("Fin.addNat"), vec![]);
        let eq = Expr::const_(
            Name::from_string("Eq"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );
        let last0 = Expr::app(fin_last.clone(), zero.clone()); // Fin 1
        let fin2 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), two.clone());
        let tc = TypeChecker::with_mode(&env, env.mode());

        // castAdd 1 1 (last 0) : Fin 2 (defeq: Fin (1+1) ≡ Fin 2), val ≡ 0
        let ca = Expr::apps(cast_add.clone(), [one.clone(), one.clone(), last0.clone()]);
        tc.check_type(&ca, &fin2)
            .unwrap_or_else(|e| panic!("castAdd 1 1 (last 0) should be Fin 2: {e:?}"));
        let ca_val = Expr::apps(fin_val.clone(), [two.clone(), ca]);
        // Goal `ca_val = 0`; refl `@Eq.refl Nat 0` checks iff ca_val ≡ 0 by ι.
        let goal0 = Expr::apps(eq.clone(), [nat.clone(), ca_val, zero.clone()]);
        let refl0 = Expr::apps(eq_refl.clone(), [nat.clone(), zero.clone()]);
        tc.check_type(&refl0, &goal0)
            .unwrap_or_else(|e| panic!("castAdd val should reduce to 0: {e:?}"));

        // addNat 1 1 (last 0) : Fin 2 (defeq), val ≡ 1 + 0 ≡ 1
        let an = Expr::apps(add_nat.clone(), [one.clone(), one.clone(), last0.clone()]);
        tc.check_type(&an, &fin2)
            .unwrap_or_else(|e| panic!("addNat 1 1 (last 0) should be Fin 2: {e:?}"));
        let an_val = Expr::apps(fin_val.clone(), [two.clone(), an]);
        let goal1 = Expr::apps(eq.clone(), [nat.clone(), an_val, one.clone()]);
        let refl1 = Expr::apps(eq_refl.clone(), [nat.clone(), one.clone()]);
        tc.check_type(&refl1, &goal1)
            .unwrap_or_else(|e| panic!("addNat val should reduce to 1: {e:?}"));
    }
}
