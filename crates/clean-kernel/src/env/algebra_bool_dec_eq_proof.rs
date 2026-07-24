// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `Bool.decEq : (a b : Bool) → Decidable (Eq a b)` — a real kernel
//! term (NO `sorry`, NO axiom), backing `instDecidableEqBool` so `if (a = b)` /
//! `decide` over `Bool` resolve.
//!
//! 2×2 case analysis via `Bool.rec` (no recursion): diagonal `isTrue (Eq.refl)`,
//! off-diagonal `isFalse (fun h => Bool.noConfusion h)` (distinct constructors
//! ⇒ `Bool.noConfusionType False _ _` δ-reduces to `False`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Bool.decEq` as a kernel-checked `Declaration::Definition`.
    /// Idempotent; axiom-free.
    pub(crate) fn register_bool_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Bool.decEq")).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_decidable()?;
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let one = Level::succ(Level::zero());
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]);
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![one.clone()]);

        let eqb = |l: Expr, r: Expr| Expr::apps(eq_c.clone(), [bool_c.clone(), l, r]);
        let dec_eqb = |l: Expr, r: Expr| Expr::app(dec.clone(), eqb(l, r));
        // diagonal `@Decidable.isTrue (Eq Bool x x) (Eq.refl Bool x)`
        let mk_true = |x: Expr| {
            Expr::apps(
                is_true.clone(),
                [
                    eqb(x.clone(), x.clone()),
                    Expr::apps(eq_refl.clone(), [bool_c.clone(), x]),
                ],
            )
        };
        // off-diagonal `@Decidable.isFalse (Eq Bool l r) (fun h => Bool.noConfusion h)`
        let mk_false = |l: Expr, r: Expr| {
            let prop = eqb(l.clone(), r.clone());
            // fun (h : Eq Bool l r) => @Bool.noConfusion.{0} False l r h   (h = BVar 0)
            let body = Expr::apps(
                no_conf.clone(),
                [false_c.clone(), l.clone(), r.clone(), Expr::bvar(0)],
            );
            let disproof = Expr::lam(BinderInfo::Default, prop.clone(), body);
            Expr::apps(is_false.clone(), [prop, disproof])
        };

        // type: (a b : Bool) → Decidable (Eq a b)
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_c.clone());
            let (bv_id, bv) = b.fresh_local(bool_c.clone());
            let concl = dec_eqb(a.clone(), bv.clone());
            let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };

        // value: fun (a b : Bool) => Bool.rec (motive_a) <a=false> <a=true> a
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_c.clone());
            let (bv_id, bv) = b.fresh_local(bool_c.clone());

            // motive_a : fun (a' : Bool) => Decidable (Eq a' b)
            let motive_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ap_id, ap) = c.fresh_local(bool_c.clone());
                c.finish_child(c.mk_lam(
                    ap_id,
                    BinderInfo::Default,
                    bool_c.clone(),
                    dec_eqb(ap, bv.clone()),
                ))
            };
            // inner motive for the b-split given a fixed `lhs`
            let inner_rec = |lhs: Expr, parent: &EnvDeclBuilder| {
                let mut c = EnvDeclBuilder::child_of(parent);
                let motive_b = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (bp_id, bp) = d.fresh_local(bool_c.clone());
                    d.finish_child(d.mk_lam(
                        bp_id,
                        BinderInfo::Default,
                        bool_c.clone(),
                        dec_eqb(lhs.clone(), bp),
                    ))
                };
                // Bool.rec minors are in ctor order: false-case, then true-case.
                let b_false = if lhs == bfalse {
                    mk_true(bfalse.clone())
                } else {
                    mk_false(lhs.clone(), bfalse.clone())
                };
                let b_true = if lhs == btrue {
                    mk_true(btrue.clone())
                } else {
                    mk_false(lhs.clone(), btrue.clone())
                };
                let e = Expr::apps(bool_rec.clone(), [motive_b, b_false, b_true, bv.clone()]);
                c.finish_child(e)
            };

            let a_false_case = inner_rec(bfalse.clone(), &b);
            let a_true_case = inner_rec(btrue.clone(), &b);

            let rec_a = Expr::apps(
                bool_rec.clone(),
                [motive_a, a_false_case, a_true_case, a.clone()],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), rec_a);
            let e = b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Bool.decEq"),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    #[test]
    fn test_bool_dec_eq_type_checks_and_axiom_free() {
        let mut env = Environment::new();
        env.register_bool_dec_eq_proof().expect("register");
        env.register_bool_dec_eq_proof().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Bool.decEq"), vec![]))
            .expect("Bool.decEq should type-check");
        let deps = env
            .axiom_deps(&Name::from_string("Bool.decEq"))
            .expect("registered");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "Bool.decEq must be axiom-free, got {names:?}"
        );
    }
}
