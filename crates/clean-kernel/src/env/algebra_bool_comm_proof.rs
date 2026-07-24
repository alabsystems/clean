// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive commutativity of the boolean binops `Bool.and`, `Bool.or`,
//! `Bool.xor` — real kernel terms (NO `sorry`, NO axiom).
//!
//! Each is a 2×2 case analysis via nested `Bool.rec` (no recursion): for every
//! pair of ground constructors `(a, b)` both sides reduce to the same ground
//! `Bool`, so the leaf proof is `@Eq.refl.{1} Bool (op a b)`, which the kernel
//! accepts against `op a b = op b a` by ι/δ-reduction of the right-hand side.
//!
//! These back trust-ir's `nat_*_comm` bitwise-commutativity proofs in
//! `lean/trust_ir-semantics/TrustIr/Basic.lean`, which rewrite with
//! `Bool.and_comm` / `Bool.or_comm` / `Bool.xor_comm` after `Nat.testBit_*`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Bool.and_comm`, `Bool.or_comm`, `Bool.xor_comm` as
    /// kernel-checked `Declaration::Theorem` terms. Idempotent; axiom-free.
    pub(crate) fn register_bool_comm_proofs(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_bool()?;

        self.register_bool_comm_proof("Bool.and", "Bool.and_comm")?;
        self.register_bool_comm_proof("Bool.or", "Bool.or_comm")?;
        // IMPORT MODE: `Bool.xor` is import-suppressed (drifted value) —
        // its comm proof rides the same gate; genuine olean lemma imports.
        if !self.suppress_lossy_structure_stubs {
            self.register_bool_comm_proof("Bool.xor", "Bool.xor_comm")?;
        }
        Ok(())
    }

    /// Register `<thm> : (a b : Bool) → Eq (op a b) (op b a)` for a single
    /// boolean binary operator `op` (one of `Bool.and`/`Bool.or`/`Bool.xor`).
    fn register_bool_comm_proof(&mut self, op: &str, thm: &str) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(thm)).is_some() {
            return Ok(());
        }

        let one = Level::succ(Level::zero());
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let op_c = Expr::const_(Name::from_string(op), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        // The motive is `fun a' => op a' b = op b a'`, an `Eq` proposition in
        // `Prop = Sort 0`, so the recursor is instantiated at universe 0.
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        let opab = |x: Expr, y: Expr| Expr::apps(op_c.clone(), [x, y]);
        // The proposition `op x y = op y x`.
        let goal = |x: Expr, y: Expr| {
            Expr::apps(
                eq_c.clone(),
                [bool_c.clone(), opab(x.clone(), y.clone()), opab(y, x)],
            )
        };
        // Leaf for ground `(x, y)`: `@Eq.refl.{1} Bool (op x y)`; its type
        // `op x y = op x y` is defeq to the goal `op x y = op y x` because the
        // RHS `op y x` reduces (ι on the recursor body) to the same ground Bool.
        let leaf = |x: Expr, y: Expr| Expr::apps(eq_refl.clone(), [bool_c.clone(), opab(x, y)]);

        // type: (a b : Bool) → Eq (op a b) (op b a)
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_c.clone());
            let (bv_id, bv) = b.fresh_local(bool_c.clone());
            let concl = goal(a.clone(), bv.clone());
            let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };

        // value: fun (a b : Bool) => Bool.rec (motive_a) <a=false> <a=true> a
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_c.clone());
            let (bv_id, bv) = b.fresh_local(bool_c.clone());

            // motive_a : fun (a' : Bool) => Eq (op a' b) (op b a')
            let motive_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ap_id, ap) = c.fresh_local(bool_c.clone());
                c.finish_child(c.mk_lam(
                    ap_id,
                    BinderInfo::Default,
                    bool_c.clone(),
                    goal(ap, bv.clone()),
                ))
            };

            // For a fixed `lhs` constructor, split on `b` and emit reflexivity
            // leaves. Bool.rec minors are in ctor order: false-case, then true.
            let inner_rec = |lhs: Expr, parent: &EnvDeclBuilder| {
                let mut c = EnvDeclBuilder::child_of(parent);
                let motive_b = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (bp_id, bp) = d.fresh_local(bool_c.clone());
                    d.finish_child(d.mk_lam(
                        bp_id,
                        BinderInfo::Default,
                        bool_c.clone(),
                        goal(lhs.clone(), bp),
                    ))
                };
                let b_false = leaf(lhs.clone(), bfalse.clone());
                let b_true = leaf(lhs.clone(), btrue.clone());
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

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(thm),
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    fn check_axiom_free(env: &Environment, thm: &str) {
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(thm), vec![]))
            .unwrap_or_else(|e| panic!("{thm} should type-check: {e:?}"));
        let deps = env
            .axiom_deps(&Name::from_string(thm))
            .unwrap_or_else(|| panic!("{thm} should be registered"));
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "{thm} must be axiom-free, got {names:?}");
    }

    #[test]
    fn test_bool_comm_proofs_type_check_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_bool_comm_proofs().expect("register");
        env.register_bool_comm_proofs().expect("idempotent");
        check_axiom_free(&env, "Bool.and_comm");
        check_axiom_free(&env, "Bool.or_comm");
        check_axiom_free(&env, "Bool.xor_comm");
    }
}
