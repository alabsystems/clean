// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `Nat.decLe : (a b : Nat) → Decidable (Nat.le a b)` and
//! `Nat.decLt : (a b : Nat) → Decidable (Nat.lt a b)` — real kernel terms
//! (NO `sorry`, NO axiom). These are the leaves that make `if (a ≤ b)` /
//! `if (a < b)` / `decide` over `Nat` orderings elaborate without a synthetic
//! `sorry`, demoting the legacy `Declaration::Axiom` `instDecidableNatLe` /
//! `instDecidableNatLt`.
//!
//! # Proof shape
//!
//! Dispatch on the *boolean* `Nat.ble a b : Bool` via `Bool.rec`, threading an
//! equality proof `Nat.ble a b = x` through the motive so each leaf has a
//! concrete `= Bool.false` / `= Bool.true` hypothesis to feed the axiom-free
//! bridge lemmas (`algebra_nat_ble_le_proof.rs`):
//!
//! ```text
//! Nat.decLe : (a b : Nat) → Decidable (Nat.le a b) :=
//!   fun (a b : Nat) =>
//!     @Bool.rec.{1}
//!       (fun (x : Bool) => @Eq Bool (Nat.ble a b) x → Decidable (Nat.le a b))   -- motive
//!       (fun (h : @Eq Bool (Nat.ble a b) Bool.false) =>                          -- false minor
//!          @Decidable.isFalse (Nat.le a b) (Nat.not_le_of_ble_eq_false a b h))
//!       (fun (h : @Eq Bool (Nat.ble a b) Bool.true) =>                           -- true minor
//!          @Decidable.isTrue  (Nat.le a b) (Nat.le_of_ble_eq_true a b h))
//!       (Nat.ble a b)
//!       (@Eq.refl Bool (Nat.ble a b))
//! ```
//!
//! `Bool.rec` is `{motive : Bool → Sort u} → motive Bool.false → motive
//! Bool.true → (t : Bool) → motive t` (constructor order: `false`, then
//! `true`). Applying the motive at the major `(Nat.ble a b)` and feeding the
//! reflexivity proof `@Eq.refl Bool (Nat.ble a b)` discharges the threaded
//! hypothesis, so the whole term has type `Decidable (Nat.le a b)`.
//!
//! `Nat.decLt a b` is the same dispatcher run at `(Nat.succ a, b)`: `Nat.lt a b`
//! reducibly unfolds to `Nat.le (Nat.succ a) b`, so the `Nat.le` bridge lemmas
//! applied at `(succ a, b)` produce a proof / disproof whose type is def-eq to
//! `Nat.lt a b`.
//!
//! # Axiom closure
//!
//! The terms mention only `Nat`, `Nat.succ`, `Nat.ble`, `Nat.le`, `Nat.lt`,
//! `Bool`(`.false`/`.true`/`.rec`), `Eq`/`Eq.refl`, `Decidable`(`.isTrue`/
//! `.isFalse`), and the axiom-free bridge lemmas `Nat.le_of_ble_eq_true` /
//! `Nat.not_le_of_ble_eq_false` — all constructive (generated recursors /
//! reducible definitions / axiom-free theorems). So `env.axiom_deps("Nat.decLe")`
//! and `env.axiom_deps("Nat.decLt")` are empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.decLe` and `Nat.decLt` as kernel-checked
    /// `Declaration::Definition`s (idempotent, axiom-free).
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat`, `Nat.succ`, `Nat.ble`, `Nat.le`, `Nat.lt`, `Bool`
    ///           (+ `Bool.rec`/ctors), `Eq`/`Eq.refl`, `Decidable` (+ ctors),
    ///           and the `Nat.ble`↔`Nat.le` bridge lemmas are registered
    ///           (auto-initialized here).
    /// ENSURES: On success, `Nat.decLe` / `Nat.decLt` are `Definition`s whose
    ///          values type-check at `(a b : Nat) → Decidable (Nat.le a b)` /
    ///          `… (Nat.lt a b)` and whose axiom closures are empty.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_dec_le_lt_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean's `Nat.decLe`/`Nat.decLt` values are Nat.rec
        // dispatcher bridges — genuine v4.31 uses `Nat.ble`-based `dite`
        // bodies, and `Decidable` is Type-valued (no proof irrelevance) so
        // conversion must genuinely unfold them (`Rat.instEncodable`'s
        // `Subtype.encodable` chain rejects against the stub). Suppressed in
        // import mode with their `instDecidableNat{Lt,Le}` wrappers so the
        // genuine olean definitions import (caller-graph closure + kernel
        // error oracle verified: nothing else in the import prelude
        // references these names).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let have_le = self.get_const(&Name::from_string("Nat.decLe")).is_some();
        let have_lt = self.get_const(&Name::from_string("Nat.decLt")).is_some();
        if have_le && have_lt {
            return Ok(());
        }

        // Dependencies. `init_true_false` before `init_decidable` so
        // `Decidable.isFalse` carries the real `(p → False)` negation type.
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_decidable()?;
        self.init_nat_cmp()?; // Nat.ble
        self.init_le()?; // Nat.le
        self.init_lt()?; // Nat.lt
                         // The axiom-free bridge lemmas backing the leaves.
        self.register_nat_ble_le_lemmas()?;

        // ----- shared constants -----
        let type1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ_c = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let ble_c = Expr::const_(Name::from_string("Nat.ble"), vec![]);
        let le_c = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let lt_c = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        // Bool.rec.{1} : {motive : Bool → Sort 1} → motive Bool.false →
        //   motive Bool.true → (t : Bool) → motive t
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![type1.clone()]);
        let eq_b = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl_b = Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let le_true_lemma = Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]);
        let not_le_false_lemma =
            Expr::const_(Name::from_string("Nat.not_le_of_ble_eq_false"), vec![]);

        // helper closures over the shared constants
        let succ = |x: Expr| Expr::app(succ_c.clone(), x);
        let ble = |x: Expr, y: Expr| Expr::apps(ble_c.clone(), [x, y]);
        let le = |x: Expr, y: Expr| Expr::apps(le_c.clone(), [x, y]);
        // `@Eq Bool (Nat.ble x y) v`
        let eq_ble =
            |x: Expr, y: Expr, v: Expr| Expr::apps(eq_b.clone(), [bool_c.clone(), ble(x, y), v]);

        // Build the dispatcher value `(a b : Nat) → Decidable (le_prop a b)` for
        // a chosen `le`-prop and a chosen `ble` discriminant pair.
        //
        // `le_prop l r`  : the `Decidable`'s proposition (e.g. `Nat.le l r` or
        //                  `Nat.lt l r` — the latter unfolds to `Nat.le (succ l) r`).
        // `ble_lhs`/`ble_rhs` : the *bridge* arguments. For `decLe` these are
        //                  `(a, b)`; for `decLt`, `(succ a, b)`, since
        //                  `Nat.lt a b ≡ Nat.le (succ a) b`. The bridge lemmas are
        //                  applied at exactly these arguments, so the leaf proof's
        //                  `Nat.le ble_lhs ble_rhs` type is def-eq to `le_prop a b`.
        let build_value = |le_prop: &dyn Fn(Expr, Expr) -> Expr,
                           bridge: &dyn Fn(Expr, Expr) -> (Expr, Expr)|
         -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());

            let (bl, br) = bridge(a.clone(), bv.clone());
            let prop = le_prop(a.clone(), bv.clone());

            // motive : fun (x : Bool) => @Eq Bool (Nat.ble bl br) x → Decidable prop
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(bool_c.clone());
                let hyp = eq_ble(bl.clone(), br.clone(), x.clone());
                let dec_prop = Expr::app(dec.clone(), prop.clone());
                let (h_id, _h) = c.fresh_local(hyp.clone());
                let pi = c.mk_pi(h_id, BinderInfo::Default, hyp, dec_prop);
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_c.clone(), pi))
            };

            // false minor : fun (h : @Eq Bool (Nat.ble bl br) Bool.false) =>
            //   @Decidable.isFalse prop (Nat.not_le_of_ble_eq_false bl br h)
            let false_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let hyp = eq_ble(bl.clone(), br.clone(), bfalse.clone());
                let (h_id, h) = c.fresh_local(hyp.clone());
                let disproof = Expr::apps(not_le_false_lemma.clone(), [bl.clone(), br.clone(), h]);
                let body = Expr::apps(is_false.clone(), [prop.clone(), disproof]);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
            };

            // true minor : fun (h : @Eq Bool (Nat.ble bl br) Bool.true) =>
            //   @Decidable.isTrue prop (Nat.le_of_ble_eq_true bl br h)
            let true_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let hyp = eq_ble(bl.clone(), br.clone(), btrue.clone());
                let (h_id, h) = c.fresh_local(hyp.clone());
                let proof = Expr::apps(le_true_lemma.clone(), [bl.clone(), br.clone(), h]);
                let body = Expr::apps(is_true.clone(), [prop.clone(), proof]);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
            };

            // major : Nat.ble bl br
            let major = ble(bl.clone(), br.clone());
            // refl : @Eq.refl Bool (Nat.ble bl br) : @Eq Bool (Nat.ble bl br) (Nat.ble bl br)
            let refl = Expr::apps(eq_refl_b.clone(), [bool_c.clone(), major.clone()]);

            // Bool.rec motive false_minor true_minor major refl
            let rec_app = Expr::apps(
                bool_rec.clone(),
                [motive, false_minor, true_minor, major, refl],
            );

            let e = b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), rec_app);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // ── Nat.decLe ──
        if !have_le {
            let le_prop = |l: Expr, r: Expr| le(l, r);
            let bridge = |a: Expr, b: Expr| (a, b);
            let value = build_value(&le_prop, &bridge);
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let (bv_id, bv) = b.fresh_local(nat.clone());
                let concl = Expr::app(dec.clone(), le(a.clone(), bv.clone()));
                let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), concl);
                let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.decLe"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // ── Nat.decLt ──
        // `Nat.lt a b` reducibly unfolds to `Nat.le (Nat.succ a) b`. We run the
        // dispatcher's bridge at `(succ a, b)` so the leaf's `Nat.le (succ a) b`
        // proof is def-eq to the `Decidable`'s `Nat.lt a b` proposition.
        if !have_lt {
            let lt_prop = |l: Expr, r: Expr| Expr::apps(lt_c.clone(), [l, r]);
            let bridge = |a: Expr, b: Expr| (succ(a), b);
            let value = build_value(&lt_prop, &bridge);
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let (bv_id, bv) = b.fresh_local(nat.clone());
                let concl = Expr::app(
                    dec.clone(),
                    Expr::apps(lt_c.clone(), [a.clone(), bv.clone()]),
                );
                let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), concl);
                let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.decLt"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nat_dec_le_lt_registered_and_type_check() {
        let mut env = Environment::new();
        env.register_nat_dec_le_lt_proof()
            .expect("first registration");
        env.register_nat_dec_le_lt_proof()
            .expect("idempotent re-registration");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["Nat.decLe", "Nat.decLt"] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition"
            );
            assert!(
                info.value.is_some(),
                "{name} Definition must retain its value"
            );
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }
    }

    #[test]
    fn test_nat_dec_le_lt_axiom_closures_empty() {
        let mut env = Environment::new();
        env.register_nat_dec_le_lt_proof().unwrap();
        for name in ["Nat.decLe", "Nat.decLt"] {
            let n = Name::from_string(name);
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(
                !names.iter().any(|s| s == "sorry" || s == "sorryAx"),
                "{name} must not depend on sorry/sorryAx; closure = {names:?}"
            );
            assert!(
                names.is_empty(),
                "{name} must have empty axiom closure, got {names:?}"
            );
        }
    }
}
