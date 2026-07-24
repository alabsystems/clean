// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive lemmas bridging `Nat.beq` (the boolean equality decision) to
//! propositional `Eq` — `Nat.beq_refl` and `Nat.ne_of_beq_false` — built as real
//! kernel terms (NO `sorry`, NO axiom).
//!
//! These let the `Nat.decEq` native-decide reducer emit a SOUND, O(1)-size
//! `Decidable.isFalse` witness for distinct literals instead of `sorryAx`:
//! ```text
//! @Decidable.isFalse (@Eq Nat a b) (Nat.ne_of_beq_false a b (Eq.refl (Nat.beq a b)))
//! ```
//! When the reducer takes the false branch, `Nat.beq a b` δι-reduces to `false`,
//! so `Eq.refl (Nat.beq a b) : Eq (Nat.beq a b) false` is accepted by def-eq and
//! the whole witness is a small, fully constructive proof of `a ≠ b`.
//!
//! # Proof sketches
//!
//! `Nat.beq_refl a : Nat.beq a a = true` — single `Nat.rec` (motive into `Prop`):
//!   * `0`: `Nat.beq 0 0` ι-reduces to `true`, so `Eq.refl true` has the type.
//!   * `succ n`: `Nat.beq (succ n) (succ n)` ι-reduces to `Nat.beq n n`, so the
//!     IH `Nat.beq n n = true` already has the goal type — return it.
//!
//! `Nat.ne_of_beq_false a b (hbeq : Nat.beq a b = false) (heq : a = b) : False`:
//!   * `congrArg (Nat.beq a) heq : Nat.beq a a = Nat.beq a b`,
//!   * `Eq.trans … hbeq : Nat.beq a a = false`,
//!   * `Nat.beq_refl a : Nat.beq a a = true`,
//!   * `Eq.trans (Eq.symm …) … : false = true`,
//!   * `Bool.noConfusion … : False` (distinct `Bool` constructors).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.beq_refl` and `Nat.ne_of_beq_false` as kernel-checked
    /// `Declaration::Theorem`s.
    ///
    /// REQUIRES: `Nat`, `Nat.beq`, `Bool`, `Bool.noConfusion`, `Eq`, `congrArg`
    /// (auto-initialized here). ENSURES: idempotent; both have empty axiom
    /// closure (`ProofQuality::Constructive`).
    pub(crate) fn register_nat_beq_lemmas(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_true_false()?; // `False` for the ne_of_beq_false conclusion
        self.init_nat_cmp()?; // Nat.beq
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let one = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let eq_bool = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_nat = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        // helper: @Eq.{1} Bool l r
        let beq_eq = |l: Expr, r: Expr| Expr::apps(eq_bool.clone(), [bool_c.clone(), l, r]);
        let beq = |x: Expr, y: Expr| Expr::apps(nat_beq.clone(), [x, y]);

        // ───────────────── Nat.beq_refl : ∀ a, Nat.beq a a = true ─────────────
        if self.get_const(&Name::from_string("Nat.beq_refl")).is_none() {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let concl = beq_eq(beq(a.clone(), a.clone()), btrue.clone());
                b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), concl))
            };

            // motive : λ (a : Nat) => @Eq Bool (Nat.beq a a) true   (Nat → Prop)
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let body = beq_eq(beq(a.clone(), a.clone()), btrue.clone());
                b.finish(b.mk_lam(a_id, BinderInfo::Default, nat.clone(), body))
            };
            // zero case: @Eq.refl Bool true : @Eq Bool (Nat.beq 0 0) true (def-eq)
            let zcase = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
                [bool_c.clone(), btrue.clone()],
            );
            // succ case: λ (n : Nat) (ih : Nat.beq n n = true) => ih
            // motive (succ n) ≡ motive n since beq (succ n)(succ n) ι-reduces to beq n n.
            let scase = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, _n) = b.fresh_local(nat.clone());
                let ih_ty = beq_eq(beq(_n.clone(), _n.clone()), btrue.clone());
                let (ih_id, ih) = b.fresh_local(ih_ty.clone());
                let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, ih);
                let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
                b.finish(e)
            };
            // @Nat.rec.{0} motive zcase scase  : ∀ a, motive a
            let value = Expr::apps(
                Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
                [motive, zcase, scase],
            );
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.beq_refl"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ───── Nat.ne_of_beq_false : ∀ a b, Nat.beq a b = false → a = b → False ─
        if self
            .get_const(&Name::from_string("Nat.ne_of_beq_false"))
            .is_none()
        {
            let nat_eq = |l: Expr, r: Expr| Expr::apps(eq_nat.clone(), [nat.clone(), l, r]);
            let false_c = Expr::const_(Name::from_string("False"), vec![]);

            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());
            let hbeq_ty = beq_eq(beq(a.clone(), bv.clone()), bfalse.clone());
            let (hbeq_id, hbeq) = b.fresh_local(hbeq_ty.clone());
            let heq_ty = nat_eq(a.clone(), bv.clone());
            let (heq_id, heq) = b.fresh_local(heq_ty.clone());

            // cong : Nat.beq a a = Nat.beq a b  :=  congrArg (Nat.beq a) heq
            let cong = Expr::apps(
                Expr::const_(
                    Name::from_string("congrArg"),
                    vec![one.clone(), one.clone()],
                ),
                [
                    nat.clone(),
                    bool_c.clone(),
                    a.clone(),
                    bv.clone(),
                    Expr::app(nat_beq.clone(), a.clone()), // f = Nat.beq a
                    heq.clone(),
                ],
            );
            // beq_aa_false : Nat.beq a a = false := Eq.trans cong hbeq
            let beq_aa_false = Expr::apps(
                Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]),
                [
                    bool_c.clone(),
                    beq(a.clone(), a.clone()),
                    beq(a.clone(), bv.clone()),
                    bfalse.clone(),
                    cong,
                    hbeq.clone(),
                ],
            );
            // beq_aa_true : Nat.beq a a = true := Nat.beq_refl a
            let beq_aa_true = Expr::app(
                Expr::const_(Name::from_string("Nat.beq_refl"), vec![]),
                a.clone(),
            );
            // false_eq_true : false = true := Eq.trans (Eq.symm beq_aa_false) beq_aa_true
            let symm = Expr::apps(
                Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]),
                [
                    bool_c.clone(),
                    beq(a.clone(), a.clone()),
                    bfalse.clone(),
                    beq_aa_false,
                ],
            );
            let false_eq_true = Expr::apps(
                Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]),
                [
                    bool_c.clone(),
                    bfalse.clone(),
                    beq(a.clone(), a.clone()),
                    btrue.clone(),
                    symm,
                    beq_aa_true,
                ],
            );
            // @Bool.noConfusion.{0} False false true false_eq_true : False
            let body = Expr::apps(
                Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
                [
                    false_c.clone(),
                    bfalse.clone(),
                    btrue.clone(),
                    false_eq_true,
                ],
            );

            let value = {
                let e = b.mk_lam(heq_id, BinderInfo::Default, heq_ty.clone(), body);
                let e = b.mk_lam(hbeq_id, BinderInfo::Default, hbeq_ty.clone(), e);
                let e = b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
                b.finish(e)
            };
            let type_ = {
                let concl = {
                    let e = b.mk_pi(heq_id, BinderInfo::Default, heq_ty, false_c.clone());
                    b.mk_pi(hbeq_id, BinderInfo::Default, hbeq_ty, e)
                };
                let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), concl);
                let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
                b.finish(e)
            };

            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.ne_of_beq_false"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nat_beq_lemmas_type_check_and_axiom_free() {
        let mut env = Environment::new();
        env.register_nat_beq_lemmas().expect("first registration");
        env.register_nat_beq_lemmas().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["Nat.beq_refl", "Nat.ne_of_beq_false"] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(n.clone(), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
            assert_eq!(
                env.proof_quality(&n).expect("quality"),
                ProofQuality::Constructive,
                "{name} must be Constructive"
            );
        }
    }
}
