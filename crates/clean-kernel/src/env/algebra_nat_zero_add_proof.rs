// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.zero_add : ∀ a : Nat, Eq (Nat.add Nat.zero a) a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof term
//! is built by induction on `a` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.add` is defined as `Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n`
//! (recurses on the SECOND argument). Specializing at `m = Nat.zero`,
//! `Nat.add Nat.zero n` does NOT reduce to `n` directly — we must induct.
//!
//! ```text
//! theorem Nat.zero_add (a : Nat) : Eq (Nat.add Nat.zero a) a :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.add Nat.zero t) t)  -- motive
//!     (@Eq.refl.{1} Nat Nat.zero)                      -- base: 0 + 0 = 0
//!     (fun (k : Nat) (ih : Eq (Nat.add Nat.zero k) k) =>
//!        @congrArg.{1,1} Nat Nat (Nat.add Nat.zero k) k Nat.succ ih)  -- step
//!     a
//! ```
//!
//! Base case type-checks because `Nat.add Nat.zero Nat.zero` reduces to
//! `Nat.zero` by iota on `Nat.rec` (zero case). Step case: `Nat.add Nat.zero
//! (Nat.succ k)` reduces via iota to `Nat.succ (Nat.add Nat.zero k)`, and
//! `congrArg Nat.succ ih` witnesses `Nat.succ (Nat.add Nat.zero k) = Nat.succ k`.
//!
//! # Axiom closure
//!
//! Proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.add`, `Nat.rec`, `congrArg` — none of which are `Declaration::Axiom`.
//! `Nat.rec` is auto-generated kernel machinery. Therefore
//! `env.axiom_deps("Nat.zero_add")` is empty and
//! `env.proof_quality("Nat.zero_add") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.zero_add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `congrArg`.
    /// ENSURES: On success, `Nat.zero_add` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_zero_add_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.zero_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        // Nat.rec.{0} — Prop-valued motive.
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]);
        // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) → Eq a₁ a₂ → Eq (f a₁) (f a₂)
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]);

        // Helper: Nat.add Nat.zero x
        let add_zero_x = |x: Expr| Expr::app(Expr::app(nat_add.clone(), nat_zero.clone()), x);

        // Type: ∀ a : Nat, Eq Nat (Nat.add Nat.zero a) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let concl = Expr::apps(
            eq_const.clone(),
            [nat_type.clone(), add_zero_x(a.clone()), a.clone()],
        );
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Motive: λ (t : Nat) => Eq Nat (Nat.add Nat.zero t) t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_type.clone());
            let body = Expr::apps(
                eq_const.clone(),
                [nat_type.clone(), add_zero_x(t.clone()), t.clone()],
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, nat_type.clone(), body);
            mb.finish_child(lam)
        };

        // Base: @Eq.refl.{1} Nat Nat.zero  :  Eq Nat Nat.zero Nat.zero
        // which type-checks against `motive Nat.zero = Eq Nat (Nat.add Nat.zero Nat.zero) Nat.zero`
        // because `Nat.add Nat.zero Nat.zero` reduces to `Nat.zero` by iota on Nat.rec zero-case.
        let base = Expr::apps(eq_refl.clone(), [nat_type.clone(), nat_zero.clone()]);

        // Step: λ (k : Nat) (ih : Eq (Nat.add Nat.zero k) k) =>
        //   @congrArg.{1,1} Nat Nat (Nat.add Nat.zero k) k Nat.succ ih
        // The result type `Eq (Nat.succ (Nat.add Nat.zero k)) (Nat.succ k)` definitionally
        // equals `motive (Nat.succ k) = Eq (Nat.add Nat.zero (Nat.succ k)) (Nat.succ k)`
        // because `Nat.add Nat.zero (Nat.succ k)` reduces to `Nat.succ (Nat.add Nat.zero k)`
        // by iota on the Nat.rec succ-case.
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(nat_type.clone());
            let ih_type = Expr::apps(
                eq_const.clone(),
                [nat_type.clone(), add_zero_x(k.clone()), k.clone()],
            );
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let congr_app = Expr::apps(
                congr_arg.clone(),
                [
                    nat_type.clone(),
                    nat_type.clone(),
                    add_zero_x(k.clone()),
                    k.clone(),
                    nat_succ.clone(),
                    ih,
                ],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, congr_app);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, nat_type.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        // Value: λ a : Nat => @Nat.rec.{0} motive base step a
        let mut vb = EnvDeclBuilder::new();
        let (va_id, va) = vb.fresh_local(nat_type.clone());
        let rec_app = Expr::apps(nat_rec, [motive, base, step, va]);
        let val_raw = vb.mk_lam(va_id, BinderInfo::Default, nat_type.clone(), rec_app);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Replaces the
        // prior `Declaration::Axiom` in
        // `data_types_nat_lemmas.rs::init_nat_arith_lemmas`.
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
    use crate::env::ConstantKind;

    #[test]
    fn test_nat_zero_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_zero_add_proof()
            .expect("first registration");
        env.register_nat_zero_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.zero_add"))
            .expect("Nat.zero_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_zero_add_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_zero_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.zero_add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.zero_add proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }
}
