// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.one_mul : ∀ a : Nat, Eq (Nat.mul (Nat.succ Nat.zero) a) a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by induction on `a` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.mul` recurses on its SECOND argument:
//!
//! ```text
//! Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n
//! ```
//!
//! So `Nat.mul (Nat.succ Nat.zero) a` does NOT reduce to `a` directly —
//! we induct on `a`:
//!
//! ```text
//! theorem Nat.one_mul (a : Nat) : Eq (Nat.mul (Nat.succ Nat.zero) a) a :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.mul (Nat.succ Nat.zero) t) t)          -- motive
//!     (@Eq.refl.{1} Nat Nat.zero)                                         -- base
//!     (fun (k : Nat) (ih : Eq (Nat.mul (Nat.succ Nat.zero) k) k) =>
//!        @congrArg.{1,1} Nat Nat
//!          (Nat.mul (Nat.succ Nat.zero) k) k
//!          Nat.succ ih)                                                   -- step
//!     a
//! ```
//!
//! **Base case.** `motive Nat.zero = Eq Nat (Nat.mul (Nat.succ Nat.zero) Nat.zero)
//! Nat.zero`. LHS reduces to `Nat.zero` via iota zero-case on `Nat.rec`
//! (base of `Nat.mul` is `Nat.zero`) + delta on the reducible `Nat.mul`
//! definition. So `motive Nat.zero ≡ Eq Nat Nat.zero Nat.zero`, witnessed
//! by `@Eq.refl.{1} Nat Nat.zero`.
//!
//! **Step case.** `motive (Nat.succ k) = Eq Nat (Nat.mul (Nat.succ Nat.zero)
//! (Nat.succ k)) (Nat.succ k)`. The LHS reduces:
//!
//! ```text
//! Nat.mul (Nat.succ Nat.zero) (Nat.succ k)
//!   δ→ Nat.rec Nat.zero (λ _ ih => Nat.add ih (Nat.succ Nat.zero)) (Nat.succ k)
//!   ι→ (λ _ ih => Nat.add ih (Nat.succ Nat.zero)) k (Nat.rec Nat.zero minor k)
//!   β→ Nat.add (Nat.rec Nat.zero minor k) (Nat.succ Nat.zero)
//!   δ← Nat.add (Nat.mul (Nat.succ Nat.zero) k) (Nat.succ Nat.zero)
//!   ι→ Nat.succ (Nat.add (Nat.mul (Nat.succ Nat.zero) k) Nat.zero)
//!   ι→ Nat.succ (Nat.mul (Nat.succ Nat.zero) k)
//! ```
//!
//! (The last two steps use the iota succ-case and zero-case of
//! `Nat.add _ (Nat.succ Nat.zero)` = `Nat.add _ (Nat.succ Nat.zero)`.)
//!
//! So `motive (Nat.succ k)` defn-equals
//! `Eq Nat (Nat.succ (Nat.mul (Nat.succ Nat.zero) k)) (Nat.succ k)`, which
//! is exactly the type of `@congrArg.{1,1} Nat Nat (Nat.mul (Nat.succ
//! Nat.zero) k) k Nat.succ ih`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.mul`, `Nat.rec`, `congrArg` — none of which are
//! `Declaration::Axiom`. `Nat.rec` is auto-generated kernel machinery,
//! `congrArg` is a kernel-level `Declaration::Theorem`. Therefore
//! `env.axiom_deps("Nat.one_mul")` is empty and
//! `env.proof_quality("Nat.one_mul") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Tier A Batch 5 Nat axiom demotion). Sibling proofs:
//! - `algebra_nat_zero_add_proof.rs` (#3604, Nat.rec induction — same shape).
//! - `algebra_nat_succ_add_proof.rs` (#3604, Nat.rec induction).
//! - `algebra_nat_mul_one_proof.rs` (#3551, companion — uses Nat.zero_add).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.one_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `congrArg`.
    /// ENSURES: On success, `Nat.one_mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_one_mul_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.one_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        // Nat.rec.{0} — Prop-valued motive.
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]);

        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());

        // Helper: Nat.mul Nat.one x
        let mul_one_x = |x: Expr| Expr::app(Expr::app(nat_mul.clone(), nat_one.clone()), x);

        // Type: ∀ a : Nat, Eq Nat (Nat.mul (Nat.succ Nat.zero) a) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let concl = Expr::apps(
            eq_const.clone(),
            [nat_type.clone(), mul_one_x(a.clone()), a.clone()],
        );
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Motive: λ (t : Nat) => Eq Nat (Nat.mul (Nat.succ Nat.zero) t) t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_type.clone());
            let body = Expr::apps(
                eq_const.clone(),
                [nat_type.clone(), mul_one_x(t.clone()), t.clone()],
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, nat_type.clone(), body);
            mb.finish_child(lam)
        };

        // Base: @Eq.refl.{1} Nat Nat.zero
        // motive Nat.zero defn-equals Eq Nat Nat.zero Nat.zero because
        // Nat.mul (Nat.succ Nat.zero) Nat.zero reduces to Nat.zero by iota
        // zero-case on Nat.rec (base of Nat.mul is Nat.zero).
        let base = Expr::apps(eq_refl.clone(), [nat_type.clone(), nat_zero.clone()]);

        // Step: λ (k : Nat) (ih : Eq (Nat.mul 1 k) k) =>
        //   @congrArg.{1,1} Nat Nat (Nat.mul 1 k) k Nat.succ ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(nat_type.clone());
            let ih_type = Expr::apps(
                eq_const.clone(),
                [nat_type.clone(), mul_one_x(k.clone()), k.clone()],
            );
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let congr_app = Expr::apps(
                congr_arg.clone(),
                [
                    nat_type.clone(),
                    nat_type.clone(),
                    mul_one_x(k.clone()),
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

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier A Batch 5).
        // Nat.rec-induction on `a`. Base case closed by `@Eq.refl.{1} Nat
        // Nat.zero` (motive at Nat.zero reduces to `Eq Nat.zero Nat.zero`
        // via iota zero-case + delta on Nat.mul). Step case closed by
        // `congrArg Nat.succ ih`: motive at `Nat.succ k` reduces to
        // `Eq (Nat.succ (Nat.mul 1 k)) (Nat.succ k)` via iota+beta+delta on
        // `Nat.mul 1 (succ k)` → `Nat.add (Nat.mul 1 k) 1` → `Nat.succ
        // (Nat.mul 1 k)`. No `sorry`, no self-reference, no axiom-wrapper.
        // Replaces the prior `Declaration::Axiom` in
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
    fn test_nat_one_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_one_mul_proof()
            .expect("first registration");
        env.register_nat_one_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.one_mul"))
            .expect("Nat.one_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_one_mul_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_one_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.one_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.one_mul proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// After peeling one outer λ binder, the proof root is `@Nat.rec.{0}`.
    #[test]
    fn test_nat_one_mul_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_one_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.one_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let body = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ a, got {:?}", k),
        };
        let mut head = body.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.one_mul proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_nat_one_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_one_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.one_mul"))
            .expect("Nat.one_mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.one_mul must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
