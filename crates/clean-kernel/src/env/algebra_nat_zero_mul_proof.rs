// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.zero_mul : ∀ a : Nat, Eq (Nat.mul Nat.zero a) Nat.zero`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by induction on `a` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.mul` is defined as
//! `Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n`
//! (recurses on the SECOND argument). Specializing to `m = Nat.zero`:
//!
//! ```text
//! theorem Nat.zero_mul (a : Nat) : Eq (Nat.mul Nat.zero a) Nat.zero :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.mul Nat.zero t) Nat.zero)       -- motive
//!     (@Eq.refl.{1} Nat Nat.zero)                                  -- base
//!     (fun (k : Nat) (ih : Eq (Nat.mul Nat.zero k) Nat.zero) => ih) -- step
//!     a
//! ```
//!
//! **Base case.** `motive Nat.zero = Eq Nat (Nat.mul Nat.zero Nat.zero) Nat.zero`.
//! `Nat.mul Nat.zero Nat.zero` reduces (iota zero-case + delta) to
//! `Nat.zero`; so `motive Nat.zero` ≡ `Eq Nat Nat.zero Nat.zero`, which
//! matches `@Eq.refl.{1} Nat Nat.zero`.
//!
//! **Step case.** Given `ih : Eq (Nat.mul Nat.zero k) Nat.zero`, we need
//! `motive (Nat.succ k) = Eq (Nat.mul Nat.zero (Nat.succ k)) Nat.zero`.
//! Reductions:
//! - `Nat.mul Nat.zero (Nat.succ k)` iota-reduces (succ-case of Nat.rec) to
//!   `Nat.add (Nat.mul Nat.zero k) Nat.zero`.
//! - `Nat.add x Nat.zero` iota-reduces (zero-case on `Nat.add`'s inner
//!   Nat.rec, which recurses on the SECOND argument) to `x`.
//! - So `Nat.mul Nat.zero (Nat.succ k)` ≡ `Nat.mul Nat.zero k`.
//!
//! Therefore `motive (Nat.succ k)` ≡ `Eq (Nat.mul Nat.zero k) Nat.zero`,
//! which is exactly the type of `ih`. The step body is simply `ih`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.mul`, `Nat.add`, `Nat.rec` — none of which are `Declaration::Axiom`.
//! `Nat.rec` is auto-generated kernel machinery. Therefore
//! `env.axiom_deps("Nat.zero_mul")` is empty and
//! `env.proof_quality("Nat.zero_mul") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604 (Int cascade — precondition for Nat.mul_comm →
//! Int.mul_comm). Sibling proofs:
//! - `algebra_nat_mul_zero_proof.rs` (#3551, Nat.mul_zero via pure Eq.refl).
//! - `algebra_nat_succ_mul_proof.rs` (#3604, companion for Nat.mul_comm).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatZeroMulConsts {
    nat_type: Expr,
    nat_mul: Expr,
    nat_zero: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
}

impl NatZeroMulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }
}

/// Build `∀ a : Nat, Eq Nat (Nat.mul Nat.zero a) Nat.zero`.
fn build_type(c: &NatZeroMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let lhs = Expr::app(Expr::app(c.nat_mul.clone(), c.nat_zero.clone()), a);
    let concl = Expr::apps(
        c.eq_const.clone(),
        [c.nat_type.clone(), lhs, c.nat_zero.clone()],
    );
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), concl);
    b.finish(ty_raw)
}

/// Motive: `λ (t : Nat) => Eq Nat (Nat.mul Nat.zero t) Nat.zero`.
fn build_motive(c: &NatZeroMulConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let m_lhs = Expr::app(Expr::app(c.nat_mul.clone(), c.nat_zero.clone()), t);
    let body = Expr::apps(
        c.eq_const.clone(),
        [c.nat_type.clone(), m_lhs, c.nat_zero.clone()],
    );
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Step case: `λ (k : Nat) (ih : Eq (Nat.mul Nat.zero k) Nat.zero) => ih`.
///
/// motive (Nat.succ k) ≡ Eq (Nat.mul Nat.zero (Nat.succ k)) Nat.zero, which
/// kernel-reduces (iota succ-case on Nat.rec for Nat.mul, then iota zero-case
/// on the outer add: Nat.add x Nat.zero ≡ x) to
/// Eq (Nat.mul Nat.zero k) Nat.zero — the type of `ih`.
fn build_step(c: &NatZeroMulConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (k_id, _k) = sb.fresh_local(c.nat_type.clone());
    let ih_lhs = Expr::app(Expr::app(c.nat_mul.clone(), c.nat_zero.clone()), _k.clone());
    let ih_type = Expr::apps(
        c.eq_const.clone(),
        [c.nat_type.clone(), ih_lhs, c.nat_zero.clone()],
    );
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, ih);
    let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_k)
}

/// Body: `λ (a : Nat) => @Nat.rec.{0} motive base step a`.
fn build_value(c: &NatZeroMulConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.nat_type.clone());
    let motive = build_motive(c, &vb);
    let base = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), c.nat_zero.clone()]);
    let step = build_step(c, &vb);
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, va]);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Nat.zero_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Nat.zero_mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_zero_mul_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.zero_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let c = NatZeroMulConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on
        // `a` via `Nat.rec.{0}`. Base case: `Eq.refl Nat.zero` (motive at
        // Nat.zero reduces via iota zero-case + delta on Nat.mul to
        // `Eq Nat.zero Nat.zero`). Step case: `λ k ih => ih` — motive at
        // `Nat.succ k` reduces (iota succ on mul's Nat.rec, then iota zero
        // on the outer add: Nat.add x Nat.zero ≡ x) to the ih type.
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
    fn test_nat_zero_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_zero_mul_proof()
            .expect("first registration");
        env.register_nat_zero_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.zero_mul"))
            .expect("Nat.zero_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_zero_mul_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_zero_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.zero_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.zero_mul proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The proof root is an `@Nat.rec.{0}` application. Guards against a
    /// trivial `Eq.refl` masquerade.
    #[test]
    fn test_nat_zero_mul_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_zero_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.zero_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let inner_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = inner_body.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.zero_mul proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_nat_zero_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_zero_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.zero_mul"))
            .expect("Nat.zero_mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.zero_mul must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
