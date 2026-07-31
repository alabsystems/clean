// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.one_pow : ∀ n : Nat, Eq Nat (Nat.pow (Nat.succ Nat.zero) n) (Nat.succ Nat.zero)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_arith.rs::init_nat_pow_ord` with a `Declaration::Theorem` whose
//! proof term is built by induction on `n` via `@Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.pow` is a reducible Definition (see `data_types_nat.rs`) that
//! recurses on its SECOND argument:
//!
//! ```text
//! Nat.pow m n := Nat.rec (Nat.succ Nat.zero) (λ _ ih => Nat.mul ih m) n
//! Nat.pow m Nat.zero      = Nat.succ Nat.zero
//! Nat.pow m (Nat.succ n)  = Nat.mul (Nat.pow m n) m
//! ```
//!
//! We induct on `n` via `@Nat.rec.{0}` with motive
//! `λ t : Nat => Eq Nat (Nat.pow (Nat.succ Nat.zero) t) (Nat.succ Nat.zero)`,
//! writing `1` for `Nat.succ Nat.zero`:
//!
//! - **base (`n = Nat.zero`)**: `Nat.pow 1 Nat.zero` reduces to `1` by the
//!   zero iota-case of `Nat.pow` + delta. The goal `Eq Nat (Nat.pow 1 0) 1`
//!   is therefore defeq to `Eq Nat 1 1`, closed by `@Eq.refl.{1} Nat 1`.
//!
//! - **step (`n = Nat.succ k`)**: given `ih : Eq Nat (Nat.pow 1 k) 1`, the
//!   goal is `Eq Nat (Nat.pow 1 (Nat.succ k)) 1`. The LHS reduces:
//!   `Nat.pow 1 (Nat.succ k) ι→ Nat.mul (Nat.pow 1 k) 1`. The constructive
//!   theorem `Nat.mul_one (Nat.pow 1 k) : Eq Nat (Nat.mul (Nat.pow 1 k) 1)
//!   (Nat.pow 1 k)` is therefore (defeq) a proof of
//!   `Eq Nat (Nat.pow 1 (Nat.succ k)) (Nat.pow 1 k)`. Chaining with `ih`
//!   via `Eq.trans` closes the goal:
//!   `Eq.trans Nat (Nat.pow 1 (succ k)) (Nat.pow 1 k) 1
//!      (Nat.mul_one (Nat.pow 1 k)) ih`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.zero`, `Nat.succ`, `Nat.pow`,
//! `Nat.rec`, `Eq`, `Eq.refl`, `Eq.trans`, and the constructive
//! `Declaration::Theorem` `Nat.mul_one` (#3551). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Nat.one_pow")` is empty and
//! `env.proof_quality("Nat.one_pow") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604 (kernel-soundness Tier 6). Sibling proofs:
//! - `algebra_int_sub_nat_nat_self_proof.rs` (#3604, `Nat.rec` + `Eq.trans`).
//! - `algebra_nat_pow_one_proof.rs` (#3604, companion — via `Nat.one_mul`).

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
#[cfg(test)]
struct NatOnePowConsts {
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_rec: Expr,
    nat_mul_one: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
}

#[cfg(test)]
impl NatOnePowConsts {
    #[cfg(test)]
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_mul_one: Expr::const_(Name::from_string("Nat.mul_one"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
        }
    }

    #[cfg(test)]
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    #[cfg(test)]
    fn one(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }

    #[cfg(test)]
    fn pow(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_pow.clone(), m), n)
    }

    #[cfg(test)]
    fn pow_one_base(&self, n: Expr) -> Expr {
        self.pow(self.one(), n)
    }

    #[cfg(test)]
    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }
}

/// Build `∀ n : Nat, Eq Nat (Nat.pow (Nat.succ Nat.zero) n) (Nat.succ Nat.zero)`.
#[cfg(test)]
fn build_type(c: &NatOnePowConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_nat(c.pow_one_base(n), c.one());
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    b.finish(ty_raw)
}

/// Body: `λ (n : Nat) => @Nat.rec.{0} motive base step n`.
#[cfg(test)]
fn build_value(c: &NatOnePowConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    // motive: λ (t : Nat) => Eq Nat (Nat.pow 1 t) 1
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_nat(c.pow_one_base(t), c.one());
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // base: @Eq.refl.{1} Nat 1. motive(Nat.zero) reduces LHS `Nat.pow 1 0`
    // to `1` via the zero iota-case of `Nat.pow`.
    let base = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), c.one()]);

    // step: λ (k : Nat) (ih : Eq Nat (Nat.pow 1 k) 1) =>
    //   Eq.trans Nat (Nat.pow 1 (succ k)) (Nat.pow 1 k) 1
    //     (Nat.mul_one (Nat.pow 1 k)) ih
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_type = c.eq_nat(c.pow_one_base(k.clone()), c.one());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        // h1 := Nat.mul_one (Nat.pow 1 k)
        //    : Eq Nat (Nat.mul (Nat.pow 1 k) 1) (Nat.pow 1 k)
        // defeq to Eq Nat (Nat.pow 1 (succ k)) (Nat.pow 1 k).
        let h1 = Expr::app(c.nat_mul_one.clone(), c.pow_one_base(k.clone()));

        let lhs = c.pow_one_base(c.succ(k.clone()));
        let mid = c.pow_one_base(k.clone());
        let trans = Expr::apps(
            c.eq_trans.clone(),
            [c.nat_type.clone(), lhs, mid, c.one(), h1, ih],
        );

        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val_raw = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    vb.finish(val_raw)
}

#[cfg(test)]
impl Environment {
    /// Register `Nat.one_pow` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.pow`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.trans`,
    ///           `congrArg`.
    /// REQUIRES: `Nat.mul_one` is registered as `Declaration::Theorem`
    ///           (constructive — see `register_nat_mul_one_proof`).
    /// ENSURES: On success, `Nat.one_pow` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.one_pow` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    #[cfg(test)]
    pub(crate) fn register_nat_one_pow_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.one_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependency: Nat.mul a (succ zero) = a.
        self.register_nat_mul_one_proof()?;

        let c = NatOnePowConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on `n`
        // via `@Nat.rec.{0}`. Base case `@Eq.refl.{1}` (zero iota-case of
        // `Nat.pow`). Step case `Eq.trans (Nat.mul_one (Nat.pow 1 k)) ih`,
        // threading the constructive `Nat.mul_one` after the kernel reduces
        // `Nat.pow 1 (succ k)` to `Nat.mul (Nat.pow 1 k) 1` (iota + delta).
        // No `sorry`, no self-reference, no domain-axiom dependency
        // (`Nat.mul_one` is itself constructive #3551). Replaces the prior
        // `Declaration::Axiom` in `order_arith.rs::init_nat_pow_ord`.
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

    /// Kernel accepts the `Nat.rec` / `Eq.trans` proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_nat_one_pow_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_one_pow_proof()
            .expect("first registration");
        env.register_nat_one_pow_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.one_pow"))
            .expect("Nat.one_pow should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the outer λ binder) must be a `@Nat.rec.{0}`
    /// application. Guards against a trivial axiom-wrapping masquerade.
    #[test]
    fn test_nat_one_pow_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_one_pow_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.one_pow"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => (**body).clone(),
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = outer_body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.one_pow proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_nat_one_pow_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_one_pow_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.one_pow"))
            .expect("Nat.one_pow is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.one_pow must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
