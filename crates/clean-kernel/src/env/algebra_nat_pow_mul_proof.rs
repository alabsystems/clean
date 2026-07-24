// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.pow_mul : ∀ (a m n : Nat),
//!     Eq Nat (Nat.pow a (Nat.mul m n)) (Nat.pow (Nat.pow a m) n)`.
//!
//! Built by induction on `n` via `@Nat.rec.{0}`, hand-constructed `Expr`
//! (no tactics). Consumes the constructive `Nat.pow_add` (this lane).
//!
//! # Proof sketch
//!
//! `Nat.pow`, `Nat.mul` are reducible Definitions recursing on their SECOND
//! argument:
//!
//! ```text
//! Nat.pow a Nat.zero      = Nat.succ Nat.zero
//! Nat.pow a (Nat.succ n)  = Nat.mul (Nat.pow a n) a
//! Nat.mul m Nat.zero      = Nat.zero
//! Nat.mul m (Nat.succ n)  = Nat.add (Nat.mul m n) m
//! ```
//!
//! We induct on `n` (with `a`, `m` fixed lambda-bound parameters) via
//! `@Nat.rec.{0}` with motive
//! `λ t : Nat => Eq Nat (Nat.pow a (Nat.mul m t)) (Nat.pow (Nat.pow a m) t)`.
//!
//! - **base (`t = Nat.zero`)**: goal
//!   `Eq Nat (Nat.pow a (Nat.mul m 0)) (Nat.pow (Nat.pow a m) 0)`.
//!   The LHS reduces: `Nat.mul m 0 ι→ 0`, then `Nat.pow a 0 ι→ 1`. The RHS
//!   reduces: `Nat.pow (Nat.pow a m) 0 ι→ 1`. Hence the goal is defeq to
//!   `Eq Nat 1 1`, closed by `@Eq.refl.{1} Nat 1`.
//!
//! - **step (`t = Nat.succ k`)**: given
//!   `ih : Eq Nat (Nat.pow a (Nat.mul m k)) (Nat.pow (Nat.pow a m) k)`,
//!   the goal is
//!   `Eq Nat (Nat.pow a (Nat.mul m (succ k))) (Nat.pow (Nat.pow a m) (succ k))`.
//!   The LHS reduces: `Nat.mul m (succ k) ι→ Nat.add (Nat.mul m k) m`, so
//!   `Nat.pow a (Nat.mul m (succ k)) ≡ Nat.pow a (Nat.add (Nat.mul m k) m)`.
//!   The RHS reduces: `Nat.pow (Nat.pow a m) (succ k) ι→
//!   Nat.mul (Nat.pow (Nat.pow a m) k) (Nat.pow a m)`. Thus the goal is defeq
//!   to
//!   `Eq Nat (Nat.pow a (Nat.add (Nat.mul m k) m))
//!           (Nat.mul (Nat.pow (Nat.pow a m) k) (Nat.pow a m))`.
//!   We close it with `Eq.trans h_add h_ih` where
//!   * `h_add := Nat.pow_add a (Nat.mul m k) m`
//!       : `Eq Nat (Nat.pow a (Nat.add (Nat.mul m k) m))
//!                 (Nat.mul (Nat.pow a (Nat.mul m k)) (Nat.pow a m))`,
//!   * `h_ih := congrArg (λ z => Nat.mul z (Nat.pow a m)) ih`
//!       : `Eq Nat (Nat.mul (Nat.pow a (Nat.mul m k)) (Nat.pow a m))
//!                 (Nat.mul (Nat.pow (Nat.pow a m) k) (Nat.pow a m))`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.zero`, `Nat.succ`, `Nat.mul`,
//! `Nat.pow`, `Nat.rec`, `Eq`, `Eq.refl`, `Eq.trans`, `congrArg`, and the
//! constructive `Declaration::Theorem` `Nat.pow_add` (this lane). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Nat.pow_mul")` is empty and
//! `env.proof_quality("Nat.pow_mul") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatPowMulConsts {
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    nat_rec: Expr,
    nat_pow_add: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl NatPowMulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_pow_add: Expr::const_(Name::from_string("Nat.pow_add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β} (f : α→β) {a₁ a₂} (h : a₁=a₂) → f a₁ = f a₂.
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn one(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), x), y)
    }

    fn pow(&self, a: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_pow.clone(), a), n)
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }
}

/// Build the statement
/// `∀ a m n : Nat, Eq Nat (Nat.pow a (Nat.mul m n)) (Nat.pow (Nat.pow a m) n)`.
fn build_type(c: &NatPowMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let lhs = c.pow(a.clone(), c.mul(m.clone(), n.clone()));
    let rhs = c.pow(c.pow(a.clone(), m.clone()), n.clone());
    let concl = c.eq_nat(lhs, rhs);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Body:
/// `λ (a m n : Nat) => @Nat.rec.{0} motive base step n`.
fn build_value(c: &NatPowMulConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.nat_type.clone());
    let (m_id, m) = vb.fresh_local(c.nat_type.clone());
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    // motive: λ (t : Nat) => Eq Nat (Nat.pow a (Nat.mul m t))
    //                               (Nat.pow (Nat.pow a m) t)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let lhs = c.pow(a.clone(), c.mul(m.clone(), t.clone()));
        let rhs = c.pow(c.pow(a.clone(), m.clone()), t.clone());
        let body = c.eq_nat(lhs, rhs);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // base: motive(Nat.zero) is defeq to Eq Nat 1 1
    // (LHS: Nat.mul m 0 → 0, Nat.pow a 0 → 1; RHS: Nat.pow (pow a m) 0 → 1).
    // Closed by @Eq.refl.{1} Nat 1.
    let base = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), c.one()]);

    // step: λ (k : Nat) (ih : motive k) => Eq.trans h_add h_ih
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let pow_am = c.pow(a.clone(), m.clone());
        let mul_mk = c.mul(m.clone(), k.clone());
        let ih_lhs = c.pow(a.clone(), mul_mk.clone());
        let ih_rhs = c.pow(pow_am.clone(), k.clone());
        let ih_type = c.eq_nat(ih_lhs.clone(), ih_rhs.clone());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        // h_add := Nat.pow_add a (Nat.mul m k) m
        //   : Eq Nat (Nat.pow a (Nat.add (Nat.mul m k) m))
        //            (Nat.mul (Nat.pow a (Nat.mul m k)) (Nat.pow a m))
        let h_add = Expr::apps(
            c.nat_pow_add.clone(),
            [a.clone(), mul_mk.clone(), m.clone()],
        );

        // mul_right_powam := λ z => Nat.mul z (Nat.pow a m)
        let mul_right_powam = {
            let mut fb = EnvDeclBuilder::child_of(&sb);
            let (z_id, z) = fb.fresh_local(c.nat_type.clone());
            let body = c.mul(z, pow_am.clone());
            let lam = fb.mk_lam(z_id, BinderInfo::Default, c.nat_type.clone(), body);
            fb.finish_child(lam)
        };

        // h_ih := congrArg (λ z => Nat.mul z (Nat.pow a m)) ih
        //   : Eq Nat (Nat.mul (Nat.pow a (Nat.mul m k)) (Nat.pow a m))
        //            (Nat.mul (Nat.pow (Nat.pow a m) k) (Nat.pow a m))
        let h_ih = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.nat_type.clone(),
                ih_lhs.clone(),
                ih_rhs.clone(),
                mul_right_powam,
                ih,
            ],
        );

        // Eq.trans Nat X Y Z h_add h_ih where
        //   X = Nat.pow a (Nat.add (Nat.mul m k) m)  [via h_add LHS]
        //   Y = Nat.mul (Nat.pow a (Nat.mul m k)) (Nat.pow a m)
        //   Z = Nat.mul (Nat.pow (Nat.pow a m) k) (Nat.pow a m)
        // X is supplied as the syntactic form `Nat.pow a (Nat.mul m (succ k))`
        // (defeq to the reduced add-form), matching the motive at `succ k`.
        let x = c.pow(a.clone(), c.mul(m.clone(), c.succ(k.clone())));
        let y = c.mul(ih_lhs, pow_am.clone());
        let z = c.mul(ih_rhs, pow_am);
        let trans = Expr::apps(
            c.eq_trans.clone(),
            [c.nat_type.clone(), x, y, z, h_add, h_ih],
        );

        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val_raw = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = vb.mk_lam(a_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Nat.pow_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.pow`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.trans`,
    ///           `congrArg`.
    /// REQUIRES: `Nat.pow_add` is registered as a constructive
    ///           `Declaration::Theorem` (see `register_nat_pow_add_proof`).
    /// ENSURES: On success, `Nat.pow_mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.pow_mul` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_pow_mul_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependency: Nat.pow_add (this lane).
        self.register_nat_pow_add_proof()?;

        let c = NatPowMulConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Induction on `n` via
        // `@Nat.rec.{0}` with `a`, `m` fixed parameters. Base case
        // `@Eq.refl.{1} Nat 1` (after the kernel reduces both sides to `1`).
        // Step case `Eq.trans (Nat.pow_add a (Nat.mul m k) m)
        //                      (congrArg (λ z => Nat.mul z (Nat.pow a m)) ih)`
        // after the kernel reduces `Nat.mul m (succ k) → Nat.add (Nat.mul m k) m`
        // and `Nat.pow (Nat.pow a m) (succ k)` (iota + delta). No `sorry`, no
        // self-reference, no domain-axiom dependency (`Nat.pow_add` is itself
        // constructive).
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

    /// Kernel accepts the `Nat.rec` / `Eq.trans` / `Nat.pow_add` proof term.
    /// Verifies the theorem is registered as a Theorem (not Axiom) and
    /// idempotent re-invocation is a no-op.
    #[test]
    fn test_nat_pow_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_pow_mul_proof()
            .expect("first registration");
        env.register_nat_pow_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.pow_mul"))
            .expect("Nat.pow_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the three outer λ binders) must be a
    /// `@Nat.rec.{0}` application. Guards against an axiom-wrapping masquerade.
    #[test]
    fn test_nat_pow_mul_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_pow_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.pow_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut body = value.clone();
        for _ in 0..3 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.pow_mul proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_nat_pow_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_pow_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.pow_mul"))
            .expect("Nat.pow_mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.pow_mul must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
