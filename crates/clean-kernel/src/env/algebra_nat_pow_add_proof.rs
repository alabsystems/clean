// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.pow_add : ∀ (a m n : Nat),
//!     Eq Nat (Nat.pow a (Nat.add m n)) (Nat.mul (Nat.pow a m) (Nat.pow a n))`.
//!
//! Built by induction on `n` via `@Nat.rec.{0}`, hand-constructed `Expr`
//! (no tactics). Foundational `Nat.rec` lemma, broadly reusable.
//!
//! # Proof sketch
//!
//! `Nat.pow` is a reducible Definition (see `data_types_nat.rs`) that
//! recurses on its SECOND argument; `Nat.add` likewise recurses on its
//! second argument:
//!
//! ```text
//! Nat.pow a Nat.zero      = Nat.succ Nat.zero
//! Nat.pow a (Nat.succ n)  = Nat.mul (Nat.pow a n) a
//! Nat.add m Nat.zero      = m
//! Nat.add m (Nat.succ n)  = Nat.succ (Nat.add m n)
//! ```
//!
//! We induct on `n` (with `a`, `m` fixed lambda-bound parameters) via
//! `@Nat.rec.{0}` with motive
//! `λ t : Nat => Eq Nat (Nat.pow a (Nat.add m t))
//!                      (Nat.mul (Nat.pow a m) (Nat.pow a t))`.
//!
//! - **base (`t = Nat.zero`)**: goal
//!   `Eq Nat (Nat.pow a (Nat.add m 0)) (Nat.mul (Nat.pow a m) (Nat.pow a 0))`.
//!   The LHS reduces: `Nat.add m 0 ι→ m`, so `Nat.pow a (Nat.add m 0) ≡
//!   Nat.pow a m`. The RHS reduces: `Nat.pow a 0 ι→ 1`, so RHS ≡
//!   `Nat.mul (Nat.pow a m) 1`. Hence the goal is defeq to
//!   `Eq Nat (Nat.pow a m) (Nat.mul (Nat.pow a m) 1)`, which is
//!   `Eq.symm (Nat.mul_one (Nat.pow a m))` — using the constructive theorem
//!   `Nat.mul_one x : Eq Nat (Nat.mul x 1) x`.
//!
//! - **step (`t = Nat.succ k`)**: given
//!   `ih : Eq Nat (Nat.pow a (Nat.add m k)) (Nat.mul (Nat.pow a m) (Nat.pow a k))`,
//!   the goal is
//!   `Eq Nat (Nat.pow a (Nat.add m (succ k)))
//!           (Nat.mul (Nat.pow a m) (Nat.pow a (succ k)))`.
//!   The LHS reduces: `Nat.add m (succ k) ι→ succ (Nat.add m k)`, then
//!   `Nat.pow a (succ (Nat.add m k)) ι→ Nat.mul (Nat.pow a (Nat.add m k)) a`.
//!   The RHS reduces: `Nat.pow a (succ k) ι→ Nat.mul (Nat.pow a k) a`, so RHS ≡
//!   `Nat.mul (Nat.pow a m) (Nat.mul (Nat.pow a k) a)`. Thus the goal is defeq
//!   to
//!   `Eq Nat (Nat.mul (Nat.pow a (Nat.add m k)) a)
//!           (Nat.mul (Nat.pow a m) (Nat.mul (Nat.pow a k) a))`.
//!   We close it with `Eq.trans h1 h2` where
//!   * `h1 := congrArg (λ z => Nat.mul z a) ih`
//!       : `Eq Nat (Nat.mul (Nat.pow a (Nat.add m k)) a)
//!                 (Nat.mul (Nat.mul (Nat.pow a m) (Nat.pow a k)) a)`,
//!   * `h2 := Nat.mul_assoc (Nat.pow a m) (Nat.pow a k) a`
//!       : `Eq Nat (Nat.mul (Nat.mul (Nat.pow a m) (Nat.pow a k)) a)
//!                 (Nat.mul (Nat.pow a m) (Nat.mul (Nat.pow a k) a))`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`,
//! `Nat.mul`, `Nat.pow`, `Nat.rec`, `Eq`, `Eq.symm`, `Eq.trans`, `congrArg`,
//! and the constructive `Declaration::Theorem`s `Nat.mul_one` (#3551) and
//! `Nat.mul_assoc` (#3604). None are `Declaration::Axiom`, so
//! `env.axiom_deps("Nat.pow_add")` is empty and
//! `env.proof_quality("Nat.pow_add") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatPowAddConsts {
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    nat_rec: Expr,
    nat_mul_one: Expr,
    nat_mul_assoc: Expr,
    eq_const: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl NatPowAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_mul_one: Expr::const_(Name::from_string("Nat.mul_one"), vec![]),
            nat_mul_assoc: Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
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

    fn add(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), m), n)
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
/// `∀ a m n : Nat, Eq Nat (Nat.pow a (Nat.add m n))
///                        (Nat.mul (Nat.pow a m) (Nat.pow a n))`.
fn build_type(c: &NatPowAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let lhs = c.pow(a.clone(), c.add(m.clone(), n.clone()));
    let rhs = c.mul(c.pow(a.clone(), m.clone()), c.pow(a.clone(), n.clone()));
    let concl = c.eq_nat(lhs, rhs);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Body:
/// `λ (a m n : Nat) => @Nat.rec.{0} motive base step n`.
fn build_value(c: &NatPowAddConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.nat_type.clone());
    let (m_id, m) = vb.fresh_local(c.nat_type.clone());
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    // motive: λ (t : Nat) => Eq Nat (Nat.pow a (Nat.add m t))
    //                               (Nat.mul (Nat.pow a m) (Nat.pow a t))
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let lhs = c.pow(a.clone(), c.add(m.clone(), t.clone()));
        let rhs = c.mul(c.pow(a.clone(), m.clone()), c.pow(a.clone(), t.clone()));
        let body = c.eq_nat(lhs, rhs);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // base: motive(Nat.zero) is defeq to
    //   Eq Nat (Nat.pow a m) (Nat.mul (Nat.pow a m) 1)
    // (LHS: Nat.add m 0 ι→ m; RHS: Nat.pow a 0 ι→ 1). Closed by
    //   Eq.symm Nat (Nat.mul (Nat.pow a m) 1) (Nat.pow a m)
    //     (Nat.mul_one (Nat.pow a m)).
    let base = {
        let pow_am = c.pow(a.clone(), m.clone());
        let mul_one = Expr::app(c.nat_mul_one.clone(), pow_am.clone());
        // Eq.symm α a b (h : a = b) : b = a, here a = Nat.mul (pow a m) 1,
        // b = Nat.pow a m.
        Expr::apps(
            c.eq_symm.clone(),
            [
                c.nat_type.clone(),
                c.mul(pow_am.clone(), c.one()),
                pow_am,
                mul_one,
            ],
        )
    };

    // step: λ (k : Nat) (ih : motive k) => Eq.trans h1 h2
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_lhs = c.pow(a.clone(), c.add(m.clone(), k.clone()));
        let pow_am = c.pow(a.clone(), m.clone());
        let pow_ak = c.pow(a.clone(), k.clone());
        let ih_rhs = c.mul(pow_am.clone(), pow_ak.clone());
        let ih_type = c.eq_nat(ih_lhs.clone(), ih_rhs.clone());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        // mul_right_a := λ z => Nat.mul z a
        let mul_right_a = {
            let mut fb = EnvDeclBuilder::child_of(&sb);
            let (z_id, z) = fb.fresh_local(c.nat_type.clone());
            let body = c.mul(z, a.clone());
            let lam = fb.mk_lam(z_id, BinderInfo::Default, c.nat_type.clone(), body);
            fb.finish_child(lam)
        };

        // h1 := congrArg (λ z => Nat.mul z a) ih
        //   : Eq Nat (Nat.mul (Nat.pow a (Nat.add m k)) a)
        //            (Nat.mul (Nat.mul (Nat.pow a m) (Nat.pow a k)) a)
        let h1 = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.nat_type.clone(),
                ih_lhs.clone(),
                ih_rhs.clone(),
                mul_right_a,
                ih,
            ],
        );

        // h2 := Nat.mul_assoc (Nat.pow a m) (Nat.pow a k) a
        //   : Eq Nat (Nat.mul (Nat.mul (Nat.pow a m) (Nat.pow a k)) a)
        //            (Nat.mul (Nat.pow a m) (Nat.mul (Nat.pow a k) a))
        let h2 = Expr::apps(
            c.nat_mul_assoc.clone(),
            [pow_am.clone(), pow_ak.clone(), a.clone()],
        );

        // Eq.trans Nat X Y Z h1 h2 where
        //   X = Nat.mul (Nat.pow a (Nat.add m k)) a
        //   Y = Nat.mul (Nat.mul (Nat.pow a m) (Nat.pow a k)) a
        //   Z = Nat.mul (Nat.pow a m) (Nat.mul (Nat.pow a k) a)
        let x = c.mul(ih_lhs, a.clone());
        let y = c.mul(ih_rhs, a.clone());
        let z = c.mul(pow_am, c.mul(pow_ak, a.clone()));
        let trans = Expr::apps(c.eq_trans.clone(), [c.nat_type.clone(), x, y, z, h1, h2]);

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
    /// Register `Nat.pow_add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.symm`, `Eq.trans`,
    ///           `congrArg`.
    /// REQUIRES: `Nat.mul_one` and `Nat.mul_assoc` are registered as
    ///           constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Nat.pow_add` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.pow_add` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_pow_add_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_nat_mul_one_proof()?;
        self.register_nat_mul_assoc_proof()?;

        let c = NatPowAddConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Induction on `n` via
        // `@Nat.rec.{0}` with `a`, `m` fixed parameters. Base case
        // `Eq.symm (Nat.mul_one (Nat.pow a m))` (after the kernel reduces
        // `Nat.add m 0 → m` and `Nat.pow a 0 → 1`). Step case
        // `Eq.trans (congrArg (λ z => Nat.mul z a) ih)
        //           (Nat.mul_assoc (Nat.pow a m) (Nat.pow a k) a)`
        // after the kernel reduces `Nat.pow a (Nat.add m (succ k))` and
        // `Nat.pow a (succ k)` (iota + delta). No `sorry`, no self-reference,
        // no domain-axiom dependency (`Nat.mul_one`, `Nat.mul_assoc` are both
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

    /// Kernel accepts the `Nat.rec` / `Eq.trans` / `congrArg` proof term.
    /// Verifies the theorem is registered as a Theorem (not Axiom) and
    /// idempotent re-invocation is a no-op.
    #[test]
    fn test_nat_pow_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_pow_add_proof()
            .expect("first registration");
        env.register_nat_pow_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.pow_add"))
            .expect("Nat.pow_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the three outer λ binders) must be a
    /// `@Nat.rec.{0}` application. Guards against an axiom-wrapping masquerade.
    #[test]
    fn test_nat_pow_add_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_pow_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.pow_add"))
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
                "Nat.pow_add proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_nat_pow_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_pow_add_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.pow_add"))
            .expect("Nat.pow_add is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.pow_add must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
