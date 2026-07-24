// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.pow_le_pow_right : ∀ a m n : Nat,
//!    Nat.le (Nat.succ Nat.zero) a → Nat.le m n →
//!    Nat.le (Nat.pow a m) (Nat.pow a n)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_arith.rs::init_nat_pow_ord` with a `Declaration::Theorem` whose proof
//! term is built by induction on the `Nat.le m n` witness via `@Nat.le.rec`.
//!
//! # Definitions in play
//!
//! `Nat.pow` recurses on its SECOND argument (see `data_types_nat.rs`):
//!
//! ```text
//! Nat.pow a Nat.zero      = Nat.succ Nat.zero
//! Nat.pow a (Nat.succ k)  = Nat.mul (Nat.pow a k) a
//! ```
//!
//! `Nat.mul` recurses on its SECOND argument:
//! `Nat.mul x (Nat.succ k) = Nat.add (Nat.mul x k) x`, so
//! `Nat.mul (a^t) (Nat.succ Nat.zero) = Nat.add (Nat.mul (a^t) Nat.zero) (a^t)`
//! — which is NOT definitionally `a^t` (it reduces to `Nat.add Nat.zero (a^t)`).
//! We therefore transport along the constructive `Nat.mul_one (a^t)` rather than
//! relying on defeq for the `· * 1` simplification.
//!
//! # Proof sketch
//!
//! Given `a : Nat` and `h1 : Nat.le (Nat.succ Nat.zero) a` (`1 ≤ a`), and
//! `m n : Nat` with `hmn : Nat.le m n`, we induct on `hmn` via `@Nat.le.rec`
//! (parameter `m`) with motive `λ (t : Nat) (_ : Nat.le m t) => Nat.le (a^m) (a^t)`:
//!
//! - **refl minor**: `Nat.le (a^m) (a^m)` = `Nat.le.refl (a^m)`.
//!
//! - **step minor**: given `t`, `_ : Nat.le m t`, and `ih : Nat.le (a^m) (a^t)`,
//!   the goal `Nat.le (a^m) (a^(succ t))` reduces to `Nat.le (a^m) ((a^t)*a)`.
//!   We chain `ih` with the one-step monotonicity `Nat.le (a^t) ((a^t)*a)` via
//!   `Nat.le_trans`. The one-step fact is
//!   `@Eq.subst Nat (λ z => Nat.le z ((a^t)*a)) ((a^t)*1) (a^t)
//!       (Nat.mul_one (a^t)) (Nat.mul_le_mul_left 1 a (a^t) h1)`,
//!   where `Nat.mul_le_mul_left 1 a (a^t) h1 : Nat.le ((a^t)*1) ((a^t)*a)`
//!   (`Nat.mul_le_mul_left : ∀ a b c, a ≤ b → c*a ≤ c*b`).
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.zero`, `Nat.succ`, `Nat.pow`,
//! `Nat.mul`, `Nat.le`, `Nat.le.refl`, `Nat.le.rec`, `Eq.subst`, and the
//! constructive `Declaration::Theorem`s `Nat.le_trans`, `Nat.mul_le_mul_left`,
//! `Nat.mul_one`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Nat.pow_le_pow_right")` is empty and the proof quality is
//! `Constructive`.
//!
//! Tracks issue #3604 (kernel-soundness arithmetic-ordering demotion vein).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatPowLePowRightConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    pow: Expr,
    mul: Expr,
    le: Expr,
    le_refl_ctor: Expr,
    le_rec: Expr,
    le_trans_thm: Expr,
    mul_le_mul_left_thm: Expr,
    mul_one_thm: Expr,
    /// `Eq.subst.{1}` over `Nat`.
    eq_subst: Expr,
}

impl NatPowLePowRightConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            le_trans_thm: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            mul_le_mul_left_thm: Expr::const_(Name::from_string("Nat.mul_le_mul_left"), vec![]),
            mul_one_thm: Expr::const_(Name::from_string("Nat.mul_one"), vec![]),
            eq_subst: Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
        }
    }

    fn one(&self) -> Expr {
        Expr::app(self.succ.clone(), self.zero.clone())
    }

    fn pow_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [m, n])
    }

    fn mul_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [x, y])
    }

    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }

    fn le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }

    fn le_trans(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans_thm.clone(), [a, b, c, hab, hbc])
    }
}

/// Build
/// `∀ a m n : Nat, Nat.le 1 a → Nat.le m n → Nat.le (Nat.pow a m) (Nat.pow a n)`.
fn build_type(c: &NatPowLePowRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h1_type = c.le_of(c.one(), a.clone());
    let (h1_id, _h1) = b.fresh_local(h1_type.clone());
    let hmn_type = c.le_of(m.clone(), n.clone());
    let (hmn_id, _hmn) = b.fresh_local(hmn_type.clone());
    let concl = c.le_of(
        c.pow_of(a.clone(), m.clone()),
        c.pow_of(a.clone(), n.clone()),
    );
    let e = b.mk_pi(hmn_id, BinderInfo::Default, hmn_type, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Body: `λ a m n (h1 : 1 ≤ a) (hmn : m ≤ n) => @Nat.le.rec m motive refl step n hmn`.
fn build_value(c: &NatPowLePowRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h1_type = c.le_of(c.one(), a.clone());
    let (h1_id, h1) = b.fresh_local(h1_type.clone());
    let hmn_type = c.le_of(m.clone(), n.clone());
    let (hmn_id, hmn) = b.fresh_local(hmn_type.clone());

    let pow_a_m = c.pow_of(a.clone(), m.clone());

    // motive: λ (t : Nat) (_ : Nat.le m t) => Nat.le (a^m) (a^t)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let le_m_t = c.le_of(m.clone(), t.clone());
        let (ht_id, _ht) = mb.fresh_local(le_m_t.clone());
        let body = c.le_of(pow_a_m.clone(), c.pow_of(a.clone(), t.clone()));
        let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_m_t, body);
        let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
        mb.finish_child(lam_t)
    };

    // refl minor: Nat.le.refl (a^m)
    let minor_refl = c.le_refl_app(pow_a_m.clone());

    // step minor: λ {t} (_ : Nat.le m t) (ih : Nat.le (a^m) (a^t)) =>
    //   Nat.le_trans (a^m) (a^t) ((a^t)*a) ih step_le
    //     : Nat.le (a^m) ((a^t)*a) ≡ Nat.le (a^m) (a^(succ t))
    // where step_le : Nat.le (a^t) ((a^t)*a)
    //   := @Eq.subst Nat (λ z => Nat.le z ((a^t)*a)) ((a^t)*1) (a^t)
    //        (Nat.mul_one (a^t)) (Nat.mul_le_mul_left 1 a (a^t) h1)
    let minor_step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = sb.fresh_local(c.nat.clone());
        let le_m_t = c.le_of(m.clone(), t.clone());
        let (ht_id, _ht) = sb.fresh_local(le_m_t.clone());
        let pow_a_t = c.pow_of(a.clone(), t.clone());
        let ih_type = c.le_of(pow_a_m.clone(), pow_a_t.clone());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        let pow_a_t_mul_a = c.mul_of(pow_a_t.clone(), a.clone()); // (a^t)*a
        let pow_a_t_mul_one = c.mul_of(pow_a_t.clone(), c.one()); // (a^t)*1

        // subst motive: λ (z : Nat) => Nat.le z ((a^t)*a)
        let subst_motive = {
            let mut zb = EnvDeclBuilder::child_of(&sb);
            let (z_id, z) = zb.fresh_local(c.nat.clone());
            let body = c.le_of(z, pow_a_t_mul_a.clone());
            let lam = zb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
            zb.finish_child(lam)
        };
        // Nat.mul_one (a^t) : Nat.mul (a^t) (succ 0) = a^t
        let mul_one_eq = Expr::app(c.mul_one_thm.clone(), pow_a_t.clone());
        // Nat.mul_le_mul_left 1 a (a^t) h1 : Nat.le ((a^t)*1) ((a^t)*a)
        let mll = Expr::apps(
            c.mul_le_mul_left_thm.clone(),
            [c.one(), a.clone(), pow_a_t.clone(), h1.clone()],
        );
        // step_le : Nat.le (a^t) ((a^t)*a)
        let step_le = Expr::apps(
            c.eq_subst.clone(),
            [
                c.nat.clone(),
                subst_motive,
                pow_a_t_mul_one,
                pow_a_t.clone(),
                mul_one_eq,
                mll,
            ],
        );
        // Nat.le_trans (a^m) (a^t) ((a^t)*a) ih step_le
        let body = c.le_trans(pow_a_m.clone(), pow_a_t.clone(), pow_a_t_mul_a, ih, step_le);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
        let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_m_t, lam_ih);
        let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam_h);
        sb.finish_child(lam_t)
    };

    let rec_app = Expr::apps(
        c.le_rec.clone(),
        [
            m.clone(),
            motive,
            minor_refl,
            minor_step,
            n.clone(),
            hmn.clone(),
        ],
    );
    let e = b.mk_lam(hmn_id, BinderInfo::Default, hmn_type, rec_app);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Nat.pow_le_pow_right` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.pow`.
    /// REQUIRES: `self.init_le()` has registered `Nat.le`, `Nat.le.refl`,
    ///           `Nat.le.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`.
    /// REQUIRES: The constructive `Nat.le_trans`, `Nat.mul_le_mul_left`,
    ///           `Nat.mul_one` theorems are available.
    /// ENSURES: On success, `Nat.pow_le_pow_right` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_pow_le_pow_right_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_le_pow_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        self.init_eq()?;
        // Constructive dependencies: Nat.mul_le_mul_left, Nat.le_trans (via the
        // arith-order proofs), and Nat.mul_one.
        self.register_nat_arith_order_proofs()?;
        self.register_nat_mul_one_proof()?;

        let c = NatPowLePowRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on the
        // `Nat.le m n` witness via `@Nat.le.rec`. Refl minor `Nat.le.refl (a^m)`,
        // step minor chains the IH with the one-step monotonicity
        // `Nat.le (a^t) ((a^t)*a)` (built by transporting
        // `Nat.mul_le_mul_left 1 a (a^t) h1 : Nat.le ((a^t)*1) ((a^t)*a)` along
        // `Nat.mul_one (a^t)` via `@Eq.subst.{1}`) through `Nat.le_trans`, with
        // the kernel reducing `Nat.pow a (succ t)` to `Nat.mul (Nat.pow a t) a`.
        // No `sorry`, no self-reference, no domain-axiom dependency. Replaces the
        // prior `Declaration::Axiom` in `order_arith.rs::init_nat_pow_ord`.
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
    fn test_nat_pow_le_pow_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_right_proof()
            .expect("first registration");
        env.register_nat_pow_le_pow_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.pow_le_pow_right"))
            .expect("Nat.pow_le_pow_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_pow_le_pow_right_proof_uses_le_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_right_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.pow_le_pow_right"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the five outer λ binders (a, m, n, h1, hmn).
        let mut body = value.clone();
        for _ in 0..5 {
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
                "Nat.le.rec",
                "Nat.pow_le_pow_right proof root must be Nat.le.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.le.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_nat_pow_le_pow_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.pow_le_pow_right"))
            .expect("Nat.pow_le_pow_right is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.pow_le_pow_right must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_nat_pow_le_pow_right_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_right_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Nat.pow_le_pow_right"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Nat.pow_le_pow_right must be Constructive, got {:?}",
            quality
        );
    }
}
