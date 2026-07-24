// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.pow_le_pow_left : ∀ a b n : Nat, Nat.le a b → Nat.le (Nat.pow a n) (Nat.pow b n)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_arith.rs::init_nat_pow_ord` with a `Declaration::Theorem` whose
//! proof term is built by induction on `n` via `@Nat.rec.{0}`.
//!
//! # Definition in play
//!
//! `Nat.pow` is a reducible Definition (see `data_types_nat.rs`) that recurses
//! on its SECOND argument:
//!
//! ```text
//! Nat.pow m n := Nat.rec (Nat.succ Nat.zero) (λ _ ih => Nat.mul ih m) n
//! Nat.pow m Nat.zero      = Nat.succ Nat.zero
//! Nat.pow m (Nat.succ n)  = Nat.mul (Nat.pow m n) m
//! ```
//!
//! # Proof sketch
//!
//! Given `a b : Nat` and `h : Nat.le a b`, we induct on `n` via `@Nat.rec.{0}`
//! with motive `λ t : Nat => Nat.le (Nat.pow a t) (Nat.pow b t)`:
//!
//! - **base (`n = Nat.zero`)**: `Nat.pow a 0` and `Nat.pow b 0` both reduce to
//!   `Nat.succ Nat.zero` (the zero iota-case of `Nat.pow`). The goal therefore
//!   reduces to `Nat.le 1 1`, closed by `Nat.le.refl (Nat.succ Nat.zero)`.
//!
//! - **step (`n = Nat.succ k`)**: given `ih : Nat.le (Nat.pow a k) (Nat.pow b k)`,
//!   the goal `Nat.le (Nat.pow a (succ k)) (Nat.pow b (succ k))` reduces (iota +
//!   delta on `Nat.pow`) to `Nat.le (Nat.mul (Nat.pow a k) a) (Nat.mul (Nat.pow b k) b)`.
//!   The constructive `Nat.mul_le_mul (Nat.pow a k) (Nat.pow b k) a b ih h`
//!   inhabits exactly this `Nat.le` (`Nat.mul_le_mul : ∀ a b c d, a ≤ b → c ≤ d → a*c ≤ b*d`).
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.zero`, `Nat.succ`, `Nat.pow`,
//! `Nat.rec`, `Nat.le`, `Nat.le.refl`, and the constructive
//! `Declaration::Theorem` `Nat.mul_le_mul` (#3604, see `nat_arith_order_proof.rs`).
//! None are `Declaration::Axiom`, so `env.axiom_deps("Nat.pow_le_pow_left")` is
//! empty and `env.proof_quality("Nat.pow_le_pow_left") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604 (kernel-soundness arithmetic-ordering demotion vein).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatPowLePowLeftConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    pow: Expr,
    /// `Nat.rec.{0}` — Prop-valued motive.
    nat_rec: Expr,
    le: Expr,
    le_refl_ctor: Expr,
    mul_le_mul_thm: Expr,
}

impl NatPowLePowLeftConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            mul_le_mul_thm: Expr::const_(Name::from_string("Nat.mul_le_mul"), vec![]),
        }
    }

    fn one(&self) -> Expr {
        Expr::app(self.succ.clone(), self.zero.clone())
    }

    fn pow_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [m, n])
    }

    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }
}

/// Build `∀ a b n : Nat, Nat.le a b → Nat.le (Nat.pow a n) (Nat.pow b n)`.
fn build_type(c: &NatPowLePowLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bv_id, bv) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h_type = c.le_of(a.clone(), bv.clone());
    let (h_id, _h) = b.fresh_local(h_type.clone());
    let concl = c.le_of(
        c.pow_of(a.clone(), n.clone()),
        c.pow_of(bv.clone(), n.clone()),
    );
    let e = b.mk_pi(h_id, BinderInfo::Default, h_type, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Body: `λ a b n (h : Nat.le a b) => @Nat.rec.{0} motive base step n`.
fn build_value(c: &NatPowLePowLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bv_id, bv) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h_type = c.le_of(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(h_type.clone());

    // motive: λ (t : Nat) => Nat.le (Nat.pow a t) (Nat.pow b t)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let body = c.le_of(
            c.pow_of(a.clone(), t.clone()),
            c.pow_of(bv.clone(), t.clone()),
        );
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };

    // base (t = 0): `Nat.pow a 0 ≡ 1`, `Nat.pow b 0 ≡ 1`, so `Nat.le 1 1` =
    // `Nat.le.refl 1`.
    let base = c.le_refl_app(c.one());

    // step: λ (k : Nat) (ih : Nat.le (Nat.pow a k) (Nat.pow b k)) =>
    //   Nat.mul_le_mul (n₁ := a^k) (m₁ := a) (n₂ := b^k) (m₂ := b) ih h
    //     : Nat.le ((Nat.pow a k) * a) ((Nat.pow b k) * b)
    //     ≡ Nat.le (Nat.pow a (succ k)) (Nat.pow b (succ k))
    // `Nat.mul_le_mul` binds `{n₁ m₁ n₂ m₂}` with `(h₁ : n₁ ≤ n₂)`,
    // `(h₂ : m₁ ≤ m₂)`, concluding `n₁*m₁ ≤ n₂*m₂` (Lean's real pairing, see
    // `nat_arith_order_proof::register_nat_mul_le_mul`). To get
    // `(a^k)*a ≤ (b^k)*b` from `ih : a^k ≤ b^k` and `h : a ≤ b`, instantiate
    // `n₁ := a^k, m₁ := a, n₂ := b^k, m₂ := b` — so the explicit-arg spine is
    // `[a^k, a, b^k, b, ih, h]` (NOT the transposed `[a^k, b^k, a, b, …]`).
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = sb.fresh_local(c.nat.clone());
        let pow_a_k = c.pow_of(a.clone(), k.clone());
        let pow_b_k = c.pow_of(bv.clone(), k.clone());
        let ih_type = c.le_of(pow_a_k.clone(), pow_b_k.clone());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());
        let body = Expr::apps(
            c.mul_le_mul_thm.clone(),
            [pow_a_k, a.clone(), pow_b_k, bv.clone(), ih, h.clone()],
        );
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Nat.pow_le_pow_left` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.pow`, `Nat.rec`.
    /// REQUIRES: `self.init_le()` has registered `Nat.le`, `Nat.le.refl`.
    /// REQUIRES: `Nat.mul_le_mul` is registered as a constructive
    ///           `Declaration::Theorem` (see `register_nat_arith_order_proofs`).
    /// ENSURES: On success, `Nat.pow_le_pow_left` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.pow_le_pow_left` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_pow_le_pow_left_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_le_pow_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        // Constructive dependency: Nat.mul_le_mul (and its le-family support).
        self.register_nat_arith_order_proofs()?;

        let c = NatPowLePowLeftConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on `n`
        // via `@Nat.rec.{0}`. Base case `Nat.le.refl 1` (both powers reduce to
        // `1` at the zero iota-case of `Nat.pow`). Step case
        // `Nat.mul_le_mul (a^k) (b^k) a b ih h`, threading the constructive
        // `Nat.mul_le_mul` after the kernel reduces `Nat.pow x (succ k)` to
        // `Nat.mul (Nat.pow x k) x` (iota + delta). No `sorry`, no
        // self-reference, no domain-axiom dependency (`Nat.mul_le_mul` is itself
        // constructive #3604). Replaces the prior `Declaration::Axiom` in
        // `order_arith.rs::init_nat_pow_ord`.
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

    /// Kernel accepts the `Nat.rec` / `Nat.mul_le_mul` proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_nat_pow_le_pow_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_left_proof()
            .expect("first registration");
        env.register_nat_pow_le_pow_left_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.pow_le_pow_left"))
            .expect("Nat.pow_le_pow_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the outer λ binders) must be a `@Nat.rec.{0}`
    /// application. Guards against a trivial axiom-wrapping masquerade.
    #[test]
    fn test_nat_pow_le_pow_left_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_left_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.pow_le_pow_left"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the four outer λ binders (a, b, n, h).
        let mut body = value.clone();
        for _ in 0..4 {
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
                "Nat.pow_le_pow_left proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_nat_pow_le_pow_left_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_left_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.pow_le_pow_left"))
            .expect("Nat.pow_le_pow_left is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.pow_le_pow_left must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    /// Proof quality is `Constructive`.
    #[test]
    fn test_nat_pow_le_pow_left_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_nat_pow_le_pow_left_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Nat.pow_le_pow_left"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Nat.pow_le_pow_left must be Constructive, got {:?}",
            quality
        );
    }
}
