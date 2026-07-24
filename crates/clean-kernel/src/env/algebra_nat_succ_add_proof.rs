// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.succ_add : ∀ a b : Nat, Eq (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof term
//! is built by induction on the SECOND argument `b` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.add` is defined as `Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n`
//! (recurses on the SECOND argument). Specializing at the LHS first argument
//! `Nat.succ a`, the expression `Nat.add (Nat.succ a) b` does NOT reduce to
//! `Nat.succ (Nat.add a b)` directly: we must induct on `b`.
//!
//! ```text
//! theorem Nat.succ_add (a b : Nat) : Eq (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b)) :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.add (Nat.succ a) t) (Nat.succ (Nat.add a t)))  -- motive
//!     (@Eq.refl.{1} Nat (Nat.succ a))                                             -- base
//!     (fun (k : Nat) (ih : Eq (Nat.add (Nat.succ a) k) (Nat.succ (Nat.add a k))) =>
//!        @congrArg.{1,1} Nat Nat
//!          (Nat.add (Nat.succ a) k) (Nat.succ (Nat.add a k))
//!          Nat.succ ih)                                                            -- step
//!     b
//! ```
//!
//! Base case type-checks because both `Nat.add (Nat.succ a) Nat.zero` and
//! `Nat.succ (Nat.add a Nat.zero)` reduce to `Nat.succ a` via iota on
//! `Nat.rec` (zero case) + delta on the reducible `Nat.add` definition; so
//! `motive Nat.zero` definitionally equals `Eq Nat (Nat.succ a) (Nat.succ a)`,
//! which is precisely the type of `@Eq.refl.{1} Nat (Nat.succ a)`.
//!
//! Step case: `congrArg Nat.succ ih` produces
//! `Eq (Nat.succ (Nat.add (Nat.succ a) k)) (Nat.succ (Nat.succ (Nat.add a k)))`.
//! On the motive side, `Nat.add (Nat.succ a) (Nat.succ k)` reduces (iota
//! succ-case + delta) to `Nat.succ (Nat.add (Nat.succ a) k)`, and
//! `Nat.add a (Nat.succ k)` reduces to `Nat.succ (Nat.add a k)`. So
//! `motive (Nat.succ k)` definitionally equals the `congrArg` result type.
//!
//! # Axiom closure
//!
//! Proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.succ`, `Nat.add`,
//! `Nat.rec`, `congrArg` — none of which are `Declaration::Axiom`. `Nat.rec`
//! is auto-generated kernel machinery, `congrArg` is a kernel-level
//! `Declaration::Theorem`. Therefore `env.axiom_deps("Nat.succ_add")` is
//! empty and `env.proof_quality("Nat.succ_add") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604. Sibling proofs:
//! - `algebra_nat_add_zero_proof.rs` (Nat.add_zero via iota zero-case).
//! - `algebra_nat_zero_add_proof.rs` (Nat.zero_add via Nat.rec induction).
//! - `algebra_nat_add_succ_proof.rs` (Nat.add_succ via pure Eq.refl — no
//!   induction needed because Nat.add recurses on its second argument and
//!   the RHS `Nat.succ b` triggers the iota succ-case directly).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction so each
/// helper is independently callable without re-resolving names.
struct NatSuccAddConsts {
    nat_type: Expr,
    nat_add: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    congr_arg: Expr,
}

impl NatSuccAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) → Eq a₁ a₂ → Eq (f a₁) (f a₂)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }
}

/// Build `∀ a b : Nat, Eq Nat (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b))`.
fn build_nat_succ_add_type(c: &NatSuccAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let succ_a = Expr::app(c.nat_succ.clone(), a.clone());
    let lhs = Expr::app(Expr::app(c.nat_add.clone(), succ_a), bv.clone());
    let ab = Expr::app(Expr::app(c.nat_add.clone(), a), bv);
    let rhs = Expr::app(c.nat_succ.clone(), ab);
    let concl = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Motive: `λ (t : Nat) => Eq Nat (Nat.add (Nat.succ a) t) (Nat.succ (Nat.add a t))`.
/// Uses `child_of(parent)` so the outer `a` FVar remains open; the caller's
/// `mk_lam` over `a` closes it later.
fn build_motive(c: &NatSuccAddConsts, parent: &EnvDeclBuilder, va: &Expr, v_succ_a: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let m_lhs = Expr::app(Expr::app(c.nat_add.clone(), v_succ_a.clone()), t.clone());
    let m_ab = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), t);
    let m_rhs = Expr::app(c.nat_succ.clone(), m_ab);
    let body = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), m_lhs, m_rhs]);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Step case: `λ (k : Nat) (ih : motive k) => @congrArg Nat Nat _ _ Nat.succ ih`.
/// `congrArg` produces `Eq (Nat.succ (Nat.add (succ a) k)) (Nat.succ (Nat.succ (Nat.add a k)))`,
/// which is definitionally equal to `motive (Nat.succ k)` after iota+delta on `Nat.add`.
fn build_step(c: &NatSuccAddConsts, parent: &EnvDeclBuilder, va: &Expr, v_succ_a: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = sb.fresh_local(c.nat_type.clone());
    let s_lhs = Expr::app(Expr::app(c.nat_add.clone(), v_succ_a.clone()), k.clone());
    let s_ak = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), k);
    let s_rhs = Expr::app(c.nat_succ.clone(), s_ak);
    let ih_type = Expr::apps(
        c.eq_const.clone(),
        [c.nat_type.clone(), s_lhs.clone(), s_rhs.clone()],
    );
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let congr_app = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            s_lhs,
            s_rhs,
            c.nat_succ.clone(),
            ih,
        ],
    );
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, congr_app);
    let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_k)
}

/// Body: `λ (a b : Nat) => @Nat.rec.{0} motive base step b`.
/// Base `@Eq.refl Nat (Nat.succ a)` closes the zero-case (motive reduces to
/// `Eq (succ a) (succ a)` via iota+delta).
fn build_nat_succ_add_value(c: &NatSuccAddConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.nat_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.nat_type.clone());
    let v_succ_a = Expr::app(c.nat_succ.clone(), va.clone());
    let motive = build_motive(c, &vb, &va, &v_succ_a);
    let base = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), v_succ_a.clone()]);
    let step = build_step(c, &vb, &va, &v_succ_a);
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, vbv]);
    let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Nat.succ_add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `congrArg`.
    /// ENSURES: On success, `Nat.succ_add` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.succ_add` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_succ_add_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_eq()?;
        let c = NatSuccAddConsts::new();
        let type_ = build_nat_succ_add_type(&c);
        let value = build_nat_succ_add_value(&c);
        // SOUNDNESS: Real kernel-checked proof term (#3604). Nat.rec-induction
        // on the second argument `b`. Base case closed by `@Eq.refl.{1} Nat
        // (Nat.succ a)` (motive reduces to `Eq (Nat.succ a) (Nat.succ a)` via
        // iota zero-case + delta on Nat.add). Step case closed by
        // `congrArg Nat.succ ih`. No `sorry`, no self-reference, no
        // axiom-wrapper. Replaces the prior `Declaration::Axiom` in
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

    /// Kernel accepts the `@Nat.rec`-rooted proof term. Verifies the theorem
    /// is registered as a Theorem (not Axiom) and idempotent re-invocation is
    /// a no-op.
    #[test]
    fn test_nat_succ_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_succ_add_proof()
            .expect("first registration");
        env.register_nat_succ_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.succ_add"))
            .expect("Nat.succ_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term whose
    /// body is a `Nat.rec` application. Guards against axiom-wrapping
    /// masquerade (#3559).
    #[test]
    fn test_nat_succ_add_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_succ_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.succ_add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.succ_add proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The proof root (after peeling two outer λ binders) is an
    /// `@Nat.rec.{0}` application, not a direct `Eq.refl` (which would
    /// indicate an unsound masquerade — `Nat.add (Nat.succ a) b` does NOT
    /// reduce to `Nat.succ (Nat.add a b)` without induction on `b`).
    #[test]
    fn test_nat_succ_add_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_succ_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.succ_add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel λ a => λ b => body
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected outer λ, got {:?}", k),
        };
        let inner_body = match outer_body.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected inner λ, got {:?}", k),
        };
        // inner_body is `@Nat.rec.{0} motive base step b`, so walking the
        // App spine to the head should reach `Const("Nat.rec", _)`.
        let mut head = inner_body.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.succ_add proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure check: the transitive axiom deps of Nat.succ_add must
    /// contain no domain-specific axiom. The `axiom_deps` API returns only
    /// Declaration::Axiom dependencies; constructive machinery (Nat.rec,
    /// Eq.refl, congrArg) does not appear there. This pins the proof as
    /// genuinely constructive (#3604) and guards against a future regression
    /// that might silently wire in a trust-marker axiom.
    #[test]
    fn test_nat_succ_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_succ_add_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.succ_add"))
            .expect("Nat.succ_add is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.succ_add must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
