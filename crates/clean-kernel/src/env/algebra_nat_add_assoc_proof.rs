// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.add_assoc : ∀ a b c : Nat, Eq (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by induction on the THIRD argument `c` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.add` is defined as `Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n`
//! (recurses on the SECOND argument). Inducting on `c`:
//!
//! ```text
//! theorem Nat.add_assoc (a b c : Nat) : Eq (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.add (Nat.add a b) t) (Nat.add a (Nat.add b t)))  -- motive
//!     (@Eq.refl.{1} Nat (Nat.add a b))                                              -- base
//!     (fun (k : Nat) (ih : Eq (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k))) =>
//!        @congrArg.{1,1} Nat Nat
//!          (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k))
//!          Nat.succ ih)                                                             -- step
//!     c
//! ```
//!
//! **Base case.** We need `motive Nat.zero = Eq Nat (Nat.add (Nat.add a b) Nat.zero)
//! (Nat.add a (Nat.add b Nat.zero))`. Both sides reduce to `Nat.add a b` via
//! iota zero-case on `Nat.rec` + delta on the reducible `Nat.add`: the LHS
//! `Nat.add (Nat.add a b) Nat.zero` reduces to `Nat.add a b` directly, and
//! the RHS `Nat.add a (Nat.add b Nat.zero)` reduces to `Nat.add a b` by
//! first reducing the inner `Nat.add b Nat.zero → b` then... wait, `Nat.add
//! a b` is not `Nat.add a b`, so the RHS definitionally reduces to
//! `Nat.add a b` because `Nat.add b Nat.zero ≡ b`, i.e. the whole RHS
//! becomes `Nat.add a b`. So `motive Nat.zero` defn-equals
//! `Eq (Nat.add a b) (Nat.add a b)`, which is precisely the type of
//! `@Eq.refl.{1} Nat (Nat.add a b)`.
//!
//! **Step case.** Given `ih : Eq (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k))`,
//! we need `motive (Nat.succ k) = Eq (Nat.add (Nat.add a b) (Nat.succ k))
//! (Nat.add a (Nat.add b (Nat.succ k)))`. Reductions:
//! - `Nat.add (Nat.add a b) (Nat.succ k) ι→ Nat.succ (Nat.add (Nat.add a b) k)`.
//! - `Nat.add b (Nat.succ k) ι→ Nat.succ (Nat.add b k)`, so
//!   `Nat.add a (Nat.add b (Nat.succ k)) ≡ Nat.add a (Nat.succ (Nat.add b k))
//!    ι→ Nat.succ (Nat.add a (Nat.add b k))`.
//!   So `motive (Nat.succ k)` defn-equals
//!   `Eq (Nat.succ (Nat.add (Nat.add a b) k)) (Nat.succ (Nat.add a (Nat.add b k)))`.
//!   `congrArg Nat.succ ih` produces exactly this type.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.succ`, `Nat.add`,
//! `Nat.rec`, `congrArg` — none of which are `Declaration::Axiom`. `Nat.rec`
//! is auto-generated kernel machinery, `congrArg` is a kernel-level
//! `Declaration::Theorem`. Therefore `env.axiom_deps("Nat.add_assoc")` is
//! empty and `env.proof_quality("Nat.add_assoc") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Tier A Batch 5 Nat axiom demotion). Sibling proofs:
//! - `algebra_nat_add_zero_proof.rs` (#3604, pure `Eq.refl` — similar iota).
//! - `algebra_nat_succ_add_proof.rs` (#3604, Nat.rec induction — same shape).
//! - `algebra_nat_add_comm_proof.rs` (#3604, Nat.rec induction).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatAddAssocConsts {
    nat_type: Expr,
    nat_add: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    congr_arg: Expr,
}

impl NatAddAssocConsts {
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

/// Build `∀ a b c : Nat, Eq Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c))`.
fn build_nat_add_assoc_type(c: &NatAddAssocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let (cv_id, cv) = b.fresh_local(c.nat_type.clone());
    let ab = Expr::app(Expr::app(c.nat_add.clone(), a.clone()), bv.clone());
    let bc = Expr::app(Expr::app(c.nat_add.clone(), bv.clone()), cv.clone());
    let lhs = Expr::app(Expr::app(c.nat_add.clone(), ab), cv);
    let rhs = Expr::app(Expr::app(c.nat_add.clone(), a.clone()), bc);
    let concl = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(cv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Motive: `λ (t : Nat) => Eq Nat (Nat.add (Nat.add a b) t) (Nat.add a (Nat.add b t))`.
fn build_motive(c: &NatAddAssocConsts, parent: &EnvDeclBuilder, va: &Expr, vb: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let ab = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), vb.clone());
    let bt = Expr::app(Expr::app(c.nat_add.clone(), vb.clone()), t.clone());
    let m_lhs = Expr::app(Expr::app(c.nat_add.clone(), ab), t);
    let m_rhs = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), bt);
    let body = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), m_lhs, m_rhs]);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Step case: `λ (k : Nat) (ih : motive k) => @congrArg Nat Nat _ _ Nat.succ ih`.
///
/// `congrArg Nat.succ ih` produces
/// `Eq (Nat.succ (Nat.add (Nat.add a b) k)) (Nat.succ (Nat.add a (Nat.add b k)))`,
/// which is definitionally equal to `motive (Nat.succ k)` after iota+delta
/// on `Nat.add`.
fn build_step(c: &NatAddAssocConsts, parent: &EnvDeclBuilder, va: &Expr, vb: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = sb.fresh_local(c.nat_type.clone());
    let ab = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), vb.clone());
    let bk = Expr::app(Expr::app(c.nat_add.clone(), vb.clone()), k.clone());
    let s_lhs = Expr::app(Expr::app(c.nat_add.clone(), ab), k);
    let s_rhs = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), bk);
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

/// Body: `λ (a b c : Nat) => @Nat.rec.{0} motive base step c`.
///
/// Base `@Eq.refl Nat (Nat.add a b)` closes the zero-case (both sides of
/// the motive reduce to `Nat.add a b` via iota zero-case + delta on
/// Nat.add).
fn build_nat_add_assoc_value(c: &NatAddAssocConsts) -> Expr {
    let mut vb_b = EnvDeclBuilder::new();
    let (va_id, va) = vb_b.fresh_local(c.nat_type.clone());
    let (vb_id, vb) = vb_b.fresh_local(c.nat_type.clone());
    let (vc_id, vc) = vb_b.fresh_local(c.nat_type.clone());
    let motive = build_motive(c, &vb_b, &va, &vb);
    let add_a_b = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), vb.clone());
    let base = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), add_a_b]);
    let step = build_step(c, &vb_b, &va, &vb);
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, vc]);
    let val_raw = vb_b.mk_lam(vc_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb_b.mk_lam(vb_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = vb_b.mk_lam(va_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb_b.finish(val_raw)
}

impl Environment {
    /// Register `Nat.add_assoc` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `congrArg`.
    /// ENSURES: On success, `Nat.add_assoc` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_add_assoc_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_eq()?;
        let c = NatAddAssocConsts::new();
        let type_ = build_nat_add_assoc_type(&c);
        let value = build_nat_add_assoc_value(&c);
        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier A Batch 5).
        // Nat.rec-induction on the third argument `c`. Base case closed by
        // `@Eq.refl.{1} Nat (Nat.add a b)` (motive at Nat.zero reduces both
        // sides to `Nat.add a b` via iota zero-case + delta on Nat.add; on
        // the RHS the inner `Nat.add b Nat.zero` reduces to `b` first). Step
        // case closed by `congrArg Nat.succ ih`. No `sorry`, no
        // self-reference, no axiom-wrapper. Replaces the prior
        // `Declaration::Axiom` in
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
    fn test_nat_add_assoc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_add_assoc_proof()
            .expect("first registration");
        env.register_nat_add_assoc_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.add_assoc"))
            .expect("Nat.add_assoc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_add_assoc_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_add_assoc_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_assoc"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.add_assoc proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// After peeling three outer λ binders, the proof root is `@Nat.rec.{0}`.
    /// Guards against a trivial `Eq.refl` masquerade — `Nat.add_assoc`
    /// cannot reduce without induction on the third argument.
    #[test]
    fn test_nat_add_assoc_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_add_assoc_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_assoc"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let b1 = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ a, got {:?}", k),
        };
        let b2 = match b1.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ b, got {:?}", k),
        };
        let b3 = match b2.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ c, got {:?}", k),
        };
        let mut head = b3.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.add_assoc proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_nat_add_assoc_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_add_assoc_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.add_assoc"))
            .expect("Nat.add_assoc is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.add_assoc must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
