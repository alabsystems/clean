// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.add_comm : ∀ a b : Nat, Eq (Nat.add a b) (Nat.add b a)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by induction on the SECOND argument `b` via
//! `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.add` is defined as `Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n`
//! (recurses on the SECOND argument). Specializing with the second
//! argument quantified, we induct on `b`:
//!
//! ```text
//! theorem Nat.add_comm (a b : Nat) : Eq (Nat.add a b) (Nat.add b a) :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.add a t) (Nat.add t a))     -- motive
//!     (@Eq.symm.{1} Nat (Nat.add Nat.zero a) a
//!                       (Nat.zero_add a))                     -- base
//!     (fun k ih =>
//!        Eq.trans
//!          (congrArg Nat.succ ih : Eq (succ (a + k)) (succ (k + a)))
//!          (Eq.symm (Nat.succ_add k a)
//!             : Eq (succ k + a) (succ (k + a))
//!             |> Eq.symm      -- gives Eq (succ (k + a)) (succ k + a)
//!          ))                                                  -- step
//!     b
//! ```
//!
//! **Base case.** We need `motive Nat.zero = Eq Nat (Nat.add a Nat.zero) (Nat.add Nat.zero a)`.
//! The LHS `Nat.add a Nat.zero` reduces definitionally to `a` via iota on
//! `Nat.rec` (zero case) + delta on the reducible `Nat.add` definition.
//! So the motive at `Nat.zero` is defn-equal to `Eq Nat a (Nat.add Nat.zero a)`.
//! `Nat.zero_add a : Eq (Nat.add Nat.zero a) a`; its `Eq.symm` witnesses
//! `Eq a (Nat.add Nat.zero a)`, which matches.
//!
//! **Step case.** Given `ih : Eq (Nat.add a k) (Nat.add k a)`, we need
//! `motive (Nat.succ k) = Eq (Nat.add a (Nat.succ k)) (Nat.add (Nat.succ k) a)`.
//! `Nat.add a (Nat.succ k)` reduces (iota succ-case + delta on Nat.add)
//! to `Nat.succ (Nat.add a k)`. The motive therefore definitionally
//! equals `Eq (Nat.succ (Nat.add a k)) (Nat.add (Nat.succ k) a)`.
//!
//! `congrArg Nat.succ ih : Eq (Nat.succ (Nat.add a k)) (Nat.succ (Nat.add k a))`.
//! `Nat.succ_add k a : Eq (Nat.add (Nat.succ k) a) (Nat.succ (Nat.add k a))`.
//! `Eq.symm (Nat.succ_add k a) : Eq (Nat.succ (Nat.add k a)) (Nat.add (Nat.succ k) a)`.
//! `Eq.trans (congrArg Nat.succ ih) (Eq.symm (Nat.succ_add k a))` witnesses
//! `Eq (Nat.succ (Nat.add a k)) (Nat.add (Nat.succ k) a)`, matching the motive.
//!
//! # Axiom closure
//!
//! The proof depends on `Nat.zero_add` (constructive #3604),
//! `Nat.succ_add` (constructive #3604), `congrArg`, `Eq.symm`, `Eq.trans`,
//! `Eq.refl`, `Nat.rec`. None of these are `Declaration::Axiom`.
//! Therefore `env.axiom_deps("Nat.add_comm")` is empty and
//! `env.proof_quality("Nat.add_comm") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604. Sibling proofs:
//! - `algebra_nat_add_zero_proof.rs` (Nat.add_zero via iota zero-case).
//! - `algebra_nat_zero_add_proof.rs` (Nat.zero_add via Nat.rec induction).
//! - `algebra_nat_succ_add_proof.rs` (Nat.succ_add via Nat.rec induction).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatAddCommConsts {
    nat_type: Expr,
    nat_add: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nat_zero_add: Expr,
    nat_succ_add: Expr,
}

impl NatAddCommConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) → Eq a₁ a₂ → Eq (f a₁) (f a₂)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_zero_add: Expr::const_(Name::from_string("Nat.zero_add"), vec![]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
        }
    }
}

/// Build `∀ a b : Nat, Eq Nat (Nat.add a b) (Nat.add b a)`.
fn build_nat_add_comm_type(c: &NatAddCommConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let lhs = Expr::app(Expr::app(c.nat_add.clone(), a.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.nat_add.clone(), bv), a);
    let concl = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Motive: `λ (t : Nat) => Eq Nat (Nat.add a t) (Nat.add t a)`.
fn build_motive(c: &NatAddCommConsts, parent: &EnvDeclBuilder, va: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let m_lhs = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), t.clone());
    let m_rhs = Expr::app(Expr::app(c.nat_add.clone(), t), va.clone());
    let body = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), m_lhs, m_rhs]);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Base case: `@Eq.symm.{1} Nat (Nat.add Nat.zero a) a (Nat.zero_add a)`.
///
/// Produces `Eq Nat a (Nat.add Nat.zero a)`. Matches `motive Nat.zero`
/// which defn-equals `Eq Nat a (Nat.add Nat.zero a)` after reducing
/// `Nat.add a Nat.zero → a` via iota zero-case + delta on Nat.add.
fn build_base(c: &NatAddCommConsts, va: &Expr) -> Expr {
    let zero_add_a = Expr::app(c.nat_zero_add.clone(), va.clone());
    let add_zero_a = Expr::app(Expr::app(c.nat_add.clone(), c.nat_zero.clone()), va.clone());
    // @Eq.symm.{1} Nat (Nat.add Nat.zero a) a (Nat.zero_add a)
    Expr::apps(
        c.eq_symm.clone(),
        [c.nat_type.clone(), add_zero_a, va.clone(), zero_add_a],
    )
}

/// Step case: `λ (k : Nat) (ih : motive k) =>
///   Eq.trans (congrArg Nat.succ ih) (Eq.symm (Nat.succ_add k a))`.
fn build_step(c: &NatAddCommConsts, parent: &EnvDeclBuilder, va: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = sb.fresh_local(c.nat_type.clone());
    // ih type: Eq Nat (Nat.add a k) (Nat.add k a)
    let ih_lhs = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), k.clone());
    let ih_rhs = Expr::app(Expr::app(c.nat_add.clone(), k.clone()), va.clone());
    let ih_type = Expr::apps(
        c.eq_const.clone(),
        [c.nat_type.clone(), ih_lhs.clone(), ih_rhs.clone()],
    );
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());

    // congrArg Nat.succ ih : Eq (Nat.succ (Nat.add a k)) (Nat.succ (Nat.add k a))
    let congr_app = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            ih_lhs.clone(),
            ih_rhs.clone(),
            c.nat_succ.clone(),
            ih,
        ],
    );

    // Nat.succ_add k a : Eq (Nat.add (Nat.succ k) a) (Nat.succ (Nat.add k a))
    let succ_add_k_a = Expr::apps(c.nat_succ_add.clone(), [k.clone(), va.clone()]);
    let succ_k = Expr::app(c.nat_succ.clone(), k);
    let add_succ_k_a = Expr::app(Expr::app(c.nat_add.clone(), succ_k), va.clone());
    let succ_of_add_k_a = Expr::app(c.nat_succ.clone(), ih_rhs.clone());
    // Eq.symm (Nat.succ_add k a) : Eq (Nat.succ (Nat.add k a)) (Nat.add (Nat.succ k) a)
    let sym_succ_add = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            add_succ_k_a.clone(),
            succ_of_add_k_a.clone(),
            succ_add_k_a,
        ],
    );

    // Eq.trans.{1} α x y z h1 h2 : Eq x z  where x = succ(add a k), y = succ(add k a),
    // z = Nat.add (Nat.succ k) a
    let succ_of_add_a_k = Expr::app(c.nat_succ.clone(), ih_lhs);
    let trans_app = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            succ_of_add_a_k,
            succ_of_add_k_a,
            add_succ_k_a,
            congr_app,
            sym_succ_add,
        ],
    );

    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans_app);
    let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_k)
}

/// Body: `λ (a b : Nat) => @Nat.rec.{0} motive base step b`.
fn build_nat_add_comm_value(c: &NatAddCommConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.nat_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.nat_type.clone());
    let motive = build_motive(c, &vb, &va);
    let base = build_base(c, &va);
    let step = build_step(c, &vb, &va);
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, vbv]);
    let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Nat.add_comm` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`,
    ///           `Eq.symm`, `Eq.trans`, `congrArg`.
    /// REQUIRES: `Nat.zero_add` and `Nat.succ_add` are registered as
    ///           `Declaration::Theorem` (constructive proofs — see
    ///           `register_nat_zero_add_proof` / `register_nat_succ_add_proof`).
    /// ENSURES: On success, `Nat.add_comm` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_add_comm_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_zero_add_proof()?;
        self.register_nat_succ_add_proof()?;

        let c = NatAddCommConsts::new();
        let type_ = build_nat_add_comm_type(&c);
        let value = build_nat_add_comm_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on
        // the second argument `b` via `Nat.rec.{0}`. Base case closed by
        // `Eq.symm (Nat.zero_add a)` (motive at Nat.zero reduces via iota
        // zero-case + delta on Nat.add to `Eq a (Nat.add Nat.zero a)`).
        // Step case composes `congrArg Nat.succ ih` with
        // `Eq.symm (Nat.succ_add k a)` via `Eq.trans` to witness the
        // motive at `Nat.succ k`. Replaces the prior `Declaration::Axiom`
        // in `data_types_nat_lemmas.rs::init_nat_arith_lemmas`.
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
    fn test_nat_add_comm_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_add_comm_proof()
            .expect("first registration");
        env.register_nat_add_comm_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.add_comm"))
            .expect("Nat.add_comm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_add_comm_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_add_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_comm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.add_comm proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The proof root (after peeling two outer λ binders) is an
    /// `@Nat.rec.{0}` application. Guards against a trivial `Eq.refl`
    /// masquerade.
    #[test]
    fn test_nat_add_comm_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_add_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_comm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected outer λ, got {:?}", k),
        };
        let inner_body = match outer_body.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected inner λ, got {:?}", k),
        };
        let mut head = inner_body.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.add_comm proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty: the transitive axiom deps of Nat.add_comm
    /// must contain no `Declaration::Axiom`. Depends on Nat.zero_add and
    /// Nat.succ_add having zero axiom deps (also #3604).
    #[test]
    fn test_nat_add_comm_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_add_comm_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.add_comm"))
            .expect("Nat.add_comm is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.add_comm must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
