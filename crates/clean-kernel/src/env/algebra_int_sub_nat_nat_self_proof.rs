// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.subNatNat_self : ∀ n : Nat, Eq Int (Int.subNatNat n n) (Int.ofNat 0)`.
//!
//! This is the self-cancellation theorem for `Int.subNatNat`. It is the key
//! local lemma behind the additive-inverse identities `Int.add_neg_self`,
//! `Int.neg_add_self` and (transitively) `Int.sub_self`, all of which reduce
//! `a + (-a)` to `Int.subNatNat (succ k) (succ k)` on their non-zero
//! constructor branches.
//!
//! # Proof sketch
//!
//! `Int.subNatNat` is a reducible Definition by recursion on its second
//! argument (see `data_types_arithmetic.rs`):
//!
//! ```text
//! Int.subNatNat m Nat.zero      = Int.ofNat m
//! Int.subNatNat (succ m) (succ n) = Int.subNatNat m n   (subNatNat_succ_succ)
//! ```
//!
//! We induct on `n` via `Nat.rec.{0}` with motive
//! `λ t : Nat => Eq Int (Int.subNatNat t t) (Int.ofNat 0)`:
//!
//! - **base (`n = Nat.zero`)**: `Int.subNatNat Nat.zero Nat.zero` reduces to
//!   `Int.ofNat Nat.zero` by the zero iota-case of `subNatNat` (second arg
//!   is `Nat.zero`) + delta. `Nat.zero` is definitionally `0`, so the goal
//!   `Eq Int (Int.subNatNat 0 0) (Int.ofNat 0)` is closed by
//!   `@Eq.refl.{1} Int (Int.ofNat Nat.zero)`.
//!
//! - **step (`n = Nat.succ k`)**: given
//!   `ih : Eq Int (Int.subNatNat k k) (Int.ofNat 0)`, the goal is
//!   `Eq Int (Int.subNatNat (Nat.succ k) (Nat.succ k)) (Int.ofNat 0)`.
//!   We close it by `Eq.trans s ih` where
//!   `s := Int.subNatNat_succ_succ k k
//!        : Eq Int (Int.subNatNat (Nat.succ k) (Nat.succ k))
//!                 (Int.subNatNat k k)`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.subNatNat`, `Int.ofNat`, `Nat`,
//! `Nat.zero`, `Nat.succ`, `Nat.rec`, `Eq`, `Eq.refl`, `Eq.trans`, and the
//! constructive `Int.subNatNat_succ_succ` (a `Declaration::Theorem`, #3604).
//! None are `Declaration::Axiom`, so `env.axiom_deps("Int.subNatNat_self")`
//! is empty and
//! `env.proof_quality("Int.subNatNat_self") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_sub_nat_nat_succ_succ_proof.rs` (dependency).
//! - `algebra_int_add_neg_self_proof.rs` (consumer — Int.add_neg_self).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubNatNatSelfConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    int_of_nat: Expr,
    int_sub_nat_nat: Expr,
    int_sub_nat_nat_succ_succ: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
}

impl IntSubNatNatSelfConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            int_sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn zero_int(&self) -> Expr {
        self.of_nat(self.nat_zero.clone())
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

/// Build `∀ n : Nat, Eq Int (Int.subNatNat n n) (Int.ofNat 0)`.
fn build_type(c: &IntSubNatNatSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.sub_nat_nat(n.clone(), n), c.zero_int());
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    b.finish(ty_raw)
}

/// Body: `λ (n : Nat) => @Nat.rec.{0} motive base step n`.
fn build_value(c: &IntSubNatNatSelfConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    // motive: λ (t : Nat) => Eq Int (Int.subNatNat t t) (Int.ofNat 0)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.sub_nat_nat(t.clone(), t), c.zero_int());
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // base: @Eq.refl.{1} Int (Int.ofNat Nat.zero). motive(Nat.zero) reduces
    // LHS `Int.subNatNat Nat.zero Nat.zero` to `Int.ofNat Nat.zero`.
    let base = Expr::apps(c.eq_refl.clone(), [c.int_type.clone(), c.zero_int()]);

    // step: λ (k : Nat) (ih : motive k) =>
    //   Eq.trans Int (subNatNat (succ k) (succ k)) (subNatNat k k) (ofNat 0)
    //     (Int.subNatNat_succ_succ k k) ih
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_type = c.eq_int(c.sub_nat_nat(k.clone(), k.clone()), c.zero_int());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        // s := Int.subNatNat_succ_succ k k
        //    : Eq Int (subNatNat (succ k) (succ k)) (subNatNat k k)
        let s = Expr::apps(c.int_sub_nat_nat_succ_succ.clone(), [k.clone(), k.clone()]);

        let lhs = c.sub_nat_nat(c.succ(k.clone()), c.succ(k.clone()));
        let mid = c.sub_nat_nat(k.clone(), k.clone());
        let trans = Expr::apps(
            c.eq_trans.clone(),
            [c.int_type.clone(), lhs, mid, c.zero_int(), s, ih],
        );

        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val_raw = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.subNatNat_self` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.subNatNat`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.trans`.
    /// ENSURES: On success, `Int.subNatNat_self` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.subNatNat_self` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_sub_nat_nat_self_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.subNatNat_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependency: subNatNat (succ m) (succ n) = subNatNat m n.
        self.register_int_sub_nat_nat_succ_succ_proof()?;

        let c = IntSubNatNatSelfConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on `n`
        // via `@Nat.rec.{0}`. Base case `@Eq.refl.{1}` (zero iota-case of
        // `subNatNat` + delta). Step case `Eq.trans (subNatNat_succ_succ k k)
        // ih`, threading the constructive successor-cancellation theorem.
        // No `sorry`, no self-reference, no domain-axiom dependency.
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
    fn test_int_sub_nat_nat_self_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_self_proof()
            .expect("first registration");
        env.register_int_sub_nat_nat_self_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_self"))
            .expect("Int.subNatNat_self should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the outer λ binder) must be a `@Nat.rec.{0}`
    /// application. Guards against a trivial axiom-wrapping masquerade.
    #[test]
    fn test_int_sub_nat_nat_self_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_self_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_self"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body.clone(),
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = outer_body;
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Int.subNatNat_self proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_int_sub_nat_nat_self_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_self_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.subNatNat_self"))
            .expect("Int.subNatNat_self is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.subNatNat_self must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
