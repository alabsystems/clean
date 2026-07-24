// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.subNatNat_zero_left : ∀ n : Nat,
//!     Eq Int (Int.subNatNat Nat.zero n) (Int.negOfNat n)`.
//!
//! Re-expresses the zero-positive-part mixed-sign `Int.subNatNat 0 n`
//! (`0 - n` clamped into `Int`) as the pure negative `Int.negOfNat n`
//! (`= -n`). Used by the multiplication-over-`subNatNat` lemmas
//! `Int.ofNat_mul_subNatNat` / `Int.negSucc_mul_subNatNat` on their
//! `p = 0` / `q = 0` corners (the bridge toward a constructive
//! `Int.left_distrib`).
//!
//! # Proof sketch
//!
//! `Int.subNatNat` and `Int.negOfNat` are reducible Definitions:
//!
//! ```text
//! Int.subNatNat 0 0          = Int.ofNat 0
//! Int.subNatNat 0 (succ k)   = Int.negSucc k
//! Int.negOfNat 0             = Int.ofNat 0
//! Int.negOfNat (succ k)      = Int.negSucc k
//! ```
//!
//! Induct on `n` via `@Nat.rec.{0}` (case analysis; the IH is unused). Note
//! that `Int.subNatNat 0 (succ k)` does NOT reduce definitionally (the
//! `Int.rec` underlying `Int.subNatNat` is stuck on the recursive
//! `Int.subNatNat 0 k`), so the successor case is discharged by the
//! constructive `Int.subNatNat_zero_succ`, not by `Eq.refl`:
//!
//! - `n = Nat.zero`: LHS `Int.subNatNat 0 0 ι→ Int.ofNat 0`; RHS
//!   `Int.negOfNat 0 ι→ Int.ofNat 0`. Closes by `@Eq.refl.{1} Int (ofNat 0)`.
//! - `n = Nat.succ k`: RHS `Int.negOfNat (succ k) ι→ Int.negSucc k`, so the
//!   goal is definitionally `Eq (Int.subNatNat 0 (succ k)) (Int.negSucc k)`,
//!   which is exactly `Int.subNatNat_zero_succ k`.
//!
//! # Axiom closure
//!
//! The proof mentions only kernel machinery / constructors / reducible
//! Definitions (`Int`, `Int.ofNat`, `Int.negSucc`, `Int.negOfNat`,
//! `Int.subNatNat`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Eq`,
//! `Eq.refl`) and the constructive `Declaration::Theorem`
//! `Int.subNatNat_zero_succ` (#3604). None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.subNatNat_zero_left")` is empty and the proof quality
//! is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_sub_nat_nat_zero_right_proof.rs` (subNatNat m 0 = ofNat m).
//! - `algebra_int_sub_nat_nat_zero_succ_proof.rs` (subNatNat 0 (succ n)).
//! - `algebra_int_sub_nat_nat_add_add_proof.rs` (subNatNat cancellation).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubNatNatZeroLeftConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    int_of_nat: Expr,
    int_neg_of_nat: Expr,
    int_sub_nat_nat: Expr,
    int_sub_nat_nat_zero_succ: Expr,
    eq_const: Expr,
    eq_refl: Expr,
}

impl IntSubNatNatZeroLeftConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            int_sub_nat_nat_zero_succ: Expr::const_(
                Name::from_string("Int.subNatNat_zero_succ"),
                vec![],
            ),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }

    /// `Int.subNatNat_zero_succ n : Eq (subNatNat 0 (succ n)) (negSucc n)`.
    fn snn_zero_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_sub_nat_nat_zero_succ.clone(), n)
    }
}

/// Build `∀ n : Nat, Eq Int (Int.subNatNat Nat.zero n) (Int.negOfNat n)`.
fn build_type(c: &IntSubNatNatZeroLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let lhs = c.sub_nat_nat(c.nat_zero.clone(), n.clone());
    let rhs = c.neg_of_nat(n);
    let concl = c.eq_int(lhs, rhs);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    b.finish(ty_raw)
}

/// Motive: `λ (t : Nat) => Eq Int (Int.subNatNat Nat.zero t) (Int.negOfNat t)`.
fn build_motive(c: &IntSubNatNatZeroLeftConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let lhs = c.sub_nat_nat(c.nat_zero.clone(), t.clone());
    let rhs = c.neg_of_nat(t);
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Body: `λ (n : Nat) => @Nat.rec.{0} motive base step n`.
fn build_value(c: &IntSubNatNatZeroLeftConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    let motive = build_motive(c, &vb);

    // Base (n = 0): both sides reduce to `Int.ofNat 0`.
    let base = c.refl_int(c.of_nat(c.nat_zero.clone()));

    // Step (n = succ k): RHS `negOfNat (succ k) ι→ negSucc k`, so the goal is
    // definitionally `Eq (subNatNat 0 (succ k)) (negSucc k)`, discharged by
    // `Int.subNatNat_zero_succ k` (LHS does NOT reduce — it is stuck on the
    // recursive `subNatNat 0 k`). IH unused.
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_ty = {
            let lhs = c.sub_nat_nat(c.nat_zero.clone(), k.clone());
            let rhs = c.neg_of_nat(k.clone());
            c.eq_int(lhs, rhs)
        };
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
        let proof = c.snn_zero_succ(k.clone());
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val_raw = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.subNatNat_zero_left` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.subNatNat`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// REQUIRES: `Int.subNatNat_zero_succ` is registered as a constructive
    ///           `Declaration::Theorem`.
    /// ENSURES: On success, `Int.subNatNat_zero_left` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_sub_nat_nat_zero_left_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.subNatNat_zero_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_sub_nat_nat_zero_succ_proof()?;

        let c = IntSubNatNatZeroLeftConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Case analysis on
        // `n` via `@Nat.rec.{0}` (the IH is unused). Zero branch closes by
        // pure `@Eq.refl.{1} Int (Int.ofNat 0)` (`subNatNat 0 0` and
        // `negOfNat 0` both reduce to `ofNat 0`). The successor branch is
        // discharged by the constructive `Int.subNatNat_zero_succ k`
        // (`subNatNat 0 (succ k)` is stuck definitionally; `negOfNat (succ k)`
        // reduces to `negSucc k`). No `sorry`, no self-reference, no
        // domain-axiom dependency (`Int.subNatNat_zero_succ` is constructive
        // #3604).
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
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_sub_nat_nat_zero_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_zero_left_proof()
            .expect("first registration");
        env.register_int_sub_nat_nat_zero_left_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_zero_left"))
            .expect("Int.subNatNat_zero_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_sub_nat_nat_zero_left_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_zero_left_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_zero_left"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let body = match value.kind() {
            ExprKind::Lam(_, _, inner) => (**inner).clone(),
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_sub_nat_nat_zero_left_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_zero_left_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.subNatNat_zero_left"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.subNatNat_zero_left must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_sub_nat_nat_zero_left_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_zero_left_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.subNatNat_zero_left"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.subNatNat_zero_left must be Constructive, got {:?}",
            quality
        );
    }
}
