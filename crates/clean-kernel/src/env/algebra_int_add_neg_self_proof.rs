// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_neg_self : ∀ a : Int, Eq Int (Int.add a (Int.neg a)) Int.zero`.
//!
//! (`Int.zero` is the reducible Definition `Int.ofNat Nat.zero`, so the
//! conclusion RHS is definitionally `Int.ofNat 0`.)
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem`. This is the
//! additive-inverse identity `a + (-a) = 0`.
//!
//! # Proof sketch
//!
//! `Int.neg` and `Int.add` are reducible Definitions. Concretely:
//!
//! ```text
//! Int.neg (ofNat 0)        = ofNat 0
//! Int.neg (ofNat (succ k)) = negSucc k
//! Int.neg (negSucc m)      = ofNat (succ m)
//!
//! Int.add (ofNat p)   (ofNat q)   = ofNat (p + q)
//! Int.add (ofNat p)   (negSucc q) = subNatNat p (succ q)
//! Int.add (negSucc p) (ofNat q)   = subNatNat q (succ p)
//! ```
//!
//! Outer `@Int.rec.{0}` case-analysis on `a`, motive
//! `λ x : Int => Eq Int (Int.add x (Int.neg x)) (Int.ofNat 0)`:
//!
//! - **`ofNat n` branch**: `Int.neg (ofNat n)` does not reduce until `n` is a
//!   constructor, so we recurse on `n` with an inner `@Nat.rec.{0}` whose
//!   motive is `λ t : Nat => Eq Int (Int.add (ofNat t) (Int.neg (ofNat t)))
//!   (Int.ofNat 0)`:
//!   - `zero`: `Int.add (ofNat 0) (Int.neg (ofNat 0)) = Int.add (ofNat 0)
//!     (ofNat 0) = ofNat (0 + 0) = ofNat 0`. Closed by
//!     `@Eq.refl.{1} Int (ofNat 0)`.
//!   - `succ k`: `Int.neg (ofNat (succ k)) = negSucc k`, then
//!     `Int.add (ofNat (succ k)) (negSucc k) = subNatNat (succ k) (succ k)`.
//!     Closed by `Int.subNatNat_self (Nat.succ k)`, whose type
//!     `Eq Int (subNatNat (succ k) (succ k)) (ofNat 0)` is definitionally the
//!     reduced motive at `succ k` (the inductive hypothesis is unused).
//!
//! - **`negSucc m` branch**: `Int.neg (negSucc m) = ofNat (succ m)`, then
//!   `Int.add (negSucc m) (ofNat (succ m)) = subNatNat (succ m) (succ m)`.
//!   Closed by `Int.subNatNat_self (Nat.succ m)`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.add`, `Int.neg`, `Int.ofNat`,
//! `Int.negSucc`, `Int.rec`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Eq`,
//! `Eq.refl`, and the constructive `Int.subNatNat_self` (#3604). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.add_neg_self")` is empty and
//! `env.proof_quality("Int.add_neg_self") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_sub_nat_nat_self_proof.rs` (dependency).
//! - `algebra_int_neg_add_self_proof.rs` (companion — Int.neg_add_self).
//! - `algebra_int_neg_neg_proof.rs` (same outer Int.rec + inner Nat.rec shape).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
struct IntAddNegSelfConsts {
    int_type: Expr,
    nat_type: Expr,
    #[cfg(test)]
    nat_zero: Expr,
    nat_succ: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_of_nat: Expr,
    #[cfg(test)]
    int_neg_succ: Expr,
    int_zero: Expr,
    int_rec: Expr,
    nat_rec: Expr,
    int_sub_nat_nat_self: Expr,
    eq_const: Expr,
    eq_refl: Expr,
}

impl IntAddNegSelfConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            #[cfg(test)]
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            #[cfg(test)]
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            // Prop-valued motives — Sort 0.
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_sub_nat_nat_self: Expr::const_(Name::from_string("Int.subNatNat_self"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn add_neg(&self, x: Expr) -> Expr {
        self.add(x.clone(), self.neg(x))
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    /// `Int.zero` — the reducible Definition `Int.ofNat Nat.zero`. Used as
    /// the conclusion RHS to match the original axiom signature exactly.
    fn zero_int(&self) -> Expr {
        self.int_zero.clone()
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }
}

/// Build `∀ a : Int, Eq Int (Int.add a (Int.neg a)) Int.zero`.
fn build_type(c: &IntAddNegSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.add_neg(a), c.zero_int());
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

/// Outer motive: `λ (x : Int) => Eq Int (Int.add x (Int.neg x)) (Int.ofNat 0)`.
fn build_outer_motive(c: &IntAddNegSelfConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let body = c.eq_int(c.add_neg(x), c.zero_int());
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Outer `ofNat` case:
/// `λ (n : Nat) => @Nat.rec.{0} inner_motive zero_case succ_case n`.
fn build_ofnat_case(c: &IntAddNegSelfConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut ob = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = ob.fresh_local(c.nat_type.clone());

    // inner motive:
    //   λ (t : Nat) => Eq Int (Int.add (ofNat t) (Int.neg (ofNat t))) (ofNat 0)
    let inner_motive = {
        let mut mb = EnvDeclBuilder::child_of(&ob);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.add_neg(c.of_nat(t)), c.zero_int());
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // zero case: @Eq.refl.{1} Int (ofNat 0). At t = zero:
    //   Int.add (ofNat 0) (Int.neg (ofNat 0)) = Int.add (ofNat 0) (ofNat 0)
    //     = ofNat (0 + 0) = ofNat 0.
    let zero_case = c.refl_int(c.zero_int());

    // succ case: λ (k : Nat) (_ih : inner_motive k) =>
    //   Int.subNatNat_self (Nat.succ k).
    // At t = succ k:
    //   Int.neg (ofNat (succ k)) = negSucc k, so
    //   Int.add (ofNat (succ k)) (negSucc k) = subNatNat (succ k) (succ k).
    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&ob);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_type = c.eq_int(c.add_neg(c.of_nat(k.clone())), c.zero_int());
        let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
        let proof = Expr::app(c.int_sub_nat_nat_self.clone(), c.succ(k.clone()));
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, proof);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [inner_motive, zero_case, succ_case, n]);
    let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    ob.finish_child(lam)
}

/// Outer `negSucc` case: `λ (m : Nat) => Int.subNatNat_self (Nat.succ m)`.
///
/// At `a = negSucc m`: `Int.neg (negSucc m) = ofNat (succ m)`, so
/// `Int.add (negSucc m) (ofNat (succ m)) = subNatNat (succ m) (succ m)`.
fn build_negsucc_case(c: &IntAddNegSelfConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut nb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = nb.fresh_local(c.nat_type.clone());
    let proof = Expr::app(c.int_sub_nat_nat_self.clone(), c.succ(m.clone()));
    let lam = nb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), proof);
    nb.finish_child(lam)
}

/// Body: `λ (a : Int) => @Int.rec.{0} outer_motive ofNat_case negSucc_case a`.
fn build_value(c: &IntAddNegSelfConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let motive = build_outer_motive(c, &vb);
    let of_nat_case = build_ofnat_case(c, &vb);
    let neg_succ_case = build_negsucc_case(c, &vb);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, of_nat_case, neg_succ_case, va]);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_neg_self` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.add`, `Int.neg`, `Int.subNatNat`,
    ///           `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.add_neg_self` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.add_neg_self` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_add_neg_self_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_neg_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependency: subNatNat n n = ofNat 0.
        self.register_int_sub_nat_nat_self_proof()?;

        let c = IntAddNegSelfConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Outer
        // `@Int.rec.{0}` on `a`; the `ofNat` branch recurses with an inner
        // `@Nat.rec.{0}` (zero closes by `@Eq.refl.{1}`, succ by
        // `Int.subNatNat_self (succ k)`), and the `negSucc` branch closes by
        // `Int.subNatNat_self (succ m)`. The kernel reduces `Int.add x
        // (Int.neg x)` to `Int.subNatNat (succ ·) (succ ·)` on the non-zero
        // constructor branches via iota + delta on the reducible `Int.neg` /
        // `Int.add` / `Int.subNatNat` definitions. No `sorry`, no
        // self-reference, no domain-axiom dependency. Replaces the prior
        // `Declaration::Axiom` in `data_types_int_lemmas.rs`.
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

    /// Kernel accepts the nested `Int.rec` / `Nat.rec` / `subNatNat_self`
    /// proof term. Verifies the theorem is registered as a Theorem (not
    /// Axiom) and idempotent re-invocation is a no-op.
    #[test]
    fn test_int_add_neg_self_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_neg_self_proof()
            .expect("first registration");
        env.register_int_add_neg_self_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_neg_self"))
            .expect("Int.add_neg_self should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the outer λ binder) must be an `@Int.rec.{0}`
    /// application. Guards against a trivial axiom-wrapping masquerade.
    #[test]
    fn test_int_add_neg_self_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_add_neg_self_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.add_neg_self"))
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
                "Int.rec",
                "Int.add_neg_self proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_int_add_neg_self_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_neg_self_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_neg_self"))
            .expect("Int.add_neg_self is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_neg_self must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
