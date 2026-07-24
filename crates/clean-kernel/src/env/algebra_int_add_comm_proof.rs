// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_comm : ∀ a b : Int, Eq Int (Int.add a b) (Int.add b a)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by NESTED induction on `a` (outer `@Int.rec.{0}`) and
//! on `b` (inner `@Int.rec.{0}`).
//!
//! # Proof sketch
//!
//! `Int.add` is a reducible Definition (see `data_types_arithmetic.rs`)
//! implemented as a 4-case split via two nested `Int.rec`:
//!
//! ```text
//! Int.add (ofNat m)  (ofNat n)  = ofNat (Nat.add m n)
//! Int.add (ofNat m)  (negSucc n) = Int.subNatNat m (Nat.succ n)
//! Int.add (negSucc m) (ofNat n)  = Int.subNatNat n (Nat.succ m)
//! Int.add (negSucc m) (negSucc n) = Int.negSucc (Nat.succ (Nat.add m n))
//! ```
//!
//! The swapped expressions reduce as follows:
//!
//! ```text
//! Int.add (ofNat n)  (ofNat m)  = ofNat (Nat.add n m)
//! Int.add (negSucc n) (ofNat m)  = Int.subNatNat m (Nat.succ n)
//! Int.add (ofNat n)  (negSucc m) = Int.subNatNat n (Nat.succ m)
//! Int.add (negSucc n) (negSucc m) = Int.negSucc (Nat.succ (Nat.add n m))
//! ```
//!
//! Per case:
//! - `ofNat × ofNat`: `Eq (ofNat (m+n)) (ofNat (n+m))` witnessed by
//!   `congrArg Int.ofNat (Nat.add_comm m n)`.
//! - `ofNat × negSucc`: both sides reduce to `Int.subNatNat m (succ n)` —
//!   closed by `@Eq.refl.{1} Int (Int.subNatNat m (succ n))`.
//! - `negSucc × ofNat`: both sides reduce to `Int.subNatNat n (succ m)` —
//!   closed by `@Eq.refl.{1} Int (Int.subNatNat n (succ m))`.
//! - `negSucc × negSucc`: `Eq (negSucc (succ (m+n))) (negSucc (succ (n+m)))`
//!   witnessed by `congrArg (λ x : Nat => Int.negSucc (Nat.succ x)) (Nat.add_comm m n)`.
//!
//! The proof term is
//!
//! ```text
//! λ (a b : Int) =>
//!   @Int.rec.{0} outer_motive outer_ofNat_case outer_negSucc_case a b
//! ```
//!
//! where
//!
//! ```text
//! outer_motive      := λ (x : Int) => ∀ b : Int, Eq Int (Int.add x b) (Int.add b x)
//! outer_ofNat_case  := λ (m : Nat) => λ (b : Int) =>
//!                        @Int.rec.{0} (inner_motive_ofNat m) oo on b
//! outer_negSucc_case:= λ (m : Nat) => λ (b : Int) =>
//!                        @Int.rec.{0} (inner_motive_negSucc m) no nn b
//! ```
//!
//! The outer `@Int.rec.{0}` application has eight explicit-argument positions
//! `(motive, ofNat_case, negSucc_case, target)`; specializing to `a` produces
//! `∀ b : Int, Eq Int (Int.add a b) (Int.add b a)` and the trailing `b`
//! application closes the outer quantifier.
//!
//! # Axiom closure
//!
//! The proof term mentions only:
//! - `Int`, `Int.add`, `Int.ofNat`, `Int.negSucc`, `Int.subNatNat`,
//!   `Int.rec` (kernel machinery / reducible definitions, none `Axiom`),
//! - `Nat`, `Nat.add`, `Nat.succ`, `Nat.rec` (kernel machinery),
//! - `Eq`, `Eq.refl`, `congrArg` (kernel Theorems / constructors),
//! - `Nat.add_comm` (constructive `Declaration::Theorem`, #3604).
//!
//! None of these are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.add_comm")` is empty and
//! `env.proof_quality("Int.add_comm") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604. Sibling proofs:
//! - `algebra_nat_add_comm_proof.rs` (Nat.add_comm via `@Nat.rec`).
//! - `algebra_int_ofnat_mul_proof.rs` (Int.ofNat_mul via pure `Eq.refl`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddCommConsts {
    int_type: Expr,
    nat_type: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    int_rec: Expr,
    nat_add: Expr,
    nat_succ: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    congr_arg: Expr,
    nat_add_comm: Expr,
}

impl IntAddCommConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            // Int.rec.{0} — Prop-valued motive.
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) → Eq a₁ a₂ → Eq (f a₁) (f a₂)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_comm: Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
        }
    }
}

/// Build `∀ a b : Int, Eq Int (Int.add a b) (Int.add b a)`.
fn build_int_add_comm_type(c: &IntAddCommConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_add.clone(), a.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_add.clone(), bv), a);
    let concl = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Outer motive: `λ (x : Int) => ∀ b : Int, Eq Int (Int.add x b) (Int.add b x)`.
fn build_outer_motive(c: &IntAddCommConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_add.clone(), x.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_add.clone(), bv), x);
    let concl = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let pi = mb.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), concl);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(lam)
}

/// Inner motive for outer ofNat-case: parameterized by `m : Nat`, produces
/// `λ (b : Int) => Eq Int (Int.add (ofNat m) b) (Int.add b (ofNat m))`.
fn build_inner_motive_ofnat(c: &IntAddCommConsts, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let of_m = Expr::app(c.int_of_nat.clone(), m.clone());
    let lhs = Expr::app(Expr::app(c.int_add.clone(), of_m.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_add.clone(), bv), of_m);
    let body = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let lam = mb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Inner motive for outer negSucc-case: parameterized by `m : Nat`, produces
/// `λ (b : Int) => Eq Int (Int.add (negSucc m) b) (Int.add b (negSucc m))`.
fn build_inner_motive_negsucc(c: &IntAddCommConsts, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let ns_m = Expr::app(c.int_neg_succ.clone(), m.clone());
    let lhs = Expr::app(Expr::app(c.int_add.clone(), ns_m.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_add.clone(), bv), ns_m);
    let body = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let lam = mb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Outer ofNat case: `λ (m : Nat) => λ (b : Int) =>
///     @Int.rec.{0} (inner_motive_ofNat m) oo on b`
/// where
///   oo := λ (n : Nat) => @congrArg.{1,1} Nat Int (Nat.add m n) (Nat.add n m)
///                            Int.ofNat (Nat.add_comm m n)
///   on := λ (n : Nat) => @Eq.refl.{1} Int (Int.subNatNat m (Nat.succ n))
fn build_outer_ofnat_case(c: &IntAddCommConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = cb.fresh_local(c.nat_type.clone());
    let (b_id, bv) = cb.fresh_local(c.int_type.clone());

    // oo: λ (n : Nat) => congrArg.{1,1} Nat Int (m+n) (n+m) Int.ofNat (Nat.add_comm m n)
    let oo = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let m_plus_n = Expr::app(Expr::app(c.nat_add.clone(), m.clone()), n.clone());
        let n_plus_m = Expr::app(Expr::app(c.nat_add.clone(), n.clone()), m.clone());
        // Nat.add_comm m n : Eq Nat (Nat.add m n) (Nat.add n m)
        let comm_witness = Expr::apps(c.nat_add_comm.clone(), [m.clone(), n.clone()]);
        // congrArg.{1,1} Nat Int (m+n) (n+m) Int.ofNat (Nat.add_comm m n)
        let congr_app = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                m_plus_n,
                n_plus_m,
                c.int_of_nat.clone(),
                comm_witness,
            ],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr_app);
        ob.finish_child(lam)
    };

    // on: λ (n : Nat) => @Eq.refl.{1} Int (Int.subNatNat m (Nat.succ n))
    // Both `Int.add (ofNat m) (negSucc n)` and `Int.add (negSucc n) (ofNat m)`
    // reduce to `Int.subNatNat m (Nat.succ n)` (iota on outer Int.rec +
    // inner Int.rec + delta on Int.add). We target the reduced form so the
    // kernel can verify both sides defn-equal to it.
    let on = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let succ_n = Expr::app(c.nat_succ.clone(), n);
        let snn = Expr::app(Expr::app(c.int_sub_nat_nat.clone(), m.clone()), succ_n);
        let refl = Expr::apps(c.eq_refl.clone(), [c.int_type.clone(), snn]);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), refl);
        nb.finish_child(lam)
    };

    let inner_motive = build_inner_motive_ofnat(c, &cb, &m);
    let rec_app = Expr::apps(c.int_rec.clone(), [inner_motive, oo, on, bv.clone()]);
    let lam_b = cb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let lam_m = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
    cb.finish_child(lam_m)
}

/// Outer negSucc case: `λ (m : Nat) => λ (b : Int) =>
///     @Int.rec.{0} (inner_motive_negSucc m) no nn b`
/// where
///   no := λ (n : Nat) => @Eq.refl.{1} Int (Int.subNatNat n (Nat.succ m))
///   nn := λ (n : Nat) => congrArg (λ x : Nat => Int.negSucc (Nat.succ x))
///                              (Nat.add_comm m n)
///       : Eq Int (Int.negSucc (Nat.succ (Nat.add m n)))
///                (Int.negSucc (Nat.succ (Nat.add n m)))
fn build_outer_negsucc_case(c: &IntAddCommConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = cb.fresh_local(c.nat_type.clone());
    let (b_id, bv) = cb.fresh_local(c.int_type.clone());

    // no: λ (n : Nat) => @Eq.refl.{1} Int (Int.subNatNat n (Nat.succ m))
    // Both `Int.add (negSucc m) (ofNat n)` and `Int.add (ofNat n) (negSucc m)`
    // reduce to `Int.subNatNat n (Nat.succ m)`.
    let no = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let succ_m = Expr::app(c.nat_succ.clone(), m.clone());
        let snn = Expr::app(Expr::app(c.int_sub_nat_nat.clone(), n), succ_m);
        let refl = Expr::apps(c.eq_refl.clone(), [c.int_type.clone(), snn]);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), refl);
        ob.finish_child(lam)
    };

    // nn: λ (n : Nat) =>
    //   @congrArg.{1,1} Nat Int (Nat.add m n) (Nat.add n m)
    //     (λ x : Nat => Int.negSucc (Nat.succ x)) (Nat.add_comm m n)
    let nn = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let m_plus_n = Expr::app(Expr::app(c.nat_add.clone(), m.clone()), n.clone());
        let n_plus_m = Expr::app(Expr::app(c.nat_add.clone(), n.clone()), m.clone());
        // func: λ (x : Nat) => Int.negSucc (Nat.succ x)
        let func = {
            let mut fb = EnvDeclBuilder::child_of(&ob);
            let (x_id, x) = fb.fresh_local(c.nat_type.clone());
            let body = Expr::app(c.int_neg_succ.clone(), Expr::app(c.nat_succ.clone(), x));
            let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
            fb.finish_child(lam)
        };
        let comm_witness = Expr::apps(c.nat_add_comm.clone(), [m.clone(), n.clone()]);
        let congr_app = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                m_plus_n,
                n_plus_m,
                func,
                comm_witness,
            ],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr_app);
        ob.finish_child(lam)
    };

    let inner_motive = build_inner_motive_negsucc(c, &cb, &m);
    let rec_app = Expr::apps(c.int_rec.clone(), [inner_motive, no, nn, bv.clone()]);
    let lam_b = cb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let lam_m = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
    cb.finish_child(lam_m)
}

/// Body: `λ (a b : Int) => @Int.rec.{0} outer_motive outer_ofNat outer_negSucc a b`.
fn build_int_add_comm_value(c: &IntAddCommConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.int_type.clone());
    let outer_motive = build_outer_motive(c, &vb);
    let outer_ofnat = build_outer_ofnat_case(c, &vb);
    let outer_negsucc = build_outer_negsucc_case(c, &vb);
    // Outer @Int.rec.{0} outer_motive outer_ofnat outer_negsucc a : ∀ b : Int, ...
    // then applied to b : Int.
    let rec_app_a = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, outer_ofnat, outer_negsucc, va],
    );
    let body = Expr::app(rec_app_a, vbv);
    let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, c.int_type.clone(), body);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_comm` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.add`, `Int.subNatNat`, `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `congrArg`.
    /// REQUIRES: `Nat.add_comm` is registered as `Declaration::Theorem`
    ///           (constructive proof — see `register_nat_add_comm_proof`).
    /// ENSURES: On success, `Int.add_comm` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_add_comm_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_comm_proof()?;

        let c = IntAddCommConsts::new();
        let type_ = build_int_add_comm_type(&c);
        let value = build_int_add_comm_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Int.rec.{0}` induction: outer on `a`, inner on `b`. Four
        // cases:
        // (ofNat m, ofNat n)   : congrArg Int.ofNat (Nat.add_comm m n)
        // (ofNat m, negSucc n) : Eq.refl Int (Int.subNatNat m (succ n))
        // (negSucc m, ofNat n) : Eq.refl Int (Int.subNatNat n (succ m))
        // (negSucc m, negSucc n): congrArg (λ x => negSucc (succ x)) (Nat.add_comm m n)
        // Replaces the prior `Declaration::Axiom` in
        // `data_types_int_lemmas.rs::init_int_arith_lemmas`.
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
    fn test_int_add_comm_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_comm_proof()
            .expect("first registration");
        env.register_int_add_comm_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_comm"))
            .expect("Int.add_comm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_comm_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_add_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.add_comm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.add_comm proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The proof root (after peeling two outer λ binders) is an
    /// `@Int.rec.{0}` application. Guards against a trivial `Eq.refl`
    /// masquerade (the 4-case split cannot collapse to a single refl).
    #[test]
    fn test_int_add_comm_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_add_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.add_comm"))
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
                "Int.rec",
                "Int.add_comm proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty: the transitive axiom deps of Int.add_comm
    /// must contain no `Declaration::Axiom`. Depends on Nat.add_comm and
    /// Nat.zero_add / Nat.succ_add having zero axiom deps (all #3604).
    #[test]
    fn test_int_add_comm_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_comm_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_comm"))
            .expect("Int.add_comm is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_comm must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
