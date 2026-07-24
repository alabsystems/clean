// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.mul_comm : ∀ a b : Nat, Eq (Nat.mul a b) (Nat.mul b a)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by induction on the SECOND argument `b` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n` — recurses
//! on second argument.
//!
//! ```text
//! theorem Nat.mul_comm (a b : Nat) : Eq (Nat.mul a b) (Nat.mul b a) :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.mul a t) (Nat.mul t a))
//!     (Eq.symm (Nat.zero_mul a))                               -- base
//!     (fun k ih =>
//!        Eq.trans (Eq.trans c1 c2) c3)                         -- step
//!     b
//! ```
//!
//! **Base case.** motive(Nat.zero) ≡ `Eq (Nat.mul a Nat.zero) (Nat.mul Nat.zero a)`.
//! `Nat.mul a Nat.zero` iota-reduces to `Nat.zero`; `Nat.mul Nat.zero a` does NOT
//! (recurses on 2nd arg). So the reduced motive is
//! `Eq Nat.zero (Nat.mul Nat.zero a)`, witnessed by
//! `@Eq.symm.{1} Nat (Nat.mul Nat.zero a) Nat.zero (Nat.zero_mul a)`.
//!
//! **Step case.** `ih : Eq (Nat.mul a k) (Nat.mul k a)`. After iota+beta on
//! LHS of motive(succ k):
//! - LHS `Nat.mul a (succ k)` ι→ `Nat.add (Nat.mul a k) a`.
//! - RHS `Nat.mul (succ k) a` does NOT reduce.
//!
//! Chain:
//! ```text
//! c1 := congrArg (λ x => Nat.add x a) ih
//!       : Eq (Nat.add (Nat.mul a k) a) (Nat.add (Nat.mul k a) a)
//! c2 := Nat.add_comm (Nat.mul k a) a
//!       : Eq (Nat.add (Nat.mul k a) a) (Nat.add a (Nat.mul k a))
//! c3 := Eq.symm (Nat.succ_mul k a)
//!       : Eq (Nat.add a (Nat.mul k a)) (Nat.mul (succ k) a)
//! ```
//!
//! `Eq.trans (Eq.trans c1 c2) c3` witnesses motive(succ k).
//!
//! # Axiom closure
//!
//! Proof mentions `Eq`, `Eq.refl`, `Eq.symm`, `Eq.trans`, `congrArg`,
//! `Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.rec`,
//! `Nat.zero_mul` (#3604, constructive sibling), `Nat.add_comm`
//! (constructive #3604), `Nat.succ_mul` (constructive #3604). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Nat.mul_comm")` is empty and
//! `env.proof_quality("Nat.mul_comm") == ProofQuality::Constructive`.
//!
//! Tracks #3604 (Int cascade — precondition for `Int.mul_comm`). Sibling
//! proofs:
//! - `algebra_nat_zero_mul_proof.rs` (#3604, Nat.zero_mul).
//! - `algebra_nat_succ_mul_proof.rs` (#3604, Nat.succ_mul).
//! - `algebra_nat_add_comm_proof.rs` (#3604, Nat.add_comm).
//! - `algebra_int_mul_comm_proof.rs` (#3604, consumer — Int.mul_comm).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatMulCommConsts {
    nat_type: Expr,
    nat_mul: Expr,
    nat_add: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nat_zero_mul: Expr,
    nat_add_comm: Expr,
    nat_succ_mul: Expr,
}

impl NatMulCommConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_zero_mul: Expr::const_(Name::from_string("Nat.zero_mul"), vec![]),
            nat_add_comm: Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
            nat_succ_mul: Expr::const_(Name::from_string("Nat.succ_mul"), vec![]),
        }
    }
}

/// Build `∀ a b : Nat, Eq Nat (Nat.mul a b) (Nat.mul b a)`.
fn build_type(c: &NatMulCommConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let lhs = Expr::app(Expr::app(c.nat_mul.clone(), a.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.nat_mul.clone(), bv), a);
    let concl = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Motive: `λ (t : Nat) => Eq Nat (Nat.mul a t) (Nat.mul t a)`.
fn build_motive(c: &NatMulCommConsts, parent: &EnvDeclBuilder, va: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let m_lhs = Expr::app(Expr::app(c.nat_mul.clone(), va.clone()), t.clone());
    let m_rhs = Expr::app(Expr::app(c.nat_mul.clone(), t), va.clone());
    let body = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), m_lhs, m_rhs]);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Base case: `@Eq.symm.{1} Nat (Nat.mul Nat.zero a) Nat.zero (Nat.zero_mul a)`.
///
/// motive(Nat.zero) reduces LHS iota to Nat.zero; RHS unchanged. So the
/// reduced motive is `Eq Nat.zero (Nat.mul Nat.zero a)`, matched by
/// `Eq.symm (Nat.zero_mul a)`.
fn build_base(c: &NatMulCommConsts, va: &Expr) -> Expr {
    let zero_mul_a = Expr::app(c.nat_zero_mul.clone(), va.clone());
    let mul_zero_a = Expr::app(Expr::app(c.nat_mul.clone(), c.nat_zero.clone()), va.clone());
    Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            mul_zero_a,
            c.nat_zero.clone(),
            zero_mul_a,
        ],
    )
}

/// Step case: chain `c1`, `c2`, `c3` via `Eq.trans`.
fn build_step(c: &NatMulCommConsts, parent: &EnvDeclBuilder, va: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = sb.fresh_local(c.nat_type.clone());

    // ih type: Eq Nat (Nat.mul a k) (Nat.mul k a)
    let mul_a_k = Expr::app(Expr::app(c.nat_mul.clone(), va.clone()), k.clone());
    let mul_k_a = Expr::app(Expr::app(c.nat_mul.clone(), k.clone()), va.clone());
    let ih_type = Expr::apps(
        c.eq_const.clone(),
        [c.nat_type.clone(), mul_a_k.clone(), mul_k_a.clone()],
    );
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());

    // c1 := congrArg (λ x => Nat.add x a) ih
    //   : Eq (Nat.add (Nat.mul a k) a) (Nat.add (Nat.mul k a) a)
    let func_c1 = {
        let mut fb = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = fb.fresh_local(c.nat_type.clone());
        let body = Expr::app(Expr::app(c.nat_add.clone(), x), va.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
        fb.finish_child(lam)
    };
    let c1 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            mul_a_k.clone(),
            mul_k_a.clone(),
            func_c1,
            ih,
        ],
    );

    // c2 := Nat.add_comm (Nat.mul k a) a
    //   : Eq (Nat.add (Nat.mul k a) a) (Nat.add a (Nat.mul k a))
    let c2 = Expr::apps(c.nat_add_comm.clone(), [mul_k_a.clone(), va.clone()]);

    // c3 := Eq.symm (Nat.succ_mul k a)
    // Nat.succ_mul k a : Eq (Nat.mul (succ k) a) (Nat.add a (Nat.mul k a))
    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let mul_succ_k_a = Expr::app(Expr::app(c.nat_mul.clone(), succ_k.clone()), va.clone());
    let add_a_mka = Expr::app(Expr::app(c.nat_add.clone(), va.clone()), mul_k_a.clone());
    let succ_mul_witness = Expr::apps(c.nat_succ_mul.clone(), [k.clone(), va.clone()]);
    let c3 = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            mul_succ_k_a.clone(),
            add_a_mka.clone(),
            succ_mul_witness,
        ],
    );

    // p = Nat.add (Nat.mul a k) a  (reduced form of Nat.mul a (succ k))
    // q = Nat.add (Nat.mul k a) a
    // r = Nat.add a (Nat.mul k a)
    // s = Nat.mul (succ k) a
    let p_expr = Expr::app(Expr::app(c.nat_add.clone(), mul_a_k.clone()), va.clone());
    let q_expr = Expr::app(Expr::app(c.nat_add.clone(), mul_k_a), va.clone());
    let r_expr = add_a_mka;
    let s_expr = mul_succ_k_a;
    let trans1 = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            p_expr.clone(),
            q_expr,
            r_expr.clone(),
            c1,
            c2,
        ],
    );
    let trans2 = Expr::apps(
        c.eq_trans.clone(),
        [c.nat_type.clone(), p_expr, r_expr, s_expr, trans1, c3],
    );

    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans2);
    let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_k)
}

/// Body: `λ (a b : Nat) => @Nat.rec.{0} motive base step b`.
fn build_value(c: &NatMulCommConsts) -> Expr {
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
    /// Register `Nat.mul_comm` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.symm`,
    ///           `Eq.trans`, `congrArg`.
    /// REQUIRES: `Nat.zero_mul`, `Nat.add_comm`, `Nat.succ_mul` are
    ///           registered as `Declaration::Theorem` (constructive).
    /// ENSURES: On success, `Nat.mul_comm` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_mul_comm_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_zero_mul_proof()?;
        self.register_nat_add_comm_proof()?;
        self.register_nat_succ_mul_proof()?;

        let c = NatMulCommConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on
        // `b` via `Nat.rec.{0}`. Base: Eq.symm (Nat.zero_mul a). Step: chains
        //   c1 := congrArg (λ x => Nat.add x a) ih
        //   c2 := Nat.add_comm (Nat.mul k a) a
        //   c3 := Eq.symm (Nat.succ_mul k a)
        // via Eq.trans. Replaces the prior `Declaration::Axiom` in
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
    fn test_nat_mul_comm_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_mul_comm_proof()
            .expect("first registration");
        env.register_nat_mul_comm_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.mul_comm"))
            .expect("Nat.mul_comm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_mul_comm_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_mul_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.mul_comm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.mul_comm proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    #[test]
    fn test_nat_mul_comm_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_mul_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.mul_comm"))
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
                "Nat.mul_comm proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_nat_mul_comm_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_mul_comm_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.mul_comm"))
            .expect("Nat.mul_comm is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.mul_comm must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
