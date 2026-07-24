// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.subNatNat_self_succ :
//!    ∀ b : Nat, Eq Int (Int.subNatNat b (Nat.succ b)) (Int.negSucc Nat.zero)`.
//!
//! Built by induction on `b` via `@Nat.rec.{0}`, hand-constructed `Expr`
//! (no tactics). Sibling of `algebra_int_sub_nat_nat_self_proof.rs`, the
//! `subNatNat b b = 0` companion. This `b` vs `succ b` "one short" form
//! gives the canonical `negSucc 0`; it is the bridge used by the reverse
//! Nat-cast (`natCast (succ b) ≤ natCast b → False`).
//!
//! # Proof sketch
//!
//! We induct on `b` via `@Nat.rec.{0}` with motive
//! `λ t : Nat => Eq Int (Int.subNatNat t (Nat.succ t)) (Int.negSucc Nat.zero)`.
//!
//! - **base (`t = Nat.zero`)**: goal
//!   `Eq Int (Int.subNatNat 0 (succ 0)) (Int.negSucc 0)`. This is exactly the
//!   constructive theorem `Int.subNatNat_zero_succ Nat.zero`
//!   (`subNatNat 0 (succ n) = negSucc n`, at `n = 0`).
//!
//! - **step (`t = Nat.succ k`)**: given
//!   `ih : Eq Int (Int.subNatNat k (succ k)) (Int.negSucc 0)`, the goal is
//!   `Eq Int (Int.subNatNat (succ k) (succ (succ k))) (Int.negSucc 0)`. The
//!   constructive theorem
//!   `Int.subNatNat_succ_succ k (succ k)
//!      : Eq Int (Int.subNatNat (succ k) (succ (succ k)))
//!               (Int.subNatNat k (succ k))`
//!   chained with `ih` via `Eq.trans` closes the goal.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.rec`, `Int.subNatNat`, `Int.negSucc`, `Eq`, `Eq.trans`, and the
//! constructive `Declaration::Theorem`s `Int.subNatNat_zero_succ` and
//! `Int.subNatNat_succ_succ`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.subNatNat_self_succ")` is empty and
//! `env.proof_quality("Int.subNatNat_self_succ") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubNatNatSelfSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    int_sub_nat_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat_zero_succ: Expr,
    int_sub_nat_nat_succ_succ: Expr,
    eq_const: Expr,
    eq_trans: Expr,
}

impl IntSubNatNatSelfSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat_zero_succ: Expr::const_(
                Name::from_string("Int.subNatNat_zero_succ"),
                vec![],
            ),
            int_sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn neg_succ_zero(&self) -> Expr {
        Expr::app(self.int_neg_succ.clone(), self.nat_zero.clone())
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

/// Build `∀ b : Nat, Eq Int (Int.subNatNat b (Nat.succ b)) (Int.negSucc Nat.zero)`.
fn build_type(c: &IntSubNatNatSelfSuccConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(
        c.sub_nat_nat(n.clone(), c.succ(n.clone())),
        c.neg_succ_zero(),
    );
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    b.finish(ty_raw)
}

/// Body: `λ (b : Nat) => @Nat.rec.{0} motive base step b`.
fn build_value(c: &IntSubNatNatSelfSuccConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    // motive: λ (t : Nat) => Eq Int (subNatNat t (succ t)) (negSucc 0)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(
            c.sub_nat_nat(t.clone(), c.succ(t.clone())),
            c.neg_succ_zero(),
        );
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // base: Int.subNatNat_zero_succ Nat.zero
    //   : Eq Int (subNatNat 0 (succ 0)) (negSucc 0)
    let base = Expr::app(c.int_sub_nat_nat_zero_succ.clone(), c.nat_zero.clone());

    // step: λ (k : Nat) (ih : Eq Int (subNatNat k (succ k)) (negSucc 0)) =>
    //   Eq.trans Int (subNatNat (succ k) (succ (succ k))) (subNatNat k (succ k))
    //     (negSucc 0) (subNatNat_succ_succ k (succ k)) ih
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_type = c.eq_int(
            c.sub_nat_nat(k.clone(), c.succ(k.clone())),
            c.neg_succ_zero(),
        );
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        // s := Int.subNatNat_succ_succ k (succ k)
        //    : Eq Int (subNatNat (succ k) (succ (succ k))) (subNatNat k (succ k))
        let s = Expr::apps(
            c.int_sub_nat_nat_succ_succ.clone(),
            [k.clone(), c.succ(k.clone())],
        );

        let lhs = c.sub_nat_nat(c.succ(k.clone()), c.succ(c.succ(k.clone())));
        let mid = c.sub_nat_nat(k.clone(), c.succ(k.clone()));
        let trans = Expr::apps(
            c.eq_trans.clone(),
            [c.int_type.clone(), lhs, mid, c.neg_succ_zero(), s, ih],
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
    /// Register `Int.subNatNat_self_succ` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`,
    ///           `Int.subNatNat`, `Int.negSucc`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`.
    /// REQUIRES: `Int.subNatNat_zero_succ` and `Int.subNatNat_succ_succ` are
    ///           registered as constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.subNatNat_self_succ` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.subNatNat_self_succ` is already
    ///          registered with any declaration kind, this call returns
    ///          `Ok(())` without modification.
    pub(crate) fn register_int_sub_nat_nat_self_succ_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.subNatNat_self_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_sub_nat_nat_zero_succ_proof()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;

        let c = IntSubNatNatSelfSuccConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Induction on `b` via
        // `@Nat.rec.{0}`. Base case `Int.subNatNat_zero_succ Nat.zero`. Step
        // case `Eq.trans (Int.subNatNat_succ_succ k (succ k)) ih`, threading
        // the constructive successor-cancellation theorem. No `sorry`, no
        // self-reference, no domain-axiom dependency (both deps constructive).
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
    fn test_int_sub_nat_nat_self_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_self_succ_proof()
            .expect("first registration");
        env.register_int_sub_nat_nat_self_succ_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_self_succ"))
            .expect("Int.subNatNat_self_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the outer λ binder) must be a `@Nat.rec.{0}`
    /// application. Guards against an axiom-wrapping masquerade.
    #[test]
    fn test_int_sub_nat_nat_self_succ_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_self_succ_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_self_succ"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => (**body).clone(),
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = outer_body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Int.subNatNat_self_succ proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_int_sub_nat_nat_self_succ_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_self_succ_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.subNatNat_self_succ"))
            .expect("Int.subNatNat_self_succ is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.subNatNat_self_succ must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
