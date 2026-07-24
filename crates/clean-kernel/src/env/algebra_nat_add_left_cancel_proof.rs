// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.add_left_cancel : ∀ a b c : Nat, Eq (Nat.add a b) (Nat.add a c) → Eq b c`.
//!
//! This is the left-cancellation helper toward demoting
//! `Nat.mul_left_cancel_succ` (see `data_types_nat_lemmas.rs`). Rather than
//! inducting on the *first* addend `a` (which would require rewriting through
//! `Nat.succ_add`, since `Nat.add` recurses on its second argument), the proof
//! composes the already-constructive `Nat.add_comm` and `Nat.add_right_cancel`.
//!
//! # Proof sketch
//!
//! ```text
//! theorem Nat.add_left_cancel (a b c : Nat) (h : Eq (Nat.add a b) (Nat.add a c)) :
//!     Eq b c :=
//!   Nat.add_right_cancel b a c
//!     (Eq.trans
//!       (Eq.trans (Nat.add_comm b a) h)        -- b + a = a + b = a + c
//!       (Eq.symm (Nat.add_comm c a)))          -- a + c = c + a
//! ```
//!
//! Reading the equality chain:
//! - `Nat.add_comm b a : Eq (b + a) (a + b)`
//! - `h : Eq (a + b) (a + c)`
//! - `Eq.trans (..) (..) : Eq (b + a) (a + c)`
//! - `Eq.symm (Nat.add_comm c a) : Eq (a + c) (c + a)`
//! - `Eq.trans (..) (..) : Eq (b + a) (c + a)`
//! - `Nat.add_right_cancel b a c (..) : Eq b c` (cancels the common `+ a`)
//!
//! `Nat.add_right_cancel`'s registered signature is `∀ n m k, Eq (n + m) (k + m)
//! → Eq n k`; instantiated at `n := b`, `m := a`, `k := c` it expects exactly
//! `Eq (b + a) (c + a)`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.symm`, `Eq.trans`, `Nat`, `Nat.add`,
//! `Nat.add_comm`, and `Nat.add_right_cancel`. The latter two are themselves
//! constructive `Declaration::Theorem`s (see `algebra_nat_add_comm_proof.rs`
//! and `algebra_nat_add_right_cancel_proof.rs`), so
//! `env.axiom_deps("Nat.add_left_cancel")` is empty and
//! `env.proof_quality("Nat.add_left_cancel") == ProofQuality::Constructive`.
//!
//! Tracks #3604 (cancellation-law demotion); prerequisite toward
//! `Nat.mul_left_cancel_succ`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatAddLeftCancelConsts {
    nat_type: Expr,
    nat_add: Expr,
    eq_const: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    add_comm: Expr,
    add_right_cancel: Expr,
}

impl NatAddLeftCancelConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
            add_comm: Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
            add_right_cancel: Expr::const_(Name::from_string("Nat.add_right_cancel"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }
}

/// Build `∀ a b c : Nat, Eq (Nat.add a b) (Nat.add a c) → Eq b c`.
fn build_type(c: &NatAddLeftCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (b_id, bv) = b.fresh_local(c.nat_type.clone());
    let (cc_id, cv) = b.fresh_local(c.nat_type.clone());
    let hyp = c.eq_nat(c.add(a.clone(), bv.clone()), c.add(a.clone(), cv.clone()));
    let concl = c.eq_nat(bv.clone(), cv.clone());
    let body = {
        let (h_id, _h) = b.fresh_local(hyp.clone());
        b.mk_pi(h_id, BinderInfo::Default, hyp, concl)
    };
    let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat_type.clone(), body);
    let e = b.mk_pi(b_id, BinderInfo::Default, c.nat_type.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), e);
    b.finish(e)
}

/// Body:
/// `λ (a b c : Nat) (h : a + b = a + c) =>
///    Nat.add_right_cancel b a c
///      (Eq.trans (Eq.trans (Nat.add_comm b a) h) (Eq.symm (Nat.add_comm c a)))`.
fn build_value(c: &NatAddLeftCancelConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.nat_type.clone());
    let (b_id, bv) = vb.fresh_local(c.nat_type.clone());
    let (cc_id, cv) = vb.fresh_local(c.nat_type.clone());
    let hyp = c.eq_nat(c.add(a.clone(), bv.clone()), c.add(a.clone(), cv.clone()));
    let (h_id, h) = vb.fresh_local(hyp.clone());

    // Endpoints used in the equality chain.
    let b_plus_a = c.add(bv.clone(), a.clone());
    let a_plus_b = c.add(a.clone(), bv.clone());
    let a_plus_c = c.add(a.clone(), cv.clone());
    let c_plus_a = c.add(cv.clone(), a.clone());

    // Nat.add_comm b a : Eq (b + a) (a + b)
    let comm_ba = Expr::apps(c.add_comm.clone(), [bv.clone(), a.clone()]);
    // Eq.trans Nat (b+a) (a+b) (a+c) (comm_ba) h : Eq (b + a) (a + c)
    let chain1 = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            b_plus_a.clone(),
            a_plus_b,
            a_plus_c.clone(),
            comm_ba,
            h,
        ],
    );
    // Nat.add_comm c a : Eq (c + a) (a + c)
    let comm_ca = Expr::apps(c.add_comm.clone(), [cv.clone(), a.clone()]);
    // Eq.symm Nat (c+a) (a+c) (comm_ca) : Eq (a + c) (c + a)
    let sym_ca = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            c_plus_a.clone(),
            a_plus_c.clone(),
            comm_ca,
        ],
    );
    // Eq.trans Nat (b+a) (a+c) (c+a) chain1 sym_ca : Eq (b + a) (c + a)
    let chain2 = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            b_plus_a,
            a_plus_c,
            c_plus_a,
            chain1,
            sym_ca,
        ],
    );
    // Nat.add_right_cancel b a c chain2 : Eq b c
    let body = Expr::apps(
        c.add_right_cancel.clone(),
        [bv.clone(), a.clone(), cv.clone(), chain2],
    );

    let val = vb.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let val = vb.mk_lam(cc_id, BinderInfo::Default, c.nat_type.clone(), val);
    let val = vb.mk_lam(b_id, BinderInfo::Default, c.nat_type.clone(), val);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.nat_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Nat.add_left_cancel` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.add`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.symm`, `Eq.trans`.
    /// REQUIRES: `Nat.add_comm` and `Nat.add_right_cancel` are registered as
    ///           constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Nat.add_left_cancel` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.add_left_cancel` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_add_left_cancel_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_left_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_comm_proof()?;
        self.register_nat_add_right_cancel_proof()?;

        let c = NatAddLeftCancelConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Left cancellation
        // is derived from the constructive `Nat.add_comm` and
        // `Nat.add_right_cancel` rather than by induction on the first addend
        // (which `Nat.add`'s right-recursion would force through `Nat.succ_add`).
        // The equality chain `b + a = a + b = a + c = c + a` is built with
        // `Eq.trans` / `Eq.symm`, then `Nat.add_right_cancel b a c` strips the
        // common `+ a`. No `sorry`, no self-reference, no domain-axiom
        // dependency (both helpers are constructive). New helper toward
        // demoting `Nat.mul_left_cancel_succ`.
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
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// Kernel accepts the comm + right-cancel composition; registered as a
    /// Theorem (not Axiom), idempotently.
    #[test]
    fn test_nat_add_left_cancel_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_add_left_cancel_proof()
            .expect("first registration");
        env.register_nat_add_left_cancel_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.add_left_cancel"))
            .expect("Nat.add_left_cancel should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Nat.add_left_cancel"),
                vec![],
            ))
            .expect("Nat.add_left_cancel should type-check");
    }

    /// After peeling four λ binders (a, b, c, h), the proof root is
    /// `Nat.add_right_cancel` — guards against an `Eq.refl` / axiom-reference
    /// masquerade (left cancellation is an implication that cannot reduce
    /// without the cancellation helper).
    #[test]
    fn test_nat_add_left_cancel_proof_uses_add_right_cancel() {
        let mut env = Environment::new();
        env.register_nat_add_left_cancel_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_left_cancel"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..4 {
            cur = match cur.kind() {
                ExprKind::Lam(_, _, body) => (**body).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = cur;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.add_right_cancel",
                "Nat.add_left_cancel proof root must be Nat.add_right_cancel"
            ),
            k => panic!("expected Const(Nat.add_right_cancel, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive). Both `Nat.add_comm` and
    /// `Nat.add_right_cancel` are constructive theorems, so left cancellation
    /// inherits empty domain-axiom deps.
    #[test]
    fn test_nat_add_left_cancel_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_add_left_cancel_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.add_left_cancel"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.add_left_cancel must have empty axiom closure, got {:?}",
            domain_deps
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.add_left_cancel"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
