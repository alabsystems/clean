// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the additive-closure helper
//! `Int.NonNeg.add : ∀ x y : Int, Int.NonNeg x → Int.NonNeg y → Int.NonNeg (Int.add x y)`.
//!
//! This is not a demoted axiom — it is a fresh constructive building block
//! used by `algebra_int_le_trans_proof.rs` to combine two `Int.NonNeg`
//! witnesses. `Int.NonNeg` is the genuine single-constructor inductive
//!
//! ```text
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! # Proof sketch
//!
//! Recurse on `hx : NonNeg x` via `@Int.NonNeg.rec.{0}` with motive
//! `fun (i : Int) (_ : NonNeg i) => NonNeg (Int.add i y)`. The single minor
//! premise receives `n : Nat` (so `i = Int.ofNat n`) and must produce
//! `NonNeg (Int.add (Int.ofNat n) y)`. There we recurse on `hy : NonNeg y`
//! via a second `@Int.NonNeg.rec.{0}` with motive
//! `fun (j : Int) (_ : NonNeg j) => NonNeg (Int.add (Int.ofNat n) j)`; its
//! minor receives `m : Nat` (so `j = Int.ofNat m`) and must produce
//! `NonNeg (Int.add (Int.ofNat n) (Int.ofNat m))`.
//!
//! `Int.add (Int.ofNat n) (Int.ofNat m)` reduces by iota on the two nested
//! `Int.rec` (ofNat/ofNat case) + delta on the reducible `Int.add` to
//! `Int.ofNat (Nat.add n m)`. So `@Int.NonNeg.mk (Nat.add n m)`, whose type
//! is `NonNeg (Int.ofNat (Nat.add n m))`, inhabits the goal up to definitional
//! equality.
//!
//! # Axiom closure
//!
//! The proof mentions only `Int`, `Int.add`, `Int.ofNat`, `Int.NonNeg`,
//! `Int.NonNeg.rec`, `Int.NonNeg.mk`, `Nat`, `Nat.add`. None are
//! `Declaration::Axiom` (`Int.NonNeg.rec` is auto-generated kernel machinery,
//! `Int.add`/`Nat.add` are reducible Definitions, the rest are
//! constructors/inductives). Therefore `env.axiom_deps("Int.NonNeg.add")` is
//! empty and `env.proof_quality("Int.NonNeg.add") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
pub(super) struct IntNonNegAddConsts {
    pub(super) int_type: Expr,
    pub(super) nat_type: Expr,
    pub(super) int_add: Expr,
    pub(super) int_of_nat: Expr,
    pub(super) nat_add: Expr,
    pub(super) nonneg: Expr,
    pub(super) nonneg_rec: Expr,
    pub(super) nonneg_mk: Expr,
}

impl IntNonNegAddConsts {
    pub(super) fn new() -> Self {
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            // Prop-valued motive — Sort 0.
            nonneg_rec: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
        }
    }

    pub(super) fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    pub(super) fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    pub(super) fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }
}

/// Build `∀ x y : Int, Int.NonNeg x → Int.NonNeg y → Int.NonNeg (Int.add x y)`.
fn build_type(c: &IntNonNegAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.int_type.clone());
    let (y_id, y) = b.fresh_local(c.int_type.clone());
    let hx_type = c.nonneg_of(x.clone());
    let (hx_id, _hx) = b.fresh_local(hx_type.clone());
    let hy_type = c.nonneg_of(y.clone());
    let (hy_id, _hy) = b.fresh_local(hy_type.clone());
    let concl = c.nonneg_of(c.add(x.clone(), y.clone()));
    let r = b.mk_pi(hy_id, BinderInfo::Default, hy_type, concl);
    let r = b.mk_pi(hx_id, BinderInfo::Default, hx_type, r);
    let r = b.mk_pi(y_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (x y : Int) (hx : NonNeg x) (hy : NonNeg y) =>
///   @Int.NonNeg.rec.{0}
///     (fun (i : Int) (_ : NonNeg i) => NonNeg (Int.add i y))
///     (fun (n : Nat) =>
///        @Int.NonNeg.rec.{0}
///          (fun (j : Int) (_ : NonNeg j) => NonNeg (Int.add (Int.ofNat n) j))
///          (fun (m : Nat) => @Int.NonNeg.mk (Nat.add n m))
///          y hy)
///     x hx
/// ```
fn build_value(c: &IntNonNegAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.int_type.clone());
    let (y_id, y) = b.fresh_local(c.int_type.clone());
    let hx_type = c.nonneg_of(x.clone());
    let (hx_id, hx) = b.fresh_local(hx_type.clone());
    let hy_type = c.nonneg_of(y.clone());
    let (hy_id, hy) = b.fresh_local(hy_type.clone());

    // Outer motive: fun (i : Int) (_ : NonNeg i) => NonNeg (Int.add i y)
    let outer_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let hi_type = c.nonneg_of(i.clone());
        let (hi_id, _hi) = mb.fresh_local(hi_type.clone());
        let body = c.nonneg_of(c.add(i.clone(), y.clone()));
        let lam = mb.mk_lam(hi_id, BinderInfo::Default, hi_type, body);
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
        mb.finish_child(lam)
    };

    // Outer minor: fun (n : Nat) => inner_rec
    let outer_minor = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let of_nat_n = c.of_nat(n.clone());

        // Inner motive: fun (j : Int) (_ : NonNeg j) => NonNeg (Int.add (ofNat n) j)
        let inner_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (j_id, j) = mb.fresh_local(c.int_type.clone());
            let hj_type = c.nonneg_of(j.clone());
            let (hj_id, _hj) = mb.fresh_local(hj_type.clone());
            let body = c.nonneg_of(c.add(of_nat_n.clone(), j.clone()));
            let lam = mb.mk_lam(hj_id, BinderInfo::Default, hj_type, body);
            let lam = mb.mk_lam(j_id, BinderInfo::Default, c.int_type.clone(), lam);
            mb.finish_child(lam)
        };

        // Inner minor: fun (m : Nat) => @Int.NonNeg.mk (Nat.add n m)
        let inner_minor = {
            let mut ib = EnvDeclBuilder::child_of(&ob);
            let (m_id, m) = ib.fresh_local(c.nat_type.clone());
            let nat_add_nm = Expr::app(Expr::app(c.nat_add.clone(), n.clone()), m.clone());
            let mk_app = Expr::app(c.nonneg_mk.clone(), nat_add_nm);
            let lam = ib.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), mk_app);
            ib.finish_child(lam)
        };

        // @Int.NonNeg.rec.{0} inner_motive inner_minor y hy
        let inner_rec = Expr::apps(
            c.nonneg_rec.clone(),
            [inner_motive, inner_minor, y.clone(), hy.clone()],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), inner_rec);
        ob.finish_child(lam)
    };

    // @Int.NonNeg.rec.{0} outer_motive outer_minor x hx
    let outer_rec = Expr::apps(
        c.nonneg_rec.clone(),
        [outer_motive, outer_minor, x.clone(), hx.clone()],
    );

    let val = b.mk_lam(hy_id, BinderInfo::Default, hy_type, outer_rec);
    let val = b.mk_lam(hx_id, BinderInfo::Default, hx_type, val);
    let val = b.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.NonNeg.add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.NonNeg`,
    ///           `Int.NonNeg.mk`, `Int.NonNeg.rec`, `Int.add`, `Int.ofNat`.
    /// ENSURES: On success, `Int.NonNeg.add` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.NonNeg.add` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_nonneg_add_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.NonNeg.add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;

        let c = IntNonNegAddConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Double `@Int.NonNeg.rec.{0}`
        // recursion extracts the two `Nat` witnesses `n`, `m` and rebuilds
        // `@Int.NonNeg.mk (Nat.add n m)`, which type-checks against the goal
        // `NonNeg (Int.add (Int.ofNat n) (Int.ofNat m))` because
        // `Int.add (Int.ofNat n) (Int.ofNat m)` reduces to
        // `Int.ofNat (Nat.add n m)` by iota on `Int.rec` (ofNat/ofNat case) +
        // delta on the reducible `Int.add`. No `sorry`, no self-reference, no
        // domain-axiom dependency.
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
    fn test_int_nonneg_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_nonneg_add_proof()
            .expect("first registration");
        env.register_int_nonneg_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.NonNeg.add"))
            .expect("Int.NonNeg.add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_nonneg_add_proof_uses_nonneg_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_nonneg_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.NonNeg.add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the four outer λ binders, then the head must be Int.NonNeg.rec.
        let mut body: Expr = value.clone();
        for _ in 0..4 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head: Expr = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.NonNeg.rec",
                "Int.NonNeg.add proof root must be Int.NonNeg.rec"
            ),
            k => panic!("expected Const(Int.NonNeg.rec), got {:?}", k),
        }
    }

    #[test]
    fn test_int_nonneg_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_nonneg_add_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.NonNeg.add"))
            .expect("Int.NonNeg.add is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.NonNeg.add must have empty axiom closure, got {:?}",
            domain_deps
        );
    }
}
