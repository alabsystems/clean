// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Int.lt_irrefl : ∀ a : Int, Not (Int.lt a a)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.lt a b := Int.le (Int.add a (Int.ofNat 1)) b   -- reducible Definition
//! Int.le a b := Int.NonNeg (Int.sub b a)             -- reducible Definition
//! Not P      := P → False                            -- reducible Definition
//! ```
//!
//! So `Not (Int.lt a a)` unfolds to
//! `Int.NonNeg (Int.sub a (Int.add a (Int.ofNat 1))) → False`.
//!
//! # Proof sketch
//!
//! Given `h : NonNeg (Int.sub a (a + 1))`:
//!
//! 1. `Int.sub_add_one_self a : Eq (Int.sub a (a + 1)) (Int.negSucc Nat.zero)`
//!    (the identity `a - (a + 1) = -1`, see
//!    `algebra_int_sub_add_one_self_proof.rs`).
//! 2. Transport `h` along (1) with `@Eq.subst.{1}` (motive `fun x => NonNeg x`)
//!    to obtain `h' : NonNeg (Int.negSucc Nat.zero)`.
//! 3. Discriminate: with the predicate
//!    `disc i := @Int.rec.{1} (fun _ => Prop) (fun _ => True) (fun _ => False) i`
//!    (`True` on `ofNat`, `False` on `negSucc`), recurse on `h'` via
//!    `@Int.NonNeg.rec.{0}` with motive `fun i _ => disc i`. The single minor
//!    receives `n : Nat` and must prove `disc (Int.ofNat n)`, which reduces to
//!    `True`, discharged by `True.intro`. The recursor at `Int.negSucc Nat.zero`
//!    yields `disc (Int.negSucc Nat.zero)`, which reduces to `False`.
//!
//! The whole term is `λ a (h : NonNeg (sub a (a+1))) => <False>`, definitionally
//! a `Not (Int.lt a a)`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.sub_add_one_self`, the foundational
//! `Eq.subst`, the auto-generated `Int.rec` / `Int.NonNeg.rec`, and the
//! `True` / `True.intro` / `False` logical primitives — none of which are
//! `Declaration::Axiom`. Therefore `env.axiom_deps("Int.lt_irrefl")` is empty
//! and `env.proof_quality("Int.lt_irrefl") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLtIrreflConsts {
    int_type: Expr,
    nat_type: Expr,
    int_lt: Expr,
    int_sub: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nonneg: Expr,
    nonneg_rec: Expr,
    int_rec_prop: Expr,
    not_const: Expr,
    false_const: Expr,
    true_const: Expr,
    true_intro: Expr,
    sub_add_one_self: Expr,
    eq_subst: Expr,
}

impl IntLtIrreflConsts {
    fn new() -> Self {
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            // NonNeg.rec into Prop (result `False : Sort 0`) — Sort 0.
            nonneg_rec: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            // Int.rec producing a `Prop : Sort 1` value — Sort 1.
            int_rec_prop: Expr::const_(
                Name::from_string("Int.rec"),
                vec![Level::succ(Level::zero())],
            ),
            not_const: Expr::const_(Name::from_string("Not"), vec![]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            true_const: Expr::const_(Name::from_string("True"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            sub_add_one_self: Expr::const_(Name::from_string("Int.sub_add_one_self"), vec![]),
            eq_subst: Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn one(&self) -> Expr {
        Expr::app(
            self.int_of_nat.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }

    fn neg_succ_zero(&self) -> Expr {
        Expr::app(self.int_neg_succ.clone(), self.nat_zero.clone())
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    /// `disc = @Int.rec.{1} (fun _ : Int => Prop) (fun _ : Nat => True)
    ///                      (fun _ : Nat => False)`.
    ///
    /// `disc (Int.ofNat n)` reduces to `True`, `disc (Int.negSucc n)` to
    /// `False`. Built as a closed (no free fvar) term so it can be reused.
    fn discriminator(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        // motive: fun _ : Int => Prop
        let prop_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (i_id, _i) = mb.fresh_local(self.int_type.clone());
            let lam = mb.mk_lam(
                i_id,
                BinderInfo::Default,
                self.int_type.clone(),
                Expr::prop(),
            );
            mb.finish_child(lam)
        };
        // ofNat minor: fun _ : Nat => True
        let of_nat_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat_type.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat_type.clone(),
                self.true_const.clone(),
            );
            mb.finish_child(lam)
        };
        // negSucc minor: fun _ : Nat => False
        let neg_succ_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat_type.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat_type.clone(),
                self.false_const.clone(),
            );
            mb.finish_child(lam)
        };
        // disc = fun i : Int => @Int.rec.{1} prop_motive of_nat_minor neg_succ_minor i
        let (i_id, i) = b.fresh_local(self.int_type.clone());
        let rec_app = Expr::apps(
            self.int_rec_prop.clone(),
            [prop_motive, of_nat_minor, neg_succ_minor, i.clone()],
        );
        let lam = b.mk_lam(i_id, BinderInfo::Default, self.int_type.clone(), rec_app);
        b.finish_child(lam)
    }
}

/// Build `∀ a : Int, Not (Int.lt a a)`.
fn build_type(c: &IntLtIrreflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = Expr::app(c.not_const.clone(), c.lt(a.clone(), a.clone()));
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(r)
}

fn build_value(c: &IntLtIrreflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());

    // h : NonNeg (Int.sub a (a + 1))   (= Int.lt a a after delta).
    let a_plus_one = c.add(a.clone(), c.one());
    let sub_term = c.sub(a.clone(), a_plus_one.clone());
    let h_type = c.nonneg_of(sub_term.clone());
    let (h_id, h) = b.fresh_local(h_type.clone());

    // motive for transport: fun x : Int => Int.NonNeg x
    let subst_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.nonneg_of(x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // Int.sub_add_one_self a : Eq (Int.sub a (a+1)) (Int.negSucc 0).
    let eq1 = Expr::app(c.sub_add_one_self.clone(), a.clone());
    let neg_succ_zero = c.neg_succ_zero();

    // h' : NonNeg (Int.negSucc 0)
    //   = @Eq.subst.{1} Int motive (sub a (a+1)) (negSucc 0) eq1 h
    let h_prime = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            subst_motive,
            sub_term.clone(),
            neg_succ_zero.clone(),
            eq1,
            h.clone(),
        ],
    );

    // Discriminator predicate.
    let disc = c.discriminator(&b);

    // NonNeg.rec motive: fun (i : Int) (_ : NonNeg i) => disc i
    let rec_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let hi_type = c.nonneg_of(i.clone());
        let (hi_id, _hi) = mb.fresh_local(hi_type.clone());
        let body = Expr::app(disc.clone(), i.clone());
        let lam = mb.mk_lam(hi_id, BinderInfo::Default, hi_type, body);
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
        mb.finish_child(lam)
    };

    // NonNeg.rec minor: fun (n : Nat) => True.intro
    //   goal at minor is `disc (Int.ofNat n)` ≡ `True`.
    let rec_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (n_id, _n) = mb.fresh_local(c.nat_type.clone());
        let lam = mb.mk_lam(
            n_id,
            BinderInfo::Default,
            c.nat_type.clone(),
            c.true_intro.clone(),
        );
        mb.finish_child(lam)
    };

    // @Int.NonNeg.rec.{0} rec_motive rec_minor (Int.negSucc 0) h'
    //   : disc (Int.negSucc 0) ≡ False
    let false_proof = Expr::apps(
        c.nonneg_rec.clone(),
        [rec_motive, rec_minor, neg_succ_zero, h_prime],
    );

    // λ a (h : NonNeg (sub a (a+1))) => false_proof   :  Int.lt a a → False ≡ Not (Int.lt a a)
    let val = b.mk_lam(h_id, BinderInfo::Default, h_type, false_proof);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.lt_irrefl` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.NonNeg`, `Int.NonNeg.rec`, `Int.sub`, `Int.add`,
    ///           `Int.rec`, `Int.ofNat`, `Int.negSucc`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`.
    /// REQUIRES: `self.init_true_false()` has registered `Not`, `True`,
    ///           `True.intro`, `False`.
    /// ENSURES: On success, `Int.lt_irrefl` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.lt_irrefl` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_lt_irrefl_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.lt_irrefl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        self.init_true_false()?;
        // Constructive arithmetic dependency: a - (a + 1) = -1.
        self.register_int_sub_add_one_self_proof()?;

        let c = IntLtIrreflConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. The incoming
        // `h : Int.lt a a` delta-reduces to `NonNeg (Int.sub a (a+1))`, which
        // transports along `Int.sub_add_one_self a : a - (a+1) = -1` (via
        // `@Eq.subst.{1}`) to `NonNeg (Int.negSucc 0)`. A `@Int.NonNeg.rec.{0}`
        // recursion against the discriminator predicate `disc` (`True` on
        // `Int.ofNat`, `False` on `Int.negSucc`, built via `@Int.rec.{1}` into
        // `Prop`) closes the single `ofNat` minor with `True.intro` and yields
        // `disc (Int.negSucc 0)` ≡ `False`. The result inhabits
        // `Int.lt a a → False` ≡ `Not (Int.lt a a)`. No `sorry`, no
        // self-reference, no domain-axiom dependency. Replaces the prior
        // `Declaration::Axiom` in `order_int.rs::init_int_ord_lemmas`.
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
    fn test_int_lt_irrefl_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_lt_irrefl_proof()
            .expect("first registration");
        env.register_int_lt_irrefl_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.lt_irrefl"))
            .expect("Int.lt_irrefl should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_lt_irrefl_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_lt_irrefl_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.lt_irrefl"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the two outer λ binders (a, h), then the head must be
        // Int.NonNeg.rec (the discriminator recursion).
        let mut body: Expr = value.clone();
        for _ in 0..2 {
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
                "Int.lt_irrefl proof root must be Int.NonNeg.rec"
            ),
            k => panic!("expected Const(Int.NonNeg.rec), got {:?}", k),
        }
    }

    #[test]
    fn test_int_lt_irrefl_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_lt_irrefl_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.lt_irrefl"))
            .expect("Int.lt_irrefl is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.lt_irrefl must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_lt_irrefl_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_lt_irrefl_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.lt_irrefl"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.lt_irrefl must be Constructive, got {:?}",
            quality
        );
    }
}
