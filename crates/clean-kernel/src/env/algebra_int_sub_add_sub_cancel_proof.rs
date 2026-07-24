// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the additive cancellation identity
//! `Int.sub_add_sub_cancel : ∀ a b c : Int,
//!    Eq Int (Int.add (Int.sub c b) (Int.sub b a)) (Int.sub c a)`.
//!
//! This is not a demoted axiom — it is a fresh constructive building block
//! used by `algebra_int_le_trans_proof.rs` to align the two combined
//! `Int.NonNeg` witnesses. The identity `(c - b) + (b - a) = c - a` is the
//! arithmetic heart of `Int.le` transitivity.
//!
//! # Proof sketch
//!
//! `Int.sub x y` is the reducible Definition `Int.add x (Int.neg y)`, so the
//! goal is definitionally
//!
//! ```text
//! Eq Int (Int.add (Int.add c (Int.neg b)) (Int.add b (Int.neg a)))
//!        (Int.add c (Int.neg a)).
//! ```
//!
//! Write `nb = Int.neg b`, `na = Int.neg a`. The chain (all over `Int.add`):
//!
//! ```text
//! (c + nb) + (b + na)
//!   = ((c + nb) + b) + na        -- Eq.symm (Int.add_assoc (c+nb) b na)
//!   = (c + (nb + b)) + na        -- congrArg (· + na) (Int.add_assoc c nb b)
//!   = (c + Int.zero) + na        -- congrArg (fun t => (c + t) + na)
//!                                 --   (Int.neg_add_self b : nb + b = 0)
//!   = c + na                     -- congrArg (· + na) (Int.add_zero c)
//! ```
//!
//! composed by `@Eq.trans.{1}`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_assoc`, `Int.neg_add_self`,
//! `Int.add_zero` theorems and the `Eq.trans` / `congrArg` foundational
//! machinery (`Int.sub` / `Int.neg` are reducible Definitions). Therefore
//! `env.axiom_deps("Int.sub_add_sub_cancel")` is empty and
//! `env.proof_quality("Int.sub_add_sub_cancel") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubAddSubCancelConsts {
    int_type: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_sub: Expr,
    int_zero: Expr,
    add_assoc: Expr,
    neg_add_self: Expr,
    add_zero: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl IntSubAddSubCancelConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            neg_add_self: Expr::const_(Name::from_string("Int.neg_add_self"), vec![]),
            add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    /// `@Eq.trans.{1} Int x y z hxy hyz : Eq Int x z`.
    fn trans(&self, x: Expr, y: Expr, z: Expr, hxy: Expr, hyz: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, hxy, hyz],
        )
    }

    /// `@congrArg.{1,1} Int Int a1 a2 f h : Eq Int (f a1) (f a2)`.
    fn congr_arg(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    /// `Int.add_assoc x y z : Eq Int ((x+y)+z) (x+(y+z))`.
    fn add_assoc(&self, x: Expr, y: Expr, z: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.add_assoc.clone(), x), y), z)
    }
}

/// Build `∀ a b c : Int, Eq Int (Int.add (Int.sub c b) (Int.sub b a)) (Int.sub c a)`.
fn build_type(c: &IntSubAddSubCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let lhs = c.add(c.sub(cc.clone(), bv.clone()), c.sub(bv.clone(), a.clone()));
    let rhs = c.sub(cc.clone(), a.clone());
    let concl = c.eq_int(lhs, rhs);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Helper: `Eq.symm (Int.add_assoc x y z) : Eq ((x+y)+z) → actually` we want
/// `Eq ((x+y)+z) (x+(y+z))` reversed. We instead build the chain forward from
/// `(c + nb) + (b + na)`.
fn build_value(c: &IntSubAddSubCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());

    let nb = c.neg(bv.clone());
    let na = c.neg(a.clone());
    // After delta on Int.sub the goal LHS is `(c + nb) + (b + na)`.
    let c_nb = c.add(cc.clone(), nb.clone()); // c + nb
    let b_na = c.add(bv.clone(), na.clone()); // b + na

    // e0 : (c + nb) + (b + na)
    let e0 = c.add(c_nb.clone(), b_na.clone());
    // e1 : ((c + nb) + b) + na
    let cnb_b = c.add(c_nb.clone(), bv.clone());
    let e1 = c.add(cnb_b.clone(), na.clone());
    // e2 : (c + (nb + b)) + na
    let nb_b = c.add(nb.clone(), bv.clone());
    let c_nbb = c.add(cc.clone(), nb_b.clone());
    let e2 = c.add(c_nbb.clone(), na.clone());
    // e3 : (c + 0) + na
    let c_zero = c.add(cc.clone(), c.int_zero.clone());
    let e3 = c.add(c_zero.clone(), na.clone());
    // e4 : c + na  (= goal RHS, definitionally Int.sub c a)
    let e4 = c.add(cc.clone(), na.clone());

    // Step 0→1: Eq.symm (Int.add_assoc (c+nb) b na) : e0 = e1.
    // add_assoc (c+nb) b na : ((c+nb)+b)+na = (c+nb)+(b+na), i.e. e1 = e0.
    // Build directly as an Eq e0 e1 via Eq.symm.
    let eq_symm = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    let assoc_0 = c.add_assoc(c_nb.clone(), bv.clone(), na.clone()); // Eq e1 e0
    let step01 = Expr::apps(
        eq_symm,
        [c.int_type.clone(), e1.clone(), e0.clone(), assoc_0],
    );

    // Step 1→2: congrArg (· + na) (Int.add_assoc c nb b : (c+nb)+b = c+(nb+b)).
    let assoc_1 = c.add_assoc(cc.clone(), nb.clone(), bv.clone()); // Eq cnb_b c_nbb
    let f_plus_na = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(t.clone(), na.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step12 = c.congr_arg(cnb_b.clone(), c_nbb.clone(), f_plus_na.clone(), assoc_1);

    // Step 2→3: congrArg (fun t => (c + t) + na) (Int.neg_add_self b : nb + b = 0).
    let neg_add_self_b = Expr::app(c.neg_add_self.clone(), bv.clone()); // Eq nb_b Int.zero
    let f_c_plus_t_plus_na = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(c.add(cc.clone(), t.clone()), na.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step23 = c.congr_arg(
        nb_b.clone(),
        c.int_zero.clone(),
        f_c_plus_t_plus_na.clone(),
        neg_add_self_b,
    );

    // Step 3→4: congrArg (· + na) (Int.add_zero c : c + 0 = c).
    let add_zero_c = Expr::app(c.add_zero.clone(), cc.clone()); // Eq c_zero c
    let step34 = c.congr_arg(c_zero.clone(), cc.clone(), f_plus_na, add_zero_c);

    // Compose: e0 = e1 = e2 = e3 = e4.
    let t01_2 = c.trans(e0.clone(), e1.clone(), e2.clone(), step01, step12);
    let t01_3 = c.trans(e0.clone(), e2.clone(), e3.clone(), t01_2, step23);
    let proof = c.trans(e0, e3, e4, t01_3, step34);

    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.sub_add_sub_cancel` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int.add`, `Int.neg`,
    ///           `Int.sub`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `Eq.symm`,
    ///           `congrArg`.
    /// ENSURES: On success, `Int.sub_add_sub_cancel` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_sub_add_sub_cancel_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.sub_add_sub_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        // Constructive arithmetic dependencies.
        self.register_int_add_assoc_proof()?;
        self.register_int_neg_add_self_proof()?;
        self.register_int_add_zero_proof()?;

        let c = IntSubAddSubCancelConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. A four-step `@Eq.trans.{1}`
        // chain rewriting `(c-b)+(b-a)` to `c-a` via the constructive
        // `Int.add_assoc`, `Int.neg_add_self`, `Int.add_zero` theorems and
        // `congrArg`/`Eq.symm`. `Int.sub` delta-reduces to `Int.add _ (Int.neg
        // _)`, so the chain endpoints are definitionally the stated goal. No
        // `sorry`, no self-reference, no domain-axiom dependency.
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
    fn test_int_sub_add_sub_cancel_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_add_sub_cancel_proof()
            .expect("first registration");
        env.register_int_sub_add_sub_cancel_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.sub_add_sub_cancel"))
            .expect("Int.sub_add_sub_cancel should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_sub_add_sub_cancel_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_add_sub_cancel_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.sub_add_sub_cancel"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.sub_add_sub_cancel must have empty axiom closure, got {:?}",
            domain_deps
        );
    }
}
