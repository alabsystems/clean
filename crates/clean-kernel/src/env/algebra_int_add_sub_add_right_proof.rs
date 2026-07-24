// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the right-cancellation identity
//! `Int.add_sub_add_right : ∀ a b c : Int,
//!    Eq Int (Int.sub (Int.add b c) (Int.add a c)) (Int.sub b a)`.
//!
//! This is `(b + c) - (a + c) = b - a`, a fresh constructive building block used
//! by `algebra_int_add_le_add_right_proof.rs` to transport a `NonNeg (b - a)`
//! witness to `NonNeg ((b+c) - (a+c))`.
//!
//! # Proof sketch
//!
//! `Int.sub x y` is the reducible Definition `Int.add x (Int.neg y)`, so the
//! goal is definitionally
//! `Eq Int (Int.add (Int.add b c) (Int.neg (Int.add a c))) (Int.add b (Int.neg a))`.
//!
//! Write `nc = neg c`, `na = neg a`. The chain (over `Int.add`):
//!
//! ```text
//! (b+c) + neg(a+c)
//!   = (b+c) + neg(c+a)         -- congrArg ((b+c) + ·) (congrArg neg (Int.add_comm a c))
//!   = (b+c) + (nc + na)        -- congrArg ((b+c) + ·) (Int.neg_add c a)
//!   = ((b+c) + nc) + na        -- Eq.symm (Int.add_assoc (b+c) nc na)
//!   = b + na                   -- congrArg (· + na) keq
//! ```
//!
//! where `keq : (b+c) + nc = b` is a three-step chain
//!
//! ```text
//! (b+c) + nc
//!   = b + (c + nc)             -- Int.add_assoc b c nc
//!   = b + Int.zero             -- congrArg (b + ·) (Int.add_neg_self c)
//!   = b                        -- Int.add_zero b
//! ```
//!
//! and `b + na` is definitionally `Int.sub b a`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_comm`, `Int.neg_add`,
//! `Int.add_assoc`, `Int.add_neg_self`, `Int.add_zero` theorems and
//! `Eq.trans` / `Eq.symm` / `congrArg`. Empty domain-axiom closure.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddSubAddRightConsts {
    int_type: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_sub: Expr,
    int_zero: Expr,
    neg_add: Expr,
    add_assoc: Expr,
    add_comm: Expr,
    add_neg_self: Expr,
    add_zero: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl IntAddSubAddRightConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            neg_add: Expr::const_(Name::from_string("Int.neg_add"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            add_neg_self: Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
            add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
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

    fn trans(&self, x: Expr, y: Expr, z: Expr, hxy: Expr, hyz: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, hxy, hyz],
        )
    }

    fn symm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), x, y, h])
    }

    fn congr_arg(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    fn add_assoc(&self, x: Expr, y: Expr, z: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.add_assoc.clone(), x), y), z)
    }

    fn add_comm(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.add_comm.clone(), x), y)
    }

    fn neg_add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.neg_add.clone(), x), y)
    }
}

/// Build `∀ a b c : Int, Eq Int (Int.sub (Int.add b c) (Int.add a c)) (Int.sub b a)`.
fn build_type(c: &IntAddSubAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let lhs = c.sub(c.add(bv.clone(), cc.clone()), c.add(a.clone(), cc.clone()));
    let rhs = c.sub(bv.clone(), a.clone());
    let concl = c.eq_int(lhs, rhs);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

fn build_value(c: &IntAddSubAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());

    let nc = c.neg(cc.clone());
    let na = c.neg(a.clone());
    let b_plus_c = c.add(bv.clone(), cc.clone());
    let a_plus_c = c.add(a.clone(), cc.clone());
    let c_plus_a = c.add(cc.clone(), a.clone());
    let neg_a_plus_c = c.neg(a_plus_c.clone());
    let neg_c_plus_a = c.neg(c_plus_a.clone());
    let nc_plus_na = c.add(nc.clone(), na.clone());

    // --- keq : (b+c) + nc = b -------------------------------------------------
    // k0 : (b+c) + nc
    let k0 = c.add(b_plus_c.clone(), nc.clone());
    // k1 : b + (c + nc)
    let c_plus_nc = c.add(cc.clone(), nc.clone());
    let k1 = c.add(bv.clone(), c_plus_nc.clone());
    // k2 : b + Int.zero
    let k2 = c.add(bv.clone(), c.int_zero.clone());
    // k3 : b
    let k3 = bv.clone();

    // k0→k1: Int.add_assoc b c nc : (b+c)+nc = b+(c+nc).
    let kstep01 = c.add_assoc(bv.clone(), cc.clone(), nc.clone());
    // k1→k2: congrArg (b + ·) (Int.add_neg_self c : c + nc = Int.zero).
    let add_neg_self_c = Expr::app(c.add_neg_self.clone(), cc.clone());
    let f_b_plus = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(bv.clone(), t.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let kstep12 = c.congr_arg(
        c_plus_nc.clone(),
        c.int_zero.clone(),
        f_b_plus,
        add_neg_self_c,
    );
    // k2→k3: Int.add_zero b : b + Int.zero = b.
    let kstep23 = Expr::app(c.add_zero.clone(), bv.clone());
    // Compose keq : k0 = k3.
    let kt02 = c.trans(k0.clone(), k1.clone(), k2.clone(), kstep01, kstep12);
    let keq = c.trans(k0.clone(), k2, k3.clone(), kt02, kstep23);

    // --- main chain -----------------------------------------------------------
    // e0 : (b+c) + neg(a+c)   (= goal LHS after Int.sub delta)
    let e0 = c.add(b_plus_c.clone(), neg_a_plus_c.clone());
    // e1 : (b+c) + neg(c+a)
    let e1 = c.add(b_plus_c.clone(), neg_c_plus_a.clone());
    // e2 : (b+c) + (nc + na)
    let e2 = c.add(b_plus_c.clone(), nc_plus_na.clone());
    // e3 : ((b+c) + nc) + na
    let e3 = c.add(k0.clone(), na.clone());
    // e4 : b + na   (= goal RHS, definitionally Int.sub b a)
    let e4 = c.add(bv.clone(), na.clone());

    // e0→e1: congrArg ((b+c) + ·) (congrArg Int.neg (Int.add_comm a c)).
    let comm_a_c = c.add_comm(a.clone(), cc.clone()); // a+c = c+a
    let neg_comm = c.congr_arg(
        a_plus_c.clone(),
        c_plus_a.clone(),
        c.int_neg.clone(),
        comm_a_c,
    );
    let f_bc_plus = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(b_plus_c.clone(), t.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step01 = c.congr_arg(
        neg_a_plus_c.clone(),
        neg_c_plus_a.clone(),
        f_bc_plus.clone(),
        neg_comm,
    );
    // e1→e2: congrArg ((b+c) + ·) (Int.neg_add c a : neg(c+a) = nc + na).
    let neg_add_c_a = c.neg_add(cc.clone(), a.clone());
    let step12 = c.congr_arg(
        neg_c_plus_a.clone(),
        nc_plus_na.clone(),
        f_bc_plus,
        neg_add_c_a,
    );
    // e2→e3: Eq.symm (Int.add_assoc (b+c) nc na : ((b+c)+nc)+na = (b+c)+(nc+na)).
    let assoc = c.add_assoc(b_plus_c.clone(), nc.clone(), na.clone()); // Eq e3 e2
    let step23 = c.symm(e3.clone(), e2.clone(), assoc);
    // e3→e4: congrArg (· + na) keq.
    let f_plus_na = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(t.clone(), na.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step34 = c.congr_arg(k0.clone(), k3, f_plus_na, keq);

    // Compose e0 = e1 = e2 = e3 = e4.
    let t02 = c.trans(e0.clone(), e1.clone(), e2.clone(), step01, step12);
    let t03 = c.trans(e0.clone(), e2.clone(), e3.clone(), t02, step23);
    let proof = c.trans(e0, e3, e4, t03, step34);

    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.add_sub_add_right` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int.add`, `Int.neg`,
    ///           `Int.sub`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `Eq.symm`,
    ///           `congrArg`.
    /// ENSURES: On success, `Int.add_sub_add_right` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_add_sub_add_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_sub_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_neg_add_proof()?;
        self.register_int_add_assoc_proof()?;
        self.register_int_add_comm_proof()?;
        self.register_int_add_neg_self_proof()?;
        self.register_int_add_zero_proof()?;

        let c = IntAddSubAddRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `@Eq.trans.{1}` chains
        // rewriting `(b+c) - (a+c)` to `b - a` via the constructive `Int.add_comm`,
        // `Int.neg_add`, `Int.add_assoc`, `Int.add_neg_self`, `Int.add_zero`
        // theorems plus `congrArg`/`Eq.symm` (the inner `keq` chain cancels the
        // common `c`). `Int.sub` delta-reduces, so chain endpoints are
        // definitionally the stated goal. No `sorry`, no self-reference, no
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
    fn test_int_add_sub_add_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_sub_add_right_proof()
            .expect("first registration");
        env.register_int_add_sub_add_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_sub_add_right"))
            .expect("Int.add_sub_add_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_sub_add_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_sub_add_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_sub_add_right"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_sub_add_right must have empty axiom closure, got {:?}",
            domain_deps
        );
    }
}
