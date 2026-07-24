// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the left-cancellation identity
//! `Int.add_sub_add_left : ∀ a b c : Int,
//!    Eq Int (Int.sub (Int.add c b) (Int.add c a)) (Int.sub b a)`.
//!
//! This is `(c + b) - (c + a) = b - a`, a fresh constructive building block used
//! by `algebra_int_add_le_add_left_proof.rs` to transport a `NonNeg (b - a)`
//! witness to `NonNeg ((c+b) - (c+a))`.
//!
//! # Proof sketch
//!
//! `Int.sub x y` is the reducible Definition `Int.add x (Int.neg y)`, so the
//! goal is definitionally
//! `Eq Int (Int.add (Int.add c b) (Int.neg (Int.add c a))) (Int.add b (Int.neg a))`.
//!
//! Write `nc = neg c`, `na = neg a`. The chain (over `Int.add`):
//!
//! ```text
//! (c+b) + neg(c+a)
//!   = (c+b) + (nc + na)        -- congrArg ((c+b) + ·) (Int.neg_add c a)
//!   = ((c+b) + nc) + na        -- Eq.symm (Int.add_assoc (c+b) nc na)
//!   = b + na                   -- congrArg (· + na) keq
//! ```
//!
//! where `keq : (c+b) + nc = b` is itself a four-step chain
//!
//! ```text
//! (c+b) + nc
//!   = (b+c) + nc               -- congrArg (· + nc) (Int.add_comm c b)
//!   = b + (c + nc)             -- Int.add_assoc b c nc
//!   = b + Int.zero             -- congrArg (b + ·) (Int.add_neg_self c)
//!   = b                        -- Int.add_zero b
//! ```
//!
//! and `b + na` is definitionally `Int.sub b a`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.neg_add`, `Int.add_assoc`,
//! `Int.add_comm`, `Int.add_neg_self`, `Int.add_zero` theorems and
//! `Eq.trans` / `Eq.symm` / `congrArg`. Empty domain-axiom closure.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddSubAddLeftConsts {
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

impl IntAddSubAddLeftConsts {
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

/// Build `∀ a b c : Int, Eq Int (Int.sub (Int.add c b) (Int.add c a)) (Int.sub b a)`.
fn build_type(c: &IntAddSubAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let lhs = c.sub(c.add(cc.clone(), bv.clone()), c.add(cc.clone(), a.clone()));
    let rhs = c.sub(bv.clone(), a.clone());
    let concl = c.eq_int(lhs, rhs);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

fn build_value(c: &IntAddSubAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());

    let nc = c.neg(cc.clone());
    let na = c.neg(a.clone());
    let c_plus_b = c.add(cc.clone(), bv.clone());
    let c_plus_a = c.add(cc.clone(), a.clone());
    let neg_c_plus_a = c.neg(c_plus_a.clone());
    let nc_plus_na = c.add(nc.clone(), na.clone());

    // --- keq : (c+b) + nc = b -------------------------------------------------
    // k0 : (c+b) + nc
    let k0 = c.add(c_plus_b.clone(), nc.clone());
    // k1 : (b+c) + nc
    let b_plus_c = c.add(bv.clone(), cc.clone());
    let k1 = c.add(b_plus_c.clone(), nc.clone());
    // k2 : b + (c + nc)
    let c_plus_nc = c.add(cc.clone(), nc.clone());
    let k2 = c.add(bv.clone(), c_plus_nc.clone());
    // k3 : b + Int.zero
    let k3 = c.add(bv.clone(), c.int_zero.clone());
    // k4 : b
    let k4 = bv.clone();

    // k0→k1: congrArg (· + nc) (Int.add_comm c b : c+b = b+c).
    let comm_c_b = c.add_comm(cc.clone(), bv.clone());
    let f_plus_nc = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(t.clone(), nc.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let kstep01 = c.congr_arg(c_plus_b.clone(), b_plus_c.clone(), f_plus_nc, comm_c_b);
    // k1→k2: Int.add_assoc b c nc : (b+c)+nc = b+(c+nc).
    let kstep12 = c.add_assoc(bv.clone(), cc.clone(), nc.clone());
    // k2→k3: congrArg (b + ·) (Int.add_neg_self c : c + nc = Int.zero).
    let add_neg_self_c = Expr::app(c.add_neg_self.clone(), cc.clone());
    let f_b_plus = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(bv.clone(), t.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let kstep23 = c.congr_arg(
        c_plus_nc.clone(),
        c.int_zero.clone(),
        f_b_plus,
        add_neg_self_c,
    );
    // k3→k4: Int.add_zero b : b + Int.zero = b.
    let kstep34 = Expr::app(c.add_zero.clone(), bv.clone());
    // Compose keq : k0 = k4.
    let kt02 = c.trans(k0.clone(), k1.clone(), k2.clone(), kstep01, kstep12);
    let kt03 = c.trans(k0.clone(), k2.clone(), k3.clone(), kt02, kstep23);
    let keq = c.trans(k0.clone(), k3, k4.clone(), kt03, kstep34);

    // --- main chain -----------------------------------------------------------
    // e0 : (c+b) + neg(c+a)   (= goal LHS after Int.sub delta)
    let e0 = c.add(c_plus_b.clone(), neg_c_plus_a.clone());
    // e1 : (c+b) + (nc + na)
    let e1 = c.add(c_plus_b.clone(), nc_plus_na.clone());
    // e2 : ((c+b) + nc) + na
    let e2 = c.add(k0.clone(), na.clone());
    // e3 : b + na   (= goal RHS, definitionally Int.sub b a)
    let e3 = c.add(bv.clone(), na.clone());

    // e0→e1: congrArg ((c+b) + ·) (Int.neg_add c a : neg(c+a) = nc + na).
    let neg_add_c_a = c.neg_add(cc.clone(), a.clone());
    let f_cb_plus = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(c_plus_b.clone(), t.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step01 = c.congr_arg(
        neg_c_plus_a.clone(),
        nc_plus_na.clone(),
        f_cb_plus,
        neg_add_c_a,
    );
    // e1→e2: Eq.symm (Int.add_assoc (c+b) nc na : ((c+b)+nc)+na = (c+b)+(nc+na)).
    let assoc = c.add_assoc(c_plus_b.clone(), nc.clone(), na.clone()); // Eq e2 e1
    let step12 = c.symm(e2.clone(), e1.clone(), assoc);
    // e2→e3: congrArg (· + na) keq.
    let f_plus_na = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(t.clone(), na.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step23 = c.congr_arg(k0.clone(), k4, f_plus_na, keq);

    // Compose e0 = e1 = e2 = e3.
    let t02 = c.trans(e0.clone(), e1.clone(), e2.clone(), step01, step12);
    let proof = c.trans(e0, e2, e3, t02, step23);

    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.add_sub_add_left` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int.add`, `Int.neg`,
    ///           `Int.sub`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `Eq.symm`,
    ///           `congrArg`.
    /// ENSURES: On success, `Int.add_sub_add_left` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_add_sub_add_left_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_sub_add_left");
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

        let c = IntAddSubAddLeftConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `@Eq.trans.{1}` chains
        // rewriting `(c+b) - (c+a)` to `b - a` via the constructive `Int.neg_add`,
        // `Int.add_assoc`, `Int.add_comm`, `Int.add_neg_self`, `Int.add_zero`
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
    fn test_int_add_sub_add_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_sub_add_left_proof()
            .expect("first registration");
        env.register_int_add_sub_add_left_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_sub_add_left"))
            .expect("Int.add_sub_add_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_sub_add_left_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_sub_add_left_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_sub_add_left"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_sub_add_left must have empty axiom closure, got {:?}",
            domain_deps
        );
    }
}
