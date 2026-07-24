// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_zero_right :
//!    ∀ a b : Int,
//!      Eq Int
//!        (Int.add (Int.add a b) Int.zero)
//!        (Int.add a (Int.add b Int.zero))`.
//!
//! This closes the right-zero branch of the remaining `Int.add_assoc` case
//! split by composing checked `Int.add_zero` with congruence over left
//! addition.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocZeroRightConsts {
    int_type: Expr,
    int_zero: Expr,
    int_add: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    int_add_zero: Expr,
}

impl IntAddAssocZeroRightConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            int_add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
        }
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, a: Expr, b: Expr) -> Expr {
        self.add_int(self.add_int(a, b), self.int_zero.clone())
    }

    fn mid(&self, a: Expr, b: Expr) -> Expr {
        self.add_int(a, b)
    }

    fn rhs(&self, a: Expr, b: Expr) -> Expr {
        self.add_int(a, self.add_int(b, self.int_zero.clone()))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_zero_right_type(c: &IntAddAssocZeroRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.lhs(a.clone(), bv.clone()), c.rhs(a, bv));
    let ty_raw = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_add_left_fn(c: &IntAddAssocZeroRightConsts, parent: &EnvDeclBuilder, left: Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(left, x);
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_assoc_zero_right_value(c: &IntAddAssocZeroRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());

    let lhs = c.lhs(a.clone(), bv.clone());
    let mid = c.mid(a.clone(), bv.clone());
    let rhs = c.rhs(a.clone(), bv.clone());

    let h_left = Expr::app(c.int_add_zero.clone(), mid.clone());
    let h_inner = Expr::app(c.int_add_zero.clone(), bv.clone());
    let add_left = build_add_left_fn(c, &b, a.clone());
    let h_right_forward = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            c.add_int(bv.clone(), c.int_zero.clone()),
            bv,
            add_left,
            h_inner,
        ],
    );
    let h_right = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            rhs.clone(),
            mid.clone(),
            h_right_forward,
        ],
    );
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.int_type.clone(), lhs, mid, rhs, h_left, h_right],
    );

    let val_raw = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_zero_right` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_zero_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_assoc_zero_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_add_zero_proof()?;

        let c = IntAddAssocZeroRightConsts::new();
        let type_ = build_int_add_assoc_zero_right_type(&c);
        let value = build_int_add_assoc_zero_right_value(&c);

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
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_add_assoc_zero_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_zero_right_proof()
            .expect("first registration");
        env.register_int_add_assoc_zero_right_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_assoc_zero_right"))
            .expect("Int.add_assoc_zero_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_zero_right_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_assoc_zero_right"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_zero_right must be Constructive, got {:?}",
            quality
        );
    }
}
