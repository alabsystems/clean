// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_zero_left :
//!    ∀ b c : Int,
//!      Eq Int
//!        (Int.add (Int.add Int.zero b) c)
//!        (Int.add Int.zero (Int.add b c))`.
//!
//! This closes the `Int.ofNat 0` / zero-left branch of the remaining
//! `Int.add_assoc` case split by composing checked `Int.zero_add` with
//! congruence over right addition.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocZeroLeftConsts {
    int_type: Expr,
    int_zero: Expr,
    int_add: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    int_zero_add: Expr,
}

impl IntAddAssocZeroLeftConsts {
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
            int_zero_add: Expr::const_(Name::from_string("Int.zero_add"), vec![]),
        }
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, b: Expr, c: Expr) -> Expr {
        self.add_int(self.add_int(self.int_zero.clone(), b), c)
    }

    fn mid(&self, b: Expr, c: Expr) -> Expr {
        self.add_int(b, c)
    }

    fn rhs(&self, b: Expr, c: Expr) -> Expr {
        self.add_int(self.int_zero.clone(), self.add_int(b, c))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_zero_left_type(c: &IntAddAssocZeroLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.lhs(bv.clone(), cv.clone()), c.rhs(bv, cv));
    let ty_raw = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_add_right_fn(c: &IntAddAssocZeroLeftConsts, parent: &EnvDeclBuilder, right: Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(x, right);
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_assoc_zero_left_value(c: &IntAddAssocZeroLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());

    let zero_add_b = Expr::app(c.int_zero_add.clone(), bv.clone());
    let add_right = build_add_right_fn(c, &b, cv.clone());
    let h_left = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            c.add_int(c.int_zero.clone(), bv.clone()),
            bv.clone(),
            add_right,
            zero_add_b,
        ],
    );

    let mid = c.mid(bv.clone(), cv.clone());
    let rhs = c.rhs(bv.clone(), cv.clone());
    let h_right_forward = Expr::app(c.int_zero_add.clone(), mid.clone());
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
        [
            c.int_type.clone(),
            c.lhs(bv.clone(), cv.clone()),
            mid,
            rhs,
            h_left,
            h_right,
        ],
    );

    let val_raw = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val_raw = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_zero_left` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_zero_left_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_assoc_zero_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_zero_add_proof()?;

        let c = IntAddAssocZeroLeftConsts::new();
        let type_ = build_int_add_assoc_zero_left_type(&c);
        let value = build_int_add_assoc_zero_left_value(&c);

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
    fn test_int_add_assoc_zero_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_zero_left_proof()
            .expect("first registration");
        env.register_int_add_assoc_zero_left_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_assoc_zero_left"))
            .expect("Int.add_assoc_zero_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_zero_left_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_assoc_zero_left"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_zero_left must be Constructive, got {:?}",
            quality
        );
    }
}
