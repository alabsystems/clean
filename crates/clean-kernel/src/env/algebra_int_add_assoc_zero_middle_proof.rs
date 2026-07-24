// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_zero_middle :
//!    ∀ a c : Int,
//!      Eq Int
//!        (Int.add (Int.add a Int.zero) c)
//!        (Int.add a (Int.add Int.zero c))`.
//!
//! This closes the middle-zero branch of the remaining `Int.add_assoc` case
//! split by composing checked `Int.add_zero` with checked `Int.zero_add`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocZeroMiddleConsts {
    int_type: Expr,
    int_zero: Expr,
    int_add: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    int_add_zero: Expr,
    int_zero_add: Expr,
}

impl IntAddAssocZeroMiddleConsts {
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
            int_zero_add: Expr::const_(Name::from_string("Int.zero_add"), vec![]),
        }
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, a: Expr, c: Expr) -> Expr {
        self.add_int(self.add_int(a, self.int_zero.clone()), c)
    }

    fn mid(&self, a: Expr, c: Expr) -> Expr {
        self.add_int(a, c)
    }

    fn rhs(&self, a: Expr, c: Expr) -> Expr {
        self.add_int(a, self.add_int(self.int_zero.clone(), c))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_zero_middle_type(c: &IntAddAssocZeroMiddleConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.lhs(a.clone(), cv.clone()), c.rhs(a, cv));
    let ty_raw = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_add_right_fn(
    c: &IntAddAssocZeroMiddleConsts,
    parent: &EnvDeclBuilder,
    right: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(x, right);
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_add_left_fn(c: &IntAddAssocZeroMiddleConsts, parent: &EnvDeclBuilder, left: Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(left, x);
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_assoc_zero_middle_value(c: &IntAddAssocZeroMiddleConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());

    let lhs = c.lhs(a.clone(), cv.clone());
    let mid = c.mid(a.clone(), cv.clone());
    let rhs = c.rhs(a.clone(), cv.clone());

    let h_add_zero = Expr::app(c.int_add_zero.clone(), a.clone());
    let add_right = build_add_right_fn(c, &b, cv.clone());
    let h_left = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            c.add_int(a.clone(), c.int_zero.clone()),
            a.clone(),
            add_right,
            h_add_zero,
        ],
    );

    let h_zero_add = Expr::app(c.int_zero_add.clone(), cv.clone());
    let add_left = build_add_left_fn(c, &b, a);
    let h_right_forward = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            c.add_int(c.int_zero.clone(), cv.clone()),
            cv,
            add_left,
            h_zero_add,
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

    let val_raw = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_zero_middle` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_zero_middle_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_assoc_zero_middle");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_add_zero_proof()?;
        self.register_int_zero_add_proof()?;

        let c = IntAddAssocZeroMiddleConsts::new();
        let type_ = build_int_add_assoc_zero_middle_type(&c);
        let value = build_int_add_assoc_zero_middle_value(&c);

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
    fn test_int_add_assoc_zero_middle_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_zero_middle_proof()
            .expect("first registration");
        env.register_int_add_assoc_zero_middle_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_assoc_zero_middle"))
            .expect("Int.add_assoc_zero_middle should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_zero_middle_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_assoc_zero_middle"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_zero_middle must be Constructive, got {:?}",
            quality
        );
    }
}
