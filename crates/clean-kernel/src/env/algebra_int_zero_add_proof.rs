// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.zero_add : ∀ a : Int, Eq Int (Int.add Int.zero a) a`.
//!
//! This closes the zero-left addition blocker for `Int.add_assoc` by
//! composing checked `Int.add_comm` with checked `Int.add_zero`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntZeroAddConsts {
    int_type: Expr,
    int_zero: Expr,
    int_add: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    int_add_comm: Expr,
    int_add_zero: Expr,
}

impl IntZeroAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
            int_add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            int_add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
        }
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, a: Expr) -> Expr {
        self.add_int(self.int_zero.clone(), a)
    }

    fn mid(&self, a: Expr) -> Expr {
        self.add_int(a, self.int_zero.clone())
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_zero_add_type(c: &IntZeroAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.lhs(a.clone()), a);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

fn build_int_zero_add_value(c: &IntZeroAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());

    let lhs = c.lhs(a.clone());
    let mid = c.mid(a.clone());
    let h_comm = Expr::app(
        Expr::app(c.int_add_comm.clone(), c.int_zero.clone()),
        a.clone(),
    );
    let h_zero = Expr::app(c.int_add_zero.clone(), a.clone());
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.int_type.clone(), lhs, mid, a, h_comm, h_zero],
    );

    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), proof);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.zero_add` as a kernel-checked theorem.
    pub(crate) fn register_int_zero_add_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.zero_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_add_zero_proof()?;
        self.register_int_add_comm_proof()?;

        let c = IntZeroAddConsts::new();
        let type_ = build_int_zero_add_type(&c);
        let value = build_int_zero_add_value(&c);

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
    fn test_int_zero_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_zero_add_proof()
            .expect("first registration");
        env.register_int_zero_add_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.zero_add"))
            .expect("Int.zero_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_zero_add_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.zero_add"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.zero_add must be Constructive, got {:?}",
            quality
        );
    }
}
