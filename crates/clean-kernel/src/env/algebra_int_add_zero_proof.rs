// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_zero : ∀ a : Int, Eq Int (Int.add a Int.zero) a`.
//!
//! This closes the zero transport case needed by the remaining
//! `Int.add_assoc` work. The proof recurses on `a : Int`:
//! - `ofNat m`: map `Nat.add_zero m` through `Int.ofNat` with `congrArg`.
//! - `negSucc m`: reuse `Int.subNatNat_zero_succ m`, because
//!   `Int.add (Int.negSucc m) Int.zero` reduces to
//!   `Int.subNatNat Nat.zero (Nat.succ m)`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddZeroConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_zero: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    int_rec: Expr,
    nat_add: Expr,
    eq_const: Expr,
    congr_arg: Expr,
    nat_add_zero: Expr,
    int_sub_nat_nat_zero_succ: Expr,
}

impl IntAddZeroConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_zero: Expr::const_(Name::from_string("Nat.add_zero"), vec![]),
            int_sub_nat_nat_zero_succ: Expr::const_(
                Name::from_string("Int.subNatNat_zero_succ"),
                vec![],
            ),
        }
    }

    fn add_zero_lhs(&self, a: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), a), self.int_zero.clone())
    }

    #[cfg(test)]
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn nat_add_zero_lhs(&self, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), n), self.nat_zero.clone())
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_zero_type(c: &IntAddZeroConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.add_zero_lhs(a.clone()), a);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

fn build_int_add_zero_value(c: &IntAddZeroConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.eq_int(c.add_zero_lhs(x.clone()), x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    let of_nat_case = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = ob.fresh_local(c.nat_type.clone());
        let proof = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                c.nat_add_zero_lhs(m.clone()),
                m.clone(),
                c.int_of_nat.clone(),
                Expr::app(c.nat_add_zero.clone(), m),
            ],
        );
        let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), proof);
        ob.finish_child(lam)
    };

    let neg_succ_case = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = nb.fresh_local(c.nat_type.clone());
        let _lhs_shape = Expr::app(
            Expr::app(c.int_sub_nat_nat.clone(), c.nat_zero.clone()),
            Expr::app(c.nat_succ.clone(), m.clone()),
        );
        let _rhs_shape = c.neg_succ(m.clone());
        let proof = Expr::app(c.int_sub_nat_nat_zero_succ.clone(), m);
        let lam = nb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), proof);
        nb.finish_child(lam)
    };

    let rec_app = Expr::apps(c.int_rec.clone(), [motive, of_nat_case, neg_succ_case, a]);
    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_zero` as a kernel-checked theorem.
    pub(crate) fn register_int_add_zero_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_zero_proof()?;
        self.register_int_sub_nat_nat_zero_succ_proof()?;

        let c = IntAddZeroConsts::new();
        let type_ = build_int_add_zero_type(&c);
        let value = build_int_add_zero_value(&c);

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
    fn test_int_add_zero_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_zero_proof()
            .expect("first registration");
        env.register_int_add_zero_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_zero"))
            .expect("Int.add_zero should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_zero_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_zero"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_zero must be Constructive, got {:?}",
            quality
        );
    }
}
