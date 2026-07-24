// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_negSucc_negSucc_negSucc :
//!    ∀ m n k : Nat,
//!      Eq Int
//!        (Int.add (Int.add (Int.negSucc m) (Int.negSucc n)) (Int.negSucc k))
//!        (Int.add (Int.negSucc m) (Int.add (Int.negSucc n) (Int.negSucc k)))`.
//!
//! This closes the all-negative branch of the remaining `Int.add_assoc` case
//! split. Both sides reduce to `Int.negSucc` over Nat indices; the proof
//! lifts checked `Nat.succ_add`, `Nat.add_assoc`, and `Nat.add_succ`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocNegSuccNegSuccNegSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_neg_succ: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    nat_succ_add: Expr,
    nat_add_assoc: Expr,
    nat_add_succ: Expr,
}

impl IntAddAssocNegSuccNegSuccNegSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            nat_add_assoc: Expr::const_(Name::from_string("Nat.add_assoc"), vec![]),
            nat_add_succ: Expr::const_(Name::from_string("Nat.add_succ"), vec![]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nat_add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), lhs), rhs)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.add_int(
            self.add_int(self.neg_succ(m), self.neg_succ(n)),
            self.neg_succ(k),
        )
    }

    fn rhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.add_int(
            self.neg_succ(m),
            self.add_int(self.neg_succ(n), self.neg_succ(k)),
        )
    }

    fn lhs_index(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.succ(self.nat_add(self.succ(self.nat_add(m, n)), k))
    }

    fn mid_left_index(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.succ(self.succ(self.nat_add(self.nat_add(m, n), k)))
    }

    fn mid_right_index(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.succ(self.succ(self.nat_add(m, self.nat_add(n, k))))
    }

    fn rhs_index(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.succ(self.nat_add(m, self.succ(self.nat_add(n, k))))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_negsucc_negsucc_negsucc_type(
    c: &IntAddAssocNegSuccNegSuccNegSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(m.clone(), n.clone(), k.clone()), c.rhs(m, n, k));
    let ty_raw = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_succ_fn(c: &IntAddAssocNegSuccNegSuccNegSuccConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), c.succ(x));
    fb.finish_child(lam)
}

fn build_succ_succ_fn(c: &IntAddAssocNegSuccNegSuccNegSuccConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let body = c.succ(c.succ(x));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
    fb.finish_child(lam)
}

fn build_neg_succ_fn(c: &IntAddAssocNegSuccNegSuccNegSuccConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), c.neg_succ(x));
    fb.finish_child(lam)
}

fn build_index_proof(
    c: &IntAddAssocNegSuccNegSuccNegSuccConsts,
    parent: &EnvDeclBuilder,
    m: Expr,
    n: Expr,
    k: Expr,
) -> Expr {
    let lhs_index = c.lhs_index(m.clone(), n.clone(), k.clone());
    let mid_left_index = c.mid_left_index(m.clone(), n.clone(), k.clone());
    let mid_right_index = c.mid_right_index(m.clone(), n.clone(), k.clone());
    let rhs_index = c.rhs_index(m.clone(), n.clone(), k.clone());

    let h_succ_add = Expr::app(
        Expr::app(c.nat_succ_add.clone(), c.nat_add(m.clone(), n.clone())),
        k.clone(),
    );
    let succ_fn = build_succ_fn(c, parent);
    let h_left = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            c.nat_add(c.succ(c.nat_add(m.clone(), n.clone())), k.clone()),
            c.succ(c.nat_add(c.nat_add(m.clone(), n.clone()), k.clone())),
            succ_fn,
            h_succ_add,
        ],
    );

    let h_assoc = Expr::app(
        Expr::app(Expr::app(c.nat_add_assoc.clone(), m.clone()), n.clone()),
        k.clone(),
    );
    let succ_succ_fn = build_succ_succ_fn(c, parent);
    let h_mid = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            c.nat_add(c.nat_add(m.clone(), n.clone()), k.clone()),
            c.nat_add(m.clone(), c.nat_add(n.clone(), k.clone())),
            succ_succ_fn,
            h_assoc,
        ],
    );

    let h_add_succ_forward = Expr::app(
        Expr::app(c.nat_add_succ.clone(), m.clone()),
        c.nat_add(n.clone(), k.clone()),
    );
    let h_add_succ = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            c.nat_add(m.clone(), c.succ(c.nat_add(n.clone(), k.clone()))),
            c.succ(c.nat_add(m.clone(), c.nat_add(n.clone(), k.clone()))),
            h_add_succ_forward,
        ],
    );
    let h_right = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            c.succ(c.nat_add(m.clone(), c.nat_add(n.clone(), k.clone()))),
            c.nat_add(m.clone(), c.succ(c.nat_add(n.clone(), k.clone()))),
            build_succ_fn(c, parent),
            h_add_succ,
        ],
    );

    let h_first = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            lhs_index,
            mid_left_index,
            mid_right_index.clone(),
            h_left,
            h_mid,
        ],
    );
    Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            c.lhs_index(m.clone(), n.clone(), k.clone()),
            mid_right_index,
            rhs_index,
            h_first,
            h_right,
        ],
    )
}

fn build_int_add_assoc_negsucc_negsucc_negsucc_value(
    c: &IntAddAssocNegSuccNegSuccNegSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());

    let h_index = build_index_proof(c, &b, m.clone(), n.clone(), k.clone());
    let proof = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.int_type.clone(),
            c.lhs_index(m.clone(), n.clone(), k.clone()),
            c.rhs_index(m.clone(), n.clone(), k.clone()),
            build_neg_succ_fn(c, &b),
            h_index,
        ],
    );

    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_negSucc_negSucc_negSucc` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_negsucc_negsucc_negsucc_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.add_assoc_negSucc_negSucc_negSucc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_succ_add_proof()?;
        self.register_nat_add_assoc_proof()?;
        self.register_nat_add_succ_proof()?;

        let c = IntAddAssocNegSuccNegSuccNegSuccConsts::new();
        let type_ = build_int_add_assoc_negsucc_negsucc_negsucc_type(&c);
        let value = build_int_add_assoc_negsucc_negsucc_negsucc_value(&c);

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
    fn test_int_add_assoc_negsucc_negsucc_negsucc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_negsucc_negsucc_negsucc_proof()
            .expect("first registration");
        env.register_int_add_assoc_negsucc_negsucc_negsucc_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_assoc_negSucc_negSucc_negSucc"))
            .expect("Int.add_assoc_negSucc_negSucc_negSucc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_negsucc_negsucc_negsucc_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_assoc_negSucc_negSucc_negSucc"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_negSucc_negSucc_negSucc must be Constructive, got {:?}",
            quality
        );
    }
}
