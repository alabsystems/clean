// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_negSucc_ofNat_succ_negSucc :
//!    ∀ k m n : Nat,
//!      Eq Int
//!        (Int.add
//!          (Int.add (Int.negSucc k) (Int.ofNat (Nat.succ m)))
//!          (Int.negSucc n))
//!        (Int.add
//!          (Int.negSucc k)
//!          (Int.add (Int.ofNat (Nat.succ m)) (Int.negSucc n)))`.
//!
//! This closes one negative outer / mixed inner-negative branch of the
//! remaining `Int.add_assoc` case split. The proof composes checked
//! left/right `Int.subNatNat` transports and rewrites the Nat index
//! `k + succ n` to `n + succ k` with checked Nat arithmetic.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocNegSuccOfNatSuccNegSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    nat_add_succ: Expr,
    nat_add_comm: Expr,
    inner_left_transport: Expr,
    inner_right_transport: Expr,
    right_transport: Expr,
    left_transport: Expr,
}

impl IntAddAssocNegSuccOfNatSuccNegSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_succ: Expr::const_(Name::from_string("Nat.add_succ"), vec![]),
            nat_add_comm: Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
            inner_left_transport: Expr::const_(
                Name::from_string("Int.add_negSucc_ofNat_succ"),
                vec![],
            ),
            inner_right_transport: Expr::const_(
                Name::from_string("Int.add_ofNat_succ_negSucc"),
                vec![],
            ),
            right_transport: Expr::const_(Name::from_string("Int.add_subNatNat_negSucc"), vec![]),
            left_transport: Expr::const_(Name::from_string("Int.add_negSucc_subNatNat"), vec![]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nat_add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), lhs), rhs)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn inner_lhs(&self, k: Expr, m: Expr) -> Expr {
        self.add_int(self.neg_succ(k), self.of_nat(self.succ(m)))
    }

    fn inner_rhs(&self, m: Expr, n: Expr) -> Expr {
        self.add_int(self.of_nat(self.succ(m)), self.neg_succ(n))
    }

    fn lhs(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.inner_lhs(k, m), self.neg_succ(n))
    }

    fn lhs_mid(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.sub_nat_nat(m, k), self.neg_succ(n))
    }

    fn lhs_normal(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.sub_nat_nat(m, self.nat_add(k, self.succ(n)))
    }

    fn rhs(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.neg_succ(k), self.inner_rhs(m, n))
    }

    fn rhs_mid(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.neg_succ(k), self.sub_nat_nat(m, n))
    }

    fn rhs_normal(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.sub_nat_nat(m, self.nat_add(n, self.succ(k)))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_negsucc_ofnat_succ_negsucc_type(
    c: &IntAddAssocNegSuccOfNatSuccNegSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(k.clone(), m.clone(), n.clone()), c.rhs(k, m, n));
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_add_right_neg_fn(
    c: &IntAddAssocNegSuccOfNatSuccNegSuccConsts,
    parent: &EnvDeclBuilder,
    n: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(x, c.neg_succ(n));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_add_left_neg_fn(
    c: &IntAddAssocNegSuccOfNatSuccNegSuccConsts,
    parent: &EnvDeclBuilder,
    k: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(c.neg_succ(k), x);
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_sub_right_fn(
    c: &IntAddAssocNegSuccOfNatSuccNegSuccConsts,
    parent: &EnvDeclBuilder,
    m: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let body = c.sub_nat_nat(m, x);
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
    fb.finish_child(lam)
}

fn build_index_proof(c: &IntAddAssocNegSuccOfNatSuccNegSuccConsts, k: Expr, n: Expr) -> Expr {
    let add_k_succ_n = c.nat_add(k.clone(), c.succ(n.clone()));
    let succ_add_k_n = c.succ(c.nat_add(k.clone(), n.clone()));
    let succ_add_n_k = c.succ(c.nat_add(n.clone(), k.clone()));
    let add_n_succ_k = c.nat_add(n.clone(), c.succ(k.clone()));

    let h_add_succ_k_n = Expr::app(Expr::app(c.nat_add_succ.clone(), k.clone()), n.clone());
    let h_comm = Expr::app(Expr::app(c.nat_add_comm.clone(), k.clone()), n.clone());
    let h_comm_succ = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            c.nat_add(k.clone(), n.clone()),
            c.nat_add(n.clone(), k.clone()),
            c.nat_succ.clone(),
            h_comm,
        ],
    );
    let h_add_succ_n_k_forward = Expr::app(Expr::app(c.nat_add_succ.clone(), n.clone()), k.clone());
    let h_add_succ_n_k = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            add_n_succ_k.clone(),
            succ_add_n_k.clone(),
            h_add_succ_n_k_forward,
        ],
    );
    let h_first = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            add_k_succ_n.clone(),
            succ_add_k_n,
            succ_add_n_k,
            h_add_succ_k_n,
            h_comm_succ,
        ],
    );
    Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            add_k_succ_n,
            c.succ(c.nat_add(n, k)),
            add_n_succ_k,
            h_first,
            h_add_succ_n_k,
        ],
    )
}

fn build_int_add_assoc_negsucc_ofnat_succ_negsucc_value(
    c: &IntAddAssocNegSuccOfNatSuccNegSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    let lhs = c.lhs(k.clone(), m.clone(), n.clone());
    let lhs_mid = c.lhs_mid(k.clone(), m.clone(), n.clone());
    let lhs_normal = c.lhs_normal(k.clone(), m.clone(), n.clone());
    let rhs_normal = c.rhs_normal(k.clone(), m.clone(), n.clone());
    let rhs_mid = c.rhs_mid(k.clone(), m.clone(), n.clone());
    let rhs = c.rhs(k.clone(), m.clone(), n.clone());

    let h_inner_left = Expr::app(
        Expr::app(c.inner_left_transport.clone(), m.clone()),
        k.clone(),
    );
    let add_right_neg = build_add_right_neg_fn(c, &b, n.clone());
    let h_lhs_inner = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            c.inner_lhs(k.clone(), m.clone()),
            c.sub_nat_nat(m.clone(), k.clone()),
            add_right_neg,
            h_inner_left,
        ],
    );
    let h_lhs_transport = Expr::app(
        Expr::app(Expr::app(c.right_transport.clone(), m.clone()), k.clone()),
        n.clone(),
    );
    let h_lhs = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            lhs.clone(),
            lhs_mid,
            lhs_normal.clone(),
            h_lhs_inner,
            h_lhs_transport,
        ],
    );

    let h_index_nat = build_index_proof(c, k.clone(), n.clone());
    let sub_right_fn = build_sub_right_fn(c, &b, m.clone());
    let h_index = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.int_type.clone(),
            c.nat_add(k.clone(), c.succ(n.clone())),
            c.nat_add(n.clone(), c.succ(k.clone())),
            sub_right_fn,
            h_index_nat,
        ],
    );

    let h_rhs_transport_forward = Expr::app(
        Expr::app(Expr::app(c.left_transport.clone(), k.clone()), m.clone()),
        n.clone(),
    );
    let h_rhs_transport = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            rhs_mid.clone(),
            rhs_normal.clone(),
            h_rhs_transport_forward,
        ],
    );
    let h_inner_right = Expr::app(
        Expr::app(c.inner_right_transport.clone(), m.clone()),
        n.clone(),
    );
    let add_left_neg = build_add_left_neg_fn(c, &b, k.clone());
    let h_rhs_inner_forward = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            c.inner_rhs(m.clone(), n.clone()),
            c.sub_nat_nat(m.clone(), n.clone()),
            add_left_neg,
            h_inner_right,
        ],
    );
    let h_rhs_inner = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            rhs.clone(),
            rhs_mid.clone(),
            h_rhs_inner_forward,
        ],
    );
    let h_rhs = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            rhs_normal.clone(),
            rhs_mid,
            rhs,
            h_rhs_transport,
            h_rhs_inner,
        ],
    );
    let h_to_rhs_normal = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            lhs,
            lhs_normal,
            rhs_normal.clone(),
            h_lhs,
            h_index,
        ],
    );
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            c.lhs(k.clone(), m.clone(), n.clone()),
            rhs_normal,
            c.rhs(k.clone(), m.clone(), n.clone()),
            h_to_rhs_normal,
            h_rhs,
        ],
    );

    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_negSucc_ofNat_succ_negSucc` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_negsucc_ofnat_succ_negsucc_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.add_assoc_negSucc_ofNat_succ_negSucc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_succ_proof()?;
        self.register_nat_add_comm_proof()?;
        self.register_int_add_negsucc_ofnat_succ_proof()?;
        self.register_int_add_ofnat_succ_negsucc_proof()?;
        self.register_int_add_sub_nat_nat_negsucc_proof()?;
        self.register_int_add_negsucc_sub_nat_nat_proof()?;

        let c = IntAddAssocNegSuccOfNatSuccNegSuccConsts::new();
        let type_ = build_int_add_assoc_negsucc_ofnat_succ_negsucc_type(&c);
        let value = build_int_add_assoc_negsucc_ofnat_succ_negsucc_value(&c);

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
    fn test_int_add_assoc_negsucc_ofnat_succ_negsucc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_negsucc_ofnat_succ_negsucc_proof()
            .expect("first registration");
        env.register_int_add_assoc_negsucc_ofnat_succ_negsucc_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string(
                "Int.add_assoc_negSucc_ofNat_succ_negSucc",
            ))
            .expect("Int.add_assoc_negSucc_ofNat_succ_negSucc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_negsucc_ofnat_succ_negsucc_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string(
                "Int.add_assoc_negSucc_ofNat_succ_negSucc",
            ))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_negSucc_ofNat_succ_negSucc must be Constructive, got {:?}",
            quality
        );
    }
}
