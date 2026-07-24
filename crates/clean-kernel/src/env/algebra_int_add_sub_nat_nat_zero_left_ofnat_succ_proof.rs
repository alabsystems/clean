// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_subNatNat_zero_left_ofNat_succ :
//!    ∀ n k : Nat,
//!      Eq Int
//!        (Int.add (Int.subNatNat Nat.zero n) (Int.ofNat (Nat.succ k)))
//!        (Int.subNatNat (Nat.succ k) n)`.
//!
//! This is the first nonzero positive transport theorem for an
//! intermediate `Int.subNatNat` result. It handles the zero-left
//! frontier needed before the general
//! `(Int.subNatNat m n) + Int.ofNat (Nat.succ k)` transport can be
//! proved.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddSubNatNatZeroLeftOfNatSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_rec: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    nat_zero_add: Expr,
    int_sub_nat_nat_zero_succ: Expr,
    int_sub_nat_nat_succ_succ: Expr,
    int_add_negsucc_ofnat_succ: Expr,
}

impl IntAddSubNatNatZeroLeftOfNatSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_zero_add: Expr::const_(Name::from_string("Nat.zero_add"), vec![]),
            int_sub_nat_nat_zero_succ: Expr::const_(
                Name::from_string("Int.subNatNat_zero_succ"),
                vec![],
            ),
            int_sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
            int_add_negsucc_ofnat_succ: Expr::const_(
                Name::from_string("Int.add_negSucc_ofNat_succ"),
                vec![],
            ),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
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

    fn sub_zero(&self, n: Expr) -> Expr {
        self.sub_nat_nat(self.nat_zero.clone(), n)
    }

    fn add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, n: Expr, k: Expr) -> Expr {
        self.add(self.sub_zero(n), self.of_nat(self.succ(k)))
    }

    fn rhs(&self, n: Expr, k: Expr) -> Expr {
        self.sub_nat_nat(self.succ(k), n)
    }

    fn nat_add_zero_lhs(&self, k: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), self.nat_zero.clone()), k)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_sub_nat_nat_zero_left_ofnat_succ_type(
    c: &IntAddSubNatNatZeroLeftOfNatSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(n.clone(), k.clone()), c.rhs(n, k));
    let ty_raw = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_add_right_ofnat_succ_fn(
    c: &IntAddSubNatNatZeroLeftOfNatSuccConsts,
    parent: &EnvDeclBuilder,
    k: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add(x, c.of_nat(c.succ(k)));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_sub_nat_nat_zero_left_ofnat_succ_value(
    c: &IntAddSubNatNatZeroLeftOfNatSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let (k_id, k) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.lhs(t.clone(), k.clone()), c.rhs(t, k));
        let pi = mb.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), body);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), pi);
        mb.finish_child(lam)
    };

    let base = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = bb.fresh_local(c.nat_type.clone());
        let succ_k = c.succ(k.clone());
        let proof = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                c.nat_add_zero_lhs(succ_k.clone()),
                succ_k,
                c.int_of_nat.clone(),
                Expr::app(c.nat_zero_add.clone(), c.succ(k)),
            ],
        );
        let lam = bb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
        bb.finish_child(lam)
    };

    let step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = sb.fresh_local(c.nat_type.clone());
        let ih_type = {
            let (k_id, k) = sb.fresh_local(c.nat_type.clone());
            let body = c.eq_int(c.lhs(t.clone(), k.clone()), c.rhs(t.clone(), k));
            sb.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), body)
        };
        let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());

        let succ_t = c.succ(t.clone());
        let succ_k = c.succ(k.clone());
        let lhs = c.lhs(succ_t.clone(), k.clone());
        let mid1 = c.add(c.neg_succ(t.clone()), c.of_nat(succ_k.clone()));
        let mid2 = c.sub_nat_nat(k.clone(), t.clone());
        let rhs = c.rhs(succ_t, k.clone());

        let h_zero_succ = Expr::app(c.int_sub_nat_nat_zero_succ.clone(), t.clone());
        let add_right_fn = build_add_right_ofnat_succ_fn(c, &sb, k.clone());
        let h0 = Expr::apps(
            c.congr_arg.clone(),
            [
                c.int_type.clone(),
                c.int_type.clone(),
                c.sub_zero(c.succ(t.clone())),
                c.neg_succ(t.clone()),
                add_right_fn,
                h_zero_succ,
            ],
        );
        let h1 = Expr::app(
            Expr::app(c.int_add_negsucc_ofnat_succ.clone(), k.clone()),
            t.clone(),
        );
        let h2_forward = Expr::app(
            Expr::app(c.int_sub_nat_nat_succ_succ.clone(), k.clone()),
            t.clone(),
        );
        let h2 = Expr::apps(
            c.eq_symm.clone(),
            [c.int_type.clone(), rhs.clone(), mid2.clone(), h2_forward],
        );

        let h01 = Expr::apps(
            c.eq_trans.clone(),
            [c.int_type.clone(), lhs.clone(), mid1, mid2.clone(), h0, h1],
        );
        let proof = Expr::apps(
            c.eq_trans.clone(),
            [c.int_type.clone(), lhs, mid2, rhs, h01, h2],
        );

        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_k);
        let lam_t = sb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_t)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_subNatNat_zero_left_ofNat_succ` as a kernel-checked theorem.
    pub(crate) fn register_int_add_sub_nat_nat_zero_left_ofnat_succ_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.add_subNatNat_zero_left_ofNat_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_zero_add_proof()?;
        self.register_int_sub_nat_nat_zero_succ_proof()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;
        self.register_int_add_negsucc_ofnat_succ_proof()?;

        let c = IntAddSubNatNatZeroLeftOfNatSuccConsts::new();
        let type_ = build_int_add_sub_nat_nat_zero_left_ofnat_succ_type(&c);
        let value = build_int_add_sub_nat_nat_zero_left_ofnat_succ_value(&c);

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
    fn test_int_add_sub_nat_nat_zero_left_ofnat_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_sub_nat_nat_zero_left_ofnat_succ_proof()
            .expect("first registration");
        env.register_int_add_sub_nat_nat_zero_left_ofnat_succ_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_subNatNat_zero_left_ofNat_succ"))
            .expect("Int.add_subNatNat_zero_left_ofNat_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_sub_nat_nat_zero_left_ofnat_succ_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_subNatNat_zero_left_ofNat_succ"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_subNatNat_zero_left_ofNat_succ must be Constructive, got {:?}",
            quality
        );
    }
}
