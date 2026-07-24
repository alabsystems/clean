// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_subNatNat_ofNat_succ :
//!    ∀ m n k : Nat,
//!      Eq Int
//!        (Int.add (Int.subNatNat m n) (Int.ofNat (Nat.succ k)))
//!        (Int.subNatNat (Nat.add m (Nat.succ k)) n)`.
//!
//! This is the general positive transport theorem for an intermediate
//! `Int.subNatNat` result. It is the direct normalization lemma needed
//! by mixed-sign `Int.add_assoc` cases.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddSubNatNatOfNatSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_rec: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    nat_zero_add: Expr,
    nat_succ_add: Expr,
    zero_left_transport: Expr,
    zero_right_transport: Expr,
    int_sub_nat_nat_succ_succ: Expr,
}

impl IntAddSubNatNatOfNatSuccConsts {
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
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_zero_add: Expr::const_(Name::from_string("Nat.zero_add"), vec![]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            zero_left_transport: Expr::const_(
                Name::from_string("Int.add_subNatNat_zero_left_ofNat_succ"),
                vec![],
            ),
            zero_right_transport: Expr::const_(
                Name::from_string("Int.add_subNatNat_zero_right_ofNat_succ"),
                vec![],
            ),
            int_sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
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

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn pos(&self, k: Expr) -> Expr {
        self.succ(k)
    }

    fn lhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.add_int(self.sub_nat_nat(m, n), self.of_nat(self.pos(k)))
    }

    fn rhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.sub_nat_nat(self.nat_add(m, self.pos(k)), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_sub_nat_nat_ofnat_succ_type(c: &IntAddSubNatNatOfNatSuccConsts) -> Expr {
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

fn build_add_right_pos_fn(
    c: &IntAddSubNatNatOfNatSuccConsts,
    parent: &EnvDeclBuilder,
    k: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(x, c.of_nat(c.pos(k)));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_sub_succ_t_fn(
    c: &IntAddSubNatNatOfNatSuccConsts,
    parent: &EnvDeclBuilder,
    t: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let body = c.sub_nat_nat(x, c.succ(t));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_sub_nat_nat_ofnat_succ_value(c: &IntAddSubNatNatOfNatSuccConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());

    let motive_n = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let (m_id, m) = mb.fresh_local(c.nat_type.clone());
        let (k_id, k) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.lhs(m.clone(), t.clone(), k.clone()), c.rhs(m, t, k));
        let pi_k = mb.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), body);
        let pi_m = mb.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), pi_k);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), pi_m);
        mb.finish_child(lam)
    };

    let base_n = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bb.fresh_local(c.nat_type.clone());
        let (k_id, k) = bb.fresh_local(c.nat_type.clone());
        let proof = Expr::app(Expr::app(c.zero_right_transport.clone(), m), k);
        let lam_k = bb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
        let lam_m = bb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_k);
        bb.finish_child(lam_m)
    };

    let step_n = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = sb.fresh_local(c.nat_type.clone());
        let ih_type = {
            let (m_id, m) = sb.fresh_local(c.nat_type.clone());
            let (k_id, k) = sb.fresh_local(c.nat_type.clone());
            let body = c.eq_int(
                c.lhs(m.clone(), t.clone(), k.clone()),
                c.rhs(m, t.clone(), k),
            );
            let pi_k = sb.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), body);
            sb.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), pi_k)
        };
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        let motive_m = {
            let mut mb = EnvDeclBuilder::child_of(&sb);
            let (x_id, x) = mb.fresh_local(c.nat_type.clone());
            let (k_id, k) = mb.fresh_local(c.nat_type.clone());
            let body = c.eq_int(
                c.lhs(x.clone(), c.succ(t.clone()), k.clone()),
                c.rhs(x, c.succ(t.clone()), k),
            );
            let pi_k = mb.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), body);
            let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), pi_k);
            mb.finish_child(lam)
        };

        let base_m = {
            let mut bb = EnvDeclBuilder::child_of(&sb);
            let (k_id, k) = bb.fresh_local(c.nat_type.clone());
            let pos = c.pos(k.clone());
            let lhs = c.lhs(c.nat_zero.clone(), c.succ(t.clone()), k.clone());
            let mid = c.sub_nat_nat(pos.clone(), c.succ(t.clone()));
            let rhs = c.rhs(c.nat_zero.clone(), c.succ(t.clone()), k.clone());

            let h_left = Expr::app(
                Expr::app(c.zero_left_transport.clone(), c.succ(t.clone())),
                k.clone(),
            );
            let zero_add = Expr::app(c.nat_zero_add.clone(), pos.clone());
            let zero_add_symm = Expr::apps(
                c.eq_symm.clone(),
                [
                    c.nat_type.clone(),
                    c.nat_add(c.nat_zero.clone(), pos.clone()),
                    pos.clone(),
                    zero_add,
                ],
            );
            let sub_fn = build_sub_succ_t_fn(c, &bb, t.clone());
            let h_rhs = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.nat_type.clone(),
                    c.int_type.clone(),
                    pos,
                    c.nat_add(c.nat_zero.clone(), c.pos(k.clone())),
                    sub_fn,
                    zero_add_symm,
                ],
            );
            let proof = Expr::apps(
                c.eq_trans.clone(),
                [c.int_type.clone(), lhs, mid, rhs, h_left, h_rhs],
            );
            let lam = bb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
            bb.finish_child(lam)
        };

        let step_m = {
            let mut mb = EnvDeclBuilder::child_of(&sb);
            let (a_id, a) = mb.fresh_local(c.nat_type.clone());
            let prev_type = {
                let (k_id, k) = mb.fresh_local(c.nat_type.clone());
                let body = c.eq_int(
                    c.lhs(a.clone(), c.succ(t.clone()), k.clone()),
                    c.rhs(a.clone(), c.succ(t.clone()), k),
                );
                mb.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), body)
            };
            let (prev_id, _prev) = mb.fresh_local(prev_type.clone());
            let (k_id, k) = mb.fresh_local(c.nat_type.clone());

            let pos = c.pos(k.clone());
            let succ_a = c.succ(a.clone());
            let succ_t = c.succ(t.clone());
            let add_a_pos = c.nat_add(a.clone(), pos.clone());
            let lhs = c.lhs(succ_a.clone(), succ_t.clone(), k.clone());
            let mid1 = c.lhs(a.clone(), t.clone(), k.clone());
            let mid2 = c.rhs(a.clone(), t.clone(), k.clone());
            let mid3 = c.sub_nat_nat(c.succ(add_a_pos.clone()), succ_t.clone());
            let rhs = c.rhs(succ_a.clone(), succ_t.clone(), k.clone());

            let h_sub = Expr::app(
                Expr::app(c.int_sub_nat_nat_succ_succ.clone(), a.clone()),
                t.clone(),
            );
            let add_right = build_add_right_pos_fn(c, &mb, k.clone());
            let h0 = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.int_type.clone(),
                    c.int_type.clone(),
                    c.sub_nat_nat(succ_a, succ_t.clone()),
                    c.sub_nat_nat(a.clone(), t.clone()),
                    add_right,
                    h_sub,
                ],
            );
            let h1 = Expr::app(Expr::app(ih.clone(), a.clone()), k.clone());
            let h2_forward = Expr::app(
                Expr::app(c.int_sub_nat_nat_succ_succ.clone(), add_a_pos.clone()),
                t.clone(),
            );
            let h2 = Expr::apps(
                c.eq_symm.clone(),
                [c.int_type.clone(), mid3.clone(), mid2.clone(), h2_forward],
            );
            let succ_add = Expr::app(Expr::app(c.nat_succ_add.clone(), a.clone()), pos.clone());
            let succ_add_symm = Expr::apps(
                c.eq_symm.clone(),
                [
                    c.nat_type.clone(),
                    c.nat_add(c.succ(a.clone()), pos.clone()),
                    c.succ(add_a_pos),
                    succ_add,
                ],
            );
            let sub_fn = build_sub_succ_t_fn(c, &mb, t.clone());
            let h3 = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.nat_type.clone(),
                    c.int_type.clone(),
                    c.succ(c.nat_add(a.clone(), c.pos(k.clone()))),
                    c.nat_add(c.succ(a), c.pos(k)),
                    sub_fn,
                    succ_add_symm,
                ],
            );

            let h01 = Expr::apps(
                c.eq_trans.clone(),
                [c.int_type.clone(), lhs.clone(), mid1, mid2.clone(), h0, h1],
            );
            let h012 = Expr::apps(
                c.eq_trans.clone(),
                [c.int_type.clone(), lhs.clone(), mid2, mid3.clone(), h01, h2],
            );
            let proof = Expr::apps(
                c.eq_trans.clone(),
                [c.int_type.clone(), lhs, mid3, rhs, h012, h3],
            );

            let lam_k = mb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
            let lam_prev = mb.mk_lam(prev_id, BinderInfo::Default, prev_type, lam_k);
            let lam_a = mb.mk_lam(a_id, BinderInfo::Default, c.nat_type.clone(), lam_prev);
            mb.finish_child(lam_a)
        };

        let (m_id, m) = sb.fresh_local(c.nat_type.clone());
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let rec_m = Expr::apps(c.nat_rec.clone(), [motive_m, base_m, step_m, m]);
        let rec_m_app = Expr::app(rec_m, k);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_m_app);
        let lam_m = sb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_k);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_m);
        let lam_t = sb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_t)
    };

    let rec_n = Expr::apps(c.nat_rec.clone(), [motive_n, base_n, step_n, n]);
    let proof = Expr::app(Expr::app(rec_n, m), k);
    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_subNatNat_ofNat_succ` as a kernel-checked theorem.
    pub(crate) fn register_int_add_sub_nat_nat_ofnat_succ_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_subNatNat_ofNat_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_zero_add_proof()?;
        self.register_nat_succ_add_proof()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;
        self.register_int_add_sub_nat_nat_zero_left_ofnat_succ_proof()?;
        self.register_int_add_sub_nat_nat_zero_right_ofnat_succ_proof()?;

        let c = IntAddSubNatNatOfNatSuccConsts::new();
        let type_ = build_int_add_sub_nat_nat_ofnat_succ_type(&c);
        let value = build_int_add_sub_nat_nat_ofnat_succ_value(&c);

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
    fn test_int_add_sub_nat_nat_ofnat_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_sub_nat_nat_ofnat_succ_proof()
            .expect("first registration");
        env.register_int_add_sub_nat_nat_ofnat_succ_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_subNatNat_ofNat_succ"))
            .expect("Int.add_subNatNat_ofNat_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_sub_nat_nat_ofnat_succ_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_subNatNat_ofNat_succ"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_subNatNat_ofNat_succ must be Constructive, got {:?}",
            quality
        );
    }
}
