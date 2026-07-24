// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.subNatNat_succ_succ :
//!    ∀ m n : Nat,
//!      Eq Int
//!        (Int.subNatNat (Nat.succ m) (Nat.succ n))
//!        (Int.subNatNat m n)`.
//!
//! This is the successor/successor cancellation theorem for
//! `Int.subNatNat`, the main local normalization primitive needed before
//! mixed-sign `Int.add_assoc` reassociation can be attacked constructively.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntSubNatNatSuccSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec_prop: Expr,
    nat_rec_type: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    int_rec_type: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    congr_arg: Expr,
}

impl IntSubNatNatSuccSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_rec_type: Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(Level::zero())],
            ),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            int_rec_type: Expr::const_(
                Name::from_string("Int.rec"),
                vec![Level::succ(Level::zero())],
            ),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn sub_succ_succ(&self, m: Expr, n: Expr) -> Expr {
        self.sub_nat_nat(self.succ(m), self.succ(n))
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_decrement_fn(c: &IntSubNatNatSuccSuccConsts) -> Expr {
    let int_motive = Expr::lam(BinderInfo::Default, c.int_type.clone(), c.int_type.clone());
    let nat_motive = Expr::lam(BinderInfo::Default, c.nat_type.clone(), c.int_type.clone());

    let of_nat_case = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(c.nat_type.clone());
        let (q_id, q) = b.fresh_local(c.nat_type.clone());
        let (ih_id, _ih) = b.fresh_local(c.int_type.clone());
        let succ_case = b.mk_lam(
            ih_id,
            BinderInfo::Default,
            c.int_type.clone(),
            Expr::app(c.int_of_nat.clone(), q),
        );
        let succ_case = b.mk_lam(q_id, BinderInfo::Default, c.nat_type.clone(), succ_case);
        let body = Expr::apps(
            c.nat_rec_type.clone(),
            [nat_motive, c.neg_succ(c.nat_zero.clone()), succ_case, p],
        );
        let lam = b.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), body);
        b.finish(lam)
    };

    let neg_succ_case = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(c.nat_type.clone());
        let body = c.neg_succ(c.succ(p));
        let lam = b.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), body);
        b.finish(lam)
    };

    let mut b = EnvDeclBuilder::new();
    let (z_id, z) = b.fresh_local(c.int_type.clone());
    let body = Expr::apps(
        c.int_rec_type.clone(),
        [int_motive, of_nat_case, neg_succ_case, z],
    );
    let lam = b.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), body);
    b.finish(lam)
}

fn build_int_sub_nat_nat_succ_succ_type(c: &IntSubNatNatSuccSuccConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.sub_succ_succ(m.clone(), n.clone()), c.sub_nat_nat(m, n));
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_int_sub_nat_nat_succ_succ_value(c: &IntSubNatNatSuccSuccConsts) -> Expr {
    let dec_fn = build_decrement_fn(c);

    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(
            c.sub_succ_succ(m.clone(), t.clone()),
            c.sub_nat_nat(m.clone(), t),
        );
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    let base = Expr::apps(
        c.eq_refl.clone(),
        [
            c.int_type.clone(),
            Expr::app(c.int_of_nat.clone(), m.clone()),
        ],
    );

    let step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_type = c.eq_int(
            c.sub_succ_succ(m.clone(), k.clone()),
            c.sub_nat_nat(m.clone(), k.clone()),
        );
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());
        let congr_app = Expr::apps(
            c.congr_arg.clone(),
            [
                c.int_type.clone(),
                c.int_type.clone(),
                c.sub_succ_succ(m.clone(), k.clone()),
                c.sub_nat_nat(m.clone(), k),
                dec_fn,
                ih,
            ],
        );
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, congr_app);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step, n]);
    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.subNatNat_succ_succ` as a kernel-checked theorem.
    ///
    /// The proof inducts on the second Nat argument. The base case closes
    /// by reduction; the step maps the induction hypothesis through the
    /// same one-step decrement function used by `Int.subNatNat`.
    pub(crate) fn register_int_sub_nat_nat_succ_succ_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.subNatNat_succ_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let c = IntSubNatNatSuccSuccConsts::new();
        let type_ = build_int_sub_nat_nat_succ_succ_type(&c);
        let value = build_int_sub_nat_nat_succ_succ_value(&c);

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
    fn test_int_sub_nat_nat_succ_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_succ_succ_proof()
            .expect("first registration");
        env.register_int_sub_nat_nat_succ_succ_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.subNatNat_succ_succ"))
            .expect("Int.subNatNat_succ_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_sub_nat_nat_succ_succ_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.subNatNat_succ_succ"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.subNatNat_succ_succ must be Constructive, got {:?}",
            quality
        );
    }
}
