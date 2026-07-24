// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_negSucc_ofNat_succ_ofNat_succ :
//!    ∀ k m n : Nat,
//!      Eq Int
//!        (Int.add
//!          (Int.add (Int.negSucc k) (Int.ofNat (Nat.succ m)))
//!          (Int.ofNat (Nat.succ n)))
//!        (Int.add
//!          (Int.negSucc k)
//!          (Int.add (Int.ofNat (Nat.succ m)) (Int.ofNat (Nat.succ n))))`.
//!
//! This closes one negative outer / positive-positive branch of the remaining
//! `Int.add_assoc` case split. The proof transports the checked
//! `Int.add_negSucc_ofNat_succ` branch through right addition, then applies
//! checked positive transport over the intermediate `Int.subNatNat` result.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocNegSuccOfNatSuccOfNatSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    nat_add: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    inner_transport: Expr,
    right_transport: Expr,
    int_of_nat_add: Expr,
    nat_succ_add: Expr,
}

impl IntAddAssocNegSuccOfNatSuccOfNatSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            inner_transport: Expr::const_(Name::from_string("Int.add_negSucc_ofNat_succ"), vec![]),
            right_transport: Expr::const_(
                Name::from_string("Int.add_subNatNat_ofNat_succ"),
                vec![],
            ),
            int_of_nat_add: Expr::const_(Name::from_string("Int.ofNat_add"), vec![]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn add_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
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

    fn lhs(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.inner_lhs(k, m), self.of_nat(self.succ(n)))
    }

    fn mid(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.sub_nat_nat(m, k), self.of_nat(self.succ(n)))
    }

    fn normal(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.sub_nat_nat(self.add_nat(m, self.succ(n)), k)
    }

    fn rhs(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(
            self.neg_succ(k),
            self.add_int(self.of_nat(self.succ(m)), self.of_nat(self.succ(n))),
        )
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_type(
    c: &IntAddAssocNegSuccOfNatSuccOfNatSuccConsts,
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

fn build_add_right_pos_fn(
    c: &IntAddAssocNegSuccOfNatSuccOfNatSuccConsts,
    parent: &EnvDeclBuilder,
    n: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(x, c.of_nat(c.succ(n)));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

/// Build `λ y : Int => Int.add (Int.negSucc k) y`, the function used to lift
/// the inner-argument equality through left addition by `negSucc k`.
fn build_add_left_negsucc_fn(
    c: &IntAddAssocNegSuccOfNatSuccOfNatSuccConsts,
    parent: &EnvDeclBuilder,
    k: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = fb.fresh_local(c.int_type.clone());
    let body = c.add_int(c.neg_succ(k), y);
    let lam = fb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_value(
    c: &IntAddAssocNegSuccOfNatSuccOfNatSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    let lhs = c.lhs(k.clone(), m.clone(), n.clone());
    let mid = c.mid(k.clone(), m.clone(), n.clone());
    let normal = c.normal(k.clone(), m.clone(), n.clone());
    let rhs = c.rhs(k.clone(), m.clone(), n.clone());

    let h_inner = Expr::app(Expr::app(c.inner_transport.clone(), m.clone()), k.clone());
    let add_right = build_add_right_pos_fn(c, &b, n.clone());
    let h_lhs = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            c.inner_lhs(k.clone(), m.clone()),
            c.sub_nat_nat(m.clone(), k.clone()),
            add_right,
            h_inner,
        ],
    );

    let h_right = Expr::app(
        Expr::app(Expr::app(c.right_transport.clone(), m.clone()), k.clone()),
        n.clone(),
    );
    let h_lhs_to_normal = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            lhs.clone(),
            mid,
            normal.clone(),
            h_lhs,
            h_right,
        ],
    );

    let normal_index = c.add_nat(m.clone(), c.succ(n.clone()));
    // `h_rhs_forward : Eq Int x_intermediate normal`, where
    // `x_intermediate = Int.add (negSucc k) (ofNat (succ (Nat.add m (succ n))))`.
    // This is `Int.add_negSucc_ofNat_succ` specialized to (Nat.add m (succ n), k).
    let h_rhs_forward = Expr::app(
        Expr::app(c.inner_transport.clone(), normal_index.clone()),
        k.clone(),
    );

    // The declared `rhs` carries the inner argument
    // `Int.add (ofNat (succ m)) (ofNat (succ n))`, but `x_intermediate` carries
    // `ofNat (succ (Nat.add m (succ n)))`. These are propositionally — not
    // definitionally — equal, so we must bridge the inner arguments explicitly.
    //
    //   `sum_ints      = Int.add (ofNat (succ m)) (ofNat (succ n))`
    //   `nat_sum_succ  = Nat.add (succ m) (succ n)`
    //   `of_nat_normal = ofNat (succ (Nat.add m (succ n)))`
    let succ_m = c.succ(m.clone());
    let succ_n = c.succ(n.clone());
    let of_succ_m = c.of_nat(succ_m.clone());
    let of_succ_n = c.of_nat(succ_n.clone());
    let sum_ints = c.add_int(of_succ_m, of_succ_n);
    let nat_sum_succ = c.add_nat(succ_m.clone(), succ_n.clone());
    let succ_normal_index = c.succ(normal_index.clone());
    let of_nat_normal = c.of_nat(succ_normal_index.clone());

    // `nat_eq : Eq Nat (Nat.add (succ m) (succ n)) (succ (Nat.add m (succ n)))`
    // via `Nat.succ_add m (succ n)`.
    let nat_eq = Expr::app(
        Expr::app(c.nat_succ_add.clone(), m.clone()),
        c.succ(n.clone()),
    );
    // Lift `nat_eq` through `Int.ofNat`:
    // `ofnat_eq : Eq Int (ofNat nat_sum_succ) of_nat_normal`.
    let ofnat_eq = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.int_type.clone(),
            nat_sum_succ.clone(),
            succ_normal_index.clone(),
            c.int_of_nat.clone(),
            nat_eq,
        ],
    );
    // `ofnat_add : Eq Int (ofNat nat_sum_succ) sum_ints` via
    // `Int.ofNat_add (succ m) (succ n)`.
    let ofnat_add = Expr::app(
        Expr::app(c.int_of_nat_add.clone(), succ_m.clone()),
        succ_n.clone(),
    );
    // `ofnat_add_sym : Eq Int sum_ints (ofNat nat_sum_succ)`.
    let ofnat_add_sym = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            c.of_nat(nat_sum_succ.clone()),
            sum_ints.clone(),
            ofnat_add,
        ],
    );
    // `inner : Eq Int sum_ints of_nat_normal`, chaining the two halves.
    let inner = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            sum_ints.clone(),
            c.of_nat(nat_sum_succ),
            of_nat_normal.clone(),
            ofnat_add_sym,
            ofnat_eq,
        ],
    );
    // Lift `inner` through `λ y => Int.add (negSucc k) y`:
    // `bridge : Eq Int rhs x_intermediate`.
    let add_left = build_add_left_negsucc_fn(c, &b, k.clone());
    let bridge = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            sum_ints,
            of_nat_normal.clone(),
            add_left,
            inner,
        ],
    );
    let x_intermediate = c.add_int(c.neg_succ(k.clone()), of_nat_normal);
    // `h_rhs_to_normal : Eq Int rhs normal`.
    let h_rhs_to_normal = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            rhs.clone(),
            x_intermediate,
            normal.clone(),
            bridge,
            h_rhs_forward,
        ],
    );
    let h_normal_to_rhs = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            rhs.clone(),
            normal.clone(),
            h_rhs_to_normal,
        ],
    );

    let proof = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            lhs,
            normal,
            rhs,
            h_lhs_to_normal,
            h_normal_to_rhs,
        ],
    );

    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_negSucc_ofNat_succ_ofNat_succ` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.add_assoc_negSucc_ofNat_succ_ofNat_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_add_negsucc_ofnat_succ_proof()?;
        self.register_int_add_sub_nat_nat_ofnat_succ_proof()?;
        self.register_int_ofnat_add_proof()?;
        self.register_nat_succ_add_proof()?;

        let c = IntAddAssocNegSuccOfNatSuccOfNatSuccConsts::new();
        let type_ = build_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_type(&c);
        let value = build_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_value(&c);

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
    fn test_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_proof()
            .expect("first registration");
        env.register_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string(
                "Int.add_assoc_negSucc_ofNat_succ_ofNat_succ",
            ))
            .expect("Int.add_assoc_negSucc_ofNat_succ_ofNat_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string(
                "Int.add_assoc_negSucc_ofNat_succ_ofNat_succ",
            ))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_negSucc_ofNat_succ_ofNat_succ must be Constructive, got {:?}",
            quality
        );
    }
}
