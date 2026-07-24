// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive additive rearrangement for Rat subtraction.
//!
//! `Rat.sub_add_assoc` is the first small normalization step needed by the
//! `Fin.sum_sub` induction case:
//! `(x - y) + z = (x + z) - y`.
//!
//! Since `Rat.sub x y` is reducible to `Rat.add x (Rat.neg y)`, the proof is
//! just associativity plus one commutation of `z` and `-y`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct RatSubAddAssocConsts {
    rat: Expr,
    rat_add: Expr,
    rat_neg: Expr,
    rat_sub: Expr,
    eq: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
}

impl RatSubAddAssocConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
            rat_add_assoc: Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
            rat_add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
        }
    }

    fn add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [lhs, rhs])
    }

    fn neg(&self, value: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), value)
    }

    fn sub(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [lhs, rhs])
    }

    fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), lhs, rhs])
    }

    fn refl(&self, value: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), value])
    }

    fn symm(&self, lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), lhs, rhs, proof])
    }

    fn trans(&self, lhs: Expr, mid: Expr, rhs: Expr, first: Expr, second: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), lhs, mid, rhs, first, second],
        )
    }

    fn subst(&self, motive: Expr, lhs: Expr, rhs: Expr, eq: Expr, proof: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, lhs, rhs, eq, proof],
        )
    }
}

fn build_type(c: &RatSubAddAssocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(c.rat.clone());
    let lhs = c.add(c.sub(x.clone(), y.clone()), z.clone());
    let rhs = c.sub(c.add(x, z), y);
    let ty = c.rat_eq(lhs, rhs);
    let ty = b.mk_pi(z_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &RatSubAddAssocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(c.rat.clone());

    let neg_y = c.neg(y.clone());
    let lhs = c.add(c.add(x.clone(), neg_y.clone()), z.clone());
    let _mid1 = c.add(x.clone(), c.add(neg_y.clone(), z.clone()));
    let mid2 = c.add(x.clone(), c.add(z.clone(), neg_y.clone()));
    let rhs = c.add(c.add(x.clone(), z.clone()), neg_y.clone());

    let step1 = Expr::apps(
        c.rat_add_assoc.clone(),
        [x.clone(), neg_y.clone(), z.clone()],
    );
    let comm = Expr::apps(c.rat_add_comm.clone(), [neg_y.clone(), z.clone()]);
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (inner_id, inner) = ch.fresh_local(c.rat.clone());
        let body = c.rat_eq(lhs.clone(), c.add(x.clone(), inner));
        let lam = ch.mk_lam(inner_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(lam)
    };
    let step2 = c.subst(
        motive,
        c.add(neg_y, z.clone()),
        c.add(z.clone(), c.neg(y.clone())),
        comm,
        step1,
    );
    let assoc_x_z_negy = Expr::apps(c.rat_add_assoc.clone(), [x.clone(), z, c.neg(y)]);
    let step3 = c.symm(rhs.clone(), mid2.clone(), assoc_x_z_negy);
    let proof = c.trans(lhs, mid2, rhs, step2, step3);

    let val = b.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), proof);
    let val = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Rat.sub_add_assoc : (x - y) + z = (x + z) - y`.
    pub(crate) fn register_rat_sub_add_assoc_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_add_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.init_rat_arith()?;
        self.init_rat_field_inst()?;

        let c = RatSubAddAssocConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rat_sub_add_assoc_registers_checked_theorem() {
        let mut env = Environment::new();
        env.register_rat_sub_add_assoc_theorem()
            .expect("Rat.sub_add_assoc should type-check");
        assert!(env
            .get_const(&Name::from_string("Rat.sub_add_assoc"))
            .is_some());
    }
}
