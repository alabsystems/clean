// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive additive rearrangement for two Rat subtractions.
//!
//! `Rat.sub_add_sub : (A - B) + (a - b) = (A + a) - (B + b)` is the
//! normalization fact needed by the `Fin.sum_sub` successor step.
//!
//! The proof cancels a common right summand `(B + b)`. Both sides plus that
//! summand normalize to `A + a` using associativity, commutativity, and
//! additive inverse laws.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct RatSubAddSubConsts {
    rat: Expr,
    rat_add: Expr,
    rat_neg: Expr,
    rat_sub: Expr,
    eq: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
    rat_add_left_neg: Expr,
    rat_add_right_cancel: Expr,
    rat_add_zero: Expr,
    rat_zero_add: Expr,
    rat_zero: Expr,
}

impl RatSubAddSubConsts {
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
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            rat_add_assoc: Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
            rat_add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
            rat_add_left_neg: Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]),
            rat_add_right_cancel: Expr::const_(Name::from_string("Rat.add_right_cancel"), vec![]),
            rat_add_zero: Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            rat_zero_add: Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
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

fn add_right_fn(c: &RatSubAddSubConsts, parent: &EnvDeclBuilder, right: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let body = c.add(x, right);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
    b.finish_child(lam)
}

fn add_left_fn(c: &RatSubAddSubConsts, parent: &EnvDeclBuilder, left: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let body = c.add(left, x);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
    b.finish_child(lam)
}

fn congr_rat(
    c: &RatSubAddSubConsts,
    domain: Expr,
    lhs: Expr,
    rhs: Expr,
    f: Expr,
    proof: Expr,
) -> Expr {
    Expr::apps(
        c.congr_arg.clone(),
        [domain, c.rat.clone(), lhs, rhs, f, proof],
    )
}

fn four_add_rearrange(
    c: &RatSubAddSubConsts,
    parent: &EnvDeclBuilder,
    a: Expr,
    b: Expr,
    x: Expr,
    d: Expr,
) -> Expr {
    let ab = c.add(a.clone(), b.clone());
    let xd = c.add(x.clone(), d.clone());
    let bx = c.add(b.clone(), x.clone());
    let xb = c.add(x.clone(), b.clone());
    let ax = c.add(a.clone(), x.clone());

    let mid0 = c.add(ab.clone(), xd.clone());
    let mid1 = c.add(c.add(ab, x.clone()), d.clone());
    let mid2 = c.add(c.add(a.clone(), bx), d.clone());
    let mid3 = c.add(c.add(a.clone(), xb.clone()), d.clone());
    let mid4 = c.add(c.add(ax.clone(), b.clone()), d.clone());
    let target = c.add(ax.clone(), c.add(b.clone(), d.clone()));

    let assoc_ab_x_d = Expr::apps(
        c.rat_add_assoc.clone(),
        [c.add(a.clone(), b.clone()), x.clone(), d.clone()],
    );
    let step1 = c.symm(mid1.clone(), mid0.clone(), assoc_ab_x_d);

    let assoc_a_b_x = Expr::apps(c.rat_add_assoc.clone(), [a.clone(), b.clone(), x.clone()]);
    let step2_fn = add_right_fn(c, parent, d.clone());
    let step2 = congr_rat(
        c,
        c.rat.clone(),
        c.add(c.add(a.clone(), b.clone()), x.clone()),
        c.add(a.clone(), c.add(b.clone(), x.clone())),
        step2_fn,
        assoc_a_b_x,
    );

    let comm_b_x = Expr::apps(c.rat_add_comm.clone(), [b.clone(), x.clone()]);
    let step3_fn = {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = ch.fresh_local(c.rat.clone());
        let body = c.add(c.add(a.clone(), y), d.clone());
        let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(lam)
    };
    let step3 = congr_rat(
        c,
        c.rat.clone(),
        c.add(b.clone(), x.clone()),
        xb.clone(),
        step3_fn,
        comm_b_x,
    );

    let assoc_a_x_b = Expr::apps(c.rat_add_assoc.clone(), [a.clone(), x.clone(), b.clone()]);
    let assoc_a_x_b_rev = c.symm(
        c.add(ax.clone(), b.clone()),
        c.add(a.clone(), xb),
        assoc_a_x_b,
    );
    let step4_fn = add_right_fn(c, parent, d.clone());
    let step4 = congr_rat(
        c,
        c.rat.clone(),
        c.add(a.clone(), c.add(x.clone(), b.clone())),
        c.add(ax.clone(), b.clone()),
        step4_fn,
        assoc_a_x_b_rev,
    );

    let step5 = Expr::apps(c.rat_add_assoc.clone(), [ax, b, d]);
    let chain12 = c.trans(mid0.clone(), mid1.clone(), mid2.clone(), step1, step2);
    let chain123 = c.trans(mid0.clone(), mid2.clone(), mid3.clone(), chain12, step3);
    let chain1234 = c.trans(mid0.clone(), mid3, mid4.clone(), chain123, step4);
    c.trans(mid0, mid4, target, chain1234, step5)
}

fn build_type(c: &RatSubAddSubConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, big_a) = b.fresh_local(c.rat.clone());
    let (b_id, big_b) = b.fresh_local(c.rat.clone());
    let (x_id, small_a) = b.fresh_local(c.rat.clone());
    let (y_id, small_b) = b.fresh_local(c.rat.clone());
    let lhs = c.add(
        c.sub(big_a.clone(), big_b.clone()),
        c.sub(small_a.clone(), small_b.clone()),
    );
    let rhs = c.sub(c.add(big_a, small_a), c.add(big_b, small_b));
    let ty = c.rat_eq(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(b_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_lhs_plus_sum_eq(
    c: &RatSubAddSubConsts,
    parent: &EnvDeclBuilder,
    big_a: Expr,
    big_b: Expr,
    small_a: Expr,
    small_b: Expr,
) -> Expr {
    let neg_big_b = c.neg(big_b.clone());
    let neg_small_b = c.neg(small_b.clone());
    let sum_b = c.add(big_b.clone(), small_b.clone());
    let sum_a = c.add(big_a.clone(), small_a.clone());

    let lhs_inner = c.add(
        c.add(big_a.clone(), neg_big_b.clone()),
        c.add(small_a.clone(), neg_small_b.clone()),
    );
    let lhs_plus_sum = c.add(lhs_inner.clone(), sum_b.clone());
    let rearranged_inner = c.add(sum_a.clone(), c.add(neg_big_b.clone(), neg_small_b.clone()));
    let after_first_rearrange = c.add(rearranged_inner.clone(), sum_b.clone());

    let step1_inner = four_add_rearrange(
        c,
        parent,
        big_a.clone(),
        neg_big_b.clone(),
        small_a.clone(),
        neg_small_b.clone(),
    );
    let step1 = congr_rat(
        c,
        c.rat.clone(),
        lhs_inner,
        rearranged_inner.clone(),
        add_right_fn(c, parent, sum_b.clone()),
        step1_inner,
    );

    let step2 = Expr::apps(
        c.rat_add_assoc.clone(),
        [
            sum_a.clone(),
            c.add(neg_big_b.clone(), neg_small_b.clone()),
            sum_b.clone(),
        ],
    );
    let after_assoc = c.add(
        sum_a.clone(),
        c.add(c.add(neg_big_b.clone(), neg_small_b.clone()), sum_b.clone()),
    );

    let inner_rearranged = c.add(
        c.add(neg_big_b.clone(), big_b.clone()),
        c.add(neg_small_b.clone(), small_b.clone()),
    );
    let step3_inner = four_add_rearrange(
        c,
        parent,
        neg_big_b.clone(),
        neg_small_b.clone(),
        big_b.clone(),
        small_b.clone(),
    );
    let step3 = congr_rat(
        c,
        c.rat.clone(),
        c.add(c.add(neg_big_b.clone(), neg_small_b.clone()), sum_b),
        inner_rearranged.clone(),
        add_left_fn(c, parent, sum_a.clone()),
        step3_inner,
    );

    let before_cancel_big = c.add(sum_a.clone(), inner_rearranged.clone());
    let after_cancel_big = c.add(
        sum_a.clone(),
        c.add(
            c.rat_zero.clone(),
            c.add(neg_small_b.clone(), small_b.clone()),
        ),
    );
    let cancel_big = Expr::app(c.rat_add_left_neg.clone(), big_b.clone());
    let motive_big = {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_eq(
            before_cancel_big.clone(),
            c.add(
                sum_a.clone(),
                c.add(x, c.add(neg_small_b.clone(), small_b.clone())),
            ),
        );
        let lam = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(lam)
    };
    let step4 = c.subst(
        motive_big,
        c.add(neg_big_b, big_b),
        c.rat_zero.clone(),
        cancel_big,
        c.refl(before_cancel_big.clone()),
    );

    let zero_plus_small_cancel = c.add(
        c.rat_zero.clone(),
        c.add(neg_small_b.clone(), small_b.clone()),
    );
    let small_cancel = c.add(neg_small_b.clone(), small_b.clone());
    let zero_add = Expr::app(c.rat_zero_add.clone(), small_cancel.clone());
    let step5 = congr_rat(
        c,
        c.rat.clone(),
        zero_plus_small_cancel,
        small_cancel.clone(),
        add_left_fn(c, parent, sum_a.clone()),
        zero_add,
    );

    let after_zero_add = c.add(sum_a.clone(), small_cancel.clone());
    let cancel_small = Expr::app(c.rat_add_left_neg.clone(), small_b);
    let step6 = congr_rat(
        c,
        c.rat.clone(),
        small_cancel,
        c.rat_zero.clone(),
        add_left_fn(c, parent, sum_a.clone()),
        cancel_small,
    );
    let step7 = Expr::app(c.rat_add_zero.clone(), sum_a.clone());

    let chain12 = c.trans(
        lhs_plus_sum.clone(),
        after_first_rearrange,
        after_assoc.clone(),
        step1,
        step2,
    );
    let chain123 = c.trans(
        lhs_plus_sum.clone(),
        after_assoc,
        before_cancel_big.clone(),
        chain12,
        step3,
    );
    let chain1234 = c.trans(
        lhs_plus_sum.clone(),
        before_cancel_big,
        after_cancel_big.clone(),
        chain123,
        step4,
    );
    let chain12345 = c.trans(
        lhs_plus_sum.clone(),
        after_cancel_big,
        after_zero_add.clone(),
        chain1234,
        step5,
    );
    let chain123456 = c.trans(
        lhs_plus_sum.clone(),
        after_zero_add,
        c.add(sum_a.clone(), c.rat_zero.clone()),
        chain12345,
        step6,
    );
    c.trans(
        lhs_plus_sum,
        c.add(sum_a.clone(), c.rat_zero.clone()),
        sum_a,
        chain123456,
        step7,
    )
}

fn build_rhs_plus_sum_eq(
    c: &RatSubAddSubConsts,
    parent: &EnvDeclBuilder,
    big_a: Expr,
    big_b: Expr,
    small_a: Expr,
    small_b: Expr,
) -> Expr {
    let sum_a = c.add(big_a, small_a);
    let sum_b = c.add(big_b.clone(), small_b.clone());
    let neg_sum_b = c.neg(sum_b.clone());
    let rhs_plus_sum = c.add(c.add(sum_a.clone(), neg_sum_b.clone()), sum_b.clone());
    let after_assoc = c.add(sum_a.clone(), c.add(neg_sum_b.clone(), sum_b.clone()));
    let after_cancel = c.add(sum_a.clone(), c.rat_zero.clone());

    let step1 = Expr::apps(
        c.rat_add_assoc.clone(),
        [sum_a.clone(), neg_sum_b.clone(), sum_b.clone()],
    );
    let cancel = Expr::app(c.rat_add_left_neg.clone(), sum_b.clone());
    let step2 = congr_rat(
        c,
        c.rat.clone(),
        c.add(neg_sum_b, c.add(big_b, small_b)),
        c.rat_zero.clone(),
        add_left_fn(c, parent, sum_a.clone()),
        cancel,
    );
    let step3 = Expr::app(c.rat_add_zero.clone(), sum_a.clone());
    let chain12 = c.trans(
        rhs_plus_sum.clone(),
        after_assoc,
        after_cancel.clone(),
        step1,
        step2,
    );
    c.trans(rhs_plus_sum, after_cancel, sum_a, chain12, step3)
}

fn build_value(c: &RatSubAddSubConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, big_a) = b.fresh_local(c.rat.clone());
    let (b_id, big_b) = b.fresh_local(c.rat.clone());
    let (x_id, small_a) = b.fresh_local(c.rat.clone());
    let (y_id, small_b) = b.fresh_local(c.rat.clone());

    let lhs = c.add(
        c.add(big_a.clone(), c.neg(big_b.clone())),
        c.add(small_a.clone(), c.neg(small_b.clone())),
    );
    let rhs = c.add(
        c.add(big_a.clone(), small_a.clone()),
        c.neg(c.add(big_b.clone(), small_b.clone())),
    );
    let sum_b = c.add(big_b.clone(), small_b.clone());
    let lhs_plus_sum = c.add(lhs.clone(), sum_b.clone());
    let rhs_plus_sum = c.add(rhs.clone(), sum_b.clone());
    let sum_a = c.add(big_a.clone(), small_a.clone());

    let lhs_norm = build_lhs_plus_sum_eq(
        c,
        &b,
        big_a.clone(),
        big_b.clone(),
        small_a.clone(),
        small_b.clone(),
    );
    let rhs_norm = build_rhs_plus_sum_eq(
        c,
        &b,
        big_a.clone(),
        big_b.clone(),
        small_a.clone(),
        small_b.clone(),
    );
    let rhs_norm_rev = c.symm(rhs_plus_sum.clone(), sum_a.clone(), rhs_norm);
    let cancelled_eq = c.trans(lhs_plus_sum, sum_a, rhs_plus_sum, lhs_norm, rhs_norm_rev);
    let proof = Expr::apps(
        c.rat_add_right_cancel.clone(),
        [lhs, sum_b, rhs, cancelled_eq],
    );

    let val = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Rat.sub_add_sub : (A - B) + (a - b) = (A + a) - (B + b)`.
    pub(crate) fn register_rat_sub_add_sub_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_add_sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.init_rat_arith()?;
        self.init_rat_field_inst()?;

        let c = RatSubAddSubConsts::new();
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
    fn rat_sub_add_sub_registers_checked_theorem() {
        let mut env = Environment::new();
        env.register_rat_sub_add_sub_theorem()
            .expect("Rat.sub_add_sub should type-check");
        assert!(env
            .get_const(&Name::from_string("Rat.sub_add_sub"))
            .is_some());
    }
}
