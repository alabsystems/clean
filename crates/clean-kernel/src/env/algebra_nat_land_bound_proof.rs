// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! A canonical-width bound for the actual Nat.land definition. Both operand
//! bounds imply vanishing high bits; testBit_and and bits-determine-bound
//! close the result. There is no supplied result or execution hypothesis.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn pow2(width: Expr) -> Expr {
    Expr::apps(k("Nat.pow"), [Expr::nat_lit(2), width])
}
fn lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(k("Nat.lt"), [a, b])
}
fn land(a: Expr, b: Expr) -> Expr {
    Expr::apps(k("Nat.land"), [a, b])
}
fn bit(value: Expr, index: Expr) -> Expr {
    Expr::apps(k("Nat.testBit"), [value, index])
}
fn eq_bool(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Bool"), a, b],
    )
}
fn subst_bool(motive: Expr, a: Expr, b: Expr, equality: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        ),
        [k("Bool"), motive, a, b, equality, proof],
    )
}

fn build_land_lt_two_pow() -> (Expr, Expr) {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(k("Nat"));
    let (a_id, a) = b.fresh_local(k("Nat"));
    let (b_id, operand_b) = b.fresh_local(k("Nat"));
    let a_bound = lt(a.clone(), pow2(n.clone()));
    let b_bound = lt(operand_b.clone(), pow2(n.clone()));
    let (ha_id, ha) = b.fresh_local(a_bound.clone());
    let (hb_id, hb) = b.fresh_local(b_bound.clone());
    let result = land(a.clone(), operand_b.clone());

    let high_bits = {
        let mut high = EnvDeclBuilder::child_of(&b);
        let (index_id, index) = high.fresh_local(k("Nat"));
        let index_bound = Expr::apps(k("Nat.le"), [n.clone(), index.clone()]);
        let (bound_id, bound) = high.fresh_local(index_bound.clone());
        let one = Expr::nat_lit(1);
        let one_le_two = Expr::apps(
            k("Nat.le.step"),
            [one.clone(), one.clone(), Expr::app(k("Nat.le.refl"), one)],
        );
        let power_bound = Expr::apps(
            k("Nat.pow_le_pow_right"),
            [
                Expr::nat_lit(2),
                n.clone(),
                index.clone(),
                one_le_two,
                bound,
            ],
        );
        let vanishes = |operand: Expr, operand_bound: Expr| {
            let below_index = Expr::apps(
                k("Nat.lt_of_lt_of_le"),
                [
                    operand.clone(),
                    pow2(n.clone()),
                    pow2(index.clone()),
                    operand_bound,
                    power_bound.clone(),
                ],
            );
            Expr::apps(
                k("Nat.testBit_lt_pow"),
                [index.clone(), operand, below_index],
            )
        };
        let a_false = vanishes(a.clone(), ha);
        let b_false = vanishes(operand_b.clone(), hb);
        let a_bit = bit(a.clone(), index.clone());
        let b_bit = bit(operand_b.clone(), index.clone());
        let result_bit = bit(result.clone(), index.clone());
        let decomposition = Expr::apps(
            k("Nat.testBit_and"),
            [a.clone(), operand_b.clone(), index.clone()],
        );
        let replace_a = {
            let mut motive = EnvDeclBuilder::child_of(&high);
            let (flag_id, flag) = motive.fresh_local(k("Bool"));
            let body = eq_bool(
                result_bit.clone(),
                Expr::apps(k("Bool.and"), [flag, b_bit.clone()]),
            );
            motive.finish_child(motive.mk_lam(flag_id, BinderInfo::Default, k("Bool"), body))
        };
        let after_a = subst_bool(replace_a, a_bit, k("Bool.false"), a_false, decomposition);
        let replace_b = {
            let mut motive = EnvDeclBuilder::child_of(&high);
            let (flag_id, flag) = motive.fresh_local(k("Bool"));
            let body = eq_bool(
                result_bit,
                Expr::apps(k("Bool.and"), [k("Bool.false"), flag]),
            );
            motive.finish_child(motive.mk_lam(flag_id, BinderInfo::Default, k("Bool"), body))
        };
        // Bool.and false false reduces to false in the actual definition.
        let proof = subst_bool(replace_b, b_bit, k("Bool.false"), b_false, after_a);
        let proof = high.mk_lam(bound_id, BinderInfo::Default, index_bound, proof);
        high.finish_child(high.mk_lam(index_id, BinderInfo::Default, k("Nat"), proof))
    };
    let mut proof = Expr::apps(
        k("Nat.lt_two_pow_of_testBit_ge"),
        [n.clone(), result.clone(), high_bits],
    );
    let mut type_ = lt(result, pow2(n));
    for (id, domain) in [
        (hb_id, b_bound),
        (ha_id, a_bound),
        (b_id, k("Nat")),
        (a_id, k("Nat")),
        (n_id, k("Nat")),
    ] {
        proof = b.mk_lam(id, BinderInfo::Default, domain.clone(), proof);
        type_ = b.mk_pi(id, BinderInfo::Default, domain, type_);
    }
    (b.finish(type_), b.finish(proof))
}

impl Environment {
    pub(crate) fn register_nat_land_bound_proof(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Nat.land_lt_two_pow");
        self.register_nat_high_bit_bound_proof()?;
        self.register_nat_testbit_lt_pow_proof()?;
        self.register_nat_testbit_bitwise_proof()?;
        self.register_nat_pow_le_pow_right_proof()?;
        self.init_nat_trans_lt_le_lt()?;
        let (type_, value) = build_land_lt_two_pow();
        self.ensure_exact_checked_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })?;
        Ok(())
    }
}

#[cfg(test)]
#[path = "algebra_nat_land_bound_proof_tests.rs"]
mod tests;
