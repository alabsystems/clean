// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Width-limited AND agrees with canonical Nat.land for two bounded operands.
//! This bridges the two actual Nat recursors, without an execution premise.
//! EvalIR's separate low-bit/division representation still needs its own bridge.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(k(name), args)
}
fn pow2(width: Expr) -> Expr {
    app("Nat.pow", [Expr::nat_lit(2), width])
}
fn eq(type_: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [type_, a, b],
    )
}
fn symm_bool(a: Expr, b: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [k("Bool"), a, b, proof],
    )
}
fn trans_bool(a: Expr, b: Expr, c: Expr, ab: Expr, bc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [k("Bool"), a, b, c, ab, bc],
    )
}
fn aux(width: Expr, a: Expr, b: Expr) -> Expr {
    app("Nat.bitwiseAux", [k("Bool.and"), width, a, b])
}

fn build_land_fuel_eq() -> (Expr, Expr) {
    let mut outer = EnvDeclBuilder::new();
    let (width_id, width) = outer.fresh_local(k("Nat"));
    let (a_id, a) = outer.fresh_local(k("Nat"));
    let (b_id, b) = outer.fresh_local(k("Nat"));
    let a_bound = app("Nat.lt", [a.clone(), pow2(width.clone())]);
    let b_bound = app("Nat.lt", [b.clone(), pow2(width.clone())]);
    let (ha_id, ha) = outer.fresh_local(a_bound.clone());
    let (hb_id, hb) = outer.fresh_local(b_bound.clone());
    let limited = aux(width.clone(), a.clone(), b.clone());
    let canonical = app("Nat.land", [a.clone(), b.clone()]);
    let result_bound = app(
        "Nat.land_lt_two_pow",
        [width.clone(), a.clone(), b.clone(), ha, hb],
    );
    let mut bits = EnvDeclBuilder::child_of(&outer);
    let (index_id, index) = bits.fresh_local(k("Nat"));
    let lhs = app("Nat.testBit", [limited.clone(), index.clone()]);
    let rhs = app("Nat.testBit", [canonical.clone(), index.clone()]);
    let goal = eq(k("Bool"), lhs.clone(), rhs.clone());
    let high_type = app("Nat.le", [width.clone(), index.clone()]);
    let low_type = app("Nat.lt", [index.clone(), width.clone()]);
    let alternatives = app("Or", [high_type.clone(), low_type.clone()]);
    let motive = {
        let mut scope = EnvDeclBuilder::child_of(&bits);
        let (id, _) = scope.fresh_local(alternatives.clone());
        scope.finish_child(scope.mk_lam(id, BinderInfo::Default, alternatives, goal))
    };
    let high = {
        let mut scope = EnvDeclBuilder::child_of(&bits);
        let (id, h) = scope.fresh_local(high_type.clone());
        let one = Expr::nat_lit(1);
        let one_le_two = app(
            "Nat.le.step",
            [one.clone(), one.clone(), app("Nat.le.refl", [one])],
        );
        let power_bound = app(
            "Nat.pow_le_pow_right",
            [
                Expr::nat_lit(2),
                width.clone(),
                index.clone(),
                one_le_two,
                h.clone(),
            ],
        );
        let below_index = app(
            "Nat.lt_of_lt_of_le",
            [
                canonical.clone(),
                pow2(width.clone()),
                pow2(index.clone()),
                result_bound,
                power_bound,
            ],
        );
        let rhs_false = app(
            "Nat.testBit_lt_pow",
            [index.clone(), canonical.clone(), below_index],
        );
        let lhs_false = app(
            "Nat.testBit_bitwiseAux_high",
            [
                k("Bool.and"),
                width.clone(),
                index.clone(),
                a.clone(),
                b.clone(),
                h,
            ],
        );
        let proof = trans_bool(
            lhs.clone(),
            k("Bool.false"),
            rhs.clone(),
            lhs_false,
            symm_bool(rhs.clone(), k("Bool.false"), rhs_false),
        );
        scope.finish_child(scope.mk_lam(id, BinderInfo::Default, high_type.clone(), proof))
    };
    let low = {
        let mut scope = EnvDeclBuilder::child_of(&bits);
        let (id, h) = scope.fresh_local(low_type.clone());
        let middle = app(
            "Bool.and",
            [
                app("Nat.testBit", [a.clone(), index.clone()]),
                app("Nat.testBit", [b.clone(), index.clone()]),
            ],
        );
        let lhs_middle = app(
            "Nat.testBit_bitwiseAux",
            [
                k("Bool.and"),
                width.clone(),
                index.clone(),
                a.clone(),
                b.clone(),
                h,
            ],
        );
        let rhs_middle = app("Nat.testBit_and", [a, b, index.clone()]);
        let proof = trans_bool(
            lhs,
            middle.clone(),
            rhs.clone(),
            lhs_middle,
            symm_bool(rhs, middle, rhs_middle),
        );
        scope.finish_child(scope.mk_lam(id, BinderInfo::Default, low_type.clone(), proof))
    };
    let split = app("Nat.le_or_lt", [width, index]);
    let bit_proof = app("Or.rec", [high_type, low_type, motive, high, low, split]);
    let bit_proof =
        bits.finish_child(bits.mk_lam(index_id, BinderInfo::Default, k("Nat"), bit_proof));
    let mut proof = app(
        "Nat.eq_of_testBit_eq",
        [limited.clone(), canonical.clone(), bit_proof],
    );
    let mut type_ = eq(k("Nat"), limited, canonical);
    for (id, domain) in [
        (hb_id, b_bound),
        (ha_id, a_bound),
        (b_id, k("Nat")),
        (a_id, k("Nat")),
        (width_id, k("Nat")),
    ] {
        proof = outer.mk_lam(id, BinderInfo::Default, domain.clone(), proof);
        type_ = outer.mk_pi(id, BinderInfo::Default, domain, type_);
    }
    (outer.finish(type_), outer.finish(proof))
}

impl Environment {
    pub(crate) fn register_nat_land_fuel_proof(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_nat_land_bound_proof()?;
        let (type_, value) = build_land_fuel_eq();
        self.ensure_exact_checked_decl(Declaration::Theorem {
            name: Name::from_string("Nat.bitwiseAux_land_eq_of_lt_two_pow"),
            level_params: vec![],
            type_,
            value,
        })?;
        Ok(())
    }
}
