// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared symbol bundle, per-component term extractor, Int-arithmetic
//! shortcuts, and motive builders used by the `Rat.add_assoc` proof
//! stages in `h_num.rs` and by the top-level registration in `mod.rs`.
//!
//! Factored out so `mod.rs` stays under the 500-line file-size budget
//! and each function stays under the 80-line function-size budget.

#![allow(non_snake_case)]

use super::super::algebra_rat_tranche_b_proofs::{mk_congr_arg, mk_eq_trans, TrancheBSymbols};
use super::super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Extended symbol bundle: TrancheB helpers plus the extra Int axioms used
/// by the assoc proof.
pub(super) struct AddAssocSymbols {
    pub(super) tb: TrancheBSymbols,
    pub(super) rat_add: Expr,
    pub(super) int_add_assoc: Expr,
    pub(super) int_mul_assoc: Expr,
    pub(super) int_mul_comm: Expr,
    pub(super) int_right_distrib: Expr,
    pub(super) int_ofnat_mul: Expr,
    pub(super) nat_mul_assoc: Expr,
    pub(super) eq_symm: Expr,
}

impl AddAssocSymbols {
    pub(super) fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            tb: TrancheBSymbols::new(),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            int_add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            int_mul_assoc: Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
            int_mul_comm: Expr::const_(Name::from_string("Int.mul_comm"), vec![]),
            int_right_distrib: Expr::const_(Name::from_string("Int.right_distrib"), vec![]),
            int_ofnat_mul: Expr::const_(Name::from_string("Int.ofNat_mul"), vec![]),
            nat_mul_assoc: Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
        }
    }
}

/// Extracted per-Rat component terms used throughout the proof body.
pub(super) struct Terms {
    pub(super) n_a: Expr, // Rat.num a
    pub(super) n_b: Expr, // Rat.num b
    pub(super) n_c: Expr, // Rat.num c
    pub(super) d_a: Expr, // Rat.denom a
    pub(super) d_b: Expr, // Rat.denom b
    pub(super) d_c: Expr, // Rat.denom c
    pub(super) p_a: Expr, // Int.ofNat (Rat.denom a)
    pub(super) p_b: Expr, // Int.ofNat (Rat.denom b)
    pub(super) p_c: Expr, // Int.ofNat (Rat.denom c)
}

pub(super) fn extract_terms(sym: &AddAssocSymbols, a: &Expr, bv: &Expr, c: &Expr) -> Terms {
    let n_a = Expr::app(sym.tb.rat_num.clone(), a.clone());
    let n_b = Expr::app(sym.tb.rat_num.clone(), bv.clone());
    let n_c = Expr::app(sym.tb.rat_num.clone(), c.clone());
    let d_a = Expr::app(sym.tb.rat_denom.clone(), a.clone());
    let d_b = Expr::app(sym.tb.rat_denom.clone(), bv.clone());
    let d_c = Expr::app(sym.tb.rat_denom.clone(), c.clone());
    let p_a = Expr::app(sym.tb.int_of_nat.clone(), d_a.clone());
    let p_b = Expr::app(sym.tb.int_of_nat.clone(), d_b.clone());
    let p_c = Expr::app(sym.tb.int_of_nat.clone(), d_c.clone());
    Terms {
        n_a,
        n_b,
        n_c,
        d_a,
        d_b,
        d_c,
        p_a,
        p_b,
        p_c,
    }
}

/// Shorthand: `Int.mul x y`.
pub(super) fn i_mul(sym: &AddAssocSymbols, x: Expr, y: Expr) -> Expr {
    Expr::app(Expr::app(sym.tb.int_mul.clone(), x), y)
}

/// Shorthand: `Int.add x y`.
pub(super) fn i_add(sym: &AddAssocSymbols, x: Expr, y: Expr) -> Expr {
    Expr::app(Expr::app(sym.tb.int_add.clone(), x), y)
}

/// Shorthand: `Nat.mul x y`.
pub(super) fn n_mul(sym: &AddAssocSymbols, x: Expr, y: Expr) -> Expr {
    Expr::app(Expr::app(sym.tb.nat_mul.clone(), x), y)
}

/// Build the lambda motive `fun z : Int => Int.add z rhs_fixed`.
pub(super) fn motive_add_left(sym: &AddAssocSymbols, b: &EnvDeclBuilder, rhs_fixed: &Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (z_id, z) = fb.fresh_local(sym.tb.int_type.clone());
    let body = i_add(sym, z, rhs_fixed.clone());
    let lam = fb.mk_lam(z_id, BinderInfo::Default, sym.tb.int_type.clone(), body);
    fb.finish_child(lam)
}

/// Build the lambda motive `fun z : Int => Int.add lhs_fixed z`.
pub(super) fn motive_add_right(
    sym: &AddAssocSymbols,
    b: &EnvDeclBuilder,
    lhs_fixed: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (z_id, z) = fb.fresh_local(sym.tb.int_type.clone());
    let body = i_add(sym, lhs_fixed.clone(), z);
    let lam = fb.mk_lam(z_id, BinderInfo::Default, sym.tb.int_type.clone(), body);
    fb.finish_child(lam)
}

/// Build the lambda motive `fun z : Int => Int.mul lhs_fixed z`.
pub(super) fn motive_mul_right(
    sym: &AddAssocSymbols,
    b: &EnvDeclBuilder,
    lhs_fixed: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (z_id, z) = fb.fresh_local(sym.tb.int_type.clone());
    let body = i_mul(sym, lhs_fixed.clone(), z);
    let lam = fb.mk_lam(z_id, BinderInfo::Default, sym.tb.int_type.clone(), body);
    fb.finish_child(lam)
}

/// Wrap `h : Eq α x y` into `Eq.symm h : Eq α y x`.
pub(super) fn eq_symm_of(sym: &AddAssocSymbols, alpha: &Expr, x: Expr, y: Expr, h: Expr) -> Expr {
    Expr::apps(sym.eq_symm.clone(), [alpha.clone(), x, y, h])
}

/// `congrArg` lifted for Int→Int motives (both domains at Type 0).
pub(super) fn int_congr(
    sym: &AddAssocSymbols,
    lhs: Expr,
    rhs: Expr,
    motive: Expr,
    h: Expr,
) -> Expr {
    mk_congr_arg(
        &sym.tb,
        &sym.tb.int_type,
        &sym.tb.int_type,
        lhs,
        rhs,
        motive,
        h,
    )
}

/// `Eq.trans` at `Int`.
pub(super) fn int_trans(
    sym: &AddAssocSymbols,
    a: Expr,
    b: Expr,
    c: Expr,
    hab: Expr,
    hbc: Expr,
) -> Expr {
    mk_eq_trans(&sym.tb, &sym.tb.int_type, a, b, c, hab, hbc)
}
