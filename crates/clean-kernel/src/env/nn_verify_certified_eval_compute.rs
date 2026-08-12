// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified computation term builders for concrete NN evaluation.
//!
//! Provides `ComputeConsts` and types for constructing concrete Expr terms:
//! - Rational number literals (`Rat.mk numerator denominator`)
//! - Integer and natural number constructor forms
//! - NNVec type expressions
//! - Equality proof terms (`Eq`, `Eq.refl`)
//!
//! The certified computation approach: construct `output_expr` and
//! `network_applied_to_input` as concrete Expr terms, then prove
//! `output = network(input)` via `@Eq.refl` (kernel definitional equality).
//! The kernel's reduction engine evaluates both sides to normal form and
//! confirms they are identical.
//!
//! Part of #3186.

#[cfg(test)]
use crate::expr::{Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Constants used for building concrete computation terms.
#[cfg(test)]
pub(crate) struct ComputeConsts {
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) nat: Expr,
    pub(crate) rat: Expr,
    pub(crate) fin: Expr,
    pub(crate) type0: Expr,
    pub(crate) rat_mk: Expr,
    pub(crate) int_of_nat: Expr,
    pub(crate) int_neg_succ: Expr,
    pub(crate) nat_zero: Expr,
    pub(crate) nat_succ: Expr,
    pub(crate) nn_vec: Expr,
    pub(crate) rat_zero: Expr,
    pub(crate) eq: Expr,
    pub(crate) eq_refl: Expr,
}

#[cfg(test)]
impl ComputeConsts {
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            eq_refl: Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
        }
    }

    /// Build a Nat literal as `Nat.succ^n(Nat.zero)`.
    ///
    /// Uses the constructor form rather than `Expr::nat_lit` because
    /// `Rat.mk` expects `Int` and `Nat` in constructor form for
    /// definitional reduction to work through `Rat.rec`.
    #[cfg(test)]
    pub(crate) fn mk_nat(&self, n: u64) -> Expr {
        let mut result = self.nat_zero.clone();
        for _ in 0..n {
            result = Expr::app(self.nat_succ.clone(), result);
        }
        result
    }

    /// Build a non-negative Int literal: `Int.ofNat (Nat.succ^n(Nat.zero))`.
    #[cfg(test)]
    pub(crate) fn mk_int_pos(&self, n: u64) -> Expr {
        Expr::app(self.int_of_nat.clone(), self.mk_nat(n))
    }

    /// Build a negative Int literal: `Int.negSucc (Nat.succ^(n-1)(Nat.zero))`.
    ///
    /// `Int.negSucc k` represents `-(k+1)`, so for value `-v` pass `v-1`.
    #[cfg(test)]
    pub(crate) fn mk_int_neg(&self, abs_minus_one: u64) -> Expr {
        Expr::app(self.int_neg_succ.clone(), self.mk_nat(abs_minus_one))
    }

    /// Build a rational literal: `Rat.mk numerator denominator`.
    ///
    /// `numerator` is an Int (positive or negative).
    /// `denominator` is a Nat (always positive).
    #[cfg(test)]
    pub(crate) fn mk_rat(&self, num: i64, denom: u64) -> Expr {
        let num_expr = if num >= 0 {
            self.mk_int_pos(num as u64)
        } else {
            // Int.negSucc k = -(k+1), so for -v we need k = v-1
            let abs_val = num.unsigned_abs();
            self.mk_int_neg(abs_val - 1)
        };
        let denom_expr = self.mk_nat(denom);
        Expr::app(Expr::app(self.rat_mk.clone(), num_expr), denom_expr)
    }

    /// Build `NNVec n` type expression.
    #[cfg(test)]
    pub(crate) fn vec_type(&self, n: u64) -> Expr {
        Expr::app(self.nn_vec.clone(), self.mk_nat(n))
    }

    /// Build `@Eq Rat a b`.
    #[cfg(test)]
    pub(crate) fn mk_rat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), a),
            b,
        )
    }

    /// Build `@Eq.refl Rat value`.
    #[cfg(test)]
    pub(crate) fn mk_rat_refl(&self, value: Expr) -> Expr {
        Expr::app(Expr::app(self.eq_refl.clone(), self.rat.clone()), value)
    }
}

/// A certified computation instance for a concrete network evaluation.
///
/// Captures: network function, input, expected output, and the proof term
/// certifying that `network(input) = output`.
#[cfg(test)]
pub(crate) struct CertifiedEvalInstance {
    /// Input dimension.
    pub(crate) input_dim: u64,
    /// Output dimension.
    pub(crate) output_dim: u64,
    /// Name of the registered network function definition.
    pub(crate) network_name: Name,
    /// Name of the registered input vector definition.
    pub(crate) input_name: Name,
    /// Name of the registered output vector definition.
    pub(crate) output_name: Name,
    /// Name of the registered proof theorem.
    pub(crate) proof_name: Name,
}
