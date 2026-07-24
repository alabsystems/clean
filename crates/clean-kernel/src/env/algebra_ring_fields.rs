// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared Ring base field construction for algebra typeclasses.
//!
//! The 17 Ring base fields (add, add_assoc, zero, zero_add, add_zero, add_comm,
//! mul, mul_assoc, one, one_mul, mul_one, zero_mul, mul_zero, left_distrib,
//! right_distrib, neg, add_left_neg) are duplicated across CommRing,
//! IntegralDomain, EuclideanDomain, DivisionRing, and Field. This module
//! extracts the shared construction into a single helper.
//!
//! See issue #2458 for the deduplication rationale.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::name::Name;

/// Result of building the 17 Ring base fields on an `EnvDeclBuilder`.
///
/// Callers get access to key operation expressions (`add`, `zero`, `mul`,
/// `one`) for constructing additional fields that depend on them,
/// plus the full list of field IDs and types for folding the pi chain.
pub(crate) struct RingBaseFields {
    /// The alpha type parameter ID (implicit binder).
    pub(crate) alpha_id: FVarId,
    /// The alpha type expression (FVar).
    pub(crate) alpha: Expr,

    // Key operation expressions needed by callers for extra fields.
    pub(crate) add: Expr,
    pub(crate) zero: Expr,
    pub(crate) mul: Expr,
    pub(crate) one: Expr,

    /// The neg type (α → α), reusable for inv fields in DivisionRing/Field.
    pub(crate) neg_type: Expr,

    /// All 17 field (id, type) pairs in declaration order.
    /// Used by `fold_pi` to build the reverse pi chain.
    fields: Vec<(FVarId, Expr)>,
}

impl RingBaseFields {
    /// Build the 17 Ring base fields on the given `EnvDeclBuilder`.
    ///
    /// The builder must already have been created (via `EnvDeclBuilder::new()`).
    /// This method allocates fresh locals for alpha and all 17 fields on `b`.
    ///
    /// The `eq_const` and `type_u` are pre-built by the caller since they
    /// depend on the universe level parameter.
    #[must_use]
    pub(crate) fn build(b: &mut EnvDeclBuilder, type_u: &Expr, eq_const: &Expr) -> Self {
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());

        // Field 0: add : α → α → α
        let add_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (x_id, _) = s.fresh_local(alpha.clone());
            let (y_id, _) = s.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
            let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (add_id, add) = b.fresh_local(add_type.clone());

        // Field 1: add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
        let add_assoc_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let (bv_id, bv) = s.fresh_local(alpha.clone());
            let (c_id, c) = s.fresh_local(alpha.clone());
            let add_a_b = Expr::app(Expr::app(add.clone(), a.clone()), bv.clone());
            let lhs = Expr::app(Expr::app(add.clone(), add_a_b), c.clone());
            let add_b_c = Expr::app(Expr::app(add.clone(), bv), c);
            let rhs = Expr::app(Expr::app(add.clone(), a), add_b_c);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                rhs,
            );
            let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
            let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (add_assoc_id, _) = b.fresh_local(add_assoc_type.clone());

        // Field 2: zero : α
        let (zero_id, zero) = b.fresh_local(alpha.clone());

        // Field 3: zero_add : ∀ a, add zero a = a
        let zero_add_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let lhs = Expr::app(Expr::app(add.clone(), zero.clone()), a.clone());
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                a,
            );
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
            s.finish_child(r)
        };
        let (zero_add_id, _) = b.fresh_local(zero_add_type.clone());

        // Field 4: add_zero : ∀ a, add a zero = a
        let add_zero_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let lhs = Expr::app(Expr::app(add.clone(), a.clone()), zero.clone());
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                a,
            );
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
            s.finish_child(r)
        };
        let (add_zero_id, _) = b.fresh_local(add_zero_type.clone());

        // Field 5: add_comm : ∀ a b, add a b = add b a
        let add_comm_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let (bv_id, bv) = s.fresh_local(alpha.clone());
            let lhs = Expr::app(Expr::app(add.clone(), a.clone()), bv.clone());
            let rhs = Expr::app(Expr::app(add.clone(), bv), a);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                rhs,
            );
            let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), eq);
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (add_comm_id, _) = b.fresh_local(add_comm_type.clone());

        // Field 6: mul : α → α → α
        let mul_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (x_id, _) = s.fresh_local(alpha.clone());
            let (y_id, _) = s.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
            let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (mul_id, mul) = b.fresh_local(mul_type.clone());

        // Field 7: mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
        let mul_assoc_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let (bv_id, bv) = s.fresh_local(alpha.clone());
            let (c_id, c) = s.fresh_local(alpha.clone());
            let mul_a_b = Expr::app(Expr::app(mul.clone(), a.clone()), bv.clone());
            let lhs = Expr::app(Expr::app(mul.clone(), mul_a_b), c.clone());
            let mul_b_c = Expr::app(Expr::app(mul.clone(), bv), c);
            let rhs = Expr::app(Expr::app(mul.clone(), a), mul_b_c);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                rhs,
            );
            let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
            let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (mul_assoc_id, _) = b.fresh_local(mul_assoc_type.clone());

        // Field 8: one : α
        let (one_id, one) = b.fresh_local(alpha.clone());

        // Field 9: one_mul : ∀ a, mul one a = a
        let one_mul_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let lhs = Expr::app(Expr::app(mul.clone(), one.clone()), a.clone());
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                a,
            );
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
            s.finish_child(r)
        };
        let (one_mul_id, _) = b.fresh_local(one_mul_type.clone());

        // Field 10: mul_one : ∀ a, mul a one = a
        let mul_one_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let lhs = Expr::app(Expr::app(mul.clone(), a.clone()), one.clone());
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                a,
            );
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
            s.finish_child(r)
        };
        let (mul_one_id, _) = b.fresh_local(mul_one_type.clone());

        // Field 11: zero_mul : ∀ a, mul zero a = zero
        let zero_mul_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let lhs = Expr::app(Expr::app(mul.clone(), zero.clone()), a);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                zero.clone(),
            );
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
            s.finish_child(r)
        };
        let (zero_mul_id, _) = b.fresh_local(zero_mul_type.clone());

        // Field 12: mul_zero : ∀ a, mul a zero = zero
        let mul_zero_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let lhs = Expr::app(Expr::app(mul.clone(), a), zero.clone());
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                zero.clone(),
            );
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
            s.finish_child(r)
        };
        let (mul_zero_id, _) = b.fresh_local(mul_zero_type.clone());

        // Field 13: left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
        let left_distrib_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let (bv_id, bv) = s.fresh_local(alpha.clone());
            let (c_id, c) = s.fresh_local(alpha.clone());
            let add_b_c = Expr::app(Expr::app(add.clone(), bv.clone()), c.clone());
            let lhs = Expr::app(Expr::app(mul.clone(), a.clone()), add_b_c);
            let mul_a_b = Expr::app(Expr::app(mul.clone(), a.clone()), bv);
            let mul_a_c = Expr::app(Expr::app(mul.clone(), a), c);
            let rhs = Expr::app(Expr::app(add.clone(), mul_a_b), mul_a_c);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                rhs,
            );
            let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
            let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (left_distrib_id, _) = b.fresh_local(left_distrib_type.clone());

        // Field 14: right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
        let right_distrib_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let (bv_id, bv) = s.fresh_local(alpha.clone());
            let (c_id, c) = s.fresh_local(alpha.clone());
            let add_a_b = Expr::app(Expr::app(add.clone(), a.clone()), bv.clone());
            let lhs = Expr::app(Expr::app(mul.clone(), add_a_b), c.clone());
            let mul_a_c = Expr::app(Expr::app(mul.clone(), a), c.clone());
            let mul_b_c = Expr::app(Expr::app(mul.clone(), bv), c);
            let rhs = Expr::app(Expr::app(add.clone(), mul_a_c), mul_b_c);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                rhs,
            );
            let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
            let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (right_distrib_id, _) = b.fresh_local(right_distrib_type.clone());

        // Field 15: neg : α → α
        let neg_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (x_id, _) = s.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };
        let (neg_id, neg) = b.fresh_local(neg_type.clone());

        // Field 16: add_left_neg : ∀ a, add (neg a) a = zero
        let add_left_neg_type = {
            let mut s = EnvDeclBuilder::child_of(b);
            let (a_id, a) = s.fresh_local(alpha.clone());
            let neg_a = Expr::app(neg.clone(), a.clone());
            let lhs = Expr::app(Expr::app(add.clone(), neg_a), a);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                zero.clone(),
            );
            let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
            s.finish_child(r)
        };
        let (add_left_neg_id, _) = b.fresh_local(add_left_neg_type.clone());

        let fields = vec![
            (add_id, add_type.clone()),
            (add_assoc_id, add_assoc_type),
            (zero_id, alpha.clone()), // zero : α
            (zero_add_id, zero_add_type),
            (add_zero_id, add_zero_type),
            (add_comm_id, add_comm_type),
            (mul_id, mul_type.clone()),
            (mul_assoc_id, mul_assoc_type),
            (one_id, alpha.clone()), // one : α
            (one_mul_id, one_mul_type),
            (mul_one_id, mul_one_type),
            (zero_mul_id, zero_mul_type),
            (mul_zero_id, mul_zero_type),
            (left_distrib_id, left_distrib_type),
            (right_distrib_id, right_distrib_type),
            (neg_id, neg_type.clone()),
            (add_left_neg_id, add_left_neg_type),
        ];

        RingBaseFields {
            alpha_id,
            alpha,
            add,
            zero,
            mul,
            one,
            neg_type,
            fields,
        }
    }

    /// Fold the reverse pi chain for all 17 Ring base fields.
    ///
    /// Given an expression `inner` (the result type or continuation from
    /// extra fields), wraps it in `Π (field_16 : T_16), ... Π (field_0 : T_0),
    /// Π {α : Type u}, inner`.
    ///
    /// This produces the standard Ring field prefix used by CommRing,
    /// IntegralDomain, EuclideanDomain, DivisionRing, and Field.
    pub(crate) fn fold_pi(&self, b: &EnvDeclBuilder, type_u: &Expr, inner: Expr) -> Expr {
        // Fold fields in reverse order (field 16 down to field 0)
        let mut r = inner;
        for (id, ty) in self.fields.iter().rev() {
            r = b.mk_pi(*id, BinderInfo::Default, ty.clone(), r);
        }
        // Close alpha (implicit)
        b.mk_pi(self.alpha_id, BinderInfo::Implicit, type_u.clone(), r)
    }

    /// Build the `mul_comm` field type: `∀ a b, mul a b = mul b a`.
    ///
    /// Many typeclasses (CommRing, IntegralDomain, EuclideanDomain, Field)
    /// include this as their next field after the Ring base.
    pub(crate) fn build_mul_comm_type(&self, b: &EnvDeclBuilder, eq_const: &Expr) -> Expr {
        let mut s = EnvDeclBuilder::child_of(b);
        let (a_id, a) = s.fresh_local(self.alpha.clone());
        let (bv_id, bv) = s.fresh_local(self.alpha.clone());
        let lhs = Expr::app(Expr::app(self.mul.clone(), a.clone()), bv.clone());
        let rhs = Expr::app(Expr::app(self.mul.clone(), bv), a);
        let eq = Expr::app(
            Expr::app(Expr::app(eq_const.clone(), self.alpha.clone()), lhs),
            rhs,
        );
        let r = s.mk_pi(bv_id, BinderInfo::Default, self.alpha.clone(), eq);
        let r = s.mk_pi(a_id, BinderInfo::Default, self.alpha.clone(), r);
        s.finish_child(r)
    }

    /// The canonical 17 Ring base field names, in declaration order.
    pub(crate) fn field_names() -> Vec<Name> {
        vec![
            Name::from_string("add"),           // 0
            Name::from_string("add_assoc"),     // 1
            Name::from_string("zero"),          // 2
            Name::from_string("zero_add"),      // 3
            Name::from_string("add_zero"),      // 4
            Name::from_string("add_comm"),      // 5
            Name::from_string("mul"),           // 6
            Name::from_string("mul_assoc"),     // 7
            Name::from_string("one"),           // 8
            Name::from_string("one_mul"),       // 9
            Name::from_string("mul_one"),       // 10
            Name::from_string("zero_mul"),      // 11
            Name::from_string("mul_zero"),      // 12
            Name::from_string("left_distrib"),  // 13
            Name::from_string("right_distrib"), // 14
            Name::from_string("neg"),           // 15
            Name::from_string("add_left_neg"),  // 16
        ]
    }
}
