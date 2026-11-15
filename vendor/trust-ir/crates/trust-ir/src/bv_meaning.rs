// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The ONE bit-vector statement of what an integer compare means.
//!
//! [`icmp_holds`] states `ICmp`'s predicate in the SMT-LIB QF_BV operators
//! (`=`, `not`, `bvult`, `bvule`, `bvugt`, `bvuge`, `bvslt`, `bvsle`, `bvsgt`,
//! `bvsge`); [`vector_icmp`] lifts it lane-wise over a vector whose lane `i`
//! occupies bits `[i*w, i*w + w)` of the vector's image (lane 0 least
//! significant, the byte image the reference interpreter stores and loads);
//! [`concat_lanes`] recomposes lanes as `concat(l_{n-1}, … concat(l_1, l_0))`.
//! The statement is generic over an algebra ([`BvCompare`] for the predicate
//! half, [`BvVector`] for the layout and carrier half), so a consumer gets the
//! format's meaning as a term of ITS OWN solver language instead of
//! restating it: trust-cg instantiates it over its `SmtExpr`, and the x86-64
//! vector-compare cell's spec side is
//! [`chc_x86_vector_icmp_spec`](crate::request::chc_x86_vector_icmp_spec).
//! [`Concrete`] is the executable instance: bit patterns and `bool`s.
//!
//! # The instance contract
//!
//! * An instance whose job is to PRINT the statement (a consumer's term
//!   builder) maps each method to exactly ONE node of its language, the node
//!   the method's SMT-LIB operator names. The certified x86-64 spec bytes are
//!   this statement printed that way; a printing instance that rewrites an
//!   operator (`ult` as `not(uge)`, `ne` as `distinct`) prints different bytes
//!   and is not this statement.
//! * An instance that REWRITES an operator (a bit-blaster spelling `ult` as a
//!   carry-out, a solver's own term graph) is admitted only with a
//!   differential against [`Concrete`] that is exhaustive at 8-bit width,
//!   landed in the instance's own commit.
//!
//! # What this is evidence of
//!
//! The statement's agreement with the format is TEST evidence, not proof:
//! `crates/trust-ir-conformance/tests/icmp_meaning.rs` checks it against the
//! reference interpreter (every pair of 8-bit lanes, sampled at 16, 32 and
//! 64 bits), and `lean_exec_differential.rs`
//! (`vector_icmp_cells_agree_across_engines_and_with_the_statement`) checks
//! both executable engines against it over every x86-64 cell's lane types:
//! each integer type of the cell's lane width the validator admits as a
//! vector lane, signed and unsigned (a cell is keyed by width and count
//! alone). The SMT-LIB operators' own meanings and a consumer's printer stay
//! trusted.

use crate::inst::ICmpOp;

/// The predicate half: the SMT-LIB QF_BV operators the format's integer
/// compare is stated in. One method per operator; both operands of a method
/// have the same width.
pub trait BvCompare {
    /// A bit-vector term.
    type Bv: Clone;
    /// A Boolean term.
    type Bool;
    /// `(= a b)`.
    fn eq(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(not b)`.
    fn not(&mut self, b: Self::Bool) -> Self::Bool;
    /// `(bvult a b)`.
    fn ult(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(bvule a b)`.
    fn ule(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(bvugt a b)`.
    fn ugt(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(bvuge a b)`.
    fn uge(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(bvslt a b)`.
    fn slt(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(bvsle a b)`.
    fn sle(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(bvsgt a b)`.
    fn sgt(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
    /// `(bvsge a b)`.
    fn sge(&mut self, a: Self::Bv, b: Self::Bv) -> Self::Bool;
}

/// The lane half: layout and carrier.
pub trait BvVector: BvCompare {
    /// `(_ bv<value> <width>)`; `value` fits `width` bits, `1 ≤ width ≤ 128`.
    fn bv_const(&mut self, value: u128, width: u32) -> Self::Bv;
    /// `((_ extract high low) v)`, `low ≤ high < width(v)`.
    fn extract(&mut self, v: Self::Bv, high: u32, low: u32) -> Self::Bv;
    /// `(concat high low)`: `high` occupies the most significant bits.
    fn concat(&mut self, high: Self::Bv, low: Self::Bv) -> Self::Bv;
    /// `(ite c t e)` over two bit-vectors of one width.
    fn ite(&mut self, c: Self::Bool, t: Self::Bv, e: Self::Bv) -> Self::Bv;
}

/// `ICmp op l r` holds: the format's integer compare, one QF_BV operator per
/// predicate (`Ne` is `not(eq)`; the unsigned and signed orders are the
/// `bvu*` / `bvs*` operators, never rewritten into one another).
pub fn icmp_holds<A: BvCompare>(a: &mut A, op: ICmpOp, l: A::Bv, r: A::Bv) -> A::Bool {
    match op {
        ICmpOp::Eq => a.eq(l, r),
        ICmpOp::Ne => {
            let eq = a.eq(l, r);
            a.not(eq)
        }
        ICmpOp::Ult => a.ult(l, r),
        ICmpOp::Ule => a.ule(l, r),
        ICmpOp::Ugt => a.ugt(l, r),
        ICmpOp::Uge => a.uge(l, r),
        ICmpOp::Slt => a.slt(l, r),
        ICmpOp::Sle => a.sle(l, r),
        ICmpOp::Sgt => a.sgt(l, r),
        ICmpOp::Sge => a.sge(l, r),
    }
}

/// Lane `i` of a vector image whose lanes are `lane_bits` wide:
/// `extract(v, i*w + w - 1, i*w)`. Lane 0 is the least significant.
pub fn vector_lane<A: BvVector>(a: &mut A, v: &A::Bv, lane_bits: u32, i: u32) -> A::Bv {
    let low = i * lane_bits;
    a.extract(v.clone(), low + lane_bits - 1, low)
}

/// The lane-wise vector compare: lane `i` of the result holds
/// [`icmp_holds`] over lane `i` of each operand ([`vector_lane`]).
pub fn vector_icmp<A: BvVector>(
    a: &mut A,
    op: ICmpOp,
    lane_bits: u32,
    lane_count: u32,
    lhs: &A::Bv,
    rhs: &A::Bv,
) -> Vec<A::Bool> {
    (0..lane_count)
        .map(|i| {
            let l = vector_lane(a, lhs, lane_bits, i);
            let r = vector_lane(a, rhs, lane_bits, i);
            icmp_holds(a, op, l, r)
        })
        .collect()
}

/// Recompose lanes into one image, lane 0 least significant:
/// `concat(l_{n-1}, … concat(l_1, l_0))`.
///
/// # Panics
///
/// On an empty lane list: a vector has at least one lane.
pub fn concat_lanes<A: BvVector>(a: &mut A, lanes: Vec<A::Bv>) -> A::Bv {
    let mut lanes = lanes.into_iter();
    let mut image = lanes
        .next()
        .expect("concat_lanes: a vector has at least one lane");
    for lane in lanes {
        image = a.concat(lane, image);
    }
    image
}

/// The executable instance: a bit-vector is `(bits, width)` with `bits` below
/// `2^width`, a Boolean is a `bool`. Every operation asserts its width
/// preconditions, so a statement that combines mismatched widths panics
/// rather than computing a value.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Concrete;

/// `2^width - 1`, the all-ones pattern of `width` bits (`1 ≤ width ≤ 128`).
#[must_use]
pub const fn all_ones(width: u32) -> u128 {
    assert!(
        width >= 1 && width <= 128,
        "a bit-vector is 1 to 128 bits wide"
    );
    if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

impl Concrete {
    fn same_width(a: (u128, u32), b: (u128, u32)) -> u32 {
        assert_eq!(a.1, b.1, "QF_BV operands of one operator have one width");
        a.1
    }

    /// The two's-complement value of `bits` at `width`.
    fn signed(bits: u128, width: u32) -> i128 {
        let shift = 128 - width;
        ((bits << shift) as i128) >> shift
    }
}

impl BvCompare for Concrete {
    type Bv = (u128, u32);
    type Bool = bool;

    fn eq(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        Self::same_width(a, b);
        a.0 == b.0
    }

    fn not(&mut self, b: bool) -> bool {
        !b
    }

    fn ult(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        Self::same_width(a, b);
        a.0 < b.0
    }

    fn ule(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        Self::same_width(a, b);
        a.0 <= b.0
    }

    fn ugt(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        Self::same_width(a, b);
        a.0 > b.0
    }

    fn uge(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        Self::same_width(a, b);
        a.0 >= b.0
    }

    fn slt(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        let w = Self::same_width(a, b);
        Self::signed(a.0, w) < Self::signed(b.0, w)
    }

    fn sle(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        let w = Self::same_width(a, b);
        Self::signed(a.0, w) <= Self::signed(b.0, w)
    }

    fn sgt(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        let w = Self::same_width(a, b);
        Self::signed(a.0, w) > Self::signed(b.0, w)
    }

    fn sge(&mut self, a: Self::Bv, b: Self::Bv) -> bool {
        let w = Self::same_width(a, b);
        Self::signed(a.0, w) >= Self::signed(b.0, w)
    }
}

impl BvVector for Concrete {
    fn bv_const(&mut self, value: u128, width: u32) -> Self::Bv {
        assert!(value <= all_ones(width), "the constant fits its width");
        (value, width)
    }

    fn extract(&mut self, v: Self::Bv, high: u32, low: u32) -> Self::Bv {
        assert!(low <= high && high < v.1, "extract stays inside the vector");
        let width = high - low + 1;
        ((v.0 >> low) & all_ones(width), width)
    }

    fn concat(&mut self, high: Self::Bv, low: Self::Bv) -> Self::Bv {
        let width = high.1 + low.1;
        assert!(width <= 128, "a concatenation is at most 128 bits wide");
        ((high.0 << low.1) | low.0, width)
    }

    fn ite(&mut self, c: bool, t: Self::Bv, e: Self::Bv) -> Self::Bv {
        Self::same_width(t, e);
        if c { t } else { e }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL_OPS: [ICmpOp; 10] = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];

    /// Rust's own `u8` / `i8` comparisons: an oracle independent of the
    /// statement's method dispatch.
    fn native_u8_i8(op: ICmpOp, a: u8, b: u8) -> bool {
        let (sa, sb) = (a as i8, b as i8);
        match op {
            ICmpOp::Eq => a == b,
            ICmpOp::Ne => a != b,
            ICmpOp::Ult => a < b,
            ICmpOp::Ule => a <= b,
            ICmpOp::Ugt => a > b,
            ICmpOp::Uge => a >= b,
            ICmpOp::Slt => sa < sb,
            ICmpOp::Sle => sa <= sb,
            ICmpOp::Sgt => sa > sb,
            ICmpOp::Sge => sa >= sb,
        }
    }

    /// The statement over `Concrete` is the native compare on every 8-bit pair.
    #[test]
    fn icmp_holds_is_the_native_compare_at_8_bits_exhaustively() {
        let mut c = Concrete;
        for op in ALL_OPS {
            for a in 0..=u8::MAX {
                for b in 0..=u8::MAX {
                    let got = icmp_holds(&mut c, op, (u128::from(a), 8), (u128::from(b), 8));
                    assert_eq!(got, native_u8_i8(op, a, b), "{op:?} {a} {b}");
                }
            }
        }
    }

    /// The 128-bit edges, where the sign extension is the identity shift.
    #[test]
    fn signed_order_at_128_bits() {
        let mut c = Concrete;
        let min = (1u128 << 127, 128);
        let max = (u128::MAX >> 1, 128);
        let minus_one = (u128::MAX, 128);
        assert!(c.slt(min, max));
        assert!(c.slt(minus_one, (0, 128)));
        assert!(c.ugt(minus_one, (0, 128)));
        assert!(c.sgt(max, minus_one));
    }

    /// Lanes are read least significant first, and `concat_lanes` puts them
    /// back where `vector_lane` found them.
    #[test]
    fn lanes_round_trip_lane0_least_significant() {
        let mut c = Concrete;
        let image = (0x0403_0201u128, 32);
        let lanes: Vec<_> = (0..4).map(|i| vector_lane(&mut c, &image, 8, i)).collect();
        assert_eq!(lanes, vec![(1, 8), (2, 8), (3, 8), (4, 8)]);
        assert_eq!(concat_lanes(&mut c, lanes), image);
    }

    #[test]
    fn vector_icmp_is_lane_wise() {
        let mut c = Concrete;
        // lhs lanes (lane 0 first): 0xff, 0x01; rhs lanes: 0x00, 0x02.
        let lhs = (0x01ffu128, 16);
        let rhs = (0x0200u128, 16);
        assert_eq!(
            vector_icmp(&mut c, ICmpOp::Ugt, 8, 2, &lhs, &rhs),
            vec![true, false]
        );
        assert_eq!(
            vector_icmp(&mut c, ICmpOp::Sgt, 8, 2, &lhs, &rhs),
            vec![false, false]
        );
    }
}
