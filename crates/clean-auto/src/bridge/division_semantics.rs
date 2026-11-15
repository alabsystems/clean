// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One integer-division meaning for the native and proof-producing SMT routes.

/// Rounding convention of an explicitly identified Lean integer operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum IntDivisionRounding {
    /// `Int.div` and `Int.mod`: quotient toward zero; remainder follows the dividend.
    Truncating,
    /// `Int.ediv` and `Int.emod`: a nonnegative remainder smaller than the divisor's magnitude.
    Euclidean,
}

/// Integer and Boolean term constructors shared by the two SMT transports.
///
/// `div` and `modulo` below have SMT-LIB's Euclidean meaning. Their values at
/// zero may be arbitrary; the public builders remove that ambiguity explicitly.
pub trait IntegerDivisionOps {
    /// A term in the target transport, including its Boolean conditions.
    type Term: Clone;
    /// Integer zero.
    fn zero(&mut self) -> Self::Term;
    /// Integer equality.
    fn eq(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;
    /// Integer strict ordering.
    fn lt(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;
    /// Integer negation.
    fn neg(&mut self, value: Self::Term) -> Self::Term;
    /// Integer multiplication.
    fn mul(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;
    /// Integer subtraction.
    fn sub(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;
    /// SMT-LIB integer division.
    fn div(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;
    /// SMT-LIB integer modulus.
    fn modulo(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;
    /// Select one term using a Boolean condition.
    fn ite(&mut self, condition: Self::Term, yes: Self::Term, no: Self::Term) -> Self::Term;
}

/// Encode Lean's integer quotient, including `a / 0 = 0`.
pub fn integer_quotient<B: IntegerDivisionOps>(
    ops: &mut B,
    lhs: B::Term,
    rhs: B::Term,
    rounding: IntDivisionRounding,
) -> B::Term {
    let zero = ops.zero();
    let divisor_zero = ops.eq(rhs.clone(), zero.clone());
    let quotient = match rounding {
        IntDivisionRounding::Euclidean => ops.div(lhs, rhs),
        IntDivisionRounding::Truncating => {
            let lhs_negative = ops.lt(lhs.clone(), zero.clone());
            let rhs_negative = ops.lt(rhs.clone(), zero.clone());
            let lhs_negated = ops.neg(lhs.clone());
            let rhs_negated = ops.neg(rhs.clone());
            let lhs_magnitude = ops.ite(lhs_negative.clone(), lhs_negated, lhs);
            let rhs_magnitude = ops.ite(rhs_negative.clone(), rhs_negated, rhs);
            let magnitude = ops.div(lhs_magnitude, rhs_magnitude);
            let negative = ops.neg(magnitude.clone());
            let lhs_negative_result =
                ops.ite(rhs_negative.clone(), magnitude.clone(), negative.clone());
            let lhs_nonnegative_result = ops.ite(rhs_negative, negative, magnitude);
            ops.ite(lhs_negative, lhs_negative_result, lhs_nonnegative_result)
        }
    };
    ops.ite(divisor_zero, zero, quotient)
}

/// Encode Lean's integer remainder, including `a % 0 = a`.
pub fn integer_remainder<B: IntegerDivisionOps>(
    ops: &mut B,
    lhs: B::Term,
    rhs: B::Term,
    rounding: IntDivisionRounding,
) -> B::Term {
    match rounding {
        IntDivisionRounding::Truncating => {
            let quotient = integer_quotient(ops, lhs.clone(), rhs.clone(), rounding);
            let product = ops.mul(rhs, quotient);
            ops.sub(lhs, product)
        }
        IntDivisionRounding::Euclidean => {
            let zero = ops.zero();
            let divisor_zero = ops.eq(rhs.clone(), zero);
            let remainder = ops.modulo(lhs.clone(), rhs);
            ops.ite(divisor_zero, lhs, remainder)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A numeric interpretation of SMT integer constructors, with deliberately
    // arbitrary div/mod-by-zero values. Inputs fit i64; i128 keeps every
    // intermediate exact, including abs(i64::MIN) and MIN / -1.
    struct Integers {
        undefined: i128,
    }

    impl IntegerDivisionOps for Integers {
        type Term = i128;
        fn zero(&mut self) -> i128 {
            0
        }
        fn eq(&mut self, lhs: i128, rhs: i128) -> i128 {
            i128::from(lhs == rhs)
        }
        fn lt(&mut self, lhs: i128, rhs: i128) -> i128 {
            i128::from(lhs < rhs)
        }
        fn neg(&mut self, value: i128) -> i128 {
            -value
        }
        fn mul(&mut self, lhs: i128, rhs: i128) -> i128 {
            lhs * rhs
        }
        fn sub(&mut self, lhs: i128, rhs: i128) -> i128 {
            lhs - rhs
        }
        fn div(&mut self, lhs: i128, rhs: i128) -> i128 {
            if rhs == 0 {
                self.undefined
            } else {
                lhs.div_euclid(rhs)
            }
        }
        fn modulo(&mut self, lhs: i128, rhs: i128) -> i128 {
            if rhs == 0 {
                self.undefined
            } else {
                lhs.rem_euclid(rhs)
            }
        }
        fn ite(&mut self, condition: i128, yes: i128, no: i128) -> i128 {
            if condition != 0 {
                yes
            } else {
                no
            }
        }
    }

    #[test]
    fn integer_division_matches_both_lean_conventions_and_totalization() {
        let mut values: Vec<i128> = (-16..=16).collect();
        values.extend([i128::from(i64::MIN), i128::from(i64::MAX)]);
        for undefined in [-91, 0, 123] {
            let mut ops = Integers { undefined };
            for &lhs in &values {
                for &rhs in &values {
                    for rounding in [
                        IntDivisionRounding::Truncating,
                        IntDivisionRounding::Euclidean,
                    ] {
                        let quotient = integer_quotient(&mut ops, lhs, rhs, rounding);
                        let remainder = integer_remainder(&mut ops, lhs, rhs, rounding);
                        let expected = if rhs == 0 {
                            (0, lhs)
                        } else {
                            match rounding {
                                IntDivisionRounding::Truncating => (lhs / rhs, lhs % rhs),
                                IntDivisionRounding::Euclidean => {
                                    (lhs.div_euclid(rhs), lhs.rem_euclid(rhs))
                                }
                            }
                        };
                        assert_eq!(
                            (quotient, remainder),
                            expected,
                            "{lhs}, {rhs}, {rounding:?}"
                        );
                        assert_eq!(lhs, rhs * quotient + remainder);
                    }
                }
            }
        }
    }
}
