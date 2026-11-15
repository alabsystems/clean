use super::{assert_eq, assert_num_args, first_conclusion_literal, RuleArgs, RuleResult};
use crate::{
    ast::{
        build_term, match_term, match_term_err, pool::TermPool, Binder, ParamOperator, Rc, Sort,
        Term,
    },
    checker::{
        budget::{is_two_to_the, ExpansionBudget},
        error::CheckerError,
        rules::cutting_planes::split_summation,
    },
};
use rug::Integer;

// Modified in Clean: every rule here reads its conclusion through `first_conclusion_literal`. They
// indexed `conclusion[0]` without checking the clause length, so a step concluding `(cl)` panicked
// (see third-party/carcara/DOWNSTREAM.md, "Malformed steps are refused, not a panic").
//
// Modified in Clean: `pbblast_bvand` and `pbblast_bvxor` charge the bits of their operands, split
// or spelled out as `@pbbterm`, to an `ExpansionBudget`, and a coefficient is compared with `2^i` without computing `2^i`, whose
// `i` the signed rules take from a sort of any width. See checker/budget.rs and
// third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource budget".

/// Helper to get the bit width of a bitvector looking into the pool
fn get_bit_width(x: &Rc<Term>, pool: &mut dyn TermPool) -> Result<usize, CheckerError> {
    // Get bit width of `x`
    let Sort::BitVec(n) = pool.sort(x).as_ref().clone() else {
        return Err(CheckerError::Explanation(
            "Was not able to get the bitvector sort".into(),
        ));
    };
    Ok(n)
}

// Helper to check that a summation has the expected shape
fn check_pbblast_sum(
    pool: &mut dyn TermPool,
    bitvector: &Rc<Term>,
    sum: &[Rc<Term>],
    signed: bool,
) -> RuleResult {
    // Obtain the bitvector width from the pool. A signed relation sums all bits but the sign bit.
    // Modified in Clean: a width with no bit to drop is refused, not an underflow.
    let width = get_bit_width(bitvector, pool)?
        .checked_sub(usize::from(signed))
        .ok_or_else(|| CheckerError::Explanation("No sign bit in bit-vector".into()))?;

    // Modified in Clean: the summation must have exactly one summand per bit. With fewer summands
    // the high bits are dropped, and distinct bit-vectors get equal sums (see
    // third-party/carcara/DOWNSTREAM.md).
    rassert!(
        width == sum.len(),
        CheckerError::Explanation(format!(
            "Mismatched number of summands {} and bits {}",
            width,
            sum.len()
        ))
    );

    for (i, element) in sum.iter().enumerate() {
        // Try to match (* c ((_ @int_of idx) bv))
        let (c, idx, bv) = match match_term!((* c ((_ int_of idx) bv)) = element) {
            Some((c, idx, bv)) => (c.as_integer_err()?, idx, bv),
            None => {
                if i == 0 {
                    // For i==0, allow the coefficient to be omitted (defaulting to 1)
                    match match_term!(((_ int_of idx) bitvector) = element) {
                        Some((idx, bv)) => (Integer::from(1), idx, bv),
                        None => {
                            return Err(CheckerError::Explanation(
                                "Summand does not match either pattern".into(),
                            ));
                        }
                    }
                } else {
                    return Err(CheckerError::Explanation(
                        "Coefficient was not found and i != 0".into(),
                    ));
                }
            }
        };

        // Convert the index term to an integer.
        let idx: Integer = idx.as_integer_err()?;
        // Check that the coefficient is 2^i.
        rassert!(
            is_two_to_the(&c, i),
            CheckerError::Explanation(format!("Coefficient {} is not 2^{}", c, i))
        );
        // Check that the index is i.
        rassert!(
            idx == i,
            CheckerError::Explanation(format!("Index {} is not {}", idx, i))
        );
        // Finally, the bitvector in the summand must be the one we expect.
        rassert!(
            *bv == *bitvector,
            CheckerError::Explanation(format!("Wrong bitvector in blasting {} {}", bv, bitvector))
        );
    }
    Ok(())
}

// Helper to check that a summation has the expected shape
// when the bitvector is a @pbbterm application "short-circuiting"
fn check_pbblast_sum_short_circuit(
    pbbterm: &[Rc<Term>],
    sum: &[Rc<Term>],
    signed: bool,
) -> RuleResult {
    // Modified in Clean: as in `check_pbblast_sum`.
    let bits = pbbterm
        .len()
        .checked_sub(usize::from(signed))
        .ok_or_else(|| CheckerError::Explanation("No sign bit in pbbterm".into()))?;
    // Modified in Clean: exactly one summand per bit, as above.
    rassert!(
        bits == sum.len(),
        CheckerError::Explanation(format!(
            "Mismatched number of summands {} and bits {}",
            bits,
            sum.len()
        ))
    );

    for (i, element) in sum.iter().enumerate() {
        // Try to match (* c bv))
        let (c, bv) = match match_term!((* c bv) = element) {
            Some((c, bv)) => (c.as_integer_err()?, bv),
            None => {
                if i == 0 {
                    (Integer::from(1), element)
                } else {
                    return Err(CheckerError::Explanation(
                        "Coefficient was not found and i != 0".into(),
                    ));
                }
            }
        };

        // Check that the coefficient is 2^i.
        rassert!(
            is_two_to_the(&c, i),
            CheckerError::Explanation(format!("Coefficient {} is not 2^{}", c, i))
        );

        assert_eq(bv, &pbbterm[i])?;
    }
    Ok(())
}

/// A helper that checks the two summations that occur in a pseudo–Boolean constraint.
/// Here, `left_sum` and `right_sum` come from two bitvectors `left_bv` and `right_bv` respectively.
/// (The overall constraint is something like `(>= (- (+ left_sum) (+ right_sum)) constant)`.)
fn check_pbblast_constraint(
    pool: &mut dyn TermPool,
    left_bv: &Rc<Term>,
    right_bv: &Rc<Term>,
    left_sum: &[Rc<Term>],
    right_sum: &[Rc<Term>],
    signed: bool,
) -> RuleResult {
    if let Some(pbb_l) = match_term!((pbbterm ...) = left_bv) {
        // Case when x is application of `@pbbterm` so we must short-circuit the indexing
        let pbb_r = match_term_err!((pbbterm ...) = right_bv)?;
        check_pbblast_sum_short_circuit(pbb_l, left_sum, signed)?;
        check_pbblast_sum_short_circuit(pbb_r, right_sum, signed)
    } else {
        check_pbblast_sum(pool, left_bv, left_sum, signed)?;
        check_pbblast_sum(pool, right_bv, right_sum, signed)
    }
}

/// Implements the equality rule
/// The expected shape is:
///    `(= (= x y) (= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bveq(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_x, sum_y) =
        match_term_err!((= (= x y) (= (- sum_x sum_y) 0)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    // Check that the summations have the correct structure.
    // (For equality the order is: sum_x for x and sum_y for y.)
    check_pbblast_constraint(pool, x, y, sum_x, sum_y, false)
}

/// Implements the unsigned-less-than rule.
/// The expected shape is:
///    `(= (bvult x y) (>= (- (+ sum_y) (+ sum_x)) 1))`
pub fn pbblast_bvult(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_y, sum_x) = match_term_err!((= (bvult x y) (>= (- sum_y sum_x) 1)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    // For bvult the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x, false)
}

/// Implements the unsigned-greater-than rule.
///
/// The expected shape is:
///    `(= (bvugt x y) (>= (- (+ sum_x) (+ sum_y)) 1))`
pub fn pbblast_bvugt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_x, sum_y) = match_term_err!((= (bvugt x y) (>= (- sum_x sum_y) 1)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    // For bvugt the summations appear in the same order as in equality.
    check_pbblast_constraint(pool, x, y, sum_x, sum_y, false)
}

/// Implements the unsigned-greater-or-equal rule.
///
/// The expected shape is:
///    `(= (bvuge x y) (>= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bvuge(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_x, sum_y) = match_term_err!((= (bvuge x y) (>= (- sum_x sum_y) 0)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    check_pbblast_constraint(pool, x, y, sum_x, sum_y, false)
}

/// Implements the unsigned-less-or-equal rule.
///
/// The expected shape is:
///    `(= (bvule x y) (>= (- (+ sum_y) (+ sum_x)) 0))`
pub fn pbblast_bvule(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_y, sum_x) = match_term_err!((= (bvule x y) (>= (- sum_y sum_x) 0)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    check_pbblast_constraint(pool, x, y, sum_x, sum_y, false)
}

/// Helper that checks the the `sign` term has the format -(2<sup>n-1</sup>) x<sub>n-1</sub>
fn check_pbblast_signed_relation(n: usize, sign: &Rc<Term>, bitvector: &Rc<Term>) -> RuleResult {
    // Modified in Clean: a width with no sign bit is refused, not an underflow of `n - 1`.
    rassert!(
        n > 0,
        CheckerError::Explanation("No sign bit in bit-vector".into())
    );
    // Short-circuited
    if let Some(pbb) = match_term!((pbbterm ...) = bitvector) {
        let last = pbb
            .last()
            .ok_or(CheckerError::Explanation("No sign bit in pbbterm".into()))?;
        let (coeff, sign_bit) = match_term_err!((* coeff sign_bit) = sign)?;
        let coeff = coeff.as_integer_err()?;

        // Check that the coefficient is 2^(n-1)
        rassert!(
            is_two_to_the(&coeff, n - 1), // 2^(n-1)
            CheckerError::Explanation(format!("Expected coefficient 2^{} got {coeff}", (n - 1)))
        );
        return assert_eq(sign_bit, last);
    }

    // Check the signs
    let (coeff, idx, bv) = match_term_err!((* coeff ((_ int_of idx) bv)) = sign)?;
    let coeff = coeff.as_integer_err()?;
    let idx = idx.as_integer_err()?;

    // Check that the coefficient is 2^(n-1)
    rassert!(
        is_two_to_the(&coeff, n - 1), // 2^(n-1)
        CheckerError::Explanation(format!("Expected coefficient 2^{} got {coeff}", (n - 1)))
    );

    // Check that the index is n-1.
    rassert!(
        idx == n - 1,
        CheckerError::Explanation(format!("Index {} is not {}", idx, n - 1))
    );

    // Finally, the bitvector in the term must be the one we expect.
    rassert!(
        *bv == *bitvector,
        CheckerError::Explanation(format!("Wrong bitvector in sign bit {} {}", bv, bitvector))
    );

    Ok(())
}

/// Implements the signed-less-than rule.
///
/// The expected shape is:
///    `(= (bvslt x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 1))`
pub fn pbblast_bvslt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_y, sign_y, sign_x, sum_x) = match_term_err!((= (bvslt x y) (>= (+ (- sum_y sign_y) (- sign_x sum_x)) 1)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_y, y)?;
    check_pbblast_signed_relation(n, sign_x, x)?;

    // For bvult the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x, true)
}

/// Implements the signed-greater-than rule.
///
/// The expected shape is:
///    `(= (bvsgt x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 1))`
pub fn pbblast_bvsgt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_x, sign_x, sign_y, sum_y) = match_term_err!((= (bvsgt x y) (>= (+ (- sum_x sign_x) (- sign_y sum_y)) 1)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    // Get bit width of `x`
    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_x, x)?;
    check_pbblast_signed_relation(n, sign_y, y)?;

    check_pbblast_constraint(pool, x, y, sum_x, sum_y, true)
}

/// Implements the signed-greater-equal rule.
///
/// The expected shape is:
///    `(= (bvsge x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 0))`
pub fn pbblast_bvsge(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_x, sign_x, sign_y, sum_y) = match_term_err!((= (bvsge x y) (>= (+ (- sum_x sign_x) (- sign_y sum_y)) 0)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    // Get bit width of `x`
    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_x, x)?;
    check_pbblast_signed_relation(n, sign_y, y)?;

    check_pbblast_constraint(pool, x, y, sum_x, sum_y, true)
}

/// Implements the signed-less-equal rule.
///
/// The expected shape is:
///    `(= (bvsle x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 0))`
pub fn pbblast_bvsle(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, sum_y, sign_y, sign_x, sum_x) = match_term_err!((= (bvsle x y) (>= (+ (- sum_y sign_y) (- sign_x sum_x)) 0)) = first_conclusion_literal(conclusion)?)?;

    // Get the summation lists
    let sum_x = split_summation(sum_x);
    let sum_y = split_summation(sum_y);

    // Get bit width of `x`
    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_y, y)?;
    check_pbblast_signed_relation(n, sign_x, x)?;

    // For bvsle the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x, true)
}

/// Implements the blasting of a bitvector variable
pub fn pbblast_pbbvar(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, pbs) = match_term_err!((= x (pbbterm ...)) = first_conclusion_literal(conclusion)?)?;

    for (i, pb) in pbs.iter().enumerate() {
        let (idx, bv) = match_term_err!(((_ int_of idx) bv) = pb)?;

        // Convert the index term to an integer.
        let idx: Integer = idx.as_integer_err()?;

        // Check that the index is `i`.
        rassert!(
            idx == i,
            CheckerError::Explanation(format!("Index {} is not {}", idx, i))
        );
        // Finally, the bitvector in the summand must be the one we expect.
        rassert!(
            *bv == *x,
            CheckerError::Explanation(format!("Mismatched bitvectors {} {}", bv, x))
        );
    }
    Ok(())
}

/// Implements the blasting of a constant
pub fn pbblast_pbbconst(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    let (bv, pbs) = match_term_err!((= bv (pbbterm ...)) = first_conclusion_literal(conclusion)?)
        .map_err(|_| CheckerError::Explanation("Malformed @pbbterm equality".into()))?;

    let (m, w) = bv.as_bitvector().ok_or(CheckerError::Explanation(
        "Expected bitvector constant".into(),
    ))?;

    if pbs.len() != w {
        return Err(CheckerError::Explanation(format!(
            "Expected {} @pbbterms, got {}",
            w,
            pbs.len()
        )));
    }

    let computed_value = pbs
        .iter()
        .enumerate()
        .try_fold(Integer::new(), |acc, (i, term)| {
            let pb = term.as_integer().ok_or(CheckerError::Explanation(format!(
                "Non-integer term at position {}",
                i
            )))?;

            // Modified in Clean: compare the integer itself. Wrapping it to `i32` first read
            // `4294967297` as the bit `1`.
            match pb.to_u8().filter(|b| *b <= 1) {
                Some(0) => Ok(acc),
                Some(1) => {
                    // Modified in Clean: a position beyond `u32` is refused, not a panic.
                    let exponent = u32::try_from(i).map_err(|_| {
                        CheckerError::Explanation(format!("Position {} out of range", i))
                    })?;
                    // Modified in Clean: set the bit rather than add a computed `2^i` (time
                    // quadratic in the width); the positions are distinct, so the sum is the same.
                    let mut acc = acc;
                    acc.set_bit(exponent, true);
                    Ok(acc)
                }
                _ => Err(CheckerError::Explanation(format!(
                    "Invalid value {} at position {}",
                    pb, i
                ))),
            }
        })?;

    if computed_value != m {
        return Err(CheckerError::Explanation(format!(
            "Computed value {} != declared value {}",
            computed_value, m
        )));
    }

    Ok(())
}

/// Helper to transform a bitvector to a list of terms, both when short-circuited or not
/// Ex: `get_bitvector_terms(x, 2)`
/// >>> `[((int_of 0) x),((int_of 1) x)]`
///
/// Ex: `get_bitvector_terms((pbbterm @x0 @x1), 2)`
/// >>> `[@x0, @x1]`
// Modified in Clean: a term that is not a bit-vector is refused with the error of `get_bit_width`
// rather than unwrapped (see third-party/carcara/DOWNSTREAM.md).
fn get_bitvector_terms(
    bv: &Rc<Term>,
    pool: &mut dyn TermPool,
    budget: &mut ExpansionBudget,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    Ok(if let Some(xs) = match_term!((pbbterm ...) = bv) {
        budget.spend_width("reading a bit-vector's spelled-out bits", xs.len())?;
        xs.to_vec()
    } else {
        // Get bit width of `x`
        let n = get_bit_width(bv, pool)?;
        budget.spend_width("splitting a bit-vector into its bits", n)?;
        (0..n)
            .map(|i| {
                build_term!(
                    pool,
                    ((_ int_of { pool.add(Term::new_int(i)) }) { bv.clone() })
                )
            })
            .collect()
    })
}

/// Modified in Clean: the `ith_bit` lemmas state that the choice term `z` satisfies its defining
/// constraints, which only has a witness when both arguments are 0/1 valued. The arguments may
/// also not mention a free `z`, which the choice binder would capture (see
/// third-party/carcara/DOWNSTREAM.md).
fn require_bit_arguments(pool: &mut dyn TermPool, x: &Rc<Term>, y: &Rc<Term>) -> RuleResult {
    for arg in [x, y] {
        let is_bit = arg.as_integer().is_some_and(|i| i == 0 || i == 1)
            || matches!(arg.as_ref(), Term::ParamOp { op: ParamOperator::BvIntOf, op_args, args: bv }
            if matches!((op_args.as_slice(), bv.as_slice()), ([index], [bv])
                if index.as_integer().is_some_and(|i| {
                    matches!(pool.sort(bv).as_ref(), Sort::BitVec(w) if i < *w)
                })));
        if !is_bit {
            return Err(CheckerError::Explanation(format!(
                "'{}' is not a 0/1 valued pseudo-Boolean bit",
                arg
            )));
        }
        require_no_free_z(pool, arg)?;
    }
    Ok(())
}

fn require_no_free_z(pool: &mut dyn TermPool, term: &Rc<Term>) -> RuleResult {
    if pool.free_vars(term).contains_name("z") {
        return Err(CheckerError::Explanation(format!(
            "'{}' has a free variable 'z' that the choice binder would capture",
            term
        )));
    }
    Ok(())
}

/// Implements the bitwise exclusive or operation.
pub fn pbblast_bvxor(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, bit_constraints) =
        match_term_err!((= (bvxor x y) (pbbterm ...)) = first_conclusion_literal(conclusion)?)?;

    let mut budget = ExpansionBudget::new();
    let xs = get_bitvector_terms(x, pool, &mut budget)?;
    let ys = get_bitvector_terms(y, pool, &mut budget)?;

    // Zip three lists into tuples
    for ((bc, xi), yi) in bit_constraints.iter().zip(xs.iter()).zip(ys.iter()) {
        // Modified in Clean: the choice variable must not capture a free `z` of the operands.
        require_no_free_z(pool, xi)?;
        require_no_free_z(pool, yi)?;
        let (bindings, c1, c2, c3, c4) = match_term_err!((choice ... (and c1 c2 c3 c4)) = bc)?;

        // Check z -> Int
        // Modified in Clean: read the binding without indexing, so no shape of binding list panics.
        let (z_name, z_type) = bindings
            .first()
            .ok_or_else(|| CheckerError::Explanation("Expected a choice binding".into()))?;
        rassert!(
            z_name == "z",
            CheckerError::Explanation(format!("Expected {z_name} to be \"z\""))
        );
        rassert!(
            *z_type.as_ref() == Sort::Int,
            CheckerError::Explanation(format!("Expected {z_type} to be Sort::Int"))
        );

        // c1 : (>= (+ xi yi) z)
        let (xic, yic, zc) = match_term_err!((>= (+ xi yi) z) = c1)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c2 : (>= (+ z xi) yi)
        let (zc, xic, yic) = match_term_err!((>= (+ z xi) yi) = c2)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c3 : (>= (+ z yi) xi)
        let (zc, yic, xic) = match_term_err!((>= (+ z yi) xi) = c3)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c4 : (>= 2 (+ z xi yi)
        let (zc, xic, yic) = match_term_err!((>= 2 (+ z xi yi)) = c4)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );
    }

    Ok(())
}

/// Implements the bitwise and operation.
pub fn pbblast_bvand(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, y, bit_constraints) =
        match_term_err!((= (bvand x y) (pbbterm ...)) = first_conclusion_literal(conclusion)?)?;

    let mut budget = ExpansionBudget::new();
    let xs = get_bitvector_terms(x, pool, &mut budget)?;
    let ys = get_bitvector_terms(y, pool, &mut budget)?;

    // Zip three lists into tuples
    for ((bc, xi), yi) in bit_constraints.iter().zip(xs.iter()).zip(ys.iter()) {
        // Modified in Clean: the choice variable must not capture a free `z` of the operands.
        require_no_free_z(pool, xi)?;
        require_no_free_z(pool, yi)?;
        let (bindings, c1, c2, c3) = match_term_err!((choice ... (and c1 c2 c3)) = bc)?;

        // Check z -> Int
        // Modified in Clean: read the binding without indexing, so no shape of binding list panics.
        let (z_name, z_type) = bindings
            .first()
            .ok_or_else(|| CheckerError::Explanation("Expected a choice binding".into()))?;
        rassert!(
            z_name == "z",
            CheckerError::Explanation(format!("Expected {z_name} to be \"z\""))
        );
        rassert!(
            *z_type.as_ref() == Sort::Int,
            CheckerError::Explanation(format!("Expected {z_type} to be Sort::Int"))
        );

        // c1 : (>= @x0 z)
        let (xic, zc) = match_term_err!((>= xi z) = c1)?;
        assert_eq(xic, xi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c2 : (>= @y0 z)
        let (yic, zc) = match_term_err!((>= yi z) = c2)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c3 : (>= (+ z 1) (+ @x0 @y0))
        let (zc, xic, yic) = match_term_err!((>= (+ z 1) (+ xi yi)) = c3)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
    }

    Ok(())
}

/// This rule extracts assertions of the ith bit of an application of
/// `pbblast_bvxor`, given its arguments were x and y, we conclude
///  `(>= (+ x y) r) (>= (+ r x) y) (>= (+ r y) x) (>= 2 (+ r x y))`
/// In which ri is the choice element from the pseudo boolean bit blasting
/// of the bvxor rule
pub fn pbblast_bvxor_ith_bit(RuleArgs { args, pool, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_args(args, 2)?;
    let x = &args[0];
    let y = &args[1];
    require_bit_arguments(pool, x, y)?;
    let (c1, c2, c3, c4) =
        match_term_err!((and c1 c2 c3 c4) = first_conclusion_literal(conclusion)?)?;

    // Build the expected choice term
    let the_r = build_term!(pool,(choice (("z" Int)) (and
         (>= (+ {x.clone()} {y.clone()}) (let z Int))
         (>= (+ (let z Int) {x.clone()}) {y.clone()})
         (>= (+ (let z Int) {y.clone()}) {x.clone()})
         (>= 2 (+ (let z Int) {x.clone()} {y.clone()}))
    )));

    // c1 : (>= (+ x y) r)
    let (xc, yc, rc) = match_term_err!((>= (+ x y) r) = c1)?;
    assert_eq(xc, x)?;
    assert_eq(yc, y)?;
    assert_eq(rc, &the_r)?;

    // c2 : (>= (+ r x) y)
    let (rc, xc, yc) = match_term_err!((>= (+ r x) y) = c2)?;
    assert_eq(xc, x)?;
    assert_eq(yc, y)?;
    assert_eq(rc, &the_r)?;

    // c3 : (>= (+ r y) x)
    let (rc, yc, xc) = match_term_err!((>= (+ r y) x) = c3)?;
    assert_eq(xc, x)?;
    assert_eq(yc, y)?;
    assert_eq(rc, &the_r)?;

    // c4 : (>= 2 (+ r x y))
    let (rc, xc, yc) = match_term_err!((>= 2 (+ r x y)) = c4)?;
    assert_eq(xc, x)?;
    assert_eq(yc, y)?;
    assert_eq(rc, &the_r)?;

    Ok(())
}

/// This rule extracts assertions of the ith bit of an application of
/// `pbblast_bvand`, given its arguments were x and y, we conclude
///  `(>= x r) (>= y r) (>= (+ r 1) (+ x y))`
/// In which ri is the choice element from the pseudo boolean bit blasting
/// of the bvand rule
pub fn pbblast_bvand_ith_bit(RuleArgs { args, pool, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_args(args, 2)?;
    let x = &args[0];
    let y = &args[1];
    require_bit_arguments(pool, x, y)?;
    let (c1, c2, c3) = match_term_err!((and c1 c2 c3) = first_conclusion_literal(conclusion)?)?;

    // Build the expected choice term
    let the_r = build_term!(pool,(choice (("z" Int)) (and
         (>= {x.clone()} (let z Int))
         (>= {y.clone()} (let z Int))
         (>= (+ (let z Int) 1) (+ {x.clone()} {y.clone()}))
    )));

    // c1 : (>= x r)
    let (xc, rc) = match_term_err!((>= x r) = c1)?;
    assert_eq(xc, x)?;
    assert_eq(rc, &the_r)?;

    // c2 : (>= y r)
    let (yc, rc) = match_term_err!((>= y r) = c2)?;
    assert_eq(yc, y)?;
    assert_eq(rc, &the_r)?;

    // c3 : (>= (+ r 1) (+ x y))
    let (rc, x, y) = match_term_err!((>= (+ r 1) (+ x y)) = c3)?;
    assert_eq(xc, x)?;
    assert_eq(yc, y)?;
    assert_eq(rc, &the_r)?;

    Ok(())
}
