use super::{assert_eq, CheckerError, RuleArgs, RuleResult};
use crate::{
    ast::{build_term, match_term_err, pool::TermPool, Operator, ParamOperator, Rc, Sort, Term},
    checker::{
        budget::{ExpansionBudget, DIVIDER_BITS_PER_STEP_BIT},
        rules::assert_clause_len,
    },
};
use rug::Integer;

// Modified in Clean: every rule here charges what it expands to an `ExpansionBudget` before
// building it, and is refused past the budget; a width in the billions is well formed and ran the
// checker out of memory (see checker/budget.rs and third-party/carcara/DOWNSTREAM.md, "Bit-vector
// expansion has a resource budget").

// Modified in Clean: a term that is not a bit-vector (`bitblast_equal` matches `(= x y)` at any
// sort) or has no bits is refused with an error. It used to `panic!`. The helpers that call it
// (`get_term_bits`, `shift_add_multiplier`, `bitblast_ult`, `bitblast_shift_op` and
// `bitblast_udiv_urem`) return that error (see third-party/carcara/DOWNSTREAM.md, "Malformed steps
// are refused, not a panic").
fn bitvector_size(pool: &mut dyn TermPool, term: &Rc<Term>) -> Result<usize, CheckerError> {
    match pool.sort(term).as_ref() {
        Sort::BitVec(size) if *size > 0 => Ok(*size),
        _ => Err(CheckerError::Explanation(format!(
            "expected a bit-vector term of positive width, got '{}'",
            term
        ))),
    }
}

fn get_term_bits(
    term: &Rc<Term>,
    pool: &mut dyn TermPool,
    budget: &mut ExpansionBudget,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    // Modified in Clean: bits the proof spells out are charged too. Each rule builds terms over
    // every bit it reads, and an n-ary step can read one shared (`:named`) `@bbterm` n times.
    let term = if let Some((Operator::BvBbTerm, args_x)) = term.as_op() {
        budget.spend_width("reading a bit-vector's spelled-out bits", args_x.len())?;
        args_x.to_vec()
    } else {
        let size = bitvector_size(pool, term)?;
        budget.spend_width("splitting a bit-vector into its bits", size)?;
        (0..size)
            .map(|i| {
                let op_args = vec![pool.add(Term::new_int(i))];
                pool.add(Term::ParamOp {
                    op: ParamOperator::BvBitOf,
                    op_args,
                    args: vec![term.clone()],
                })
            })
            .collect()
    };
    Ok(term)
}

/// Returns the sum bits and the carry *out of* the most significant bit.
// Modified in Clean: the carry returned used to be the carry *into* the most significant bit, so
// `bitblast_udiv`/`bitblast_urem` compared against the wrong bit (see third-party/carcara/DOWNSTREAM.md).
fn ripple_carry_adder(
    x: &[Rc<Term>],
    y: &[Rc<Term>],
    carry: Option<Rc<Term>>,
    pool: &mut dyn TermPool,
) -> (Vec<Rc<Term>>, Rc<Term>) {
    let size = x.len();
    let mut carries = vec![carry.unwrap_or_else(|| pool.bool_false())];

    for i in 1..=size {
        let carry_i = build_term!(
          pool,
            (or
              (and
                {x[i - 1].clone()}
                {y[i - 1].clone()})
              (and
                (xor
                  {x[i - 1].clone()}
                  {y[i - 1].clone()})
                {carries[i - 1].clone()}))
        );
        carries.push(carry_i);
    }

    let res = (0..size)
        .map(|i| build_term!(pool, (xor (xor {x[i].clone()} {y[i].clone()}) {carries[i].clone()})))
        .collect();
    (res, carries[size].clone())
}

fn shift_add_multiplier(
    x: &Rc<Term>,
    y: &Rc<Term>,
    pool: &mut dyn TermPool,
    budget: &mut ExpansionBudget,
) -> Result<Rc<Term>, CheckerError> {
    let size = bitvector_size(pool, x)?;
    budget.spend("the multiplier", (size as u128) * (size as u128))?;
    let x = get_term_bits(x, pool, budget)?;
    let y = get_term_bits(y, pool, budget)?;

    let false_term = pool.bool_false();
    let shift: Vec<Vec<_>> = (0..size)
        .map(|j| {
            (0..size)
                .map(|i| {
                    // if j <= i { build_term!(pool, (and {x[i-j].clone()} {y[j].clone()})) }
                    if j <= i {
                        build_term!(pool, (and {y[j].clone()} {x[i-j].clone()}))
                    } else {
                        false_term.clone()
                    }
                })
                .collect()
        })
        .collect();

    let mut carry: Vec<Vec<_>> = vec![(0..size).map(|_i| false_term.clone()).collect()];
    let mut res: Vec<Vec<_>> = vec![(0..size).map(|i| shift[0][i].clone()).collect()];

    for j in 1..size {
        // carry^j+1_i+1
        carry.push(vec![false_term.clone()]);
        for i in 1..size {
            let prev_carry = if j < i {
                carry[j][i - 1].clone()
            } else {
                false_term.clone()
            };
            carry[j].push(
                if j < i {
                    build_term!(pool,
                                (or (and {res[j-1][i-1].clone()} {shift[j][i-1].clone()})
                                 (and (xor {res[j-1][i-1].clone()} {shift[j][i-1].clone()}) {prev_carry})
                                )
                    )
                }
                else {false_term.clone()});
        }

        // res^j+1_i
        res.push((0..size)
                      .map(|i| {
                          // res^j_0 = sh^0_0
                          if i == 0 { shift[0][0].clone() }
                          else if j > i { res[i][i].clone() }
                          else {
                              build_term!(pool,
                                    (xor (xor {res[j-1][i].clone()} {shift[j][i].clone()}) {carry[j][i].clone()})
                              )
                          }
                      }).collect());
    }

    Ok(pool.add(Term::Op(Operator::BvBbTerm, res[size - 1].clone())))
}

pub fn value(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (v, res_args) = match_term_err!((= v (bbterm ...)) = &conclusion[0])?;

    if let Some((m, size)) = v.as_bitvector() {
        let true_term = pool.bool_true();
        let false_term = pool.bool_false();
        // the number of arguments of bbterm must be the same as the width of v
        if size == res_args.len() {
            // the computed value from res_args must be the same as m
            let mut computed_value = Integer::new();
            for (i, arg) in res_args.iter().enumerate() {
                if *arg == true_term {
                    // Modified in Clean: a bit index beyond `u32` is refused, not a panic.
                    let exponent = u32::try_from(i).map_err(|_| {
                        CheckerError::Explanation(format!("bit index {} out of range", i))
                    })?;
                    // Modified in Clean: set the bit, rather than add a freshly computed `2^i`,
                    // which took time quadratic in the width. The bits are distinct, so the
                    // value is the same.
                    computed_value.set_bit(exponent, true);
                } else if *arg != false_term {
                    return Err(CheckerError::Explanation(format!(
                        "bitblasted const {}-th arg neither true nor false",
                        i
                    )));
                }
            }
            if m == computed_value {
                return Ok(());
            }
            return Err(CheckerError::Explanation(format!(
                "const is {} but bitblasting computes to {}",
                m, computed_value
            )));
        }
    }
    Err(CheckerError::Explanation(
        "Not a const being bitblasted.".to_owned(),
    ))
}

pub fn var(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, res) = match_term_err!((= x res) = &conclusion[0])?;

    rassert!(
        matches!(pool.sort(x).as_ref(), &Sort::BitVec(_)),
        CheckerError::Explanation(format!(
            "Could not get BV sort out of (expected-to-be variable) term {}",
            x
        ))
    );
    let x = get_term_bits(x, pool, &mut budget)?;

    assert_eq(&pool.add(Term::Op(Operator::BvBbTerm, x)), res)
}

pub fn and(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (bvand_args, res) = match_term_err!((= (bvand ...) res) = &conclusion[0])?;

    let size = bitvector_size(pool, &bvand_args[0])?;

    // the conjunction is build left-to-right
    let mut i = 1;
    let mut expected_res = bvand_args[0].clone();

    while i < bvand_args.len() {
        let x = get_term_bits(&expected_res, pool, &mut budget)?;
        let y = get_term_bits(&bvand_args[i], pool, &mut budget)?;

        let res_args: Vec<_> = (0..size)
            .map(|i| {
                build_term!(
                    pool,
                    (and {x[i].clone()} {y[i].clone()})
                )
            })
            .collect();
        expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));
        i += 1;
    }

    assert_eq(&expected_res, res)
}

pub fn or(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (bvor_args, res) = match_term_err!((= (bvor ...) res) = &conclusion[0])?;

    let size = bitvector_size(pool, &bvor_args[0])?;

    // the disjunction is build left-to-right
    let mut i = 1;
    let mut expected_res = bvor_args[0].clone();

    while i < bvor_args.len() {
        let x = get_term_bits(&expected_res, pool, &mut budget)?;
        let y = get_term_bits(&bvor_args[i], pool, &mut budget)?;

        let res_args: Vec<_> = (0..size)
            .map(|i| {
                build_term!(
                    pool,
                    (or {x[i].clone()} {y[i].clone()})
                )
            })
            .collect();
        expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));
        i += 1;
    }

    assert_eq(&expected_res, res)
}

pub fn xor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (bvxor_args, res) = match_term_err!((= (bvxor ...) res) = &conclusion[0])?;

    let size = bitvector_size(pool, &bvxor_args[0])?;

    // the conjunction is build left-to-right
    let mut i = 1;
    let mut expected_res = bvxor_args[0].clone();

    while i < bvxor_args.len() {
        let x = get_term_bits(&expected_res, pool, &mut budget)?;
        let y = get_term_bits(&bvxor_args[i], pool, &mut budget)?;

        let res_args: Vec<_> = (0..size)
            .map(|i| {
                build_term!(
                    pool,
                    (xor {x[i].clone()} {y[i].clone()})
                )
            })
            .collect();
        expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));
        i += 1;
    }

    assert_eq(&expected_res, res)
}

pub fn xnor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvxnor x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x)?;
    let x = get_term_bits(x, pool, &mut budget)?;
    let y = get_term_bits(y, pool, &mut budget)?;

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn not(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, res) = match_term_err!((= (bvnot x) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x)?;
    let x = get_term_bits(x, pool, &mut budget)?;

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (not {x[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

/// Bitblasts `(bvult x y)`
fn bitblast_ult(
    pool: &mut dyn TermPool,
    x: &Rc<Term>,
    y: &Rc<Term>,
    budget: &mut ExpansionBudget,
) -> Result<Rc<Term>, CheckerError> {
    let size = bitvector_size(pool, x)?;
    let x = get_term_bits(x, pool, budget)?;
    let y = get_term_bits(y, pool, budget)?;

    let mut res = build_term!(pool, (and (not {x[0].clone()}) {y[0].clone()}));

    for i in 1..size {
        res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
    }
    Ok(res)
}

pub fn ult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvult x y) res) = &conclusion[0])?;

    let expected = bitblast_ult(pool, x, y, &mut budget)?;

    assert_eq(&expected, res)
}

pub fn slt(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvslt x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x)?;
    let x = get_term_bits(x, pool, &mut budget)?;
    let y = get_term_bits(y, pool, &mut budget)?;

    // if size is 1, check directly if x, whose only bit is its LSB,
    // is negative (i.e., first bit is 1) and y positive (i.e., it is
    // zero)
    if size == 1 {
        return assert_eq(
            &build_term!(pool, (and {x[0].clone()} (not {y[0].clone()}))),
            res,
        );
    }

    let mut expected_res = build_term!(pool, (and (not {x[0].clone()}) {y[0].clone()}));

    for i in 1..(size - 1) {
        let new_res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {expected_res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
        expected_res = new_res;
    }

    let new_res = build_term!(
        pool,
        (or
         (and (= {x[size - 1].clone()} {y[size - 1].clone()}) {expected_res.clone()})
         (and {x[size - 1].clone()} (not {y[size - 1].clone()}))
        )
    );
    expected_res = new_res;

    assert_eq(&expected_res, res)
}

pub fn add(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (add_args, res) = match_term_err!((= (bvadd ...) res) = &conclusion[0])?;

    let mut i = 1;
    let mut expected_res = get_term_bits(&add_args[0], pool, &mut budget)?;
    while i < add_args.len() {
        expected_res = ripple_carry_adder(
            &expected_res,
            &get_term_bits(&add_args[i], pool, &mut budget)?,
            None,
            pool,
        )
        .0;
        i += 1;
    }
    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, expected_res));
    assert_eq(&expected_res, res)
}

pub fn mult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (mult_args, res) = match_term_err!((= (bvmul ...) res) = &conclusion[0])?;

    let mut i = 1;
    let mut expected_res = mult_args[0].clone();
    while i < mult_args.len() {
        expected_res = shift_add_multiplier(&expected_res, &mult_args[i], pool, &mut budget)?;
        i += 1;
    }
    assert_eq(&expected_res, res)
}

pub fn neg(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, res) = match_term_err!((= (bvneg x) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x)?;
    let x = get_term_bits(x, pool, &mut budget)?;

    let mut carries = vec![pool.bool_true()];

    for i in 1..size {
        let carry_i = build_term!(
          pool,
          (or (and (not {x[i - 1].clone()}) false) (and (xor (not {x[i - 1].clone()}) false) {carries[i - 1].clone()}))
        );
        carries.push(carry_i);
    }

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (xor (xor (not {x[i].clone()}) false) {carries[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn equality(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (= x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x)?;
    let x = get_term_bits(x, pool, &mut budget)?;
    let y = get_term_bits(y, pool, &mut budget)?;

    let expected_res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
                pool,
                (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();
    let expected_res = if expected_res_args.len() > 1 {
        pool.add(Term::Op(Operator::And, expected_res_args))
    } else {
        expected_res_args[0].clone()
    };

    assert_eq(&expected_res, res)
}

pub fn comp(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvcomp x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x)?;
    let x = get_term_bits(x, pool, &mut budget)?;
    let y = get_term_bits(y, pool, &mut budget)?;

    let expected_res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
                pool,
                (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();
    let expected_res = if expected_res_args.len() > 1 {
        pool.add(Term::Op(Operator::And, expected_res_args))
    } else {
        expected_res_args[0].clone()
    };
    let expected_res = build_term!(pool, (bbterm { expected_res }));

    assert_eq(&expected_res, res)
}

//TODO I think this can be redone with build_term_vec.
pub fn extract(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (_, left_j, left_x, right) =
        match_term_err!((= ((_ extract i j) x) (bbterm ...)) = &conclusion[0])?;

    // Modified in Clean: the index and the range of bits are checked, not unwrapped and indexed.
    // The parser already requires numerals `j <= i` below the operand's width, so this refuses
    // nothing a parsed step could reach (see third-party/carcara/DOWNSTREAM.md).
    let left_j = left_j.as_integer_err()?;
    let mut index = left_j;

    if let Some((Operator::BvBbTerm, args)) = left_x.as_op() {
        let start = index.to_usize().ok_or_else(|| {
            CheckerError::Explanation(format!("extract index {} out of range", index))
        })?;
        let bits = args.get(start..).unwrap_or_default();
        rassert!(
            right.len() <= bits.len(),
            CheckerError::Explanation(format!(
                "extract of {} bits from bit {} of a {}-bit term",
                right.len(),
                start,
                args.len()
            ))
        );
        for (expected, arg) in bits.iter().zip(right) {
            assert_eq(expected, arg)?;
        }
        return Ok(());
    }

    for arg in right {
        let expected_arg = Term::ParamOp {
            op: ParamOperator::BvBitOf,
            op_args: vec![pool.add(Term::new_int(index.clone()))],
            args: vec![left_x.clone()],
        };
        let new_arg = pool.add(expected_arg);
        assert_eq(&new_arg, arg)?;
        index += 1;
    }
    Ok(())
}

pub fn concat(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (concat_args, res_args) = match_term_err!((= (concat ...) (bbterm ...)) = &conclusion[0])?;

    let mut size = bitvector_size(pool, &concat_args[concat_args.len() - 1])?;
    let mut expected_res = get_term_bits(&concat_args[concat_args.len() - 1], pool, &mut budget)?;

    let mut i = 1;
    while i < concat_args.len() {
        let size_i = bitvector_size(pool, &concat_args[concat_args.len() - 1 - i])?;
        expected_res.extend(get_term_bits(
            &concat_args[concat_args.len() - 1 - i],
            pool,
            &mut budget,
        )?);

        size += size_i;
        i += 1;
    }

    if res_args.len() != size {
        return Err(CheckerError::Explanation(format!(
            "Concat size {} different from sum of argument size {}",
            res_args.len(),
            size
        )));
    }
    assert_eq(
        &pool.add(Term::Op(Operator::BvBbTerm, expected_res)),
        &pool.add(Term::Op(Operator::BvBbTerm, res_args.to_vec())),
    )
}

pub fn sign_extend(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (i, x, res) = match_term_err!((= ((_ sign_extend i) x) res) = &conclusion[0])?;

    // Modified in Clean: as in `extract`, the index is checked rather than unwrapped.
    let i = i.as_usize_err()?;
    if i == 0 {
        return assert_eq(x, res);
    }

    let size = bitvector_size(pool, x)?;
    budget.spend_width("the bits sign_extend adds", i)?;
    let mut x = get_term_bits(x, pool, &mut budget)?;

    for _j in 0..i {
        x.push(x[size - 1].clone());
    }

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, x));
    assert_eq(&expected_res, res)
}

/// Bitblasts an application of either `bvshl`, `bvlshr` or `bvashr`.
fn bitblast_shift_op(
    pool: &mut dyn TermPool,
    op: Operator,
    x: &Rc<Term>,
    y: &Rc<Term>,
    budget: &mut ExpansionBudget,
) -> Result<Rc<Term>, CheckerError> {
    let size = bitvector_size(pool, x)?;

    // We only need to check the bits upto k = ceil(log2(size)). Note that ilog2 rounds down, so we
    // add 1 if it's not an exact power of 2
    let k = size.ilog2() as usize + if size.is_power_of_two() { 0 } else { 1 };
    // Modified in Clean: the `k` stages of the shifter and the final selection build a term per
    // bit each (see checker/budget.rs).
    budget.spend("the barrel shifter", (k as u128 + 1) * size as u128)?;

    // First, we will need to bitblast a term that corresponds to `(bvult y size)`
    let size_term = pool.add(Term::new_bv(size, size));
    let y_ult_size = bitblast_ult(pool, y, &size_term, budget)?;

    let x = get_term_bits(x, pool, budget)?;
    let y = get_term_bits(y, pool, budget)?;

    let sign_bit = x.last().unwrap().clone();
    let mut res = x;

    for (s, ys) in y.into_iter().enumerate().take(k) {
        let previous = res.clone();
        let thresh = 1 << s;
        for i in 0..size {
            let ys = ys.clone();
            res[i] = match op {
                Operator::BvShl => {
                    if i < thresh {
                        build_term!(pool, (ite {ys} {pool.bool_false()} {previous[i].clone()}))
                    } else {
                        build_term!(pool,
                            (ite {ys} {previous[i - thresh].clone()} {previous[i].clone()}))
                    }
                }
                Operator::BvLShr => {
                    if i + thresh >= size {
                        build_term!(pool, (ite {ys} false {previous[i].clone()}))
                    } else {
                        build_term!(pool,
                            (ite (not {ys}) {previous[i].clone()} {previous[i + thresh].clone()}))
                    }
                }
                Operator::BvAShr => {
                    if i + thresh >= size {
                        build_term!(pool, (ite {ys} {sign_bit.clone()} {previous[i].clone()}))
                    } else {
                        build_term!(pool,
                            (ite (not {ys}) {previous[i].clone()} {previous[i + thresh].clone()}))
                    }
                }
                _ => unreachable!(),
            };
        }
    }

    // Modified in Clean: an arithmetic shift by at least the width fills with the sign bit, not
    // with zeros (SMT-LIB `bvashr`; see third-party/carcara/DOWNSTREAM.md).
    let overshift_fill = match op {
        Operator::BvAShr => sign_bit,
        _ => pool.bool_false(),
    };
    for bit in &mut res {
        *bit = build_term!(pool, (ite {y_ult_size.clone()} {bit.clone()} {overshift_fill.clone()}));
    }

    Ok(pool.add(Term::Op(Operator::BvBbTerm, res)))
}

pub fn shl(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvshl x y) res) = &conclusion[0])?;

    let expected = bitblast_shift_op(pool, Operator::BvShl, x, y, &mut budget)?;

    assert_eq(&expected, res)
}

pub fn lshr(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvlshr x y) res) = &conclusion[0])?;

    let expected = bitblast_shift_op(pool, Operator::BvLShr, x, y, &mut budget)?;

    assert_eq(&expected, res)
}

pub fn ashr(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvashr x y) res) = &conclusion[0])?;

    let expected = bitblast_shift_op(pool, Operator::BvAShr, x, y, &mut budget)?;

    assert_eq(&expected, res)
}

/// Returns a quotient/remainder pair.
///
/// Modified in Clean: a loop over the divider's steps, from the last to the first, where upstream
/// recursed once per step, so a `w`-bit division recursed `w` deep. It builds the same terms. Step
/// `k` divides `x >> k`. The steps end at the first shift of `x` whose bits are all `false`, where
/// the recursion's base case stopped, and their cost is charged to the budget before any is built
/// (see checker/budget.rs and third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a
/// resource budget").
fn bitblast_udiv_urem_steps(
    pool: &mut dyn TermPool,
    x: &[Rc<Term>],
    y: &[Rc<Term>],
    budget: &mut ExpansionBudget,
) -> Result<(Vec<Rc<Term>>, Vec<Rc<Term>>), CheckerError> {
    fn shift_left(pool: &mut dyn TermPool, v: &mut [Rc<Term>]) {
        v.rotate_right(1); // Rust and SMT-LIB disagree on endianness
        *v.first_mut().unwrap() = pool.bool_false();
    }

    let width = x.len();
    // `x >> k` has only `false` bits exactly when every bit of `x` from `k` up is `false`.
    let steps = x
        .iter()
        .rposition(|xi| !xi.is_bool_false())
        .map_or(0, |top| top + 1);
    budget.spend(
        "the divider",
        DIVIDER_BITS_PER_STEP_BIT * steps as u128 * width as u128,
    )?;

    let zero = vec![pool.bool_false(); width];
    let (mut quot, mut rem) = (zero.clone(), zero.clone());
    if steps == 0 {
        return Ok((quot, rem));
    }
    let not_y: Vec<_> = y
        .iter()
        .map(|yi| build_term!(pool, (not {yi.clone()})))
        .collect();

    for k in (0..steps).rev() {
        // `x >> k`, the dividend of this step.
        let x: Vec<_> = (0..width)
            .map(|i| x.get(i + k).cloned().unwrap_or_else(|| pool.bool_false()))
            .collect();
        let (mut q1, mut r1) = (quot, rem);

        shift_left(pool, &mut q1);
        shift_left(pool, &mut r1);

        let one_if_odd = build_term!(pool, (ite (= {x[0].clone()} true) true false));

        let (mut r1_shift_add, _) = ripple_carry_adder(&r1, &zero, Some(one_if_odd), pool);

        // Modified in Clean: when the shifted remainder is at least `y`, the new remainder is the
        // difference `r1_shift_add - y`, not all ones (see third-party/carcara/DOWNSTREAM.md).
        let (r_minus_y, co1) =
            ripple_carry_adder(&r1_shift_add, &not_y, Some(pool.bool_true()), pool);
        let sign = build_term!(pool, (not { co1 }));
        q1[0] = build_term!(pool, (ite {sign.clone()} {q1[0].clone()} true));

        for (bit, diff) in r1_shift_add.iter_mut().zip(r_minus_y) {
            *bit = build_term!(pool, (ite {sign.clone()} {bit.clone()} {diff}));
        }

        let (_, co2) = ripple_carry_adder(&x, &not_y, Some(pool.bool_true()), pool);
        let x_lt_y = build_term!(pool, (not { co2 }));

        (quot, rem) = (0..width)
            .map(|i| {
                let q = build_term!(pool, (ite {x_lt_y.clone()} false {q1[i].clone()}));
                let r = build_term!(pool,
                    (ite {x_lt_y.clone()} {x[i].clone()} {r1_shift_add[i].clone()}));
                (q, r)
            })
            .unzip();
    }
    Ok((quot, rem))
}

fn bitblast_udiv_urem(
    pool: &mut dyn TermPool,
    x: &Rc<Term>,
    y: &Rc<Term>,
    budget: &mut ExpansionBudget,
) -> Result<(Vec<Rc<Term>>, Vec<Rc<Term>>), CheckerError> {
    let (x, y) = (
        get_term_bits(x, pool, budget)?,
        get_term_bits(y, pool, budget)?,
    );

    let (quot, rem) = bitblast_udiv_urem_steps(pool, &x, &y, budget)?;

    let y_is_zero = {
        let args: Vec<_> = y
            .into_iter()
            .map(|yi| build_term!(pool, (= {yi} false)))
            .collect();
        pool.add(Term::Op(Operator::And, args))
    };

    let quot = quot
        .into_iter()
        .map(|qi| build_term!(pool, (ite {y_is_zero.clone()} true {qi})))
        .collect();
    let rem = rem
        .into_iter()
        .zip(x)
        .map(|(ri, xi)| build_term!(pool, (ite {y_is_zero.clone()} {xi} {ri})))
        .collect();
    Ok((quot, rem))
}

pub fn udiv(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvudiv x y) res) = &conclusion[0])?;

    let (expected, _) = bitblast_udiv_urem(pool, x, y, &mut budget)?;
    let expected = pool.add(Term::Op(Operator::BvBbTerm, expected));

    assert_eq(&expected, res)
}

pub fn urem(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let mut budget = ExpansionBudget::new();
    let (x, y, res) = match_term_err!((= (bvurem x y) res) = &conclusion[0])?;

    let (_, expected) = bitblast_udiv_urem(pool, x, y, &mut budget)?;
    let expected = pool.add(Term::Op(Operator::BvBbTerm, expected));

    assert_eq(&expected, res)
}

// Added in Clean: the divider's loop is held to upstream's recursion, kept here verbatim (with fix
// 1) as the reference (see third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource
// budget").
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::pool::PrimitivePool, checker::budget::MAX_EXPANDED_BITS};

    /// Upstream's recursive divider, verbatim apart from this comment and its name.
    fn reference_udiv_urem_rec(
        pool: &mut dyn TermPool,
        x: &[Rc<Term>],
        y: &[Rc<Term>],
        n: usize,
    ) -> (Vec<Rc<Term>>, Vec<Rc<Term>>) {
        fn shift_right(pool: &mut dyn TermPool, v: &mut [Rc<Term>]) {
            v.rotate_left(1); // Rust and SMT-LIB disagree on endianness
            *v.last_mut().unwrap() = pool.bool_false();
        }

        fn shift_left(pool: &mut dyn TermPool, v: &mut [Rc<Term>]) {
            v.rotate_right(1); // Rust and SMT-LIB disagree on endianness
            *v.first_mut().unwrap() = pool.bool_false();
        }

        if n == 0 || x.iter().all(|xi| xi.is_bool_false()) {
            let zero = vec![pool.bool_false(); x.len()];
            return (zero.clone(), zero);
        }

        let mut x1 = x.to_vec();
        shift_right(pool, &mut x1);

        let (mut q1, mut r1) = reference_udiv_urem_rec(pool, &x1, y, n - 1);

        shift_left(pool, &mut q1);
        shift_left(pool, &mut r1);

        let one_if_odd = build_term!(pool, (ite (= {x[0].clone()} true) true false));

        let (mut r1_shift_add, _) = ripple_carry_adder(
            &r1,
            &vec![pool.bool_false(); x.len()],
            Some(one_if_odd),
            pool,
        );
        let not_y: Vec<_> = y
            .iter()
            .map(|yi| build_term!(pool, (not {yi.clone()})))
            .collect();

        let (r_minus_y, co1) =
            ripple_carry_adder(&r1_shift_add, &not_y, Some(pool.bool_true()), pool);
        let sign = build_term!(pool, (not { co1 }));
        q1[0] = build_term!(pool, (ite {sign.clone()} {q1[0].clone()} true));

        for (bit, diff) in r1_shift_add.iter_mut().zip(r_minus_y) {
            *bit = build_term!(pool, (ite {sign.clone()} {bit.clone()} {diff}));
        }

        let (_, co2) = ripple_carry_adder(x, &not_y, Some(pool.bool_true()), pool);
        let x_lt_y = build_term!(pool, (not { co2 }));

        let (quot, rem) = (0..x.len())
            .map(|i| {
                let q = build_term!(pool, (ite {x_lt_y.clone()} false {q1[i].clone()}));
                let r = build_term!(pool,
                    (ite {x_lt_y.clone()} {x[i].clone()} {r1_shift_add[i].clone()}));
                (q, r)
            })
            .unzip();
        (quot, rem)
    }

    /// A word whose bit `i` is `false`, `true` or the variable `{name}{i}`, as `digits` (base 3,
    /// least significant first) says.
    fn word(pool: &mut PrimitivePool, name: &str, width: usize, mut digits: u64) -> Vec<Rc<Term>> {
        let bool_sort = pool.add_sort(Sort::Bool);
        (0..width)
            .map(|i| {
                let digit = digits % 3;
                digits /= 3;
                match digit {
                    0 => pool.bool_false(),
                    1 => pool.bool_true(),
                    _ => pool.add(Term::new_var(format!("{name}{i}"), bool_sort.clone())),
                }
            })
            .collect()
    }

    /// The loop builds the terms the recursion built (the pool shares equal terms, so the same
    /// `Rc`s), for every dividend of up to 4 bits against every divisor, and for sampled words up
    /// to 12 bits; dividends with high `false` bits are where the steps stop early.
    #[test]
    fn the_divider_loop_builds_the_recursions_terms() {
        let mut cases = Vec::new();
        for width in 1..=4usize {
            let all = 3u64.pow(width as u32);
            for x in 0..all {
                for y in 0..all {
                    cases.push((width, x, y));
                }
            }
        }
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        for width in 5..=12usize {
            for _ in 0..200 {
                // xorshift64
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                let all = 3u64.pow(width as u32);
                cases.push((width, seed % all, (seed >> 32) % all));
            }
        }
        for (width, x, y) in cases {
            let mut pool = PrimitivePool::new();
            let x = word(&mut pool, "x", width, x);
            let y = word(&mut pool, "y", width, y);
            let expected = reference_udiv_urem_rec(&mut pool, &x, &y, width);
            let got = bitblast_udiv_urem_steps(&mut pool, &x, &y, &mut ExpansionBudget::new())
                .expect("within the budget");
            assert_eq!(got, expected, "x = {x:?}, y = {y:?}");
        }
    }

    /// The divider charges `DIVIDER_BITS_PER_STEP_BIT * w` for each of its steps, one per bit of
    /// the dividend up to its highest bit that is not `false`, before it builds any.
    #[test]
    fn the_divider_charges_its_steps_up_front() {
        let mut pool = PrimitivePool::new();
        let width = 8;
        let y = word(&mut pool, "y", width, 3u64.pow(width as u32) - 1);
        for top in 0..width {
            // Bits above `top` are `false`, bit `top` is a variable.
            let mut x = word(&mut pool, "x", width, 0);
            let bool_sort = pool.add_sort(Sort::Bool);
            x[top] = pool.add(Term::new_var("x_top", bool_sort));
            let cost = DIVIDER_BITS_PER_STEP_BIT * (top as u128 + 1) * width as u128;

            let mut budget = ExpansionBudget::new();
            budget
                .spend("the rest of the step", MAX_EXPANDED_BITS - cost)
                .unwrap();
            bitblast_udiv_urem_steps(&mut pool, &x, &y, &mut budget).expect("exactly the budget");

            let mut budget = ExpansionBudget::new();
            budget
                .spend("the rest of the step", MAX_EXPANDED_BITS - cost + 1)
                .unwrap();
            let error = bitblast_udiv_urem_steps(&mut pool, &x, &y, &mut budget).unwrap_err();
            assert!(
                matches!(&error, CheckerError::ResourceBudgetExceeded(b) if b.what == "the divider"),
                "{error:?}"
            );
        }
        // A dividend with no bit that is not `false` takes no step and costs nothing.
        let x = word(&mut pool, "x", width, 0);
        let mut budget = ExpansionBudget::new();
        budget.spend("everything", MAX_EXPANDED_BITS).unwrap();
        let (quot, rem) = bitblast_udiv_urem_steps(&mut pool, &x, &y, &mut budget).unwrap();
        assert!(quot.iter().chain(&rem).all(|b| b.is_bool_false()));
    }
}
