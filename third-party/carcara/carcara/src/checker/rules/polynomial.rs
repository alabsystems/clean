use super::{assert_clause_len, assert_eq, RuleArgs, RuleResult};
use crate::{
    ast::{match_term, match_term_err, Operator, Rc, Sort, Term},
    checker::{
        budget::{integer_words, rational_words, ExpansionBudget, MONOMIAL_WORDS},
        error::{CheckerError, PolynomialError},
        rules::{assert_num_premises, get_premise_term},
    },
};
use indexmap::{map::Entry, IndexMap};
use rug::{ops::NegAssign, Integer, Rational};

// Modified in Clean: normalizing a term charges what it builds to the step's `ExpansionBudget`
// before building it, and a step past the budget is refused. The walk has no cache, so a term that
// shares a subterm (`:named`) is walked once per path to it, and a product of `k` sums of two has
// `2^k` monomials: a certificate of 2 KB grew past 8 GB. What is charged, in words (the budget's
// `WORDS_PER_EXPANDED_BIT` to an expanded bit): one for each term visited, plus the 64-bit words
// of the coefficient it is scaled by and of the numeral it reads; `MONOMIAL_WORDS` for each
// monomial entry built (an atom's, a product's, or one moved out of a product), plus its factors
// and coefficient words (a constant that is not zero counting as a monomial of degree 0); and,
// reducing modulo `2^w`, `w / 64` for each negative coefficient. See checker/budget.rs and
// third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource budget".

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct Monomial(Vec<Rc<Term>>);

impl Monomial {
    fn mul(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self.0.sort_unstable_by_key(Rc::as_ptr);
        self
    }
}

#[derive(Debug, Clone)]
struct Polynomial(pub(crate) IndexMap<Monomial, Rational>, pub(crate) Rational);

impl Polynomial {
    fn new() -> Self {
        Self(IndexMap::new(), Rational::new())
    }

    /// Builds a polynomial from a term. Takes a term with nested additions, subtractions and
    /// multiplications, and flattens it to polynomial, calculating the coefficient of each
    /// monomial.
    fn from_term(term: &Rc<Term>, budget: &mut ExpansionBudget) -> Result<Self, CheckerError> {
        let mut result = Self::new();
        result.add_term(term, &Rational::from(1), budget)?;
        Ok(result)
    }

    /// Processes a term and adds it to the polynomial.
    fn add_term(
        &mut self,
        term: &Rc<Term>,
        coeff: &Rational,
        budget: &mut ExpansionBudget,
    ) -> Result<(), CheckerError> {
        // We traverse the term without using a cache for the same reasons as `LinearComb`.
        budget.spend_words("normalizing a polynomial", 1 + rational_words(coeff))?;
        match term.as_ref() {
            Term::Op(Operator::Add | Operator::BvAdd, args) => {
                for a in args {
                    self.add_term(a, coeff, budget)?;
                }
            }
            Term::Op(Operator::Sub | Operator::BvNeg, args) if args.len() == 1 => {
                self.add_term(&args[0], &coeff.as_neg(), budget)?;
            }
            Term::Op(Operator::Sub | Operator::BvSub, args) => {
                self.add_term(&args[0], coeff, budget)?;
                for a in &args[1..] {
                    self.add_term(a, &coeff.as_neg(), budget)?;
                }
            }
            Term::Op(Operator::Mult | Operator::BvMul, args) => {
                let mut result: Option<Self> = None;
                for a in args {
                    let factor = Self::from_term(a, budget)?;
                    result = Some(match result {
                        None => factor,
                        Some(product) => product.mul(factor, budget)?,
                    });
                }
                let result = result.unwrap();
                // Each monomial is moved to this polynomial's map, and each coefficient is scaled
                // by `coeff`.
                let monomials = result.0.len() as u128;
                budget.spend_words(
                    "normalizing a polynomial",
                    (monomials.saturating_mul(MONOMIAL_WORDS))
                        .saturating_add((monomials + 1).saturating_mul(rational_words(coeff))),
                )?;
                for (var, inner_coeff) in result.0 {
                    self.insert(var, inner_coeff * coeff);
                }
                self.1 += coeff * result.1;
            }
            Term::Op(Operator::RealDiv, args)
                if args.len() == 2 && args[1].as_fraction().is_some_and(|r| !r.is_zero()) =>
            {
                let r = args[1].as_fraction().unwrap();
                budget.spend_words("normalizing a polynomial", rational_words(&r))?;
                self.add_term(&args[0], &(coeff / r), budget)?;
            }
            Term::Op(Operator::ToReal, args) => {
                self.add_term(&args[0], coeff, budget)?;
            }
            // We check for division by zero separately because `.as_fraction` panics if the
            // denominator is zero. In this case, we consider the term an atom.
            Term::Op(Operator::RealDiv | Operator::IntDiv, args)
                if args.len() == 2 && args[1].as_fraction().is_some_and(|r| r.is_zero()) =>
            {
                self.insert_atom(term, coeff, budget)?;
            }
            _ => {
                if let Some(mut r) = term.as_fraction() {
                    budget.spend_words("normalizing a polynomial", rational_words(&r))?;
                    r *= coeff;
                    self.1 += r;
                } else if let Some((value, _)) = term.as_bitvector() {
                    budget.spend_words("normalizing a polynomial", integer_words(&value))?;
                    // The width is irrelevant for the normalization, overflow will be dealt with
                    // later, using the `modulo` method
                    self.1 += Rational::from(value) * coeff;
                } else {
                    self.insert_atom(term, coeff, budget)?;
                }
            }
        }
        Ok(())
    }

    /// Adds `coeff` times the monomial of one factor, `term`, after charging its entry.
    fn insert_atom(
        &mut self,
        term: &Rc<Term>,
        coeff: &Rational,
        budget: &mut ExpansionBudget,
    ) -> Result<(), CheckerError> {
        budget.spend_words(
            "normalizing a polynomial",
            MONOMIAL_WORDS + 1 + rational_words(coeff),
        )?;
        self.insert(Monomial(vec![term.clone()]), coeff.clone());
        Ok(())
    }

    /// The monomials of the polynomial, a constant that is not zero counting as one, and their
    /// factors and coefficient words.
    fn size(&self) -> (u128, u128) {
        let monomials = self.0.len() as u128 + u128::from(!self.1.is_zero());
        let contents = self
            .0
            .iter()
            .map(|(m, c)| m.0.len() as u128 + rational_words(c))
            .fold(rational_words(&self.1), u128::saturating_add);
        (monomials, contents)
    }

    /// Multiplies two polynomials, after charging what the product builds: an entry for each
    /// pair of monomials, plus the factors and the coefficient words of both. A constant counts as
    /// a monomial of degree 0 only when it is not zero, since a zero one builds nothing: `(* x x
    /// ... x)` is charged the monomials it builds, each one factor longer, not twice that.
    fn mul(self, other: Self, budget: &mut ExpansionBudget) -> Result<Self, CheckerError> {
        let ((n_a, s_a), (n_b, s_b)) = (self.size(), other.size());
        let cost = n_a
            .saturating_mul(n_b)
            .saturating_mul(MONOMIAL_WORDS)
            .saturating_add(n_b.saturating_mul(s_a))
            .saturating_add(n_a.saturating_mul(s_b));
        budget.spend_words("multiplying polynomials", cost)?;
        let mut result = Self::new();
        for (x_1, c_1) in self.0 {
            for (x_2, c_2) in &other.0 {
                result.insert(x_1.clone().mul(x_2.clone()), c_1.clone() * c_2);
            }
            result.insert(x_1, c_1 * &other.1);
        }
        for (x_2, c_2) in other.0 {
            result.insert(x_2, c_2 * &self.1);
        }
        result.1 += self.1 * other.1;
        Ok(result)
    }

    fn insert(&mut self, key: Monomial, value: Rational) {
        if value == 0 {
            return;
        }
        match self.0.entry(key) {
            Entry::Occupied(mut e) => {
                *e.get_mut() += value;
                if *e.get() == 0 {
                    e.swap_remove();
                }
            }
            Entry::Vacant(e) => {
                e.insert(value);
            }
        }
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty() && self.1.is_zero()
    }

    fn add(mut self, other: Self) -> Self {
        for (var, coeff) in other.0 {
            self.insert(var, coeff);
        }
        self.1 += other.1;
        self
    }

    fn neg(&mut self) {
        for coeff in self.0.values_mut() {
            coeff.neg_assign();
        }
        self.1.neg_assign();
    }

    fn sub(self, mut other: Self) -> Self {
        other.neg();
        self.add(other)
    }

    /// Added in Clean: the coefficients, the constant included, that are negative. Reducing one
    /// modulo `2^w` makes it a `w`-bit number.
    fn negative_coefficients(&self) -> u128 {
        let negative = self.0.values().filter(|c| c.is_negative()).count() as u128;
        negative + u128::from(self.1.is_negative())
    }

    fn modulo(mut self, n: &Integer) -> Option<Self> {
        for (_, coeff) in &mut self.0 {
            if !coeff.is_integer() {
                return None;
            }
            *coeff = coeff.numer().clone().modulo(n).into();
        }
        if self.1.is_integer() {
            self.1 = self.1.numer().clone().modulo(n).into();
            Some(self)
        } else {
            None
        }
    }
}

pub fn poly_simp(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (t, s) = match_term_err!((= t s) = &conclusion[0])?;
    let mut budget = ExpansionBudget::new();

    // Modified in Clean: `2^width` is charged to the step's expansion budget before it is
    // computed, and before either side is normalized. A width in the billions is well formed;
    // `2^w` then takes gigabytes, and past GMP's integer type (`w` near 2^37) it aborts the
    // process (see checker/budget.rs).
    let modulus = match pool.sort(t).as_ref() {
        Sort::BitVec(width) => {
            budget.spend_width("the modulus 2^w", *width)?;
            Some((Integer::from(1) << width, *width))
        }
        _ => None,
    };
    let mut t_norm = Polynomial::from_term(t, &mut budget)?;
    let mut s_norm = Polynomial::from_term(s, &mut budget)?;

    // If the sort is a bitvector sort, we must take the modulo
    if let Some((max, width)) = modulus {
        // Modified in Clean: a negative coefficient becomes a `w`-bit number, charged before it
        // is built. The budget admits `2^17` monomials at `2^17` bits, so uncharged, a step
        // negating that many atoms (`(bvneg (bvadd a_1 ... a_n))`) would build 2 GiB of numbers.
        let negative = t_norm.negative_coefficients() + s_norm.negative_coefficients();
        budget.spend_words(
            "reducing negative coefficients modulo 2^w",
            negative.saturating_mul(width as u128 / 64),
        )?;
        t_norm = t_norm.modulo(&max).unwrap();
        s_norm = s_norm.modulo(&max).unwrap();
    }

    if !t_norm.sub(s_norm).is_zero() {
        Err(PolynomialError::PolynomialsNotEqual(t.clone(), s.clone()).into())
    } else {
        Ok(())
    }
}

pub fn poly_simp_rel(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    use Operator::*;

    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;
    let prem = get_premise_term(&premises[0])?;

    // Bitvector case: (= (bvmul c1 (bvsub x1 x2)) (bvmul c2 (bvsub y1 y2)))
    let bitvector_case = match_term!(
        (= (bvmul c1 (bvsub x1 x2)) (bvmul c2 (bvsub y1 y2)))
        = get_premise_term(&premises[0])?);
    if let Some((c1, x1, x2, c2, y1, y2)) = bitvector_case {
        let sort = pool.sort(c1);
        let Sort::BitVec(_) = sort.as_ref() else {
            unreachable!()
        };
        for c in [c1, c2] {
            let (c, _) = c.as_bitvector_err()?;
            rassert!(c.is_odd(), PolynomialError::CoeffEven(c));
        }

        let (l1, l2, r1, r2) = match_term_err!((= (= x1 x2) (= y1 y2)) = &conclusion[0])?;

        assert_eq(l1, x1)?;
        assert_eq(l2, x2)?;
        assert_eq(r1, y1)?;
        assert_eq(r2, y2)?;
        return Ok(());
    }

    let (c1, xs, c2, ys) = match_term_err!((= (* c1 xs) (* c2 ys)) = prem)?;
    let (x1, x2) =
        match_term_err!((to_real (- x1 x2)) = xs).or_else(|_| match_term_err!((- x1 x2) = xs))?;
    let (y1, y2) =
        match_term_err!((to_real (- y1 y2)) = ys).or_else(|_| match_term_err!((- y1 y2) = ys))?;

    let (c1, c2) = (c1.as_fraction_err()?, c2.as_fraction_err()?);
    for c in [&c1, &c2] {
        rassert!(!c.is_zero(), PolynomialError::CoeffIsZero(c.clone()));
    }

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    match (left.as_op_err()?, right.as_op_err()?) {
        (
            (op @ (LessThan | LessEq | Equals | GreaterEq | GreaterThan), [l1, l2]),
            (op2, [r1, r2]),
        ) if op2 == op => {
            rassert!(
                op == Equals || c1.is_positive() == c2.is_positive(),
                PolynomialError::CoeffDifferentSignums(c1.clone(), c2.clone()),
            );

            assert_eq(l1, x1)?;
            assert_eq(l2, x2)?;
            assert_eq(r1, y1)?;
            assert_eq(r2, y2)?;
            Ok(())
        }
        ((op1, _), (op2, _)) => Err(PolynomialError::InvalidOperators(op1, op2).into()),
    }
}
