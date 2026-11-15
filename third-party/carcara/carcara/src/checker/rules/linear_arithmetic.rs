use super::{assert_clause_len, assert_eq, assert_num_args, RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, *},
    checker::{
        budget::{rational_words, ExpansionBudget},
        error::{CheckerError, LinearArithmeticError},
    },
};
use indexmap::{map::Entry, IndexMap};
use rug::{ops::NegAssign, Integer, Rational};

pub fn la_rw_eq(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= (= t u) (and (<= t u) (<= u t))) = &conclusion[0])?;
    Ok(())
}

/// Takes a disequality term and returns its negation, represented by an operator and two linear
/// combinations.
/// The disequality can be:
///
/// - An application of the `<`, `>`, `<=` or `>=` operators
/// - The negation of an application of one of these operators
/// - The negation of an application of the `=` operator
fn negate_disequality(
    term: &Rc<Term>,
    budget: &mut ExpansionBudget,
) -> Result<(Operator, LinearComb, LinearComb), CheckerError> {
    use Operator::*;

    fn negate_operator(op: Operator) -> Option<Operator> {
        Some(match op {
            LessThan => GreaterEq,
            GreaterThan => LessEq,
            LessEq => GreaterThan,
            GreaterEq => LessThan,
            _ => return None,
        })
    }

    fn inner(term: &Rc<Term>) -> Option<(Operator, &[Rc<Term>])> {
        if let Some(Term::Op(op, args)) = term.remove_negation().map(Rc::as_ref) {
            if matches!(op, GreaterEq | LessEq | GreaterThan | LessThan | Equals) {
                return Some((*op, args));
            }
        } else if let Term::Op(op, args) = term.as_ref() {
            return Some((negate_operator(*op)?, args));
        }
        None
    }

    let (op, args) =
        inner(term).ok_or_else(|| LinearArithmeticError::InvalidDisequalityOp(term.clone()))?;

    match args {
        [a, b] => Ok((
            op,
            LinearComb::from_term(a, budget)?,
            LinearComb::from_term(b, budget)?,
        )),
        _ => Err(LinearArithmeticError::TooManyArgsInDisequality(term.clone()).into()),
    }
}

/// A linear combination, represented by a hash map from non-constant terms to their coefficients,
/// plus a constant term. This is also used to represent a disequality, in which case the left side
/// is the non-constant terms and their coefficients, and the right side is the constant term.
#[derive(Debug)]
pub struct LinearComb(pub(crate) IndexMap<Rc<Term>, Rational>, pub(crate) Rational);

/// Added in Clean: what `LinearComb::add_term`'s charges are for.
const NORMALIZING: &str = "normalizing a linear combination";

impl LinearComb {
    fn new() -> Self {
        Self(IndexMap::new(), Rational::new())
    }

    /// Flattens a term and adds it to the linear combination, multiplying by the coefficient
    /// `coeff`. This method is only intended to be used in `LinearComb::from_term`.
    ///
    /// Modified in Clean: each term visited is charged to the step's `budget`, one word and the
    /// words of the coefficient it is scaled by, and so is each numeral read, as
    /// `Polynomial::add_term` (`poly_simp`) is charged; a step past the budget is refused. The walk
    /// has no cache (see below), so a shared subterm is visited once per path to it: over
    /// `d_i = (+ d_(i-1) d_(i-1))`, `la_generic` took 4.7 s at 26 deep (1 KB) and about 21 hours
    /// at 40 (see third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource
    /// budget", `la_generic`).
    fn add_term(
        &mut self,
        term: &Rc<Term>,
        coeff: &Rational,
        budget: &mut ExpansionBudget,
    ) -> Result<(), CheckerError> {
        // A note on performance: this function traverses the term recursively without making use
        // of a cache, which means sometimes it has to recompute the result for the same term more
        // than once. However, an old implementation of this method that could use a cache showed
        // that making use of one can actually make the performance of this function worse.
        // Benchmarks showed that it would more than double the average time of the `la_generic`
        // rule, which makes extensive use of `LinerComb`s. Because of that, we prefer to not use
        // a cache here, and traverse the term naively.
        budget.spend_words(NORMALIZING, 1 + rational_words(coeff))?;

        match term.as_ref() {
            Term::Op(Operator::Add, args) => {
                for a in args {
                    self.add_term(a, coeff, budget)?;
                }
            }
            Term::Op(Operator::Sub, args) if args.len() == 1 => {
                self.add_term(&args[0], &coeff.as_neg(), budget)?;
            }
            Term::Op(Operator::Sub, args) => {
                self.add_term(&args[0], coeff, budget)?;
                for a in &args[1..] {
                    self.add_term(a, &coeff.as_neg(), budget)?;
                }
            }
            Term::Op(Operator::Mult, args) if args.len() == 2 => {
                let (var, mut inner_coeff) = match (args[0].as_fraction(), args[1].as_fraction()) {
                    (None, Some(coeff)) => (&args[0], coeff),
                    (Some(coeff), _) => (&args[1], coeff),
                    (None, None) => {
                        self.insert(term.clone(), coeff.clone());
                        return Ok(());
                    }
                };
                budget.spend_words(NORMALIZING, rational_words(&inner_coeff))?;
                inner_coeff *= coeff;
                self.add_term(var, &inner_coeff, budget)?;
            }
            _ => {
                if let Some(mut r) = term.as_fraction() {
                    budget.spend_words(NORMALIZING, rational_words(&r))?;
                    r *= coeff;
                    self.1 += r;
                } else {
                    self.insert(term.clone(), coeff.clone());
                }
            }
        }
        Ok(())
    }

    /// Builds a linear combination from a term. Takes a term with nested additions, subtractions
    /// and multiplications, and flattens it to linear combination, calculating the coefficient of
    /// each atom.
    fn from_term(term: &Rc<Term>, budget: &mut ExpansionBudget) -> Result<Self, CheckerError> {
        let mut result = Self::new();
        result.add_term(term, &Rational::from(1), budget)?;
        Ok(result)
    }

    fn insert(&mut self, key: Rc<Term>, value: Rational) {
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

    fn add(mut self, other: Self) -> Self {
        for (var, coeff) in other.0 {
            self.insert(var, coeff);
        }
        self.1 += other.1;
        self
    }

    fn mul(&mut self, scalar: &Rational) {
        if *scalar == 0 {
            self.0.clear();
            self.1 = Rational::new();
            return;
        }

        if *scalar == 1 {
            return;
        }

        for coeff in self.0.values_mut() {
            *coeff *= scalar;
        }
        self.1 *= scalar;
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
}

// Modified in Clean: the strengthening rules (`s > d` into `s >= floor(d) + 1`, and `s >= d` into
// `s >= ceil(d)`) are only valid when `s` is integer valued, that is, when every atom of the linear
// combination is `Int` sorted. They used to be applied whatever the sorts, and depending on whether
// `d * a` happened to be an integer, so `r > 0` over a `Real` `r` became `r >= 1`, and even over
// integers `n >= 1` became `n >= 2` for a non-integer coefficient `a`. Now the combination is scaled
// by the lcm `L` of the coefficient denominators, so that `L * s` ranges over multiples of the gcd
// `g` of the scaled coefficients, and the bound is rounded to that lattice (see
// third-party/carcara/DOWNSTREAM.md).
fn strengthen(op: Operator, disequality: &mut LinearComb, pool: &mut dyn TermPool) -> Operator {
    if !matches!(op, Operator::GreaterThan | Operator::GreaterEq) {
        return op;
    }
    if !disequality
        .0
        .keys()
        .all(|atom| pool.sort(atom).as_ref() == &Sort::Int)
    {
        return op;
    }

    let mut lcm = Integer::from(1);
    for coeff in disequality.0.values() {
        lcm.lcm_mut(coeff.denom());
    }
    let lcm_rational = Rational::from(lcm.clone());
    let mut gcd = Integer::new();
    for coeff in disequality.0.values() {
        let scaled = coeff.clone() * &lcm_rational;
        gcd.gcd_mut(scaled.numer());
    }
    if gcd.is_zero() {
        // No atoms: the left side is the integer 0.
        gcd = Integer::from(1);
    }
    let gcd_rational = Rational::from(gcd);

    // `L * s` is a multiple of `g`, so round `L * d / g` and scale back.
    let quotient = disequality.1.clone() * &lcm_rational / &gcd_rational;
    let rounded = match op {
        Operator::GreaterThan => quotient.floor() + 1,
        _ => quotient.ceil(),
    };
    disequality.1 = rounded * gcd_rational / lcm_rational;
    Operator::GreaterEq
}

fn process_disequality(
    (acc_op, acc): (Operator, LinearComb),
    (phi, arg): (&Rc<Term>, Option<Rational>),
    coeff_trace: &mut Option<Vec<Rational>>,
    pool: &mut dyn TermPool,
    budget: &mut ExpansionBudget,
) -> Result<(Operator, LinearComb), CheckerError> {
    // Steps 1 and 2: Negate the disequality
    let (mut op, s1, s2) = negate_disequality(phi, budget)?;

    // Step 3: Move all non constant terms to the left side, and the d terms to the right.
    // We move everything to the left side by subtracting s2 from s1
    let mut disequality = s1.sub(s2);
    disequality.1 = -disequality.1; // We negate d to move it to the other side

    // If the operator is < or <=, we flip the disequality so it is > or >=
    if op == Operator::LessThan {
        disequality.neg();
        op = Operator::GreaterThan;
    } else if op == Operator::LessEq {
        disequality.neg();
        op = Operator::GreaterEq;
    }

    // Extra step: infer argument if it is missing
    let arg = match arg {
        Some(a) => a,
        None => {
            rassert!(
                disequality.0.len() == 1,
                CheckerError::Explanation("disequality not unit".to_owned())
            );
            let (var, coeff_1) = disequality.0.iter().next().unwrap();
            assert!(!coeff_1.is_zero()); // TODO
            let coeff_2 = acc
                .0
                .get(var)
                .ok_or(CheckerError::Explanation("coeff not found".to_owned()))?;
            let inferred = -coeff_2.clone() / coeff_1;
            if let Some(trace) = coeff_trace {
                trace.push(inferred.clone());
            }
            inferred
        }
    };

    // Modified in Clean: a literal multiplied by zero contributes nothing. Without this, a strict
    // literal scaled by zero would still make the sum strict, turning `0 >= 0` into `0 > 0`.
    if arg.is_zero() {
        return Ok((acc_op, acc));
    }

    // Step 4: Apply strengthening rules
    let op = strengthen(op, &mut disequality, pool);

    // Step 5: Multiply disequality by a
    let arg = match op {
        Operator::Equals => arg,
        _ => arg.abs(),
    };
    disequality.mul(&arg);

    // let (op, diseq) = item?;
    let new_acc = acc.add(disequality);
    // Modified in Clean: a sum is strict as soon as one strictly positive multiple of a strict
    // disequality takes part. Adding `>=` to an accumulated `>` used to weaken the result to `>=`;
    // over the reals, the upstream tests only passed because `r > 0` was (unsoundly) strengthened to
    // `r >= 1` (see third-party/carcara/DOWNSTREAM.md).
    let new_op = match (acc_op, op) {
        (Operator::GreaterThan, _) | (_, Operator::GreaterThan) => Operator::GreaterThan,
        (Operator::GreaterEq, _) | (_, Operator::GreaterEq) => Operator::GreaterEq,
        _ => Operator::Equals,
    };
    Ok((new_op, new_acc))
}

pub fn la_generic(rule_args: RuleArgs) -> RuleResult {
    assert_num_args(rule_args.args, rule_args.conclusion.len())?;
    la_generic_partial(
        rule_args.conclusion,
        rule_args.args,
        &mut None,
        rule_args.pool,
    )
}

pub fn bounded_farkas(rule_args: RuleArgs) -> RuleResult {
    la_generic_partial(
        rule_args.conclusion,
        rule_args.args,
        &mut None,
        rule_args.pool,
    )
}

pub fn la_generic_partial(
    conclusion: &[Rc<Term>],
    args: &[Rc<Term>],
    coeff_trace: &mut Option<Vec<Rational>>,
    pool: &mut dyn TermPool,
) -> RuleResult {
    let args: Vec<_> = args
        .iter()
        .map(|a| {
            a.as_fraction()
                .ok_or_else(|| CheckerError::ExpectedAnyNumber(a.clone()))
        })
        .collect::<Result<_, _>>()?;
    let args = args.into_iter().map(Some).chain(std::iter::repeat(None));

    // Added in Clean: the step's budget for its linear combinations (see `LinearComb::add_term`).
    let mut budget = ExpansionBudget::new();
    let (op, final_disequality) = conclusion
        .iter()
        .zip(args)
        .try_fold((Operator::Equals, LinearComb::new()), |acc, diseq| {
            process_disequality(acc, diseq, coeff_trace, pool, &mut budget)
        })?;

    let LinearComb(left_side, right_side): &LinearComb = &final_disequality;
    let is_disequality_true = {
        use std::cmp::Ordering;
        use Operator::*;

        // If the operator encompasses the actual relationship between 0 and the right side, the
        // disequality is true
        match Rational::new().cmp(right_side) {
            Ordering::Less => matches!(op, LessThan | LessEq),
            Ordering::Equal => matches!(op, LessEq | GreaterEq | Equals),
            Ordering::Greater => matches!(op, GreaterThan | GreaterEq),
        }
    };

    // The left side must be empty (that is, equal to 0), and the final disequality must be
    // contradictory
    if left_side.is_empty() && !is_disequality_true {
        Ok(())
    } else {
        Err(
            LinearArithmeticError::DisequalityIsNotContradiction(op, Box::new(final_disequality))
                .into(),
        )
    }
}

pub fn la_disequality(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    match_term_err!((or (= t1 t2) (not (<= t1 t2)) (not (<= t2 t1))) = &conclusion[0])?;
    Ok(())
}

pub fn la_totality(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    match_term_err!((or (<= t1 t2) (<= t2 t1)) = &conclusion[0])?;
    Ok(())
}

fn assert_less_than(a: &Rc<Term>, b: &Rc<Term>) -> RuleResult {
    rassert!(
        a.as_signed_number_err()? < b.as_signed_number_err()?,
        LinearArithmeticError::ExpectedLessThan(a.clone(), b.clone())
    );
    Ok(())
}

fn assert_less_eq(a: &Rc<Term>, b: &Rc<Term>) -> RuleResult {
    rassert!(
        a.as_signed_number_err()? <= b.as_signed_number_err()?,
        LinearArithmeticError::ExpectedLessEq(a.clone(), b.clone())
    );
    Ok(())
}

pub fn la_tautology(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    if let Some((first, second)) = match_term!((or phi_1 phi_2) = conclusion[0]) {
        // If the conclusion if of the second form, there are 5 possible cases:
        if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((not (<= s d1)) = first),
            match_term!((<= s d2) = second),
        ) {
            // First case
            assert_eq(s_1, s_2)?;
            assert_less_eq(d_1, d_2)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((<= s d1) = first),
            match_term!((not (<= s d2)) = second),
        ) {
            // Second case
            assert_eq(s_1, s_2)?;
            assert_eq(d_1, d_2)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((not (>= s d1)) = first),
            match_term!((>= s d2) = second),
        ) {
            // Third case
            assert_eq(s_1, s_2)?;
            assert_less_eq(d_2, d_1)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((>= s d1) = first),
            match_term!((not (>= s d2)) = second),
        ) {
            // Fourth case
            assert_eq(s_1, s_2)?;
            assert_eq(d_1, d_2)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((not (<= s d1)) = first),
            match_term!((not (>= s d2)) = second),
        ) {
            // Fifth case
            assert_eq(s_1, s_2)?;
            assert_less_than(d_1, d_2)
        } else {
            Err(LinearArithmeticError::NotValidTautologyCase(conclusion[0].clone()).into())
        }
    } else {
        // If the conclusion is of the first form, we apply steps 1 through 3 from `la_generic`

        // Steps 1 and 2: Negate the disequality
        let (mut op, s1, s2) = negate_disequality(&conclusion[0], &mut ExpansionBudget::new())?;

        // Step 3: Move all non constant terms to the left side, and the d terms to the right.
        let mut disequality = s1.sub(s2);
        disequality.1 = -disequality.1;

        // If the operator is < or <=, we flip the disequality so it is > or >=
        if op == Operator::LessThan {
            disequality.neg();
            op = Operator::GreaterThan;
        } else if op == Operator::LessEq {
            disequality.neg();
            op = Operator::GreaterEq;
        }

        // The final disequality should be tautological
        let is_disequality_true = disequality.0.is_empty()
            && (disequality.1 > 0 || op == Operator::GreaterThan && disequality.1 == 0);
        rassert!(
            is_disequality_true,
            LinearArithmeticError::DisequalityIsNotTautology(op, Box::new(disequality)),
        );
        Ok(())
    }
}
