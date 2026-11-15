//! This module contains rules that are not yet in the specification for the Alethe format.

use super::{
    assert_clause_len, assert_eq, assert_num_premises, get_premise_term, CheckerError,
    EqualityError, RuleArgs, RuleResult,
};
use crate::{
    ast::{
        pool::{first_free_var, FreeVars},
        *,
    },
    checker::{
        error::{CongruenceError, SubproofError},
        rules::assert_operation_len,
    },
    utils::{MultiSet, MultiSetDifference},
};
use std::collections::HashMap;

pub fn reordering(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let premise = premises[0].clause;
    assert_clause_len(conclusion, premise.len())?;

    let premise_set: MultiSet<_> = premise.iter().collect();
    let conclusion_set: MultiSet<_> = conclusion.iter().collect();
    match conclusion_set.symmetric_difference(&premise_set) {
        MultiSetDifference::None => Ok(()),
        MultiSetDifference::Missing(t) => Err(CheckerError::ContractionMissingTerm((*t).clone())),
        MultiSetDifference::Extra(t) => Err(CheckerError::ContractionExtraTerm((*t).clone())),
    }
}

pub fn shuffle(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (left_args, right_args) = {
        let ((l_op, l), (r_op, r)) = (left.as_op_err()?, right.as_op_err()?);
        if l_op != r_op {
            return Err(CongruenceError::DifferentOperators(l_op, r_op).into());
        }
        match l_op {
            Operator::Add | Operator::Mult | Operator::And | Operator::Or => (l, r),
            other => return Err(CheckerError::OperatorNotCommutative(other)),
        }
    };

    let left_multiset: MultiSet<_> = left_args.iter().collect();
    let right_multiset: MultiSet<_> = right_args.iter().collect();
    if left_multiset != right_multiset {
        return Err(CheckerError::ShuffleArgsNotEqual);
    }
    Ok(())
}

pub fn symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise = get_premise_term(&premises[0])?;
    let (p_1, q_1) = match_term_err!((= p q) = premise)?;
    let (q_2, p_2) = match_term_err!((= q p) = &conclusion[0])?;
    assert_eq(p_1, p_2)?;
    assert_eq(q_1, q_2)
}

pub fn not_symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise = get_premise_term(&premises[0])?;
    let (p_1, q_1) = match_term_err!((not (= p q)) = premise)?;
    let (q_2, p_2) = match_term_err!((not (= q p)) = &conclusion[0])?;
    assert_eq(p_1, p_2)?;
    assert_eq(q_1, q_2)
}

pub fn eq_symmetric(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    match_term_err!((= (= t u) (= u t)) = &conclusion[0])?;
    Ok(())
}

pub fn eq_mp(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    let phi_1 = get_premise_term(&premises[0])?;
    let equivalence = get_premise_term(&premises[1])?;
    let (left, right) = match_term_err!((= phi_1 phi_2) = equivalence)?;

    assert_eq(left, phi_1)?;
    assert_eq(right, &conclusion[0])
}

pub fn weakening(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = premises[0].clause;
    assert_clause_len(conclusion, premise.len()..)?;
    for (t, u) in premise.iter().zip(conclusion) {
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn and_intro(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let and_contents = match_term_err!((and ...) = &conclusion[0])?;
    assert_num_premises(premises, and_contents.len())?;

    // for the rule to be correct, each element of `and_contents` must
    // be the conclusion of a premise, in the right order. If a
    // premise has a non-unit conclusion, it must correspond to an OR
    // term in `and_contents`
    for i in 0..and_contents.len() {
        let and_arg = &and_contents[i];
        match premises[i].clause {
            [term] => {
                assert_eq(and_arg, term)?;
            }
            _ => {
                let premise_as_or = pool.add(Term::Op(Operator::Or, premises[i].clause.to_vec()));
                assert_eq(and_arg, &premise_as_or)?;
            }
        };
    }
    Ok(())
}

pub fn bind_let(
    RuleArgs {
        conclusion,
        premises,
        previous_command,
        context,
        pool,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (phi, phi_prime) = match_term_err!((= p q) = get_premise_term(&previous_command)?)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    let (l_bindings, left) = left.as_let_err()?;
    let (r_bindings, right) = right.as_let_err()?;

    if l_bindings.len() != r_bindings.len() {
        return Err(EqualityError::ExpectedEqual(l_bindings.clone(), r_bindings.clone()).into());
    }

    // Modified in Clean: `phi = phi'` is instantiated with the let values, so it must hold for
    // every value of each let variable that occurs in it. Such a variable must therefore be a
    // fixed variable of the anchor (a let variable that occurs in neither `phi` nor `phi'` needs
    // nothing), and the anchor may not assign anything. Before, the anchor was never inspected:
    // `(= (let ((x b)) (P x)) (let ((x b)) (P a)))` was accepted from `(= (P x) (P a))` proved
    // under `(:= (x U) a)`, or from a premise `(= x a)` outside the anchor (see
    // third-party/carcara/DOWNSTREAM.md).
    {
        let args = context
            .last()
            .and_then(|ctx| ctx.as_ref().map(|ctx| ctx.args.clone()))
            .unwrap_or_default();
        if let Some((name, _)) = args.iter().find_map(AnchorArg::as_assign) {
            return Err(CheckerError::Explanation(format!(
                "the anchor of a 'bind_let' step may not assign '{}'",
                name
            )));
        }
        let fixed: Vec<_> = args.iter().filter_map(AnchorArg::as_variable).collect();
        let occurring = pool.free_vars(phi).union(&pool.free_vars(phi_prime));
        for (name, value) in l_bindings.iter() {
            let sort = pool.sort(value);
            if occurring.contains_name(name) && !fixed.iter().any(|(n, s)| n == name && *s == sort)
            {
                return Err(SubproofError::BindingIsNotInContext(name.clone()).into());
            }
        }
    }

    let mut premises_iter = premises
        .iter()
        .map(|p| match_term_err!((= t u) = get_premise_term(p)?))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter();
    for (left, right) in l_bindings.iter().zip(r_bindings) {
        if left.0 != right.0 {
            return Err(
                EqualityError::ExpectedEqual(l_bindings.clone(), r_bindings.clone()).into(),
            );
        }

        // This will consume premises until it finds one that justifies the needed equality, so
        // unnecessary premises are just ignored
        if left.1 != right.1 && !premises_iter.any(|p| p == (&left.1, &right.1)) {
            return Err(EqualityError::ExpectedEqual(left.1.clone(), right.1.clone()).into());
        }
    }

    assert_eq(left, phi)?;
    assert_eq(right, phi_prime)
}

pub fn la_mult_pos(args: RuleArgs) -> RuleResult {
    la_mult_generic(args.conclusion, true)
}

pub fn la_mult_neg(args: RuleArgs) -> RuleResult {
    la_mult_generic(args.conclusion, false)
}

fn la_mult_generic(conclusion: &[Rc<Term>], is_pos: bool) -> RuleResult {
    use rug::Rational;

    fn match_comparison_term(
        op: Operator,
        term: &Rc<Term>,
    ) -> Result<(&Rc<Term>, &Rc<Term>), CheckerError> {
        match op {
            Operator::Equals => match_term_err!((= a b) = term),
            Operator::LessThan => match_term_err!((< a b) = term),
            Operator::GreaterThan => match_term_err!((> a b) = term),
            Operator::LessEq => match_term_err!((<= a b) = term),
            Operator::GreaterEq => match_term_err!((>= a b) = term),
            _ => unreachable!(),
        }
    }

    assert_clause_len(conclusion, 1)?;
    let (m_comparison, original, scaled) =
        match_term_err!((=> (and m_comparison original) scaled) = &conclusion[0])?;
    let (m, zero) = if is_pos {
        match_term_err!((> m zero) = m_comparison)
    } else {
        match_term_err!((< m zero) = m_comparison)
    }?;
    rassert!(
        zero.as_number_err()? == 0,
        CheckerError::ExpectedNumber(Rational::new(), zero.clone())
    );

    let (op, args) = original.as_op_err()?;
    // Modified in Clean: an operator other than a comparison, such as `(cl x y)`'s, reached the
    // `unreachable!()`s below (see third-party/carcara/DOWNSTREAM.md, "Malformed steps are refused,
    // not a panic").
    if !matches!(
        op,
        Operator::Equals
            | Operator::LessThan
            | Operator::GreaterThan
            | Operator::LessEq
            | Operator::GreaterEq
    ) {
        return Err(CheckerError::ExpectedComparisonOp(original.clone()));
    }
    assert_operation_len(op, args, 2)?;
    let (l, r) = (&args[0], &args[1]);

    let op = if is_pos {
        op
    } else {
        match op {
            Operator::Equals => Operator::Equals,
            Operator::LessThan => Operator::GreaterThan,
            Operator::GreaterThan => Operator::LessThan,
            Operator::LessEq => Operator::GreaterEq,
            Operator::GreaterEq => Operator::LessEq,
            _ => unreachable!(),
        }
    };

    let (ml, mr) = match_comparison_term(op, scaled)?;
    let ((m_1, l_1), (m_2, r_2)) = (
        match_term_err!((* m l) = ml)?,
        match_term_err!((* m r) = mr)?,
    );
    assert_eq(m, m_1)?;
    assert_eq(m, m_2)?;

    assert_eq(l, l_1)?;
    assert_eq(r, r_2)
}

pub fn la_mult_sign(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    #[derive(Clone, Copy, PartialEq)]
    enum Comparison {
        Less,
        Greater,
        NotEq,
    }

    assert_clause_len(conclusion, 1)?;
    let (comparisons, right) = match_term_err!((=> left right) = &conclusion[0])?;
    let comparisons = match comparisons.as_ref() {
        Term::Op(Operator::And, args) => args.as_slice(),
        _ => std::slice::from_ref(comparisons),
    };
    let map: HashMap<_, _> = comparisons
        .iter()
        .map(|comp| {
            if let Some(var) = match_term!((< var 0) = comp) {
                Ok((var, Comparison::Less))
            } else if let Some(var) = match_term!((> var 0) = comp) {
                Ok((var, Comparison::Greater))
            } else if let Some(var) = match_term!((not (= var 0)) = comp) {
                Ok((var, Comparison::NotEq))
            } else {
                Err(CheckerError::ExpectedComparisonOp(comp.clone()))
            }
        })
        .collect::<Result<_, _>>()?;

    let (monomial, monomial_comp) = {
        if let Some(var) = match_term!((< mono 0) = right) {
            (var, Comparison::Less)
        } else if let Some(var) = match_term!((> mono 0) = right) {
            (var, Comparison::Greater)
        } else {
            return Err(CheckerError::ExpectedComparisonOp(right.clone()));
        }
    };
    let monomial = match monomial.as_ref() {
        Term::Op(Operator::Mult, args) => args.as_slice(),
        _ => std::slice::from_ref(monomial),
    };
    let multiset: MultiSet<_> = monomial.iter().collect();

    // We interate directly on the underlying hashmap of the multiset (`.0`), so we can get at the
    // (term, quantity) pairs.
    let got = multiset
        .0
        .into_iter()
        .map(|(var, quantity)| {
            // Modified in Clean: a factor of the monomial with no sign hypothesis is refused. It
            // reached a `todo!()` (see third-party/carcara/DOWNSTREAM.md, "Malformed steps are
            // refused, not a panic").
            let Some(comp) = map.get(var) else {
                return Err(CheckerError::Explanation(format!(
                    "no sign hypothesis for the factor '{}'",
                    var
                )));
            };
            // The contribution for this variable will always be `>` if its power is even
            Ok(if quantity % 2 == 0 {
                Comparison::Greater
            } else {
                *comp
            })
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .reduce(|a, b| match (a, b) {
            // negative * negative = negative
            (Comparison::Less, Comparison::Less) => Comparison::Greater,

            // positive * whatever = whatever
            (Comparison::Greater, other) | (other, Comparison::Greater) => other,

            // otherwise we don't know the sign
            (Comparison::NotEq, _) | (_, Comparison::NotEq) => Comparison::NotEq,
        })
        .unwrap();

    if got == monomial_comp {
        Ok(())
    } else {
        Err(CheckerError::LaMultSignWrongRelation(right.clone()))
    }
}

pub fn la_mult_abs_comparison(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (root_op, t, s) =
        if let Some((t, s)) = match_term!((= (abs (* ...)) (abs (* ...))) = &conclusion[0]) {
            (Operator::Equals, t, s)
        } else {
            let (t, s) = match_term_err!((> (abs (* ...)) (abs (* ...))) = &conclusion[0])?;
            (Operator::GreaterThan, t, s)
        };

    if t.len() != s.len() {
        return Err(CheckerError::WrongNumberOfTermsInOp(
            Operator::Mult,
            t.len().into(),
            s.len(),
        ));
    }
    assert_num_premises(premises, t.len())?;

    for (i, (premise, (ti, si))) in premises.iter().zip(t.iter().zip(s)).enumerate() {
        let premise = get_premise_term(premise)?;
        let (prem_ti, prem_si) = if root_op == Operator::Equals {
            match_term_err!((= (abs ti) (abs si)) = premise)?
        } else if i == 0 {
            // If the root operator is `>`, The first premise must have the `>` form
            match_term_err!((> (abs ti) (abs si)) = premise)?
        } else if let Some((prem_ti, prem_si)) =
            match_term!((and (= (abs ti) (abs si)) (not (= ti 0))) = premise)
        {
            // ...but all others can optionally have this different form
            (prem_ti, prem_si)
        } else {
            match_term_err!((> (abs ti) (abs si)) = premise)?
        };

        assert_eq(ti, prem_ti)?;
        assert_eq(si, prem_si)?;
    }

    Ok(())
}

pub fn mod_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (t1, t2) = match_term_err!((mod t1 t2) = left)?;

    let [a, b] = [t1, t2].map(|term| {
        let value = term.as_signed_number_err()?;
        if !value.is_integer() {
            return Err(CheckerError::ExpectedAnyInteger(term.clone()));
        }
        Ok(value.into_numer_denom().0)
    });
    // I wouldn't need to do this if `array_try_map` was stable:
    // https://github.com/rust-lang/rust/issues/79711
    let [a, b] = [a?, b?];

    let result = right.as_signed_number_err()?;

    if b.is_zero() {
        return Err(CheckerError::DivOrModByZero);
    }

    let expected = a.modulo(&b);
    rassert!(
        result == expected,
        CheckerError::ExpectedNumber(expected.into(), right.clone())
    );
    Ok(())
}

pub fn evaluate(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (term, value) = match_term_err!((= term value) = &conclusion[0])?;
    assert_eq(&term.evaluate(pool)?, value)
}

pub fn beta_equiv(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= left right) = &conclusion[0])?;

    let Term::App(lambda, args) = left.as_ref() else {
        return Err(CheckerError::TermOfWrongForm(
            "((lambda ... body) args)",
            left.clone(),
        ));
    };
    let (left_bindings, left) = match_term_err!((lambda ... body) = lambda)?;

    let (right_bindings, right) = if args.len() == left_bindings.len() {
        (BindingList::EMPTY, right)
    } else {
        match_term_err!((lambda ... body) = right)?
    };

    if args.len() > left_bindings.len() {
        return Err(CheckerError::TermOfWrongForm(
            "((lambda ... body) args)",
            left.clone(),
        ));
    }
    let remaining_bindings = &left_bindings[args.len()..];
    if remaining_bindings != right_bindings.as_slice() {
        // We avoid calling `to_vec` until we know for sure the rule will fail
        let list = BindingList(remaining_bindings.to_vec());
        return Err(EqualityError::ExpectedEqual(list, right_bindings.clone()).into());
    }

    // Modified in Clean: in a partial application the remaining binders stay in scope, so an
    // argument whose free variable has the name of a remaining binder would be captured by the
    // result `(lambda remaining body[args])`. Such an instance is not a beta reduction and is
    // refused (see third-party/carcara/DOWNSTREAM.md).
    // Likewise, an applied binder shadowed by a remaining binder of the same name does not reach
    // the body, so substituting for it would be wrong.
    // Modified in Clean: the remaining binders' names are looked up in a set, not compared with each
    // applied binder (quadratic in the binders: 20,000 of each took 0.6 s).
    let remaining: std::collections::HashSet<&str> = remaining_bindings
        .iter()
        .map(|(bound, _)| bound.as_str())
        .collect();
    if let Some((name, _)) = left_bindings[..args.len()]
        .iter()
        .find(|(applied, _)| remaining.contains(applied.as_str()))
    {
        return Err(CheckerError::Explanation(format!(
            "applied binder '{}' is shadowed by a remaining binder",
            name
        )));
    }
    // Modified in Clean: the variables that would be captured are found by reading whichever is
    // shorter, the argument's free variables or the remaining binders' names, and when several
    // would be captured the message names the one `first_free_var` chooses (see
    // third-party/carcara/DOWNSTREAM.md, "Free-variable sets share structure").
    for arg in args {
        let free = pool.free_vars(arg);
        if free.is_empty() {
            continue;
        }
        let captured = if free.len() <= remaining.len() {
            free.filter(|var| var.as_var().is_some_and(|name| remaining.contains(name)))
        } else {
            let mut captured = FreeVars::default();
            for bound in &remaining {
                for var in free.named(bound) {
                    captured = captured.union(&FreeVars::singleton(var));
                }
            }
            captured
        };
        if let Some(var) = first_free_var(pool, arg, &captured) {
            return Err(CheckerError::Explanation(format!(
                "argument '{}' would be captured by the remaining binder '{}'",
                arg,
                var.as_var().unwrap()
            )));
        }
    }

    let substitution = left_bindings
        .iter()
        .zip(args)
        .map(|(var, value)| (pool.add(var.clone().into()), value.clone()))
        .collect();
    let reduced = Substitution::new(pool, substitution)?.apply(pool, left);
    assert_eq(&reduced, right)
}

pub fn div_intro(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (b, _, c) =
        match_term_err!((and (<= (* b (div a b)) a) (< a (* b (+ (div a b) c)))) = &conclusion[0])?;

    let b = b.as_signed_number_err()?;
    if b.is_zero() {
        return Err(CheckerError::DivOrModByZero);
    }
    let expected = if b.is_positive() { 1 } else { -1 };
    if c.as_signed_number_err()? != expected {
        return Err(CheckerError::ExpectedNumber(expected.into(), c.clone()));
    }

    Ok(())
}

pub fn log2_intro(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    match_term_err!(
        (and
            (=> (< 0 x) (and (<= (int_pow2 (int_log2 x)) x) (< x (int_pow2 (+ (int_log2 x) 1)))))
            (=> (not (< 0 x)) (= (int_log2 x) 0))
        ) = &conclusion[0]
    )?;
    Ok(())
}

pub fn to_int_intro(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    match_term_err!(
        (and (<= 0 (- x (to_real (to_int x)))) (< (- x (to_real (to_int x))) 1))
        = &conclusion[0]
    )?;
    Ok(())
}
