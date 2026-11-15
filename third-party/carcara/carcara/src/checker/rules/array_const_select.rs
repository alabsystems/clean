// Added in Clean: dialect:array_const_select_v1.
//
// Independently inspect the freshly parsed native AST. The exact theorem is
// select(const-array(fill), key) = fill, in either equality orientation.
// The v1 carrier is Bool fill atoms and flat Bool/Int/BV<=128 index atoms;
// Int literals are at most 128 significant bits. Nothing is evaluated, no
// solver result is trusted, and no term or owned name is cloned.

use super::{RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, Constant, Operator, QualifiedOperator, Rc, Sort, Term},
    checker::{deadline, error::CheckerError},
};

const WORK: usize = 64;

fn bool_atom(t: &Rc<Term>) -> bool {
    match t.as_ref() {
        Term::Var(_, sort) => matches!(sort.as_ref(), Sort::Bool),
        Term::Op(Operator::True | Operator::False, args) => args.is_empty(),
        _ => false,
    }
}

fn index_atom(t: &Rc<Term>) -> bool {
    match t.as_ref() {
        Term::Var(_, sort) => match sort.as_ref() {
            Sort::Bool | Sort::Int => true,
            Sort::BitVec(width) => (1..=128).contains(width),
            _ => false,
        },
        Term::Op(Operator::True | Operator::False, args) => args.is_empty(),
        Term::Const(Constant::Integer(value)) => value.significant_bits() <= 128,
        // AY prints a negative Int literal as SMT-LIB unary minus. Accept
        // exactly that parsed literal representation, not arithmetic keys.
        Term::Op(Operator::Sub, args) => matches!(args.as_slice(), [value]
            if matches!(value.as_ref(),Term::Const(Constant::Integer(value)) if !value.is_negative() && value.significant_bits() <= 128)),
        Term::Const(Constant::BitVec(value, width)) => {
            (1..=128).contains(width)
                && !value.is_negative()
                && value.significant_bits() <= *width as u32
        }
        _ => false,
    }
}

fn holds(pool: &dyn TermPool, clause: &[Rc<Term>]) -> bool {
    let [equality] = clause else { return false };
    let Term::Op(Operator::Equals, sides) = equality.as_ref() else {
        return false;
    };
    let [left, right] = sides.as_slice() else {
        return false;
    };
    for (read, fill) in [(left, right), (right, left)] {
        if !bool_atom(fill) {
            continue;
        }
        let Term::Op(Operator::Select, children) = read.as_ref() else {
            continue;
        };
        let [array, key] = children.as_slice() else {
            continue;
        };
        if !index_atom(key) {
            continue;
        }
        let Term::AsOp(QualifiedOperator::Const, sort, values) = array.as_ref() else {
            continue;
        };
        let [actual_fill] = values.as_slice() else {
            continue;
        };
        let Sort::Array(index, element) = sort.as_ref() else {
            continue;
        };
        // Since the key is a flat atom, descriptor comparison is constant
        // bounded work; malformed compound descriptors fail by discriminant.
        if !matches!(element.as_ref(), Sort::Bool)
            || index.as_ref() != pool.sort(key).as_ref()
            || actual_fill != fill
        {
            continue;
        }
        return true;
    }
    false
}

pub fn validate(args: RuleArgs<'_>) -> RuleResult {
    validate_with_control(args, WORK, &mut deadline::expired_now)
}

fn validate_with_control(
    args: RuleArgs<'_>,
    work: usize,
    expired: &mut dyn FnMut() -> bool,
) -> RuleResult {
    if work < WORK {
        return Err(CheckerError::ArrayConstSelectWorkExceeded);
    }
    if expired() {
        return Err(CheckerError::DeadlineExceeded);
    }
    if !args.premises.is_empty()
        || !args.args.is_empty()
        || !args.discharge.is_empty()
        || !holds(args.pool, args.conclusion)
    {
        return Err(CheckerError::ArrayConstSelectInvalid);
    }
    if expired() {
        return Err(CheckerError::DeadlineExceeded);
    }
    Ok(())
}

#[cfg(test)]
mod tests;
