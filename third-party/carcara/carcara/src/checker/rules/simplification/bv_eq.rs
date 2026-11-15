// Added in Clean (not upstream Carcara): scalar equality in Z/(2^w).
// See DOWNSTREAM.md, dialect:eq_simplify_bv_offsets.
//
// Adding a fixed word is a bijection, so x+a=x+b iff a=b, including
// wraparound. The common word is an opaque, identical hash-consed term.
// There are no aliases, hypotheses, arithmetic normalization or solver calls.

use crate::{
    ast::{pool::TermPool, Constant, Operator, Rc, Sort, Term},
    checker::error::CheckerError,
};

const MAX_WORK: usize = 256;

/// Every slot read, cached sort lookup, pointer comparison and at-most-two-limb
/// literal inspection is charged BEFORE it runs. Both orientations and failed
/// candidates share one fixed budget. The inspector borrows all terms: no
/// private heap and no intermediate equality/Boolean term is materialized.
struct Inspector<'a> {
    pool: &'a dyn TermPool,
    remaining: usize,
    refused: bool,
}

#[derive(Clone, Copy)]
struct Offset<'a> {
    base: &'a Rc<Term>,
    literal: &'a Rc<Term>,
    value: u128,
}

impl Inspector<'_> {
    fn spend(&mut self, units: usize) -> Option<()> {
        match self.remaining.checked_sub(units) {
            Some(next) if !self.refused => {
                self.remaining = next;
                Some(())
            }
            _ => {
                self.refused = true;
                None
            }
        }
    }

    fn binary<'a>(
        &mut self,
        term: &'a Rc<Term>,
        op: Operator,
    ) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
        self.spend(4)?;
        let Term::Op(actual, args) = term.as_ref() else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        (*actual == op).then_some((left, right))
    }

    fn is_bool(&mut self, term: &Rc<Term>) -> Option<()> {
        self.spend(3)?;
        matches!(self.pool.sort(term).as_ref(), Sort::Bool).then_some(())
    }

    fn width(&mut self, term: &Rc<Term>) -> Option<usize> {
        self.spend(3)?;
        match self.pool.sort(term).as_ref() {
            Sort::BitVec(width) if (1..=128).contains(width) => Some(*width),
            _ => None,
        }
    }

    fn literal(&mut self, term: &Rc<Term>, width: usize) -> Option<u128> {
        self.spend(12)?;
        let Term::Const(Constant::BitVec(value, literal_width)) = term.as_ref() else {
            return None;
        };
        if *literal_width != width || value.is_negative() || value.significant_bits() > width as u32
        {
            return None;
        }
        // The checks above bound the conversion to two machine limbs; no
        // modulus, arbitrary-size clone or numeric allocation is needed.
        value.to_u128()
    }

    fn offsets<'a>(&mut self, term: &'a Rc<Term>, width: usize) -> Option<[Option<Offset<'a>>; 2]> {
        let (left, right) = self.binary(term, Operator::BvAdd)?;
        if self.width(term)? != width || self.width(left)? != width || self.width(right)? != width {
            return None;
        }
        Some([
            self.literal(right, width)
                .map(|value| Offset { base: left, literal: right, value }),
            self.literal(left, width)
                .map(|value| Offset { base: right, literal: left, value }),
        ])
    }

    fn target(
        &mut self,
        target: &Rc<Term>,
        a: &Rc<Term>,
        b: &Rc<Term>,
        equal: bool,
    ) -> Option<bool> {
        self.is_bool(target)?;
        self.spend(2)?;
        if target.is_bool_constant(equal) {
            return Some(true);
        }
        let (left, right) = self.binary(target, Operator::Equals)?;
        self.spend(2)?;
        Some(left == a && right == b)
    }

    fn direction(&mut self, source: &Rc<Term>, target: &Rc<Term>) -> Option<bool> {
        self.is_bool(source)?;
        let (left, right) = self.binary(source, Operator::Equals)?;
        let width = self.width(left)?;
        if self.width(right)? != width {
            return None;
        }
        if let (Some(a), Some(b)) = (self.literal(left, width), self.literal(right, width)) {
            self.is_bool(target)?;
            self.spend(2)?;
            return Some(target.is_bool_constant(a == b));
        }
        let left = self.offsets(left, width)?;
        let right = self.offsets(right, width)?;
        for a in left.into_iter().flatten() {
            for b in right.into_iter().flatten() {
                self.spend(1)?;
                if a.base == b.base
                    && self.target(target, a.literal, b.literal, a.value == b.value)?
                {
                    return Some(true);
                }
            }
        }
        Some(false)
    }
}

pub(super) fn holds(conclusion: &[Rc<Term>], pool: &dyn TermPool) -> Result<bool, CheckerError> {
    holds_with_budget(conclusion, pool, MAX_WORK)
}

fn holds_with_budget(
    conclusion: &[Rc<Term>],
    pool: &dyn TermPool,
    remaining: usize,
) -> Result<bool, CheckerError> {
    let mut inspect = Inspector { pool, remaining, refused: false };
    let accepted = (|| {
        inspect.spend(1)?;
        let [root] = conclusion else { return None };
        inspect.is_bool(root)?;
        let (left, right) = inspect.binary(root, Operator::Equals)?;
        if inspect.direction(left, right).unwrap_or(false) {
            return Some(true);
        }
        inspect.direction(right, left)
    })()
    .unwrap_or(false);
    if inspect.refused {
        Err(CheckerError::BvEqSimplifyWorkExceeded)
    } else {
        Ok(accepted)
    }
}

#[cfg(test)]
mod tests;
