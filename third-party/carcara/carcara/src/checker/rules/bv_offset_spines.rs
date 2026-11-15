// Added in Clean (not upstream Carcara): dialect:eq_simplify_bv_offset_spines_v1.
//
// Each peeled frame adds or subtracts one canonical literal in Z/(2^w).
// Induction gives value(S) = value(base(S)) + offset(S). For identical opaque
// bases, equality is therefore exactly equality of their modular offsets.
// This checker recomputes the judgement, without trusting producer offsets,
// aliases or paths, and without constructing intermediate terms.

use super::{Premise, RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, Constant, Operator, ProofCommand, Rc, Sort, Term},
    checker::{deadline, error::CheckerError},
};

const MAX_FRAMES: usize = 16;
const MAX_WORK: usize = 8_192;

/// Accounting table, including failed candidates and the one over-limit
/// lookahead per side:
///
/// - schema, both root/Boolean orientations, width and mask: <= 256 units;
/// - one loop visit: <= 192 units (deadline 8, current sort/literal/head 30,
///   child slots/sorts/literals 50, decisions/arithmetic/state <= 32, with
///   remaining slack for loop and option dispatch);
/// - endpoint pointer/offset/truth comparison: <= 32 units.
///
/// Thus 34 visits * 192 + 256 + 32 = 6816 < 8192. Every bounded operation is
/// charged before it runs. The reserve is never reset for another direction
/// or side. All state is borrowed or fixed-size stack data; zero private heap,
/// no BigInt clone, argument vector, map, memo table or materialized term.
struct Inspector<'a, 'p> {
    pool: &'a dyn TermPool,
    remaining: usize,
    stopped: Option<Stop>,
    expired: &'p mut dyn FnMut() -> bool,
}

#[derive(Clone, Copy)]
enum Stop {
    Work,
    Deadline,
}

struct Spine<'a> {
    base: &'a Rc<Term>,
    offset: u128,
}

enum Frame<'a> {
    Base,
    Add(&'a Rc<Term>, u128),
    Sub(&'a Rc<Term>, u128),
}

impl Inspector<'_, '_> {
    fn spend(&mut self, work: usize) -> Option<()> {
        if self.stopped.is_some() {
            return None;
        }
        match self.remaining.checked_sub(work) {
            Some(next) => {
                self.remaining = next;
                Some(())
            }
            None => {
                self.stopped = Some(Stop::Work);
                None
            }
        }
    }

    fn poll(&mut self) -> Option<()> {
        self.spend(8)?;
        if (self.expired)() {
            self.stopped = Some(Stop::Deadline);
            None
        } else {
            Some(())
        }
    }

    fn is_bool(&mut self, term: &Rc<Term>) -> Option<()> {
        self.spend(6)?;
        matches!(self.pool.sort(term).as_ref(), Sort::Bool).then_some(())
    }

    fn width(&mut self, term: &Rc<Term>) -> Option<usize> {
        self.spend(6)?;
        match self.pool.sort(term).as_ref() {
            Sort::BitVec(width) if (1..=128).contains(width) => Some(*width),
            _ => None,
        }
    }

    fn boolean(&mut self, term: &Rc<Term>) -> Option<bool> {
        self.is_bool(term)?;
        self.spend(6)?;
        match term.as_ref() {
            Term::Op(Operator::True, args) if args.is_empty() => Some(true),
            Term::Op(Operator::False, args) if args.is_empty() => Some(false),
            _ => None,
        }
    }

    fn equality<'a>(&mut self, term: &'a Rc<Term>) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
        self.spend(6)?;
        let Term::Op(Operator::Equals, args) = term.as_ref() else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        self.is_bool(term)?;
        Some((left, right))
    }

    /// `Some(None)` is a nonliteral; `None` refuses a malformed encountered
    /// literal or exhausted budget. A malformed literal must not become a base.
    fn literal(&mut self, term: &Rc<Term>, width: usize) -> Option<Option<u128>> {
        self.spend(16)?;
        let Term::Const(Constant::BitVec(value, actual_width)) = term.as_ref() else {
            return Some(None);
        };
        if *actual_width != width || value.is_negative() || value.significant_bits() > width as u32
        {
            return None;
        }
        // Width and canonical sign/bit count bound this to two 64-bit words.
        // No arbitrary-size arithmetic, modulus or literal clone is needed.
        Some(Some(value.to_u128()?))
    }

    fn frame<'a>(&mut self, term: &'a Rc<Term>, width: usize) -> Option<Frame<'a>> {
        self.spend(6)?;
        let Term::Op(op @ (Operator::BvAdd | Operator::BvSub), args) = term.as_ref() else {
            return Some(Frame::Base);
        };
        self.spend(4)?;
        let [left, right] = args.as_slice() else {
            return None;
        };
        if self.width(left)? != width || self.width(right)? != width {
            return None;
        }
        let a = self.literal(left, width)?;
        let b = self.literal(right, width)?;
        self.spend(8)?;
        match (op, a, b) {
            (_, Some(_), Some(_)) => None,
            (Operator::BvAdd, Some(k), None) => Some(Frame::Add(right, k)),
            (Operator::BvAdd, None, Some(k)) => Some(Frame::Add(left, k)),
            (Operator::BvSub, None, Some(k)) => Some(Frame::Sub(left, k)),
            // Nonliteral addition, symbolic subtraction and literal-left
            // subtraction stay opaque. Their interiors grant no arithmetic
            // authority; the parsed pipeline retains its typing obligations.
            _ => Some(Frame::Base),
        }
    }

    fn spine<'a>(&mut self, mut term: &'a Rc<Term>, width: usize, mask: u128) -> Option<Spine<'a>> {
        // Prepay fixed state and every bounded loop-control operation before
        // constructing the iterator; early refusals keep that debit.
        self.spend(8 + 2 * (MAX_FRAMES + 1))?;
        let mut offset = 0u128;
        for frames in 0..=MAX_FRAMES {
            self.poll()?;
            if self.width(term)? != width || self.literal(term, width)?.is_some() {
                return None;
            }
            match self.frame(term, width)? {
                Frame::Base => {
                    self.spend(4)?;
                    return Some(Spine { base: term, offset });
                }
                Frame::Add(_, _) | Frame::Sub(_, _) if frames == MAX_FRAMES => {
                    // Inspect, but never peel or silently hide, frame 17.
                    return None;
                }
                Frame::Add(next, k) => {
                    self.spend(8)?;
                    offset = offset.wrapping_add(k) & mask;
                    term = next;
                }
                Frame::Sub(next, k) => {
                    self.spend(8)?;
                    offset = offset.wrapping_sub(k) & mask;
                    term = next;
                }
            }
        }
        None
    }

    fn holds(
        &mut self,
        conclusion: &[Rc<Term>],
        premises: &[Premise<'_>],
        args: &[Rc<Term>],
        discharge: &[&ProofCommand],
    ) -> Option<bool> {
        self.poll()?;
        self.spend(12)?;
        if !premises.is_empty() || !args.is_empty() || !discharge.is_empty() {
            return None;
        }
        let [root] = conclusion else { return None };
        let (left, right) = self.equality(root)?;
        let (source, truth) = match (self.boolean(left), self.boolean(right)) {
            (None, Some(truth)) => (left, truth),
            (Some(truth), None) => (right, truth),
            _ => return None,
        };
        let (left, right) = self.equality(source)?;
        let width = self.width(left)?;
        if self.width(right)? != width {
            return None;
        }
        self.spend(8)?;
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let left = self.spine(left, width, mask)?;
        let right = self.spine(right, width, mask)?;
        self.spend(8)?;
        Some(left.base == right.base && (left.offset == right.offset) == truth)
    }
}

pub fn validate(args: RuleArgs<'_>) -> RuleResult {
    let mut expired = deadline::expired_now;
    validate_with_control(args, MAX_WORK, &mut expired)
}

fn validate_with_control(
    args: RuleArgs<'_>,
    work: usize,
    expired: &mut dyn FnMut() -> bool,
) -> RuleResult {
    let RuleArgs {
        conclusion,
        premises,
        args,
        pool,
        discharge,
        ..
    } = args;
    let mut inspect = Inspector {
        pool,
        remaining: work,
        stopped: None,
        expired,
    };
    // Borrowed views only; no intermediate terms or arithmetic proof producer.
    let holds = inspect
        .holds(conclusion, premises, args, discharge)
        .unwrap_or(false);
    match (inspect.stopped, holds) {
        (Some(Stop::Work), _) => Err(CheckerError::BvOffsetSpinesWorkExceeded),
        (Some(Stop::Deadline), _) => Err(CheckerError::DeadlineExceeded),
        (None, true) => Ok(()),
        (None, false) => Err(CheckerError::BvOffsetSpinesInvalid),
    }
}

#[cfg(test)]
mod tests;
