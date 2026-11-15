// Added in Clean, not upstream Carcara: dialect:bv_reconstruct_v1.
//
// Inspect the actual parsed AST. Each extract contributes its original bit
// positions through OR, literal shifts and zero extensions. An independent
// 128-entry occupancy array checks disjoint complete coverage. The identical
// opaque word is compared by pool pointer, never by traversing its body.
// Clean's existing parser reads zero_extend(k,t) as concat(0_k,t), or t for
// k=0. Exactly that canonical zero-prefix concat is also an extension here;
// the parser contract and every other checker rule remain unchanged.

use super::{Premise, RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, Constant, Operator, ParamOperator, ProofCommand, Rc, Sort, Term},
    checker::{deadline, error::CheckerError},
};

const WORK: usize = 524_288;
const BYTES: usize = 16_384;
const MAX_NODES: usize = 2_048;
const MAX_DEPTH: usize = 256;

#[derive(Clone, Copy)]
struct Pending<'a> {
    term: &'a Rc<Term>,
    width: usize,
    destination: usize,
    boundary: usize,
    depth: usize,
}

struct Inspector<'a, 'p> {
    pool: &'a dyn TermPool,
    work: usize,
    stop: Option<Stop>,
    expired: &'p mut dyn FnMut() -> bool,
    nodes: usize,
}
#[derive(Clone, Copy)]
enum Stop {
    Work,
    Deadline,
}

impl Inspector<'_, '_> {
    fn charge(&mut self, n: usize) -> Option<()> {
        if self.stop.is_some() {
            return None;
        }
        match self.work.checked_sub(n) {
            Some(remaining) => {
                self.work = remaining;
                Some(())
            }
            None => {
                self.stop = Some(Stop::Work);
                None
            }
        }
    }
    fn poll(&mut self) -> Option<()> {
        self.charge(8)?;
        if (self.expired)() {
            self.stop = Some(Stop::Deadline);
            None
        } else {
            Some(())
        }
    }
    fn visit(&mut self, depth: usize) -> Option<()> {
        // Fixed per-occurrence reservation includes all head/slot/index/sort
        // and bounded literal operations below, including failed branches.
        self.charge(128)?;
        self.poll()?;
        self.nodes = self.nodes.checked_add(1)?;
        (self.nodes <= MAX_NODES && depth <= MAX_DEPTH).then_some(())
    }
    fn width(&self, t: &Rc<Term>) -> Option<usize> {
        match self.pool.sort(t).as_ref() {
            Sort::BitVec(w) if (1..=128).contains(w) => Some(*w),
            _ => None,
        }
    }
    fn literal(&self, t: &Rc<Term>, width: usize) -> Option<Option<u128>> {
        if self.width(t) != Some(width) {
            return None;
        }
        Some(match t.as_ref() {
            Term::Const(Constant::BitVec(value, w)) => {
                if *w != width || value.is_negative() || value.significant_bits() > width as u32 {
                    return None;
                }
                Some(value.to_u128()?)
            }
            Term::Const(_) => return None,
            _ => None,
        })
    }
    fn index(&self, t: &Rc<Term>) -> Option<usize> {
        if !matches!(self.pool.sort(t).as_ref(), Sort::Int) {
            return None;
        }
        let Term::Const(Constant::Integer(value)) = t.as_ref() else {
            return None;
        };
        if value.is_negative() || value.significant_bits() > 8 {
            return None;
        }
        value.to_usize()
    }
    fn holds(
        &mut self,
        conclusion: &[Rc<Term>],
        premises: &[Premise<'_>],
        args: &[Rc<Term>],
        discharge: &[&ProofCommand],
    ) -> Option<bool> {
        // Fixed header/scratch admission precedes payload inspection and stack
        // initialization. No fallback, private heap, integer clone or terms.
        self.charge(4096)?;
        self.poll()?;
        if !premises.is_empty() || !args.is_empty() || !discharge.is_empty() {
            return None;
        }
        let [root] = conclusion else {
            return None;
        };
        let Term::Op(Operator::Equals, pair) = root.as_ref() else {
            return None;
        };
        let [packed, word] = pair.as_slice() else {
            return None;
        };
        if !matches!(self.pool.sort(root).as_ref(), Sort::Bool) {
            return None;
        }
        let width = self.width(word)?;
        if self.width(packed) != Some(width) {
            return None;
        }
        self.literal(word, width)?;
        let mut pending = [None; MAX_DEPTH + 1];
        pending[0] = Some(Pending {
            term: packed,
            width,
            destination: 0,
            boundary: width,
            depth: 0,
        });
        let mut length = 1;
        let mut occupied = [false; 128];
        let mut covered = 0usize;
        while length > 0 {
            length -= 1;
            let current = pending[length].take()?;
            self.visit(current.depth)?;
            if self.width(current.term) != Some(current.width)
                || current.boundary > width
                || current.destination >= current.boundary
            {
                return None;
            }
            let (low, span) = if current.term == word {
                if current.width != width || current.destination != 0 || current.boundary < width {
                    return None;
                }
                (0usize, width)
            } else {
                if let Some(value) = self.literal(current.term, current.width)? {
                    if value != 0 {
                        return None;
                    }
                    continue;
                }
                let depth = current.depth.checked_add(1)?;
                let (first, second) = match current.term.as_ref() {
                    Term::Op(Operator::BvOr, children) => {
                        let [a, b] = children.as_slice() else {
                            return None;
                        };
                        (
                            Pending { term: a, depth, ..current },
                            Some(Pending { term: b, depth, ..current }),
                        )
                    }
                    Term::Op(Operator::BvShl, children) => {
                        let [value, amount] = children.as_slice() else {
                            return None;
                        };
                        self.visit(depth)?;
                        let amount = self.literal(amount, current.width)??;
                        if amount >= current.width as u128 {
                            return None;
                        }
                        let destination = current
                            .destination
                            .checked_add(usize::try_from(amount).ok()?)?;
                        if destination >= current.boundary {
                            return None;
                        }
                        (
                            Pending {
                                term: value,
                                destination,
                                depth,
                                ..current
                            },
                            None,
                        )
                    }
                    Term::ParamOp {
                        op: ParamOperator::ZeroExtend,
                        op_args,
                        args: children,
                    } => {
                        let [extra] = op_args.as_slice() else {
                            return None;
                        };
                        let extra = self.index(extra)?;
                        let [child] = children.as_slice() else {
                            return None;
                        };
                        let child_width = self.width(child)?;
                        if child_width.checked_add(extra)? != current.width {
                            return None;
                        }
                        let boundary = current
                            .boundary
                            .min(current.destination.checked_add(child_width)?);
                        (
                            Pending {
                                term: child,
                                width: child_width,
                                boundary,
                                depth,
                                ..current
                            },
                            None,
                        )
                    }
                    Term::Op(Operator::BvConcat, children) => {
                        let [prefix, child] = children.as_slice() else {
                            return None;
                        };
                        let prefix_width = self.width(prefix)?;
                        let child_width = self.width(child)?;
                        if self.literal(prefix, prefix_width)?? != 0
                            || prefix_width.checked_add(child_width)? != current.width
                        {
                            return None;
                        }
                        let boundary = current
                            .boundary
                            .min(current.destination.checked_add(child_width)?);
                        (
                            Pending {
                                term: child,
                                width: child_width,
                                boundary,
                                depth,
                                ..current
                            },
                            None,
                        )
                    }
                    Term::ParamOp {
                        op: ParamOperator::BvExtract,
                        op_args,
                        args: children,
                    } => {
                        let [high, low] = op_args.as_slice() else {
                            return None;
                        };
                        let high = self.index(high)?;
                        let low = self.index(low)?;
                        let [source] = children.as_slice() else {
                            return None;
                        };
                        if source != word
                            || self.width(source) != Some(width)
                            || high < low
                            || high >= width
                            || high.checked_sub(low)?.checked_add(1)? != current.width
                            || current.destination != low
                            || current.destination.checked_add(current.width)? > current.boundary
                        {
                            return None;
                        }
                        // At most 128 successful bit admissions and one refused
                        // overlap can occur across the entire attempt.
                        for bit in low..=high {
                            self.charge(8)?;
                            if occupied[bit] {
                                return None;
                            }
                            occupied[bit] = true;
                            covered += 1;
                        }
                        continue;
                    }
                    _ => return None,
                };
                if depth > MAX_DEPTH {
                    return None;
                }
                let count = 1 + usize::from(second.is_some());
                if length.checked_add(count)? > pending.len() {
                    return None;
                }
                pending[length] = Some(first);
                length += 1;
                if let Some(second) = second {
                    pending[length] = Some(second);
                    length += 1;
                }
                continue;
            };
            for bit in low..low.checked_add(span)? {
                self.charge(8)?;
                if occupied[bit] {
                    return None;
                }
                occupied[bit] = true;
                covered += 1;
            }
        }
        Some(covered == width)
    }
}

pub fn validate(args: RuleArgs<'_>) -> RuleResult {
    let mut expired = deadline::expired_now;
    validate_with_control(args, WORK, BYTES, &mut expired)
}
fn validate_with_control(
    args: RuleArgs<'_>,
    work: usize,
    bytes: usize,
    expired: &mut dyn FnMut() -> bool,
) -> RuleResult {
    // One fixed 16KiB private-state reservation. The fixed stack plus occupancy
    // array fits inside it; insufficient admission fails before all AST reads.
    if bytes < BYTES {
        return Err(CheckerError::BvReconstructWorkExceeded);
    }
    let RuleArgs {
        conclusion,
        premises,
        args,
        pool,
        discharge,
        ..
    } = args;
    let mut inspector = Inspector {
        pool,
        work,
        stop: None,
        expired,
        nodes: 0,
    };
    let holds = inspector
        .holds(conclusion, premises, args, discharge)
        .unwrap_or(false);
    match (inspector.stop, holds) {
        (Some(Stop::Work), _) => Err(CheckerError::BvReconstructWorkExceeded),
        (Some(Stop::Deadline), _) => Err(CheckerError::DeadlineExceeded),
        (None, true) => Ok(()),
        (None, false) => Err(CheckerError::BvReconstructInvalid),
    }
}

#[cfg(test)]
mod tests;
