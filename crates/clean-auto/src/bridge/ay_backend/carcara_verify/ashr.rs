// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bound the domain of the pinned arithmetic-right-shift bitblast rule.
//!
//! Upstream Carcara d62d45cf fills overshifts with zero, including negative
//! operands. Its rule is sound when the operand is nonnegative or the shift
//! cannot reach the width. Reject all other instances before normal checking;
//! this does not introduce a replacement rule or trust a producer's result.
//!
//! The vendored copy in `third-party/carcara` now fills with the sign bit, as
//! SMT-LIB `bvashr` requires. This guard stays as defense in depth: it only
//! refuses, and never accepts, a step.

use carcara::ast::{pool::TermPool, Operator, ProofStep, Rc, Sort, Term};

pub(super) fn safe_shift(step: &ProofStep, pool: &mut dyn TermPool) -> bool {
    if step.rule != "bitblast_ashr" {
        return true;
    }
    let result = (|| {
        let [clause] = step.clause.as_slice() else {
            return None;
        };
        let Term::Op(Operator::Equals, sides) = clause.as_ref() else {
            return None;
        };
        let [source, _] = sides.as_slice() else {
            return None;
        };
        let Term::Op(Operator::BvAShr, operands) = source.as_ref() else {
            return None;
        };
        let [word, amount] = operands.as_slice() else {
            return None;
        };
        let Sort::BitVec(width) = pool.sort(word).as_ref().clone() else {
            return None;
        };
        if width == 0 || pool.sort(amount).as_ref() != &Sort::BitVec(width) {
            return None;
        }
        Some(nonnegative(word, width) || below_width(amount, width))
    })();
    result == Some(true)
}

fn nonnegative(word: &Rc<Term>, width: usize) -> bool {
    if let Some((value, actual)) = word.as_bitvector() {
        return actual == width && value >= 0 && (value.significant_bits() as usize) < width;
    }
    matches!(word.as_ref(), Term::Op(Operator::BvBbTerm, bits)
        if bits.len() == width && bits.last().is_some_and(|bit| bit.is_bool_false()))
}

fn below_width(amount: &Rc<Term>, width: usize) -> bool {
    if let Some((value, actual)) = amount.as_bitvector() {
        return actual == width && value >= 0 && value < width;
    }
    let Term::Op(Operator::BvBbTerm, bits) = amount.as_ref() else {
        return false;
    };
    if bits.len() != width {
        return false;
    }
    let mut largest = 0usize;
    for (i, bit) in bits.iter().enumerate() {
        if bit.is_bool_false() {
            continue;
        }
        // Unknown bits may be one. Use their joint upper bound without
        // assuming independence, Boolean identities, or surrounding guards.
        let Some(weight) = u32::try_from(i).ok().and_then(|i| 1usize.checked_shl(i)) else {
            return false;
        };
        largest |= weight;
        if largest >= width {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests;
