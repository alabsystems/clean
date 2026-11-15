// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The order on canonical levels, `l1 >= l2` (Lean's `level.cpp:is_geq`).

use std::collections::HashMap;

use super::limit::Limit;
use super::{Level, Repr};

/// One comparison's work so far and the answers it has found (R172).
pub(super) struct Geq {
    spent: u64,
    seen: HashMap<(Level, Level), bool>,
}

impl Geq {
    pub(super) fn new() -> Geq {
        Geq {
            spent: 0,
            seen: HashMap::new(),
        }
    }
}

/// `is_geq` on canonical inputs: Lean's `is_geq_core` (`level.cpp`), rule
/// for rule and in its order (R172, R174). ck0's canonical forms are not
/// always Lean's normal forms; validation refuses the levels written in the
/// forms where the answers differ, and a level that instantiation builds can
/// still differ (R177's residue; both in `tests/level_as_written.rs`).
///
/// Against an `imax` spine the rules try both ways of splitting a `max`, and
/// Lean's comparison remembers nothing, so its steps grow exponentially in
/// the operands' depths: unremembered, in a debug build, a `max` of 16
/// parameters against a spine of 8 took 0.43 s, 18 against 9 took 2.8 s and
/// 20 against 10 took 17 s. The answer to each pair of operands is
/// remembered, so the steps are bounded by the pairs of their subterms. Each step is charged one plus both
/// operands' sizes, which bounds its hashing, comparing and offset copies;
/// under [`Bounded`] a comparison past [`super::MAX_LEVEL_GEQ_WORK`] is
/// refused. A comparison is a function of its operands, so remembering it
/// changes no answer.
///
/// [`Bounded`]: super::limit::Bounded
pub(super) fn is_geq_core<L: Limit>(
    l1: &Level,
    l2: &Level,
    cx: &mut Geq,
) -> Result<bool, L::Error> {
    // AUDIT: saturating; a count compared with a bound, never a value.
    let cost = u64::from(l1.size)
        .saturating_add(u64::from(l2.size))
        .saturating_add(1);
    L::admit_work(&mut cx.spent, cost)?;
    let key = (l1.clone(), l2.clone());
    if let Some(&answer) = cx.seen.get(&key) {
        return Ok(answer);
    }
    let answer = geq_step::<L>(l1, l2, cx)?;
    cx.seen.insert(key, answer);
    Ok(answer)
}

/// One application of Lean's rules, in Lean's order and no others. Until
/// R174 a rule answered `succ^k l >= l` before the `max` and `imax` rules.
/// It holds at every assignment, but Lean has no such rule: on an irreducible
/// `imax` Lean answers `false`, so this checker admitted
/// `inductive S.{u,v} (α : Sort u) (β : Sort v) : Sort (imax u v + 1)` with a
/// field `α → β`, which Lean refuses ("Invalid universe level in
/// constructor").
fn geq_step<L: Limit>(l1: &Level, l2: &Level, cx: &mut Geq) -> Result<bool, L::Error> {
    if l1 == l2 || l2.is_zero() {
        return Ok(true);
    }
    if let Repr::Max(a, b) = &l2.repr {
        return Ok(is_geq_core::<L>(l1, a, cx)? && is_geq_core::<L>(l1, b, cx)?);
    }
    if let Repr::Max(a, b) = &l1.repr {
        if is_geq_core::<L>(a, l2, cx)? || is_geq_core::<L>(b, l2, cx)? {
            return Ok(true);
        }
    }
    if let Repr::IMax(a, b) = &l2.repr {
        return Ok(is_geq_core::<L>(l1, a, cx)? && is_geq_core::<L>(l1, b, cx)?);
    }
    if let Repr::IMax(_, b) = &l1.repr {
        return is_geq_core::<L>(b, l2, cx);
    }
    let (base1, off1) = l1.get_offset();
    let (base2, off2) = l2.get_offset();
    if base1 == base2 || base2.is_zero() {
        return Ok(off1 >= off2);
    }
    if off1 == off2 && off1 > 0 {
        return is_geq_core::<L>(&base1, &base2, cx);
    }
    Ok(false)
}
