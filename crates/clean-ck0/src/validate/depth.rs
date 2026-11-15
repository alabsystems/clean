// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The input depth bound, checked iteratively before anything recurses.

use super::*;
use crate::rawexpr::RawLevel;

/// Reject any [`RawExpr`] whose structural nesting depth exceeds
/// [`MAX_VALIDATE_DEPTH`]. Iterative (explicit work stack of `(node, depth)`),
/// so it never grows the native stack — it can vet an arbitrarily deep,
/// attacker-supplied term that the natively-recursive `validate_rec` could not
/// touch without overflowing. Returns on the *first* over-deep node, so it does
/// O(min(size, work-until-first-violation)) and never materializes anything.
///
/// Note `RawExpr`'s own `Drop` is native recursion owned by the *caller* of
/// `validate` (the untrusted boundary holds the value); the kernel's invariant
/// is only that it never *mints a `Term`* from an over-deep input.
pub(super) fn check_raw_depth(root: &RawExpr) -> Result<(), ValidateError> {
    // Each stack entry is a subterm together with the depth at which it sits.
    let mut stack: Vec<(&RawExpr, u32)> = vec![(root, 1)];
    let mut seen = std::collections::HashMap::<*const RawExpr, u32>::new();
    while let Some((node, depth)) = stack.pop() {
        if depth > MAX_VALIDATE_DEPTH {
            return Err(ValidateError::MaxDepthExceeded {
                max: MAX_VALIDATE_DEPTH,
            });
        }
        let child_depth = depth.saturating_add(1);
        match node {
            RawExpr::Shared(node) => {
                let key = std::sync::Arc::as_ptr(node);
                if seen.get(&key).is_some_and(|prior| *prior >= depth) {
                    continue;
                }
                seen.insert(key, depth);
                stack.push((node, depth));
            }
            RawExpr::BVar(_) | RawExpr::Lit(_) => {}
            RawExpr::Sort(l) => check_raw_level_depth(l, depth)?,
            RawExpr::Const(_, levels) => {
                for l in levels {
                    check_raw_level_depth(l, depth)?;
                }
            }
            RawExpr::Elim(_, motive, levels) => {
                check_raw_level_depth(motive, depth)?;
                for l in levels {
                    check_raw_level_depth(l, depth)?;
                }
            }
            RawExpr::App(f, a) => {
                stack.push((f, child_depth));
                stack.push((a, child_depth));
            }
            RawExpr::Lam(_, ty, body) | RawExpr::Pi(_, ty, body) => {
                stack.push((ty, child_depth));
                stack.push((body, child_depth));
            }
            RawExpr::Let(ty, val, body) => {
                stack.push((ty, child_depth));
                stack.push((val, child_depth));
                stack.push((body, child_depth));
            }
            RawExpr::Proj(_, _, e) => stack.push((e, child_depth)),
        }
    }
    Ok(())
}

/// A level counts toward the depth of the term it sits in, one more for each
/// `Succ`, `Max` and `IMax` node, as [`Term`]'s cached height counts it (R166):
/// `validate_level` and the level operations recurse natively over it from
/// wherever the term walk reached. Iterative, like [`check_raw_depth`]; `at` is
/// the depth of the `Sort`, `Const` or `Elim` node that holds `root`.
pub(super) fn check_raw_level_depth(root: &RawLevel, at: u32) -> Result<(), ValidateError> {
    let mut stack: Vec<(&RawLevel, u32)> = vec![(root, at)];
    while let Some((node, depth)) = stack.pop() {
        if depth > MAX_VALIDATE_DEPTH {
            return Err(ValidateError::MaxDepthExceeded {
                max: MAX_VALIDATE_DEPTH,
            });
        }
        let below = depth.saturating_add(1);
        match node {
            RawLevel::Zero | RawLevel::Param(_) => {}
            RawLevel::Succ(l) => stack.push((l, below)),
            RawLevel::Max(a, b) | RawLevel::IMax(a, b) => {
                stack.push((a, below));
                stack.push((b, below));
            }
        }
    }
    Ok(())
}
