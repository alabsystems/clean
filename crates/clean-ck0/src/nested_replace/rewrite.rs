// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What phase 3's rewrite and the auxiliary's self-reference rewrite share
//! (R176): a spine's arguments lowered once each, and a spine rebuilt over
//! what does not mention the constant they look for, which is itself.

use super::index::mix;
use super::walk::{Mentions, Spine};
use super::{lower_params_charged, map_children_depth, Charge};
use crate::nested::NestedError;
use crate::term::Term;

/// A spine's arguments lowered into the canonical frame from the first, each
/// at most once, each node charged before lowering builds it (R176).
pub(super) struct Lowered {
    below: u32,
    num_params: u32,
    canon: Vec<Term>,
    /// `keys[i]` is the [`super::args_key`] of `canon[..=i]`.
    keys: Vec<u64>,
    /// An argument could not be lowered: it names a field or index binder.
    failed: bool,
}

impl Lowered {
    pub(super) fn new(below: u32, num_params: u32) -> Lowered {
        Lowered {
            below,
            num_params,
            canon: Vec::new(),
            keys: Vec::new(),
            failed: false,
        }
    }

    /// Lower those of `args[..n]` not lowered yet: `false` when one of them
    /// cannot be lowered, or `args` has fewer than `n`. Lowering an argument
    /// charges each node before it builds it, so one that cannot be lowered
    /// has been charged the nodes looked at up to the variable that fails it.
    pub(super) fn reach(
        &mut self,
        args: &[&Term],
        n: usize,
        charge: &mut Charge<'_>,
    ) -> Result<bool, NestedError> {
        while self.canon.len() < n {
            if self.failed {
                return Ok(false);
            }
            let Some(arg) = args.get(self.canon.len()) else {
                return Ok(false);
            };
            let Some(lowered) = lower_params_charged(arg, self.below, self.num_params, charge)?
            else {
                self.failed = true;
                return Ok(false);
            };
            let key = mix(self.keys.last().copied().unwrap_or(0), &lowered);
            self.keys.push(key);
            self.canon.push(lowered);
        }
        Ok(true)
    }

    /// The first `n` lowered arguments and their key, once `reach` has
    /// returned `true` for `n` (`n > 0`).
    pub(super) fn prefix(&self, n: usize) -> Option<(&[Term], u64)> {
        let key = *self.keys.get(n.checked_sub(1)?)?;
        Some((self.canon.get(..n)?, key))
    }
}

/// A rewrite that changes only what mentions one constant (R176): a node
/// that does not mention it is its own rewrite, returned as it is, and a
/// spine is rebuilt above its matched application, or else above its
/// longest application that does not mention it (or its head), over the
/// rest of its arguments, each rewritten.
pub(super) trait Rewrite {
    /// The nodes of the term being rewritten that mention the constant.
    fn marks(&self) -> &Mentions<'_>;

    /// The rewrite of `t`, a node of that term `depth` binders in.
    fn rewrite(&self, t: &Term, depth: u32, charge: &mut Charge<'_>) -> Result<Term, NestedError>;

    /// The head of a spine rewritten: it is not an application, so its
    /// children are rewritten, never itself again.
    fn head(&self, t: &Term, depth: u32, charge: &mut Charge<'_>) -> Result<Term, NestedError> {
        if !self.marks().contains(t) {
            return Ok(t.clone());
        }
        map_children_depth(t, depth, &mut |child, depth| {
            self.rewrite(child, depth, charge)
        })
    }

    /// `spine` with `matched`, the rewrite of its application of that many
    /// arguments, in place of that application, applied to the rest of its
    /// arguments, each rewritten.
    fn rebuild(
        &self,
        spine: &Spine<'_>,
        matched: Option<(Term, usize)>,
        depth: u32,
        charge: &mut Charge<'_>,
    ) -> Result<Term, NestedError> {
        let (mut result, from) = match matched {
            Some(found) => found,
            None => {
                let unmarked = spine
                    .apps
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|(_, app)| !self.marks().contains(app));
                match unmarked {
                    // It and everything in it are their own rewrite.
                    Some((i, app)) => ((*app).clone(), i.saturating_add(1)),
                    None => (self.head(spine.head, depth, charge)?, 0),
                }
            }
        };
        for arg in spine.args.get(from..).unwrap_or_default() {
            result = Term::app(result, self.rewrite(arg, depth, charge)?);
        }
        Ok(result)
    }
}
