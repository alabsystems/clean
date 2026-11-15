// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Container variance: whether parameter slot `i` of an already-admitted
//! inductive `C` is **strictly positive**: across every constructor of `C` the
//! parameter appears only strictly positively (never to the left of an arrow,
//! and never in a slot of a deeper container that is not itself strictly
//! positive). Fail-closed: an unknown container, an index or out-of-range
//! slot, or unknown constructors refuse.
//!
//! A slot is an **obligation**: the pass that finds a block type (or a
//! container's parameter) in it requires it, and `Obligations::discharge`
//! checks each one once, by the same pass over the container's constructors,
//! which may require more (R176). The oracle this replaces recursed into the
//! deeper container at each use and forgot it on return, so it enumerated
//! every simple path through the containers: `2^k` scans for `k` containers
//! that each use the next one twice, and some four native frames per container
//! on the path. A slot required again while it is pending or checked is not
//! checked again, as the oracle held a slot on its stack positive: an admitted
//! container's own recursion is positive by construction.
//!
//! Why once is enough: the oracle answered false for a slot exactly when some
//! slot reachable from it through these uses fails its own checks (each check
//! is a conjunction, and a path that repeats a slot reaches nothing a shorter
//! one does not). A discharge that succeeds has checked every slot reachable
//! from those it was given, so every slot it leaves seen is strictly positive;
//! the first that fails ends the check, and `Positivity` refuses for good.

use std::collections::HashSet;

use super::strict::{scan_telescope, Target};
use crate::name::Name;
use crate::validate::Env;

/// The slots one block's check has required: each is checked once.
pub(super) struct Obligations<'e> {
    env: &'e dyn Env,
    /// Every slot required so far: checked, or in `pending`.
    seen: HashSet<(Name, usize)>,
    /// The slots required and not yet checked.
    pending: Vec<(Name, usize)>,
}

impl<'e> Obligations<'e> {
    /// No slot required yet.
    pub(super) fn new(env: &'e dyn Env) -> Self {
        Obligations {
            env,
            seen: HashSet::new(),
            pending: Vec::new(),
        }
    }

    /// Require slot `slot` of `container` to be strictly positive.
    pub(super) fn require(&mut self, container: &Name, slot: usize) {
        let key = (container.clone(), slot);
        if self.seen.insert(key.clone()) {
            self.pending.push(key);
        }
    }

    /// Check every pending slot, and those they require. `Err(())` on the
    /// first that is not strictly positive.
    pub(super) fn discharge(&mut self) -> Result<(), ()> {
        while let Some((container, slot)) = self.pending.pop() {
            self.check_slot(&container, slot)?;
        }
        Ok(())
    }

    /// The checks of one slot: `container` is a known inductive, `slot` one of
    /// its parameters, and the parameter strictly positive in each of its
    /// constructors' telescopes (parameter types and fields alike, each at its
    /// own binder depth; the return type permits any occurrence). The
    /// parameter types and the fields were two loops before R176, each domain
    /// scanned at the same depth as here.
    fn check_slot(&mut self, container: &Name, slot: usize) -> Result<(), ()> {
        // unknown container ⇒ fail-closed
        let n_params = self.env.inductive_num_params(container).ok_or(())?;
        if u32::try_from(slot).map(|p| p >= n_params).unwrap_or(true) {
            // The parent is applied at an INDEX (or out-of-range) slot, not a
            // parameter. Indices are not abstracted by the aux construction and
            // we cannot certify their variance ⇒ fail-closed.
            return Err(());
        }
        let ctors = self.env.inductive_constructors(container).ok_or(())?;
        for (_, ctor_ty) in &ctors {
            scan_telescope(ctor_ty, Target::Param(slot), self)?;
        }
        Ok(())
    }
}
