// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Provenance for elaborator-generated codata constants (rank 7, brick B2).
//!
//! # What this is, and emphatically what it is not
//!
//! A [`CodataOrigin`] is a **hint**: it records that the `codata`/`codef`
//! elaborator generated a particular constant, and names the pieces a later
//! consumer should go and look at. It is *not* evidence, and holding one is
//! *not* permission to do anything.
//!
//! The rank-7 direct-lazy lowering needs to recognize a corecursive definition
//! in order to emit `Corec`/`Delay`/`Force` instead of the generic (and
//! uncompilable) `M`-type path. The one thing that recognition must never be is
//! name-based: `C.corec` is a *user-derivable* name — nothing stops anyone
//! hand-writing `def Stream.corec` — so matching on the name, or trusting a
//! record that merely asserts "this is codata", is a soundness hole dressed up
//! as metadata.
//!
//! The contract is therefore:
//!
//! - **Absence downgrades, never authorizes.** No origin ⇒ the consumer
//!   declines. For rank 7 a decline is a hard compile error, which is the
//!   honest outcome, not a silent fallback.
//!   `verify_recursor_calls_certifiable` already refuses the generic path.
//! - **Presence still authorizes nothing.** A consumer must independently
//!   re-resolve the named constants in the current environment and
//!   **structurally replay** the canonical generated body, comparing against a
//!   freshly re-derived expectation. The origin says *what to check*; the check
//!   is what justifies the transformation.
//! - **Transient, exactly like [`super::DeclarationVerification`].** The map is
//!   `#[serde(skip)]`, so a deserialized environment carries no origins at all.
//!   That closes the forgery route: a crafted artifact cannot ship an origin
//!   claiming a hand-written constant is generated codata. Structural replay is
//!   the real defense; refusing to deserialize the hint means an attacker must
//!   defeat the replay rather than the record.
//!
//! Nothing here is consulted by type checking, conversion, or any kernel
//! acceptance path. Deleting every entry can only cause consumers to decline.

use crate::name::Name;
use serde::{Deserialize, Serialize};

use super::Environment;

/// Which `codata` lane generated the constant.
///
/// Recorded so a consumer can re-derive the *right* canonical body shape: the
/// plain and indexed lanes build different corecursor applications (the indexed
/// lane threads an index argument and a state family), and replaying the wrong
/// shape would reject a legitimate definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CodataLane {
    /// `codata C : Type where …` — no index.
    Plain,
    /// `codata C : (n : I) → Type where …` — an index that the recursive
    /// fields move.
    Indexed,
}

/// Provenance for one elaborator-generated codata constant.
///
/// Read the module docs before using this: it is a hint to be verified, never
/// a claim to be trusted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodataOrigin {
    /// Which lane generated it (drives which canonical shape to replay).
    pub lane: CodataLane,
    /// The codata carrier type, e.g. `IS2`.
    pub carrier: Name,
    /// The generated corecursor the canonical body applies, e.g. `IS2.corec`.
    ///
    /// A consumer must RE-RESOLVE this in the current environment and check its
    /// type, rather than assuming the name still denotes what it did at
    /// generation time.
    pub corec: Name,
    /// The corecursor's explicit slot names, in canonical application order.
    ///
    /// Order is load-bearing: the generated body supplies exactly one lambda
    /// per slot in this order, so a replay walks the application spine
    /// positionally against this list. Recorded as the corecursor's own
    /// recorded parameter names rather than as a reconstructed
    /// observation/step split, because the application order is what replay
    /// actually compares — a derived split would be a second source of truth.
    pub slots: Vec<String>,
}

impl CodataOrigin {
    /// Number of slot lambdas the canonical body must supply.
    #[must_use]
    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }
}

impl Environment {
    /// Record that the `codata` command GENERATED this carrier type.
    ///
    /// Distinct from [`Self::set_codata_origin`], which marks a `codef`. This
    /// marks the carrier, and it exists because an adversarial review found
    /// that recognition could be satisfied without the `codata` command ever
    /// having run: `codef` accepted any carrier that merely happened to own a
    /// constant named `<C>.corec` with the right recorded parameter names, so a
    /// hand-written type plus a hand-written corecursor passed every check.
    ///
    /// Same contract as the rest of this module: transient, absence downgrades,
    /// presence authorizes nothing on its own.
    pub fn mark_codata_carrier(&mut self, name: Name) {
        self.codata_carriers.insert(name);
    }

    /// Did the `codata` command generate this carrier in THIS environment?
    ///
    /// `false` for a hand-written type, and for any environment restored from
    /// an artifact — which correctly declines rather than trusting a record it
    /// cannot re-derive.
    #[must_use]
    pub fn is_codata_carrier(&self, name: &Name) -> bool {
        self.codata_carriers.contains(name)
    }

    /// Record that the codata elaborator generated `name`.
    ///
    /// Callers must write this into the same transactional environment clone
    /// that carries the generated declarations, so a `codef` whose generated
    /// body fails to kernel-check leaves behind no origin either.
    ///
    /// Deliberately `pub` rather than trust-gated: writing an origin authorizes
    /// nothing. A consumer must still re-resolve the named constants and
    /// structurally replay the canonical body, so a caller who writes a false
    /// origin gains no capability — it only makes the replay fail. The
    /// privileged operation is the replay, and that lives in the consumer.
    pub fn set_codata_origin(&mut self, name: Name, origin: CodataOrigin) {
        self.codata_origins.insert(name, origin);
    }

    /// The recorded codata provenance for `name`, if any.
    ///
    /// `None` means "no hint" — decline, or verify from scratch by other
    /// means. It never means "not codata": an environment restored from an
    /// artifact has no origins at all by construction.
    #[must_use]
    pub fn get_codata_origin(&self, name: &Name) -> Option<&CodataOrigin> {
        self.codata_origins.get(name)
    }

    /// Number of recorded codata origins (diagnostics and tests).
    #[must_use]
    pub fn codata_origin_count(&self) -> usize {
        self.codata_origins.len()
    }
}
