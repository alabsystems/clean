// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Obligation sources for the swarm worker.
//!
//! An [`ObligationSource`] is a pull stream of `(name, goal)` pairs. Two
//! concrete sources back the worker:
//!
//! * [`ShardObligations`] — a corpus `.mathverse` shard directory. It iterates
//!   every shard's constants, keeps only those whose import confidence is
//!   [`ImportConfidence::Unverified`] (the ~89% name+statement-only frontier),
//!   and reconstructs each constant's `type_idx` into a goal [`Expr`].
//! * [`DemoSource`] — a handful of constructed tier-1 goals, for the smoke
//!   test and `--demo` mode. No corpus required.
//!
//! The trait keeps the worker loop agnostic so the smoke can feed either.
//!
//! # The two upstream walls (now broken)
//!
//! A richer corpus than `Init` was tried: a shard built from
//! `Mathlib.Algebra.Group.Basic` (507 constants; 471 Axiomatized goals —
//! `mul_one`, `inv_inv`, `zpow_add`, `eq_sub_iff_add_eq'`, … — the equational
//! "derivable middle tier" `Init` lacks). The premise-guided swarm originally
//! proved 0 of them because of two structural walls UPSTREAM of the ATP, both
//! now addressed:
//!
//! * **WALL 1 — missing hierarchy.** The goals reference Mathlib hierarchy
//!   constants (`Group`, `Monoid`, `HMul`, …) absent from the bare import
//!   prelude, so the C1 recheck environment could not even TYPE them. Fixed by
//!   [`super::Hierarchy::Algebra`], which seeds the in-repo algebra structure
//!   hierarchy (the local stand-in for a loaded module dep-closure) into the
//!   search + recheck environments.
//! * **WALL 2 — universe-polymorphism.** Every Mathlib algebra lemma is
//!   universe-POLYMORPHIC and typeclass-parameterised (`∀ {G : Type u}
//!   [Group G], …`), and [`super::tier2_classify`] rejected the leading `Type u`
//!   binder as `BadBinderType(UniversePolymorphic)`. Fixed by the tier-3 peel:
//!   TYPE and INSTANCE binders are peeled into the local context, the goal's
//!   universe params are extracted into the graduated theorem's `level_params`,
//!   and the kernel re-checks the polymorphic term against the original
//!   `∀`-type.
//!
//! See `super::tests::test_worker_universe_polymorphic_monoid_lemma_proves_and_kernel_accepts`
//! (end-to-end, both walls) and
//! `test_worker_instance_field_mul_one_graduates_polymorphic_theorem` (the
//! instance-axiom graduation path). What remains a per-goal concern is whether
//! the in-repo first-order/equational ATP can CLOSE a given opened body — it has
//! no induction and limited quantified-hypothesis instantiation, so a
//! `mul_one`-over-arbitrary-`a` body still depends on the prover's reach even
//! though the classifier and environment no longer block it.

use std::path::{Path, PathBuf};
use std::vec::IntoIter;

use clean_kernel::{Expr, Level};

use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;
use crate::types::ImportConfidence;

use super::Obligation;

/// A pull stream of obligations. `None` ends the stream; `Some(Err(_))`
/// surfaces a source error the worker turns into a [`super::WorkerError`].
pub trait ObligationSource {
    /// Yield the next obligation, or `None` at end of stream.
    fn next_obligation(&mut self) -> Option<Result<Obligation, String>>;
}

/// A constructed set of tier-1 goals for the smoke test and `--demo` mode.
///
/// The default set contains closed reflexive equalities the hammer's
/// reflexivity lane discharges (`@Eq.{1} Nat n n`).
#[derive(Debug)]
pub struct DemoSource {
    remaining: IntoIter<Obligation>,
}

impl DemoSource {
    /// Build a demo source from an explicit obligation list.
    #[must_use]
    pub fn new(obligations: Vec<Obligation>) -> Self {
        Self {
            remaining: obligations.into_iter(),
        }
    }

    /// The default constructed tier-1 goals: reflexive equalities over `Nat`.
    #[must_use]
    pub fn default_goals() -> Vec<Obligation> {
        (0u64..3)
            .map(|n| Obligation::new(format!("SwarmWorker.demo_refl_{n}"), nat_eq_refl_goal(n)))
            .collect()
    }
}

impl Default for DemoSource {
    fn default() -> Self {
        Self::new(Self::default_goals())
    }
}

impl ObligationSource for DemoSource {
    fn next_obligation(&mut self) -> Option<Result<Obligation, String>> {
        self.remaining.next().map(Ok)
    }
}

/// `@Eq.{1} Nat n n` — a closed proposition the reflexivity lane proves.
fn nat_eq_refl_goal(n: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                Expr::const_str("Nat"),
            ),
            Expr::nat_lit(n),
        ),
        Expr::nat_lit(n),
    )
}

/// The pool a corpus constant must belong to be offered as an obligation: the
/// UNPROVEN frontier. A Lean4 build tags pure axioms/opaques and statement-only
/// theorems/definitions [`ImportConfidence::Axiomatized`] (a type but no
/// Clean-checked proof — the autoprove target), and a handful of unparseable
/// imports [`ImportConfidence::Unverified`]. Everything stronger
/// (`SourceVerified`, `Translated`, `KernelVerified`) already carries a proof
/// and is not an autoprove candidate. This is the same pool the tier-1 baseline
/// run was scoped to.
fn is_unproven_pool(confidence: ImportConfidence) -> bool {
    matches!(
        confidence,
        ImportConfidence::Axiomatized | ImportConfidence::Unverified
    )
}

/// A corpus shard-directory obligation source.
///
/// Lazily walks the shards in a directory; within each shard it reconstructs
/// the type of every UNPROVEN-pool constant ([`is_unproven_pool`]) into a goal.
/// Constants whose type is not reconstructable (beyond the shard's
/// reconstructable prefix, unsupported flat tags, …) are silently skipped —
/// they were never tier-1/tier-2 candidates.
#[derive(Debug)]
pub struct ShardObligations {
    /// Remaining shard files to open.
    shards: IntoIter<PathBuf>,
    /// Obligations buffered from the currently-open shard.
    buffer: IntoIter<Obligation>,
}

impl ShardObligations {
    /// Discover `.mathverse` shards in `dir` (non-recursive) and build a source.
    ///
    /// # Errors
    ///
    /// Returns an error string if the directory cannot be read.
    pub fn from_dir(dir: impl AsRef<Path>) -> Result<Self, String> {
        let dir = dir.as_ref();
        let entries = std::fs::read_dir(dir)
            .map_err(|e| format!("cannot read shard dir `{}`: {e}", dir.display()))?;
        let mut shards: Vec<PathBuf> = entries
            .filter_map(|entry| entry.ok().map(|e| e.path()))
            .filter(|path| path.extension().is_some_and(|ext| ext == "mathverse"))
            .collect();
        shards.sort();
        Ok(Self {
            shards: shards.into_iter(),
            buffer: Vec::new().into_iter(),
        })
    }

    /// Read the next shard into the buffer. Returns `Ok(true)` if a shard was
    /// loaded, `Ok(false)` if there are no more shards, or an error string if
    /// a shard file is unreadable.
    fn load_next_shard(&mut self) -> Result<bool, String> {
        let Some(path) = self.shards.next() else {
            return Ok(false);
        };
        let reader = ShardReader::from_file(&path)
            .map_err(|e| format!("cannot read shard `{}`: {e}", path.display()))?;
        self.buffer = Self::obligations_from_shard(&reader).into_iter();
        Ok(true)
    }

    /// Reconstruct every unproven-pool constant's type into an obligation.
    fn obligations_from_shard(reader: &ShardReader) -> Vec<Obligation> {
        reader
            .constants
            .iter()
            .filter(|c| c.confidence().is_ok_and(is_unproven_pool))
            .filter_map(|c| {
                let name = reader.strings.get(c.name_idx as usize)?.clone();
                let goal = reconstruct_from_shard_with_level_lists(
                    &reader.exprs,
                    &reader.levels,
                    &reader.strings,
                    &reader.level_lists,
                    c.type_idx,
                )
                .ok()?;
                Some(Obligation::new(name, goal))
            })
            .collect()
    }
}

impl ObligationSource for ShardObligations {
    fn next_obligation(&mut self) -> Option<Result<Obligation, String>> {
        loop {
            if let Some(obligation) = self.buffer.next() {
                return Some(Ok(obligation));
            }
            match self.load_next_shard() {
                Ok(true) => continue,
                Ok(false) => return None,
                Err(e) => return Some(Err(e)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_demo_source_yields_default_goals() {
        let mut source = DemoSource::default();
        let mut count = 0;
        while let Some(result) = source.next_obligation() {
            let obligation = result.expect("demo obligations are infallible");
            assert!(obligation.name.starts_with("SwarmWorker.demo_refl_"));
            count += 1;
        }
        assert_eq!(count, 3, "default demo source has three goals");
    }

    #[test]
    fn test_unproven_pool_admits_axiomatized_and_unverified_only() {
        // The autoprove frontier: statement-only (Axiomatized) + unparseable
        // (Unverified). Everything that already carries a proof is excluded.
        assert!(is_unproven_pool(ImportConfidence::Axiomatized));
        assert!(is_unproven_pool(ImportConfidence::Unverified));
        assert!(!is_unproven_pool(ImportConfidence::SourceVerified));
        assert!(!is_unproven_pool(ImportConfidence::Translated));
        assert!(!is_unproven_pool(ImportConfidence::KernelVerified));
    }

    #[test]
    fn test_shard_obligations_missing_dir_errors() {
        let err = ShardObligations::from_dir("/swarm-worker/no/such/dir")
            .expect_err("a missing directory must error");
        assert!(err.contains("cannot read shard dir"));
    }
}
