// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe levels in the checker's kernel theory (DECISIONS R150, plan item
//! `kernel-level-normalizer-lean-profile`).
//!
//! Under [`KernelTheory::Lean`] and [`KernelTheory::LeanReference`] the
//! checker compares levels with Lean's `is_equivalent`, builds a Π-type's
//! sort with Lean's `mk_imax`, and instantiates universe parameters with
//! Lean's `instantiate_lparams` (`level/lean_kernel.rs`,
//! `expr/subst_lean_levels.rs`), and the inductive checks read Lean's
//! structural `is_zero`. On every level comparison in the pinned table
//! (`level/fixtures/lean_kernel_verdicts_v4.30.0-rc2.tsv`) and on the reach
//! shapes in `level_profile_reach_tests.rs` its verdict is pinned Lean
//! v4.30.0-rc2's. That is a measured agreement, not an equivalence: an
//! instantiation whose Lean verdict depends on `.olean` object sharing is
//! refused by name instead (`TypeError::LevelSharingDependent`), and the
//! certificate verifier (`cert/`) keeps Clean's algebra. Under
//! [`KernelTheory::Extended`] Clean's own algebra stays: its normaliser proves
//! equalities Lean's does not (the join-subsumption, #1436's `imax`
//! re-flattening), a scoped R2 exception.

use super::{TypeChecker, TypeError};
use crate::env::KernelTheory;
use crate::expr::Expr;
use crate::level::{
    LeanLevelProfile, Level, LevelConstruction, SharingChoices, SliceLookup, ZeroReading,
};
use crate::name::Name;

impl KernelTheory {
    /// How this theory builds and compares universe levels.
    #[must_use]
    pub(crate) fn level_construction(self) -> LevelConstruction {
        match self {
            KernelTheory::Extended => LevelConstruction::Clean,
            KernelTheory::Lean | KernelTheory::LeanReference => LevelConstruction::LeanKernel,
        }
    }
}

/// Why a universe instantiation could not be given Lean's answer.
struct SharingDependent;

/// `e` with `params := levels`, as `construction` instantiates universe
/// parameters.
fn instantiate_levels(
    construction: LevelConstruction,
    e: &Expr,
    params: &[Name],
    levels: &[Level],
    choices: Option<&dyn SharingChoices>,
    profile: LeanLevelProfile,
) -> Result<Expr, SharingDependent> {
    if params.is_empty() {
        return Ok(e.clone());
    }
    match construction {
        LevelConstruction::Clean => Ok(e.instantiate_level_params_direct(params, levels)),
        LevelConstruction::LeanKernel => {
            let lookup = SliceLookup { params, levels };
            let out = if profile == LeanLevelProfile::Lean430 && choices.is_none() {
                e.lean_instantiate_level_params(&lookup)
            } else if profile == LeanLevelProfile::Lean430 {
                e.lean_instantiate_level_params_with_choices(&lookup, choices)
            } else {
                e.lean_instantiate_level_params_in_profile(&lookup, choices, profile)
            };
            if out.sharing_dependent {
                Err(SharingDependent)
            } else {
                Ok(out.expr)
            }
        }
    }
}

impl crate::env::Environment {
    /// Lean's `is_equivalent` under the Lean theories, Clean's
    /// [`Level::is_def_eq`] under `Extended`.
    pub(crate) fn levels_equiv_in_theory(&self, l1: &Level, l2: &Level) -> bool {
        match self.kernel_theory().level_construction() {
            LevelConstruction::Clean => Level::is_def_eq(l1, l2),
            LevelConstruction::LeanKernel => {
                if self.lean_level_profile() == LeanLevelProfile::Lean430 {
                    Level::lean_is_equivalent(l1, l2)
                } else {
                    Level::lean_is_equivalent_in_profile(l1, l2, self.lean_level_profile())
                }
            }
        }
    }

    /// Lean's `is_geq` under the Lean theories, Clean's under `Extended`.
    pub(crate) fn level_geq_in_theory(&self, l1: &Level, l2: &Level) -> bool {
        match self.kernel_theory().level_construction() {
            LevelConstruction::Clean => Level::is_geq(l1, l2),
            LevelConstruction::LeanKernel => {
                if self.lean_level_profile() == LeanLevelProfile::Lean430 {
                    Level::lean_is_geq(l1, l2)
                } else {
                    Level::lean_is_geq_in_profile(l1, l2, self.lean_level_profile())
                }
            }
        }
    }

    /// The `is_zero` this environment's inductive checks read: Lean's
    /// structural one (the `Zero` node; `inductive.cpp:439,517,557` @
    /// v4.30.0-rc2) under the Lean theories, Clean's semantic
    /// [`Level::is_zero`] (`0` at every assignment, v4.33.1's
    /// `normalizes_to_zero`) under `Extended`.
    #[must_use]
    pub(crate) fn zero_reading(&self) -> ZeroReading {
        match self.kernel_theory().level_construction() {
            LevelConstruction::Clean => ZeroReading::Semantic,
            LevelConstruction::LeanKernel => ZeroReading::Structural,
        }
    }

    /// Whether `level` is `0` for the inductive checks, under
    /// [`Self::zero_reading`].
    pub(crate) fn level_is_zero_in_theory(&self, level: &Level) -> bool {
        self.zero_reading().is_zero(level)
    }

    /// `e`, a part of constant `name`, with `params := levels`, as this
    /// environment's theory instantiates universe parameters, for a Clean-only
    /// check whose result a checker of this environment compares.
    ///
    /// # Errors
    ///
    /// [`TypeError::LevelSharingDependent`] when Lean's own answer depends on
    /// `.olean` object sharing.
    pub(crate) fn instantiate_levels_in_theory(
        &self,
        name: &Name,
        e: &Expr,
        params: &[Name],
        levels: &[Level],
    ) -> Result<Expr, TypeError> {
        instantiate_levels(
            self.kernel_theory().level_construction(),
            e,
            params,
            levels,
            None,
            self.lean_level_profile(),
        )
        .map_err(|SharingDependent| TypeError::LevelSharingDependent { name: name.clone() })
    }
}

impl TypeChecker<'_> {
    /// How this checker's theory builds and compares universe levels.
    #[must_use]
    pub(crate) fn level_construction(&self) -> LevelConstruction {
        self.kernel_theory().level_construction()
    }

    /// Level definitional equality in this checker's theory (no elaborator
    /// override: [`Self::levels_eq`] consults that first).
    pub(crate) fn levels_equiv_in_theory(&self, l1: &Level, l2: &Level) -> bool {
        match self.level_construction() {
            LevelConstruction::Clean => Level::is_def_eq(l1, l2),
            LevelConstruction::LeanKernel => {
                if self.env.lean_level_profile() == LeanLevelProfile::Lean430 {
                    Level::lean_is_equivalent(l1, l2)
                } else {
                    Level::lean_is_equivalent_in_profile(l1, l2, self.env.lean_level_profile())
                }
            }
        }
    }

    /// The sort level of `Π (x : A), B` from `A : Sort l1` and `B : Sort l2`
    /// (Lean's `infer_pi` folds `mk_imax`, `type_checker.cpp:150-154`).
    pub(crate) fn level_imax(&self, l1: Level, l2: Level) -> Level {
        match self.level_construction() {
            LevelConstruction::Clean => Level::imax(l1, l2),
            LevelConstruction::LeanKernel => {
                if self.env.lean_level_profile() == LeanLevelProfile::Lean430 {
                    Level::lean_mk_imax(l1, l2)
                } else {
                    Level::lean_mk_imax_in_profile(l1, l2, self.env.lean_level_profile())
                }
            }
        }
    }

    /// `e`, a part of constant `name`, with `params := levels`, as this
    /// checker's theory instantiates universe parameters
    /// (`instantiate_type_lparams` / `instantiate_value_lparams`).
    ///
    /// # Errors
    ///
    /// [`TypeError::LevelSharingDependent`] when Lean's own answer depends on
    /// `.olean` object sharing. The dependence is also recorded (see the
    /// `level_sharing_hazard` field), so a caller that turns the error into
    /// "no answer" (a quick inference path) cannot let the check go on.
    pub(crate) fn instantiate_levels_checked(
        &self,
        name: &Name,
        e: &Expr,
        params: &[Name],
        levels: &[Level],
    ) -> Result<Expr, TypeError> {
        let sharing = self.sharing_choices(name, e, params, levels);
        let choices = sharing.as_ref().map(|owner| owner as &dyn SharingChoices);
        instantiate_levels(
            self.level_construction(),
            e,
            params,
            levels,
            choices,
            self.env.lean_level_profile(),
        )
        .map_err(|SharingDependent| {
            self.record_level_sharing(name);
            TypeError::LevelSharingDependent { name: name.clone() }
        })
    }

    /// As [`Self::instantiate_levels_checked`], for a path that cannot return
    /// an error (δ-unfolding, ι-reduction, quick inference): on a sharing
    /// dependence it records `name` (see the `level_sharing_hazard` field) and
    /// answers `None`, so the term stays as it is and the checker refuses at
    /// its next heartbeat site or definitional-equality answer.
    pub(crate) fn instantiate_levels_or_record(
        &self,
        name: &Name,
        e: &Expr,
        params: &[Name],
        levels: &[Level],
    ) -> Option<Expr> {
        let sharing = self.sharing_choices(name, e, params, levels);
        let choices = sharing.as_ref().map(|owner| owner as &dyn SharingChoices);
        match instantiate_levels(
            self.level_construction(),
            e,
            params,
            levels,
            choices,
            self.env.lean_level_profile(),
        ) {
            Ok(out) => Some(out),
            Err(SharingDependent) => {
                self.record_level_sharing(name);
                None
            }
        }
    }

    /// Record that an instantiation of `name` depended on object sharing; the
    /// first one recorded is the one every later refusal names.
    fn record_level_sharing(&self, name: &Name) {
        self.level_sharing_hazard
            .borrow_mut()
            .get_or_insert_with(|| name.clone());
    }

    /// `name`'s type at `levels` in this checker's theory; `None` when the
    /// constant is unknown, the level count does not match, or the
    /// instantiation depends on object sharing (recorded).
    pub(crate) fn instantiate_type_in_theory(&self, name: &Name, levels: &[Level]) -> Option<Expr> {
        let info = self.env.get_const(name)?;
        if info.level_params.len() != levels.len() {
            return None;
        }
        self.instantiate_levels_or_record(name, &info.type_, &info.level_params, levels)
    }

    /// The value of definition `name` at `levels` (Lean's
    /// `unfold_definition_core`), instantiated in this checker's theory.
    /// `None` exactly when [`crate::env::Environment::unfold_definition`] is,
    /// or when the instantiation depends on object sharing (recorded).
    pub(crate) fn unfold_definition_in_theory(
        &self,
        name: &Name,
        levels: &[Level],
    ) -> Option<Expr> {
        if self.level_construction() == LevelConstruction::Clean {
            return self.env.unfold_definition(name, levels);
        }
        let info = self.env.get_const(name)?;
        if info.kind == crate::env::ConstantKind::Opaque {
            return None;
        }
        let value = info.value.as_ref()?;
        if info.level_params.len() != levels.len() {
            return None;
        }
        self.instantiate_levels_or_record(name, value, &info.level_params, levels)
    }

    /// The recorded sharing dependence, as the error every later heartbeat
    /// site returns. A caller that reuses one checker across declarations
    /// reads it after each check: once it is set the checker answers nothing
    /// more, so that caller refuses the check that met it, even one that
    /// swallowed the error, and goes on with a fresh checker (clean-olean
    /// `ReplayChecker::check`).
    #[must_use]
    pub fn level_sharing_error(&self) -> Option<TypeError> {
        self.level_sharing_hazard
            .borrow()
            .as_ref()
            .map(|name| TypeError::LevelSharingDependent { name: name.clone() })
    }

    /// Whether an instantiation on an error-free path depended on object
    /// sharing (see the `level_sharing_hazard` field).
    pub(crate) fn level_sharing_recorded(&self) -> bool {
        self.level_sharing_hazard.borrow().is_some()
    }
}

#[cfg(test)]
#[path = "level_profile_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "level_profile_reach_tests.rs"]
mod reach_tests;
