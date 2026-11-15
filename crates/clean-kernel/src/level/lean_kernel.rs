// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4's kernel universe-level algebra, ported from
//! `src/kernel/level.cpp@v4.30.0-rc2` (identical through v4.35.0 except the
//! added `normalizes_to_zero`, which nothing here uses). Under
//! [`crate::env::KernelTheory::Lean`] and `LeanReference` the kernel builds and
//! compares universe levels only through this file
//! (`tc/level_profile.rs`); `Extended` keeps Clean's own algebra in
//! `level/mod.rs`, a superset recorded as a scoped R2 exception
//! (`docs/DECISIONS.md` R150, plan item `kernel-level-normalizer-lean-profile`).
//!
//! Every rule here is syntactic: `==` is structural equality, "zero" is the
//! `Zero` node, never Clean's semantic [`Level::is_zero`]. Pinned Lean refuses
//! equalities Clean's normaliser proves (the join-subsumption of `dbf4f20ce` /
//! `71446b04f`, and #1436's re-flattening of an `imax` whose right side is
//! never zero), so this port keeps neither.
//!
//! **Object sharing.** Lean's `instantiate` (level.cpp:302, through
//! `update_max`, 286-300) keeps a node whose new children are POINTER-equal to
//! the old ones and rebuilds it with `mk_max`/`mk_imax` otherwise. On a stored
//! level that `mk_max`/`mk_imax` would not rebuild to itself, Lean's verdict
//! therefore depends on whether the `.olean` shares the level objects (measured
//! 2026-10-17: `reports/level-normalizer-probe-2026-10-17/critic/run/`). Clean
//! has no object identity to consult, so [`Level::lean_instantiate_with`]
//! reports such a node as a hazard and the checker refuses the check
//! (`TypeError::LevelSharingDependent`), fail-closed. Every composite level
//! stored in pinned `Init`, `Std` and `Lean` (1,022 distinct) is rebuilt to
//! itself, so no honest declaration measured reaches the hazard.

use super::{level_arc, Level};
use crate::expr::stack_safe;
use crate::name::Name;
/// The exact universe-constructor algebra of a source Lean world. This is
/// a checker input, independent of the reduction/theory safety policy.
#[derive(
    Debug, Clone, Copy, Default, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum LeanLevelProfile {
    /// Lean4.8 keeps `imax 1 u` as a raw node for unknown `u`.
    Lean48,
    /// The repository's existing Lean4.30 algebra.
    #[default]
    Lean430,
}

/// How a level built from other levels is constructed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LevelConstruction {
    /// Clean's smart constructors ([`Level::max`] / [`Level::imax`]), which
    /// collapse by `is_geq`.
    Clean,
    /// Lean's kernel `mk_max` / `mk_imax` (level.cpp:81-123): cheap syntactic
    /// rules only.
    LeanKernel,
}

/// Which `is_zero` an inductive check reads (DECISIONS R150).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ZeroReading {
    /// Lean v4.30.0-rc2's `is_zero`: the level IS the `Zero` node
    /// (`inductive.cpp:439,517,557`).
    Structural,
    /// Clean's [`Level::is_zero`]: `0` at every assignment (v4.33.1's
    /// `normalizes_to_zero`).
    Semantic,
}

impl ZeroReading {
    /// Whether `level` is `0` under this reading. `Structural` answers yes
    /// only where `Semantic` does, so a check that reads it is never the more
    /// permissive of the two.
    #[must_use]
    pub(crate) fn is_zero(self, level: &Level) -> bool {
        match self {
            ZeroReading::Structural => matches!(level, Level::Zero),
            ZeroReading::Semantic => level.is_zero(),
        }
    }
}

/// One level instantiated the way level.cpp:302 `instantiate` does.
pub(crate) struct LeanInstantiated {
    /// The new level when it differs structurally from the input, `None` when
    /// the input is kept.
    pub(crate) level: Option<Level>,
    /// A parameter being substituted occurs in the input.
    pub(crate) touched: bool,
}

/// Where a substituted parameter is looked up.
pub(crate) trait LevelParamLookup {
    /// The replacement for `name`, if `name` is substituted.
    fn replacement(&self, name: &Name) -> Option<&Level>;
}

/// One dynamic ambiguity, answered only by a bounded universal replay owner.
/// `None` suspends/refuses; it never chooses a successful interpretation.
pub(crate) trait SharingChoices {
    fn choose_rebuild(&self, original: &Level) -> Option<bool>;
}

/// Parallel parameter / replacement slices (Lean's `names` / `levels` lists).
pub(crate) struct SliceLookup<'a> {
    /// The parameters.
    pub(crate) params: &'a [Name],
    /// Their replacements, positionally.
    pub(crate) levels: &'a [Level],
}

impl LevelParamLookup for SliceLookup<'_> {
    fn replacement(&self, name: &Name) -> Option<&Level> {
        // level.cpp:310-318 walks both lists together and stops at the first
        // match, or when either list ends.
        self.params
            .iter()
            .zip(self.levels)
            .find_map(|(param, level)| (param == name).then_some(level))
    }
}

impl LevelParamLookup for std::collections::HashMap<Name, Level> {
    fn replacement(&self, name: &Name) -> Option<&Level> {
        self.get(name)
    }
}

impl Level {
    /// Lean's `mk_max_core` (level.cpp:34): a `max` node exactly as given.
    pub(crate) fn lean_max_core(l1: Level, l2: Level) -> Level {
        Level::Max(level_arc(l1), level_arc(l2))
    }

    /// Lean's `mk_imax_core` (level.cpp:35): an `imax` node exactly as given.
    pub(crate) fn lean_imax_core(l1: Level, l2: Level) -> Level {
        Level::IMax(level_arc(l1), level_arc(l2))
    }

    /// Lean's `is_not_zero` (level.cpp:160-172). Clean's [`Level::is_nonzero`]
    /// has exactly these arms (`Succ` true; `Max` either side; `IMax` its right
    /// side; `Zero`/`Param` false).
    fn lean_is_not_zero(&self) -> bool {
        self.is_nonzero()
    }

    /// Lean's `mk_max` (level.cpp:81-103), branch for branch.
    pub(crate) fn lean_mk_max(l1: Level, l2: Level) -> Level {
        if l1.is_explicit() && l2.is_explicit() {
            // `get_depth` of an explicit level is its offset.
            return if l1.get_offset().1 >= l2.get_offset().1 {
                l1
            } else {
                l2
            };
        }
        if l1 == l2 {
            return l1;
        }
        if matches!(l1, Level::Zero) {
            return l2;
        }
        if matches!(l2, Level::Zero) {
            return l1;
        }
        if let Level::Max(a, b) = &l2 {
            if **a == l1 || **b == l1 {
                return l2;
            }
        }
        if let Level::Max(a, b) = &l1 {
            if **a == l2 || **b == l2 {
                return l1;
            }
        }
        let (base1, k1) = l1.get_offset();
        let (base2, k2) = l2.get_offset();
        if base1 == base2 {
            // Equal bases with equal offsets would be `l1 == l2`, handled above.
            return if k1 > k2 { l1 } else { l2 };
        }
        Level::lean_max_core(l1, l2)
    }

    /// Lean's `mk_imax` (level.cpp:112-123), branch for branch.
    pub(crate) fn lean_mk_imax(l1: Level, l2: Level) -> Level {
        Self::lean_mk_imax_in_profile(l1, l2, LeanLevelProfile::Lean430)
    }

    pub(crate) fn lean_mk_imax_in_profile(
        l1: Level,
        l2: Level,
        profile: LeanLevelProfile,
    ) -> Level {
        if l2.lean_is_not_zero() {
            return Level::lean_mk_max(l1, l2);
        }
        if matches!(l2, Level::Zero) {
            return l2;
        }
        if matches!(l1, Level::Zero) {
            return l2;
        }
        if profile == LeanLevelProfile::Lean430 && l1 == Level::succ(Level::zero()) {
            return l2;
        }
        if l1 == l2 {
            return l1;
        }
        Level::lean_imax_core(l1, l2)
    }

    /// Lean's `mk_max(buffer)` (level.cpp:414-429): the right fold of the
    /// binary `mk_max`.
    fn lean_mk_max_args(mut args: Vec<Level>) -> Level {
        let Some(mut acc) = args.pop() else {
            return Level::Zero;
        };
        while let Some(next) = args.pop() {
            acc = Level::lean_mk_max(next, acc);
        }
        acc
    }

    /// Lean's `normalize` (level.cpp:439-501).
    ///
    /// Unlike [`Level::normalize`], an `imax` is rebuilt with `mk_imax` and is
    /// never re-flattened into the enclosing `max` (#1436 does), and no
    /// argument is dropped for being dominated by the join of its siblings: the
    /// only subsumptions are an explicit level by an argument of at least its
    /// offset, and an argument by a same-base argument of larger offset.
    pub(crate) fn lean_normalize(&self) -> Level {
        self.lean_normalize_in_profile(LeanLevelProfile::Lean430)
    }

    pub(crate) fn lean_normalize_in_profile(&self, profile: LeanLevelProfile) -> Level {
        stack_safe(|| self.lean_normalize_impl(profile))
    }

    fn lean_normalize_impl(&self, profile: LeanLevelProfile) -> Level {
        let (base, offset) = self.get_offset();
        match base {
            // `Succ` is never a base after `get_offset`.
            Level::Zero | Level::Param(_) | Level::Succ(_) => self.clone(),
            Level::IMax(l1, l2) => {
                let l1 = stack_safe(|| l1.lean_normalize_impl(profile));
                let l2 = stack_safe(|| l2.lean_normalize_impl(profile));
                Level::lean_mk_imax_in_profile(l1, l2, profile).add_offset(offset)
            }
            Level::Max(_, _) => {
                let mut todo = Vec::new();
                Self::push_max_args(base, &mut todo);
                let mut args = Vec::new();
                for arg in &todo {
                    let normalized = stack_safe(|| arg.lean_normalize_impl(profile));
                    Self::push_max_args(&normalized, &mut args);
                }
                args.sort_by(|a, b| {
                    if Self::is_norm_lt(a, b) {
                        std::cmp::Ordering::Less
                    } else if Self::is_norm_lt(b, a) {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Equal
                    }
                });
                // level.cpp:463-494, which `dedup_max_args` ports line for line:
                // the largest explicit level survives only if no argument has an
                // offset at least its own, and same-base neighbours keep the
                // larger offset.
                let kept = Self::dedup_max_args(&args)
                    .into_iter()
                    .map(|arg| arg.add_offset(offset))
                    .collect();
                Self::lean_mk_max_args(kept)
            }
        }
    }

    /// Lean's `is_equivalent` (level.cpp:503-506), which is the kernel's
    /// `is_def_eq` on levels (`type_checker.cpp:719-725`).
    #[must_use]
    pub(crate) fn lean_is_equivalent(l1: &Level, l2: &Level) -> bool {
        l1 == l2 || l1.lean_normalize() == l2.lean_normalize()
    }

    pub(crate) fn lean_is_equivalent_in_profile(
        l1: &Level,
        l2: &Level,
        profile: LeanLevelProfile,
    ) -> bool {
        l1 == l2 || l1.lean_normalize_in_profile(profile) == l2.lean_normalize_in_profile(profile)
    }

    /// Lean's `is_geq` (level.cpp:508-529). Every recursive step goes back
    /// through `is_geq`, so it re-normalises; the answers are memoised within
    /// this call, which changes no verdict (each is a pure function of its
    /// pair) and bounds the work Lean's recursion would repeat.
    #[must_use]
    pub(crate) fn lean_is_geq(l1: &Level, l2: &Level) -> bool {
        Self::lean_is_geq_in_profile(l1, l2, LeanLevelProfile::Lean430)
    }

    pub(crate) fn lean_is_geq_in_profile(
        l1: &Level,
        l2: &Level,
        profile: LeanLevelProfile,
    ) -> bool {
        let mut memo = hashbrown::HashMap::new();
        Self::lean_is_geq_memo(l1, l2, &mut memo, profile)
    }

    fn lean_is_geq_memo(
        l1: &Level,
        l2: &Level,
        memo: &mut hashbrown::HashMap<(Level, Level), bool>,
        profile: LeanLevelProfile,
    ) -> bool {
        let key = (l1.clone(), l2.clone());
        if let Some(&answer) = memo.get(&key) {
            return answer;
        }
        let n1 = l1.lean_normalize_in_profile(profile);
        let n2 = l2.lean_normalize_in_profile(profile);
        let answer = stack_safe(|| Self::lean_is_geq_core(&n1, &n2, memo, profile));
        memo.insert(key, answer);
        answer
    }

    /// Lean's `is_geq_core` (level.cpp:508-526) on normalised levels.
    fn lean_is_geq_core(
        l1: &Level,
        l2: &Level,
        memo: &mut hashbrown::HashMap<(Level, Level), bool>,
        profile: LeanLevelProfile,
    ) -> bool {
        if l1 == l2 || matches!(l2, Level::Zero) {
            return true;
        }
        if let Level::Max(a, b) = l2 {
            return Self::lean_is_geq_memo(l1, a, memo, profile)
                && Self::lean_is_geq_memo(l1, b, memo, profile);
        }
        if let Level::Max(a, b) = l1 {
            if Self::lean_is_geq_memo(a, l2, memo, profile)
                || Self::lean_is_geq_memo(b, l2, memo, profile)
            {
                return true;
            }
        }
        if let Level::IMax(a, b) = l2 {
            return Self::lean_is_geq_memo(l1, a, memo, profile)
                && Self::lean_is_geq_memo(l1, b, memo, profile);
        }
        if let Level::IMax(_, b) = l1 {
            return Self::lean_is_geq_memo(b, l2, memo, profile);
        }
        let (base1, k1) = l1.get_offset();
        let (base2, k2) = l2.get_offset();
        if base1 == base2 || matches!(base2, Level::Zero) {
            return k1 >= k2;
        }
        if k1 == k2 && k1 > 0 {
            return Self::lean_is_geq_memo(base1, base2, memo, profile);
        }
        false
    }

    /// Whether Lean's `mk_max`/`mk_imax` rebuild this `max`/`imax` node from
    /// its own children to itself. Other nodes are their own rebuild.
    fn lean_rebuilds_to_itself(&self, profile: LeanLevelProfile) -> bool {
        match self {
            Level::Max(a, b) => Level::lean_mk_max(Level::clone(a), Level::clone(b)) == *self,
            Level::IMax(a, b) => {
                Level::lean_mk_imax_in_profile(Level::clone(a), Level::clone(b), profile) == *self
            }
            Level::Zero | Level::Succ(_) | Level::Param(_) => true,
        }
    }

    /// Lean's `instantiate` (level.cpp:302, through `replace` and
    /// `update_succ`/`update_max`, 286-300), with Clean's structural reading
    /// of "the children did not change".
    ///
    /// A node whose children changed is rebuilt with `mk_max`/`mk_imax`
    /// (`succ` is rebuilt raw, as `update_succ` does); a node with no
    /// substituted parameter is kept. A node that holds a substituted parameter
    /// but whose children are structurally unchanged (an identity renaming) is
    /// kept too, which is Lean's answer only when the `.olean` shares the
    /// objects; when `mk_max`/`mk_imax` would rebuild it to something else, the
    /// two answers differ, and `hazard` is set so the caller can refuse.
    pub(crate) fn lean_instantiate_with(
        &self,
        lookup: &dyn LevelParamLookup,
        hazard: &mut bool,
    ) -> LeanInstantiated {
        self.lean_instantiate_with_choices(lookup, hazard, None, LeanLevelProfile::Lean430)
    }

    pub(crate) fn lean_instantiate_with_choices(
        &self,
        lookup: &dyn LevelParamLookup,
        hazard: &mut bool,
        choices: Option<&dyn SharingChoices>,
        profile: LeanLevelProfile,
    ) -> LeanInstantiated {
        match self {
            Level::Zero => LeanInstantiated {
                level: None,
                touched: false,
            },
            Level::Param(name) => match lookup.replacement(name) {
                Some(replacement) => LeanInstantiated {
                    level: (replacement != self).then(|| replacement.clone()),
                    touched: true,
                },
                None => LeanInstantiated {
                    level: None,
                    touched: false,
                },
            },
            Level::Succ(inner) => {
                let inner = stack_safe(|| {
                    inner.lean_instantiate_with_choices(lookup, hazard, choices, profile)
                });
                LeanInstantiated {
                    level: inner.level.map(Level::succ),
                    touched: inner.touched,
                }
            }
            Level::Max(a, b) | Level::IMax(a, b) => {
                let left = stack_safe(|| {
                    a.lean_instantiate_with_choices(lookup, hazard, choices, profile)
                });
                let right = stack_safe(|| {
                    b.lean_instantiate_with_choices(lookup, hazard, choices, profile)
                });
                let touched = left.touched || right.touched;
                if left.level.is_none() && right.level.is_none() {
                    if touched && !self.lean_rebuilds_to_itself(profile) {
                        match choices.and_then(|owner| owner.choose_rebuild(self)) {
                            Some(true) => {
                                let rebuilt = if matches!(self, Level::Max(_, _)) {
                                    Level::lean_mk_max(Level::clone(a), Level::clone(b))
                                } else {
                                    Level::lean_mk_imax_in_profile(
                                        Level::clone(a),
                                        Level::clone(b),
                                        profile,
                                    )
                                };
                                return LeanInstantiated {
                                    level: Some(rebuilt),
                                    touched,
                                };
                            }
                            Some(false) => {}
                            None => *hazard = true,
                        }
                    }
                    return LeanInstantiated {
                        level: None,
                        touched,
                    };
                }
                let l1 = left.level.unwrap_or_else(|| Level::clone(a));
                let l2 = right.level.unwrap_or_else(|| Level::clone(b));
                let rebuilt = if matches!(self, Level::Max(_, _)) {
                    Level::lean_mk_max(l1, l2)
                } else {
                    Level::lean_mk_imax_in_profile(l1, l2, profile)
                };
                LeanInstantiated {
                    level: Some(rebuilt),
                    touched,
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "lean_kernel_tests.rs"]
mod tests;
