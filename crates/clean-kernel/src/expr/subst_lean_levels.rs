// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's kernel `instantiate_lparams` (`src/kernel/instantiate.cpp:232-246`
//! @ v4.30.0-rc2): universe parameters substituted in every `Sort` and
//! `Const` level with level.cpp's `instantiate`
//! ([`Level::lean_instantiate_with`]), which rebuilds a changed `max`/`imax`
//! node with Lean's cheap `mk_max`/`mk_imax` rather than Clean's collapsing
//! smart constructors. The checker uses it under
//! [`crate::env::KernelTheory::Lean`] and `LeanReference`
//! (`tc/level_profile.rs`).

use super::{FoldMemo, MemoizedSubst};
use crate::expr::{ek, Expr, ExprFolderOpt, ExprKind, LevelVec};
use crate::level::{LeanLevelProfile, Level, LevelParamLookup, SharingChoices};
use crate::name::Name;
use std::sync::Arc;

/// An expression instantiated the way Lean's kernel does.
pub(crate) struct LeanLevelInstantiation {
    /// The instantiated expression.
    pub(crate) expr: Expr,
    /// Some kept node would have been rebuilt to something else without
    /// object sharing, so Lean's own result depends on the `.olean`'s sharing
    /// (see `level/lean_kernel.rs`). The caller refuses.
    pub(crate) sharing_dependent: bool,
}

struct LeanLevelParamSubst<'a> {
    lookup: &'a dyn LevelParamLookup,
    sharing_dependent: bool,
    /// Pointer-identity memo: see [`FoldMemo`]. Depth pinned to `0`. A hit
    /// skips a node already folded, whose `sharing_dependent` contribution
    /// was recorded on the first visit.
    memo: FoldMemo,
    choices: Option<&'a dyn SharingChoices>,
    profile: LeanLevelProfile,
}

impl MemoizedSubst for LeanLevelParamSubst<'_> {
    fn fold_memo(&mut self) -> &mut FoldMemo {
        &mut self.memo
    }
}

impl ExprFolderOpt for LeanLevelParamSubst<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_level_param_quick()
    }

    fn fold_expr_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        if self.choices.is_some() {
            self.fold_expr_opt(expr).map(Arc::new)
        } else {
            self.fold_shared(expr)
        }
    }

    fn fold_binder_body_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_expr_arc_opt(expr)
    }

    fn fold_sort_opt(&mut self, level: &Level) -> Option<Expr> {
        let out = if self.choices.is_none() && self.profile == LeanLevelProfile::Lean430 {
            level.lean_instantiate_with(self.lookup, &mut self.sharing_dependent)
        } else {
            level.lean_instantiate_with_choices(
                self.lookup,
                &mut self.sharing_dependent,
                self.choices,
                self.profile,
            )
        };
        out.level.map(|nl| ek(ExprKind::Sort(nl)))
    }

    fn fold_const_opt(&mut self, name: &Name, levels: &LevelVec) -> Option<Expr> {
        let mut changed = false;
        let new_levels: LevelVec = levels
            .iter()
            .map(|l| {
                match l
                    .lean_instantiate_with_choices(
                        self.lookup,
                        &mut self.sharing_dependent,
                        self.choices,
                        self.profile,
                    )
                    .level
                {
                    Some(nl) => {
                        changed = true;
                        nl
                    }
                    None => l.clone(),
                }
            })
            .collect();
        changed.then(|| ek(ExprKind::Const(name.clone(), new_levels)))
    }
}

impl Expr {
    /// Lean's `instantiate_lparams`: substitute universe parameters as
    /// `instantiate.cpp:232` does. With no parameters, or none occurring,
    /// the expression is returned unchanged (`instantiate_type_lparams`'s
    /// `is_nil(ls) || !has_param_univ` guard).
    pub(crate) fn lean_instantiate_level_params(
        &self,
        lookup: &dyn LevelParamLookup,
    ) -> LeanLevelInstantiation {
        self.lean_instantiate_level_params_with_choices(lookup, None)
    }

    pub(crate) fn lean_instantiate_level_params_with_choices(
        &self,
        lookup: &dyn LevelParamLookup,
        choices: Option<&dyn SharingChoices>,
    ) -> LeanLevelInstantiation {
        self.lean_instantiate_level_params_in_profile(lookup, choices, LeanLevelProfile::Lean430)
    }

    pub(crate) fn lean_instantiate_level_params_in_profile(
        &self,
        lookup: &dyn LevelParamLookup,
        choices: Option<&dyn SharingChoices>,
        profile: LeanLevelProfile,
    ) -> LeanLevelInstantiation {
        let mut folder = LeanLevelParamSubst {
            lookup,
            sharing_dependent: false,
            memo: FoldMemo::default(),
            choices,
            profile,
        };
        let expr = self.fold_opt_or_clone(&mut folder);
        LeanLevelInstantiation {
            expr,
            sharing_dependent: folder.sharing_dependent,
        }
    }

    /// Lean's `instantiate_lparams` with `params := levels`, keeping every
    /// node whose children did not change (Lean's answer when the objects are
    /// shared). For rebuilding what Lean's kernel generates from stored
    /// declarations (nested-inductive auxiliaries, recursor renaming), where
    /// Clean compares the rebuild with the stored copy structurally.
    pub(crate) fn lean_instantiate_level_params_kept(
        &self,
        params: &[Name],
        levels: &[Level],
    ) -> Expr {
        self.lean_instantiate_level_params_kept_in_profile(
            params,
            levels,
            LeanLevelProfile::Lean430,
        )
    }

    pub(crate) fn lean_instantiate_level_params_kept_in_profile(
        &self,
        params: &[Name],
        levels: &[Level],
        profile: LeanLevelProfile,
    ) -> Expr {
        if params.is_empty() {
            return self.clone();
        }
        self.lean_instantiate_level_params_in_profile(
            &crate::level::SliceLookup { params, levels },
            None,
            profile,
        )
        .expr
    }
}
