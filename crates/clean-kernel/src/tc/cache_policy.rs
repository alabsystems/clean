// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reduction-policy custody across checker cache handoffs.
//!
//! The environment, locals and opaque level callback remain the caller's
//! compatibility obligation. This tag authenticates the explicit policies that
//! govern retained answers, without granting a bundle environment authority.

use super::{CleanMode, Name, TransparencyMode, TypeChecker};
use crate::env::KernelTheory;
use crate::level::LeanLevelProfile;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CachePolicy {
    mode: CleanMode,
    theory: KernelTheory,
    level_profile: LeanLevelProfile,
    transparency: TransparencyMode,
    honor_reducibility: bool,
    allow_unsafe: bool,
    allow_partial: bool,
    cumulative: bool,
    level_params: Option<Vec<Name>>,
}

impl CachePolicy {
    pub(super) fn capture(tc: &TypeChecker<'_>) -> Self {
        Self {
            mode: tc.mode,
            theory: tc.kernel_theory(),
            level_profile: tc.env.lean_level_profile(),
            transparency: tc.transparency,
            honor_reducibility: tc.honor_reducibility.get(),
            allow_unsafe: tc.allow_unsafe,
            allow_partial: tc.allow_partial,
            cumulative: tc.cumulative,
            level_params: tc.level_params.clone(),
        }
    }

    fn matches(&self, tc: &TypeChecker<'_>) -> bool {
        self.mode == tc.mode
            && self.theory == tc.kernel_theory()
            && self.level_profile == tc.env.lean_level_profile()
            && self.transparency == tc.transparency
            && self.honor_reducibility == tc.honor_reducibility.get()
            && self.allow_unsafe == tc.allow_unsafe
            && self.allow_partial == tc.allow_partial
            && self.cumulative == tc.cumulative
            && self.level_params == tc.level_params
    }
}

impl<'env> TypeChecker<'env> {
    /// Establish ownership only at literal construction or immediately after
    /// adoption clears all local answer state. Those bounded call sites default
    /// or clear every non-exported container; only the six retained containers
    /// below can then carry answers. This is not a general checker-state test
    /// and must never be called from a semantic or export fence.
    pub(super) fn establish_empty_cache_policy(self) -> Self {
        let empty_unowned = self.cached_policy.borrow().is_none()
            && self.whnf_cache.borrow().is_empty()
            && self.whnf_core_cache.borrow().is_empty()
            && self.def_eq_cache.borrow().is_empty()
            && self.proj_type_cache.borrow().is_empty()
            && self.unfold_cache.borrow().is_empty()
            && self.equiv_manager.borrow().is_empty();
        if empty_unowned {
            self.cached_policy
                .replace(Some(CachePolicy::capture(&self)));
        }
        self
    }

    /// Settle policy custody before any semantic lookup or cache export.
    /// Scalar settings and the allowed universe names are compared without a
    /// warm-path clone. Defaults are read from the checker, never duplicated.
    pub(super) fn ensure_cache_theory(&self) {
        let matches = self
            .cached_policy
            .borrow()
            .as_ref()
            .is_some_and(|policy| policy.matches(self));
        if !matches {
            self.clear_theory_answers();
            self.cached_policy.replace(Some(CachePolicy::capture(self)));
        }
    }

    /// Adopt saved answers after configuring a fresh checker.
    ///
    /// The bundle must come from the same environment and compatible local
    /// context and opaque level callback. This checks explicit reduction policy
    /// at the ordinary semantic/export fence; it does not authenticate those
    /// caller-owned identities. Configure callbacks before calling this method:
    /// their setters continue to invalidate all live answers.
    ///
    /// The FVar allocation floor is preserved. Checker defaults, resource limits,
    /// context, and configured callbacks are unchanged. Any answers already held
    /// by this checker are discarded before adopting the supplied bundle.
    #[must_use]
    pub fn with_configured_caches(mut self, caches: super::TcCaches) -> Self {
        self.clear_theory_answers();
        self.next_fvar_floor = self.next_fvar_floor.max(caches.next_fvar_id);
        self.cached_policy.replace(caches.policy);
        self.whnf_cache.replace(caches.whnf);
        self.whnf_core_cache.replace(caches.whnf_core);
        self.def_eq_cache.replace(caches.def_eq);
        self.proj_type_cache.replace(caches.proj_type);
        self.unfold_cache.replace(caches.unfold);
        self.equiv_manager.replace(caches.equiv);
        self.establish_empty_cache_policy()
    }
}
