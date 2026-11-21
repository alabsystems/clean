// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Conservative immutable-expression FVar upper bounds. This is not a support
//! set or a typing answer: a hit can be a false positive; a miss proves absence.
//! Direct children supply their already computed bounds. Unknown/contextual set
//! payloads use MAX. No environment, checker scope or node address is retained.
use super::{Expr, ExprKind, FVarId};

impl ExprKind {
    pub(super) fn fvar_upper_bound(&self) -> u64 {
        match self {
            Self::FVar(id) => id.as_u64(),
            Self::App(a, b)
            | Self::Lam(_, a, b)
            | Self::Pi(_, a, b)
            | Self::ZFCMem { element: a, set: b }
            | Self::ZFCComprehension { domain: a, pred: b } => {
                a.fvar_upper_bound().max(b.fvar_upper_bound())
            }
            Self::Let(_, ty, value, body, _) => ty
                .fvar_upper_bound()
                .max(value.fvar_upper_bound())
                .max(body.fvar_upper_bound()),
            Self::Proj(_, _, inner)
            | Self::MData(_, inner)
            | Self::Squash(inner)
            | Self::CubicalPathLam { body: inner } => inner.fvar_upper_bound(),
            Self::CubicalPath { ty, left, right } => ty
                .fvar_upper_bound()
                .max(left.fvar_upper_bound())
                .max(right.fvar_upper_bound()),
            Self::CubicalPathApp { path, arg } => {
                path.fvar_upper_bound().max(arg.fvar_upper_bound())
            }
            Self::CubicalHComp { ty, phi, u, base } => ty
                .fvar_upper_bound()
                .max(phi.fvar_upper_bound())
                .max(u.fvar_upper_bound())
                .max(base.fvar_upper_bound()),
            Self::CubicalTransp { ty, phi, base } => ty
                .fvar_upper_bound()
                .max(phi.fvar_upper_bound())
                .max(base.fvar_upper_bound()),
            Self::CubicalCoe { ty, r, s, base } => ty
                .fvar_upper_bound()
                .max(r.fvar_upper_bound())
                .max(s.fvar_upper_bound())
                .max(base.fvar_upper_bound()),
            Self::ZFCSet(_) => u64::MAX,
            Self::BVar(_)
            | Self::Sort(_)
            | Self::Const(..)
            | Self::Lit(_)
            | Self::SProp
            | Self::CubicalInterval
            | Self::CubicalI0
            | Self::CubicalI1 => 0,
        }
    }
}

impl Expr {
    /// False proves target absence, assuming the existing immutable metadata
    /// invariant. True is only a conservative possibility, including MAX IDs.
    pub(crate) fn may_contain_fvar(&self, target: FVarId) -> bool {
        self.may_contain_fvar_at_or_above(target)
    }

    /// Whether the expression may contain a free variable with an ID at
    /// least `lower`. A negative result rules out the entire upper interval.
    /// Unknown extension payloads retain the conservative upper bound.
    pub fn may_contain_fvar_at_or_above(&self, lower: FVarId) -> bool {
        #[cfg(test)]
        if UNHINTED.with(std::cell::Cell::get) {
            return self.has_fvar_quick();
        }
        self.has_fvar_quick() && lower.as_u64() <= self.fvar_upper_bound()
    }
}

#[cfg(test)]
thread_local! { static UNHINTED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }

#[cfg(test)]
fn without_hint<R>(f: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            UNHINTED.with(|flag| flag.set(self.0));
        }
    }
    let _restore = Restore(UNHINTED.with(|flag| flag.replace(true)));
    f()
}

#[cfg(test)]
#[path = "fvar_bound_tests.rs"]
mod tests;
