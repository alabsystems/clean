// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One inductive family's result level, computed once, the way Lean's kernel
//! computes it, and the one helper every elimination decision reads.
//!
//! Lean's `check_inductive_types` (`inductive.cpp@v4.30.0-rc2:211-256`) finds
//! the result level with a whnf between binders and `ensure_sort`
//! ([`crate::tc::TypeChecker::type_former_result_sort`]), and every later step
//! reads that level: the per-field universe bound, `elim_only_at_universe_zero`
//! (through `m_is_not_zero`) and `init_K_target`. The kernel's native admission
//! (`add_inductive`), the structural import tier's recursor regeneration
//! (`imported_family`), the import's large-elimination fixup
//! (`import_large_elim`) and the noConfusion/below generators all ask THIS
//! module, so none of them can read a different level off the syntactic
//! codomain.

use super::types::EnvError;
use super::Environment;
use crate::expr::Expr;
use crate::inductive::{count_pi_args, InductiveDecl, InductiveError, InductiveType};
use crate::level::Level;
use crate::tc::{TypeChecker, TypeFormerSort};

impl Environment {
    /// [`TypeChecker::type_former_result_sort`] under this environment's mode
    /// and subtyping rule (cumulative on the Coq lane, as the declaration
    /// checks that admit the family). The syntactic fast path builds no
    /// checker.
    pub(crate) fn type_former_result_sort(&self, ty: &Expr) -> Option<TypeFormerSort> {
        if let Some(sort) = TypeFormerSort::syntactic(ty) {
            return Some(sort);
        }
        let mut tc = TypeChecker::new(self);
        tc.set_cumulative(self.is_cumulative());
        tc.type_former_result_sort(ty)
    }

    /// The result level of the type former `ty` up to whnf, or `None` when it
    /// is not a sort-valued telescope even after reduction.
    pub(crate) fn type_former_result_level(&self, ty: &Expr) -> Option<Level> {
        self.type_former_result_sort(ty).map(|sort| sort.level)
    }

    /// Whether the type former `ty` is a `Prop` former (result level `0` up to
    /// whnf), the test Lean's `isPropFormerType` makes before generating
    /// `noConfusion` (it reduces too). `None` when the result sort cannot be
    /// determined.
    pub(crate) fn type_former_is_prop(&self, ty: &Expr) -> Option<bool> {
        self.type_former_result_level(ty)
            .map(|level| level.is_zero())
    }

    /// The result level of a type former with exactly `arity` binders up to
    /// whnf (no binder hidden behind a definition), or `None`. The
    /// noConfusion builders read the `Eq` universe of a non-indexed family
    /// here.
    pub(crate) fn type_former_level_at_arity(&self, ty: &Expr, arity: u32) -> Option<Level> {
        self.type_former_result_sort(ty)
            .filter(|sort| sort.arity == arity)
            .map(|sort| sort.level)
    }

    /// The result level of one family member, for the builders that construct
    /// its eliminators. Refuses, naming the member, a type former that does not
    /// reduce to a sort, and one whose reduction exposes binders the syntactic
    /// telescope does not show: every builder downstream counts parameters and
    /// indices off the syntactic `Pi` telescope, so such a family is refused
    /// rather than mis-indexed (the safe direction: Lean admits it).
    pub(crate) fn member_result_level(&self, member: &InductiveType) -> Result<Level, EnvError> {
        let Some(sort) = self.type_former_result_sort(&member.type_) else {
            return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                "type former of {} does not end in a sort, even up to whnf",
                member.name
            ))));
        };
        let syntactic = count_pi_args(&member.type_);
        if sort.arity != syntactic {
            return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                "type former of {} hides binders behind a definition ({} binders up to whnf, \
                 {syntactic} syntactically); Clean builds eliminators from the syntactic \
                 telescope and refuses such a family",
                member.name, sort.arity
            ))));
        }
        Ok(sort.level)
    }

    /// [`Self::member_result_level`] for every member of `decl`, in order.
    pub(crate) fn block_result_levels(&self, decl: &InductiveDecl) -> Result<Vec<Level>, EnvError> {
        decl.types
            .iter()
            .map(|member| self.member_result_level(member))
            .collect()
    }
}

#[cfg(test)]
#[path = "inductive_result_sort_tests.rs"]
mod tests;
