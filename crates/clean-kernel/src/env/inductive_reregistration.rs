// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact input agreement for the successful inductive re-registration path.
//!
//! This compares an input to a stored complete family/constructor payload; it
//! neither registers a declaration nor grants verification provenance. It does
//! not recheck recursors or generate missing convenience definitions. Soundness
//! of the stored environment remains a separate invariant.

use crate::expr::Expr;
use crate::inductive::{count_pi_args, InductiveDecl};
use crate::name::Name;

use super::inductive_fixed_indices::fixed_indices_to_params;
use super::{ConstantKind, EnvError, Environment, Reducibility};

impl Environment {
    /// Return false for an entirely fresh namespace, true for a matching stored
    /// block, or the first existing name when a conflicting block is submitted.
    ///
    /// Equality is structural, including complete member/constructor order.
    /// Exact parameter counts match directly, including imported blocks. The
    /// sole permitted difference is the builder's fixed-index promotion for a
    /// non-nested block. Nested blocks retain the input parameter count and
    /// original constructor spelling, so must not be promoted here.
    pub(super) fn check_inductive_reregistration(
        &self,
        decl: &InductiveDecl,
    ) -> Result<bool, EnvError> {
        let mut names = decl.types.iter().map(|member| &member.name).chain(
            decl.types
                .iter()
                .flat_map(|member| member.constructors.iter().map(|ctor| &ctor.name)),
        );
        let Some(conflict) = names.find(|name| {
            self.constants.contains_key(*name)
                || self.inductives.contains_key(*name)
                || self.constructors.contains_key(*name)
        }) else {
            return Ok(false);
        };
        if self.registered_inductive_payload_matches(decl) {
            Ok(true)
        } else {
            Err(EnvError::DuplicateName(conflict.clone()))
        }
    }

    fn registered_inductive_payload_matches(&self, decl: &InductiveDecl) -> bool {
        let Some(first) = decl
            .types
            .first()
            .and_then(|m| self.inductives.get(&m.name))
        else {
            return false;
        };
        let all_names: Vec<Name> = decl.types.iter().map(|m| m.name.clone()).collect();
        let signature_matches = |name: &Name, type_: &Expr| {
            self.constants.get(name).is_some_and(|constant| {
                constant.name == *name
                    && constant.level_params == decl.level_params
                    && constant.type_ == *type_
                    && constant.value.is_none()
                    && constant.kind == ConstantKind::Definition
                    && !constant.is_reducible
                    && constant.reducibility == Reducibility::Regular(0)
                    && !self.is_unsafe(name)
                    && !self.is_partial(name)
            })
        };

        // Refuse changed syntax/lists before deriving anything from the input.
        // In particular, a truncated constructor list cannot pass vacuously.
        let same_payload = decl.types.iter().all(|member| {
            self.inductives.get(&member.name).is_some_and(|stored| {
                stored.name == member.name
                    && stored.all_names == all_names
                    && stored.level_params == decl.level_params
                    && stored.type_ == member.type_
                    && stored
                        .constructor_names
                        .iter()
                        .eq(member.constructors.iter().map(|c| &c.name))
                    && signature_matches(&member.name, &member.type_)
                    && member.constructors.iter().enumerate().all(|(index, ctor)| {
                        self.constructors
                            .get(&ctor.name)
                            .is_some_and(|stored_ctor| {
                                stored_ctor.name == ctor.name
                                    && stored_ctor.inductive_name == member.name
                                    && stored_ctor.level_params == decl.level_params
                                    && stored_ctor.type_ == ctor.type_
                                    && stored_ctor.constructor_idx == Self::usize_to_u32(index)
                                    && stored_ctor.num_params == stored.num_params
                                    && stored_ctor.num_fields
                                        == count_pi_args(&ctor.type_)
                                            .saturating_sub(stored.num_params)
                                    && signature_matches(&ctor.name, &ctor.type_)
                            })
                    })
            })
        });
        if !same_payload {
            return false;
        }
        // An imported exact block need not have undergone Clean's maximal
        // fixed-index promotion. Preserve exact reuse without recomputing it.
        let num_params = first.num_params;
        let has_nested_member = decl.types.iter().any(|member| {
            self.inductives
                .get(&member.name)
                .is_some_and(|stored| stored.is_nested)
        });
        if decl.num_params != num_params
            && (has_nested_member || fixed_indices_to_params(decl) != num_params)
        {
            return false;
        }
        decl.types.iter().all(|member| {
            self.inductives.get(&member.name).is_some_and(|stored| {
                stored.num_params == num_params
                    && stored.num_indices == count_pi_args(&member.type_).saturating_sub(num_params)
            })
        })
    }
}
