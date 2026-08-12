// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unification algorithm
//!
//! Handles metavariable instantiation and constraint solving.
//!
//! # Universe Level Unification
//!
//! Fresh universe parameters (like `u_0`, `u_1`) are unified using a union-find
//! structure. When `u_0 = u_1` is established, both are mapped to a canonical
//! representative. When a param is constrained to a concrete level (like `Zero`),
//! the concrete level is propagated to all equivalent params.
//!
//! This ensures that `instantiate_level(u_0)` and `instantiate_level(u_1)` return
//! the same result, avoiding kernel type mismatches like:
//! `TypeMismatch { expected: Sort(Param("u_1")), inferred: Sort(Param("u_0")) }`

pub(crate) mod level_solve;
mod meta_id;
mod meta_state;
mod unifier;

#[cfg(test)]
mod tests;

pub use meta_id::{MetaId, MetaVar};
pub(crate) use meta_state::push_expr_children;
pub use meta_state::MetaState;
pub(crate) use meta_state::{OwnedMetaScopeCloseError, OwnedMetaScopeToken};
pub use unifier::{Unifier, UnifyResult};
