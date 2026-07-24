// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MetaM primitives for runtime metaprogramming
//!
//! This module provides operations that correspond to Lean 4's MetaM monad,
//! enabling runtime type checking and unification operations.
//!
//! Part of #23: Qq Phase 4 - Runtime pattern matching
//!
//! # Design
//!
//! Runtime q-pattern matching requires checking definitional equality at runtime,
//! not just at elaboration time. This module provides the primitives:
//!
//! - `isDefEq`: Check if two expressions are definitionally equal
//! - `withReducible`: Run with reducible transparency
//! - `withNewMCtxDepth`: Run with a fresh metavariable context depth
//! - `instantiateMVars`: Replace metavariables with their assigned values
//!
//! # Usage
//!
//! ```text
//! // Runtime q-pattern matching generates code like:
//! let pattern = mk_app(HAdd.hAdd, [fresh_meta_a, fresh_meta_b]);
//! if is_def_eq(&e, &pattern) {
//!     let a = instantiate_mvars(meta_a);
//!     let b = instantiate_mvars(meta_b);
//!     body(a, b)
//! } else {
//!     fallback
//! }
//! ```
//!
//! Copyright (c) 2026 Andrew Yates. All rights reserved.
//! SPDX-License-Identifier: Apache-2.0

mod context;
mod interpreter;
mod synth;

pub use context::MetaCtx;
pub use synth::{FreshMVarQ, SynthInstanceQResult};

// Re-export TransparencyMode from kernel to avoid duplication (#334)
pub use clean_kernel::TransparencyMode;

#[cfg(test)]
pub(crate) use interpreter::{
    interpret_runtime_match, try_runtime_match, RuntimeInterpretResult, RuntimeInterpreter,
};

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_traversal;
