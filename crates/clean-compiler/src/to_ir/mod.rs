// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5CNF to L5IR Conversion
//!
//! Converts high-level L5CNF (clean Compiler Normal Form) to low-level L5IR
//! (clean Intermediate Representation) for backend code generation.
//!
//! # Pipeline Position
//!
//! ```text
//! Expr → L5CNF → [Opt] → [RC] → L5IR → Backend (C/LLVM)
//!                              ^^^^^
//!                              This module
//! ```
//!
//! # Key Transformations
//!
//! 1. **Variable renumbering**: FVarId → VarId (dense local numbering)
//! 2. **Type lowering**: Expr types → IRType (runtime types)
//! 3. **RC pseudo-ops**: `_inc`/`_dec` calls → Inc/Dec IR nodes
//! 4. **Trivial structure elimination**: Single-field wrappers removed
//!
//! # Module Structure
//!
//! - `state`: Conversion state (`ToIRState`, `CtorMeta`, `ToIRConfig`)
//! - `types`: Type conversion (`expr_to_ir_type`)
//! - `ctor_env`: Constructor environment building (`build_ctor_env`)
//! - `lower`: Literal, argument, and parameter lowering
//! - `code`: Core code conversion (`lower_code`, `lower_let_value`)
//! - `pseudo_ops`: Pseudo-op lowering (RC, set, reset/reuse)
//! - `decl`: Declaration-level conversion and public API entry points
//!
//! # References
//!
//! - Lean 4: `src/Lean/Compiler/IR/ToIR.lean` (377 lines)
//! - Lean 4: `src/Lean/Compiler/IR/ToIRType.lean` (250 lines)
//!
//! Part of #994 - L5CNF-to-L5IR conversion module.

pub(crate) mod code;
pub(crate) mod ctor_env;
pub(crate) mod decl;
pub(crate) mod lower;
pub(crate) mod pseudo_ops;
pub(crate) mod state;
pub(crate) mod types;

#[cfg(test)]
mod tests;

// ════════════════════════════════════════════════════════════════════════════
// Public API re-exports
// ════════════════════════════════════════════════════════════════════════════

pub use code::lower_code;
pub use ctor_env::build_ctor_env;
pub use decl::{
    lower_decl, lower_decl_with_arities, lower_decl_with_env, lower_decls, lower_decls_with_env,
    to_ir, to_ir_with_env, ToIROutput,
};
pub use state::{CtorMeta, ToIRConfig, ToIRState};
pub use types::expr_to_ir_type;

// Internal re-exports for test access via `use super::*;`
#[cfg(test)]
pub(crate) use code::compute_proj_expr;
#[cfg(test)]
pub(crate) use types::name_to_ir_type;
