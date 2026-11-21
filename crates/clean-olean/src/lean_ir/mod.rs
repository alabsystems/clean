// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's compiled IR (λRC), decoded from the `.olean` and IR files that
//! Lean and Lake write. The same representation supports a census,
//! imported-binding checks, and bounded evaluation of pure compiled code.
//!
//! * `types` — the IR data model, a faithful mirror of
//!   `Lean/Compiler/IR/Basic.lean`.
//! * `module_ir::load_module_ir_at` — one module's IR as a root-level `private` import
//!   sees it: `Lean.IR.declMapExt` from the module's main data and its `.ir` file,
//!   plus the `externAttr`, `implementedByAttr`, `regularInitAttr` and
//!   `builtinInitAttr` entries.
//! * `format_decl::format_decl` / `format::name_to_string` — Lean's own text rendering,
//!   for comparison with what the pinned toolchain prints.
//! * `census` — the per-module census behind `clean olean ir-census`.
//! * `exported_term_eval` — execute a measured pure subset from the exported
//!   base part with a numeral syntax invocation and typed host operations.
//! * `nat_eval` — execute first-order Nat functions from captured split IR.
//!
//! # Why this model is not `clean_compiler::ir`
//!
//! `clean-compiler`'s L5IR is Lean-INSPIRED, not Lean-shaped enough to carry
//! what Lean stores, and it cannot be the decode target from here at all:
//! `clean-compiler` depends on `clean-olean` (its `runtime-lcnf` feature and
//! its tests), so `clean-olean` depending on `clean-compiler` would be a
//! package cycle. What L5IR lacks, measured against `Basic.lean` v4.30.0-rc2:
//!
//! * `IRType.tagged`, and the `leanTypeName` of `struct`/`union`;
//! * `Param.borrow` (L5IR params are `(VarId, IRType)`);
//! * `CtorInfo.size`/`usize`/`ssize` as Lean counts them (L5IR keeps
//!   `num_scalars`/`num_objects`/field types);
//! * `LitVal.num` beyond `2^128` and `LitVal.str` as a literal kind;
//! * `Expr.reset`'s field count, `Expr.reuse`'s `updtHeader`;
//! * `FnBody.inc`'s `c`/`persistent` flags, `dec`'s count and flags, `del`;
//! * `case`'s type id, scrutinee type and ORDERED alternatives (L5IR splits
//!   the `default` out);
//! * `Decl.extern` with its `ExternAttrData`, and `DeclInfo.sorryDep?`.
//!
//! Lowering this model into L5IR is a separate, lossy step that belongs with
//! the consumer that needs it (the landing rule: no capability without its
//! caller).
//!
//! # Visibility
//!
//! The decoded types are crate-private. The census and late
//! `@[implemented_by]` judgement read them directly. The public term
//! elaborator entry point takes captured bytes and returns a kernel
//! expression for normal elaboration and verification. The Nat entry point
//! takes a checked capture, an exported name and its Nat arguments.

#[cfg(any(test, feature = "cli"))]
pub(crate) mod census;
mod decode;
mod error;
pub(crate) mod exported_term_eval;
pub(crate) mod format;
#[cfg(any(test, feature = "cli"))]
pub(crate) mod format_decl;
pub(crate) mod module_ir;
pub(crate) mod nat_eval;
pub(crate) mod nat_program;
pub(crate) mod native_char;
pub(crate) mod native_io_error;
pub(crate) mod native_nat_dictionary;
pub(crate) mod native_owners;
pub(crate) mod native_stdout;
#[cfg(any(test, feature = "cli"))]
mod profile;
pub(crate) mod types;

#[cfg(test)]
mod adversarial_tests;
#[cfg(test)]
mod tests;
