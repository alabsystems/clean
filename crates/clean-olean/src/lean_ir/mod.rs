// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's compiled IR (λRC), decoded from the `.olean`/`.ir` files the pinned
//! toolchain and Lake write.
//!
//! Stock Lean runs every imported metaprogram — Mathlib's tactics, macros,
//! elaborators and initializers — from this IR (compiled into the binary for
//! core, through `ir_interpreter.cpp` for Mathlib, which has no shared
//! library). Executing it is the route the 2026-09-24 replacement audit names
//! for metaprogramming (`reports/lean4-replacement-audit-2026-09-24/`,
//! `metaprogramming.json` move M1); this module is the first increment:
//! decode, don't run.
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
//! Everything here is crate-private. Its callers are `clean olean ir-census`
//! (the `census`, compiled with the `cli` feature or for tests) and `.olean`
//! import, which reads a module's IR to judge a late `@[implemented_by]`
//! binding (`import::late_binding`, `docs/DECISIONS.md` R149).

#[cfg(any(test, feature = "cli"))]
pub(crate) mod census;
mod decode;
mod error;
mod format;
#[cfg(any(test, feature = "cli"))]
mod format_decl;
pub(crate) mod module_ir;
#[cfg(any(test, feature = "cli"))]
mod profile;
pub(crate) mod types;

#[cfg(test)]
mod adversarial_tests;
#[cfg(test)]
mod tests;
