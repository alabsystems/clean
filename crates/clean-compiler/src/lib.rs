// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// The compiler keeps staged Lean compatibility passes compiled before every
// downstream call path is wired; keep consumer builds quiet while narrower
// hygiene lints remain active.
//! - `opt` — Optimization passes (inline, CSE, DCE, constant fold, simp)
//! - `pass_manager` — Phase-aware pass manager
//! - `probing` — IR inspection and querying utilities
//! - `rc` — Reference counting insertion
//! - `to_ir` — L5CNF to L5IR conversion
//! - `to_lcnf` — Kernel Expr to L5CNF conversion
//! - `to_mono` — Type erasure and monomorphization
//!
//! # References
//!
//! - Lean 4 LCNF: src/Lean/Compiler/LCNF/Basic.lean
//! - Lean 4 IR: src/Lean/Compiler/IR.lean (compile function, lines 44-78)
//! - Ullrich & de Moura (2020). "Counting Immutable Beans" (IFL 2020)
//!
//! Part of #963 - Compiler IR infrastructure.

#[cfg(feature = "cli")]
pub mod cli;

pub mod back_translate;
#[cfg(test)]
pub(crate) mod back_translate_ext;
#[cfg(test)]
#[path = "back_translate_ext_tests.rs"]
mod back_translate_ext_tests;
#[cfg(test)]
pub(crate) mod borrow_infer;
#[cfg(test)]
pub(crate) mod borrow_infer_ext;
#[cfg(test)]
pub(crate) mod borrow_infer_ext2;
pub mod boxing;
pub mod boxing_cache;
#[cfg(test)]
pub(crate) mod boxing_cache_ext;
#[cfg(test)]
#[path = "boxing_cache_ext_tests.rs"]
mod boxing_cache_ext_tests;
pub mod boxing_expensive_const;
#[cfg(test)]
pub(crate) mod boxing_expensive_const_ext;
#[cfg(test)]
#[path = "boxing_expensive_const_ext_tests.rs"]
mod boxing_expensive_const_ext_tests;
#[cfg(test)]
pub(crate) mod boxing_ext;
#[cfg(test)]
#[path = "boxing_ext_tests.rs"]
mod boxing_ext_tests;
#[cfg(test)]
pub(crate) mod closure;
#[cfg(test)]
pub(crate) mod closure_convert;
#[cfg(test)]
pub(crate) mod closure_convert_ext;
#[cfg(test)]
pub(crate) mod closure_convert_ext_rewrite;
#[cfg(test)]
#[path = "closure_convert_ext_tests.rs"]
mod closure_convert_ext_tests;
#[cfg(test)]
pub(crate) mod closure_convert_fva;
#[cfg(test)]
pub(crate) mod closure_convert_fva_ext;
#[cfg(test)]
pub(crate) mod closure_convert_fva_ext2;
#[cfg(test)]
#[path = "closure_convert_fva_ext_tests.rs"]
mod closure_convert_fva_ext_tests;
#[cfg(test)]
pub(crate) mod closure_ext;
#[cfg(test)]
#[path = "closure_ext_tests.rs"]
mod closure_ext_tests;
pub mod code_visitor;
pub use code_visitor::{CodeFolder, CodeVisitor};
#[cfg(test)]
pub(crate) mod code_visitor_ext;
#[cfg(test)]
#[path = "code_visitor_ext_tests.rs"]
mod code_visitor_ext_tests;
pub mod compile;
#[cfg(test)]
pub(crate) mod compile_ext;
#[cfg(test)]
#[path = "compile_ext_tests.rs"]
mod compile_ext_tests;
pub mod compiler_env;
#[cfg(test)]
pub(crate) mod compiler_env_ext;
#[cfg(test)]
#[path = "compiler_env_ext_tests.rs"]
mod compiler_env_ext_tests;
#[cfg(test)]
pub(crate) mod const_fold;
#[cfg(test)]
pub(crate) mod const_fold_ext;
#[cfg(test)]
pub(crate) mod const_fold_ext2;
#[cfg(test)]
#[path = "const_fold_ext2_integ_tests.rs"]
mod const_fold_ext2_integ_tests;
#[cfg(test)]
#[path = "const_fold_ext2_tests.rs"]
mod const_fold_ext2_tests;
#[cfg(test)]
pub(crate) mod dce;
#[cfg(test)]
pub(crate) mod dce_ext;
#[cfg(test)]
#[path = "dce_ext_tests.rs"]
mod dce_ext_tests;
#[cfg(test)]
pub(crate) mod dce_local;
#[cfg(test)]
pub(crate) mod dce_local_ext;
#[cfg(test)]
#[path = "dce_local_ext_tests.rs"]
mod dce_local_ext_tests;
#[cfg(test)]
#[path = "dce_local_tests.rs"]
mod dce_local_tests;
pub(crate) mod emit_base;
#[cfg(test)]
pub(crate) mod emit_base_ext;
#[cfg(test)]
#[path = "emit_base_ext_tests.rs"]
mod emit_base_ext_tests;
pub mod emit_c;
#[cfg(test)]
pub(crate) mod emit_c_ext;
#[cfg(test)]
#[path = "emit_c_ext_tests.rs"]
mod emit_c_ext_tests;
pub mod emit_rust;
#[cfg(test)]
pub(crate) mod emit_rust_ext;
#[cfg(test)]
#[path = "emit_rust_ext_tests.rs"]
mod emit_rust_ext_tests;
// Experimental, unverified, non-TCB trust-ir backend. Off by default; the
// entire module (and its trust-ir / trust-ir-build dependencies) compile only
// when the `trust-ir-backend` feature is enabled.
#[cfg(feature = "trust-ir-backend")]
pub mod emit_trust_ir;
#[cfg(feature = "trust-ir-backend")]
pub(crate) mod emit_trust_ir_runtime;
// Backend translation-validation minter (P2): kernel-decided semantics-
// preservation certificates for in-fragment decls, attached post-finalize.
#[cfg(feature = "trust-ir-backend")]
pub mod emit_trust_ir_tv;
// WebAssembly backend for the straight-line first-order fragment: `.wat` text
// plus the matching binary encoding, both from one lowering.
pub mod emit_wasm;
pub mod error;
pub mod extraction_ir;
pub mod ffi_bridge;
#[cfg(test)]
pub(crate) mod ffi_bridge_ext;
#[cfg(test)]
#[path = "ffi_bridge_ext_tests.rs"]
mod ffi_bridge_ext_tests;
pub mod ffi_verify;
#[cfg(test)]
pub(crate) mod ffi_verify_ext;
#[cfg(test)]
#[path = "ffi_verify_ext_tests.rs"]
mod ffi_verify_ext_tests;
pub(crate) mod inline_pass;
#[cfg(test)]
pub(crate) mod inline_pass_ext;
#[cfg(test)]
#[path = "inline_pass_ext_tests.rs"]
mod inline_pass_ext_tests;
pub mod ir;
pub mod ir_checker;
#[cfg(test)]
pub(crate) mod ir_checker_ext;
#[cfg(test)]
pub(crate) mod ir_checker_ext2;
#[cfg(test)]
#[path = "ir_checker_ext2_tests.rs"]
mod ir_checker_ext2_tests;
#[cfg(test)]
#[path = "ir_checker_ext_tests.rs"]
mod ir_checker_ext_tests;
#[cfg(test)]
pub(crate) mod ir_ext;
#[cfg(test)]
#[path = "ir_ext_tests.rs"]
mod ir_ext_tests;
pub mod ir_norm_ids;
#[cfg(test)]
pub(crate) mod ir_norm_ids_ext;
#[cfg(test)]
#[path = "ir_norm_ids_ext_tests.rs"]
mod ir_norm_ids_ext_tests;
#[cfg(test)]
pub(crate) mod ir_pretty;
#[cfg(test)]
pub(crate) mod ir_pretty_ext;
#[cfg(test)]
pub(crate) mod ir_pretty_ext2;
#[cfg(test)]
#[path = "ir_pretty_ext2_tests.rs"]
mod ir_pretty_ext2_tests;
#[cfg(test)]
#[path = "ir_pretty_ext_tests.rs"]
mod ir_pretty_ext_tests;
#[cfg(test)]
#[path = "ir_pretty_tests.rs"]
mod ir_pretty_tests;
pub mod join_point_lower;
#[cfg(test)]
pub(crate) mod join_point_lower_ext;
#[cfg(test)]
#[path = "join_point_lower_ext_tests.rs"]
mod join_point_lower_ext_tests;
pub mod lcnf;
#[cfg(test)]
pub(crate) mod lcnf_ext;
#[cfg(test)]
pub(crate) mod lcnf_ext2;
#[cfg(test)]
#[path = "lcnf_ext2_tests.rs"]
mod lcnf_ext2_tests;
#[cfg(test)]
#[path = "lcnf_ext_tests.rs"]
mod lcnf_ext_tests;
pub mod mangle;
#[cfg(test)]
pub(crate) mod mangle_ext;
#[cfg(test)]
#[path = "mangle_ext_tests.rs"]
mod mangle_ext_tests;
pub mod match_compile;
#[cfg(test)]
pub(crate) mod match_compile_ext;
#[cfg(test)]
#[path = "match_compile_ext_tests.rs"]
mod match_compile_ext_tests;
pub mod match_eval;
#[cfg(test)]
pub(crate) mod match_eval_ext;
#[cfg(test)]
pub(crate) mod match_eval_ext2;
#[cfg(test)]
#[path = "match_eval_ext2_tests.rs"]
mod match_eval_ext2_tests;
#[cfg(test)]
#[path = "match_eval_ext_tests.rs"]
mod match_eval_ext_tests;
#[cfg(test)]
pub(crate) mod match_exhaustive;
#[cfg(test)]
pub(crate) mod match_exhaustive_ext;
#[cfg(test)]
#[path = "match_exhaustive_ext_tests.rs"]
mod match_exhaustive_ext_tests;
#[cfg(test)]
pub(crate) mod match_tree;
#[cfg(test)]
pub(crate) mod match_tree_ext;
#[cfg(test)]
#[path = "match_tree_ext_tests.rs"]
mod match_tree_ext_tests;
#[cfg(test)]
pub mod native_codegen;
#[cfg(test)]
pub(crate) mod native_codegen_ext;
#[cfg(test)]
pub(crate) mod native_codegen_ext2;
#[cfg(test)]
#[path = "native_codegen_ext2_tests.rs"]
mod native_codegen_ext2_tests;
#[cfg(test)]
#[path = "native_codegen_ext_tests.rs"]
mod native_codegen_ext_tests;
pub mod native_eval;
#[cfg(test)]
pub(crate) mod native_eval_ext;
#[cfg(test)]
#[path = "native_eval_ext_tests.rs"]
mod native_eval_ext_tests;
pub mod native_types;
#[cfg(test)]
pub(crate) mod native_types_ext;
pub mod opt;
#[cfg(test)]
pub(crate) mod opt_ext;
#[cfg(test)]
#[path = "opt_ext_tests.rs"]
mod opt_ext_tests;
#[cfg(test)]
pub(crate) mod opt_passes;
#[cfg(test)]
pub(crate) mod opt_passes_ext;
#[cfg(test)]
#[path = "opt_passes_ext_tests.rs"]
mod opt_passes_ext_tests;
pub mod pass_manager;
#[cfg(test)]
pub(crate) mod pass_manager_ext;
#[cfg(test)]
#[path = "pass_manager_ext_tests.rs"]
mod pass_manager_ext_tests;
pub mod probing;
#[cfg(test)]
pub(crate) mod probing_ext;
#[cfg(test)]
#[path = "probing_ext_tests.rs"]
mod probing_ext_tests;
pub mod rc;
#[cfg(test)]
pub(crate) mod rc_ext;
#[cfg(test)]
#[path = "rc_ext_tests.rs"]
mod rc_ext_tests;
#[cfg(test)]
pub(crate) mod reg_alloc;
#[cfg(test)]
pub(crate) mod reg_alloc_ext;
#[cfg(test)]
#[path = "reg_alloc_ext_tests.rs"]
mod reg_alloc_ext_tests;
#[cfg(test)]
pub(crate) mod reset_reuse;
#[cfg(test)]
pub(crate) mod reset_reuse_ext;
#[cfg(test)]
#[path = "reset_reuse_ext_tests.rs"]
mod reset_reuse_ext_tests;
#[cfg(test)]
pub(crate) mod specialize;
#[cfg(test)]
pub(crate) mod specialize_ext;
#[cfg(test)]
#[path = "specialize_ext_tests.rs"]
mod specialize_ext_tests;
#[cfg(test)]
pub(crate) mod tail_call;
#[cfg(test)]
pub(crate) mod tail_call_ext;
#[cfg(test)]
#[path = "tail_call_ext_opt_tests.rs"]
mod tail_call_ext_opt_tests;
#[cfg(test)]
#[path = "tail_call_ext_tests.rs"]
mod tail_call_ext_tests;
#[cfg(test)]
#[path = "tail_call_tests.rs"]
mod tail_call_tests;
pub mod to_ir;
#[cfg(test)]
pub(crate) mod to_ir_ext;
#[cfg(test)]
#[path = "to_ir_ext_tests.rs"]
mod to_ir_ext_tests;
pub mod to_lcnf;
#[cfg(test)]
pub(crate) mod to_lcnf_ext;
#[cfg(test)]
#[path = "to_lcnf_ext_tests.rs"]
mod to_lcnf_ext_tests;
pub mod to_mono;
#[cfg(test)]
pub(crate) mod to_mono_ext;
#[cfg(test)]
#[path = "to_mono_ext_tests.rs"]
mod to_mono_ext_tests;
#[cfg(test)]
pub(crate) mod unboxing;
#[cfg(test)]
pub(crate) mod unboxing_ext;
#[cfg(test)]
#[path = "unboxing_ext_tests.rs"]
mod unboxing_ext_tests;

// Re-export the stable crate-root pipeline API used by integration tests and
// examples so callers do not need to depend on internal module layout.
pub use boxing::BoxingConfig;
pub use error::CompilerError;
pub use lcnf::Decl;
pub use opt::{optimize, optimize_all, OptConfig};
pub use rc::RCConfig;
pub use to_ir::CtorMeta;
pub use to_lcnf::{constant_to_decl, expr_to_code, is_erasable};
