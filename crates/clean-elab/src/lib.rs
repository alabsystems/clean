// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The elaborator keeps staged Lean compatibility and tactic APIs compiled
// before every downstream call path is wired; keep consumer builds quiet while
// narrower hygiene lints remain active.
//! clean Elaborator
//!
//! Converts surface syntax to kernel terms via:
//! - Type inference with metavariables
//! - Named to de Bruijn conversion
//! - Implicit argument insertion
//! - Type class instance resolution
//! - Macro expansion before elaboration
//!
//! # Example
//!
//! ```
//! use clean_elab::{elaborate, ElabCtx};
//! use clean_kernel::Environment;
//! use clean_parser::parse_expr;
//!
//! let env = Environment::new();
//! let mut ctx = ElabCtx::new(&env);
//! let surface = parse_expr("fun (x : Type) => x").unwrap();
//! let kernel_expr = ctx.elaborate(&surface).unwrap();
//! ```

pub mod agent_diagnostics;
pub mod attr_macro;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod attr_macro_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod attr_scoping;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod attr_scoping_integration;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod attribute_ext;
pub(crate) mod attribute_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod attribute_handlers;
pub mod attribute_registry;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod attribute_registry_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod auto_bound;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod auto_bound_ext;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent. Its one production
// caller, `tactic::mathverse_use`'s goal-universe pinning, now uses the production
// `infer::collect_level_params` (no depth cap; this prototype stops at depth 64).
#[cfg(test)]
pub(crate) mod auto_param_ext;
pub mod cert;
pub mod check_cmd;
mod class_attribute;
#[cfg(feature = "cli")]
pub mod cli;
pub(crate) mod coercion;
mod csimp_attribute;
pub(crate) mod decl_attributes;
mod definition_attrs;
pub mod source_diagnostics;
mod source_kind;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod coercion_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod coercion_ext2;
pub mod command_elab;
pub mod command_line_options;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod command_elab_ext;
pub mod command_elab_registry;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod command_elab_registry_ext;
pub(crate) mod commands;
pub(crate) mod guard_msgs;
pub(crate) mod reduce_command;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod commands_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod dep_graph;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod dep_graph_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod dep_graph_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod dep_graph_ext2_impact;
pub mod derive;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod derive_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod derive_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod derive_ext_handlers;
pub(crate) mod derive_ext_handlers2;
pub mod derive_handlers;
pub(crate) mod derive_handlers_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod deriving_handlers;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod diamond_resolution;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod diamond_resolution_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod do_notation;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod do_notation_desugar;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod do_notation_desugar_control;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod do_notation_desugar_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod do_notation_ext;
pub mod elab_cmd;
pub mod elab_hooks;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod elab_hooks_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod env_snapshot;
// Unwired roadmap prototype (2026-08-04): compiled only with its unit tests until the live
// pipeline owns it. Mirrors the pattern already used for pattern_match_ext / error_recovery*.
#[cfg(test)]
pub(crate) mod env_snapshot_ext;
pub(crate) mod error;
pub mod eval_cmd;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod eval_cmd_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
// DELETION CANDIDATE (2026-07-30): the EvalCache/EvalHistory/ExprKey cluster has no
// production caller anywhere in the crate; a future owner pass should decide keep-vs-delete.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod eval_cmd_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod ffi_extern;
// Which elaboration run added a declaration: Lean's imported-module check
// for the `attribute [..]` command.
pub(crate) mod declared_here;
mod source_family_authority;
mod source_prelude;
// `@[implemented_by]`: resolution in Lean's order, and the command form's
// order record.
pub(crate) mod implemented_by;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
pub(crate) mod codata_cmd;
pub(crate) mod codata_seed;
pub(crate) mod codata_variant;
pub(crate) mod codata_variant_coind;
#[cfg(test)]
mod codata_variant_coind_tests;
pub(crate) mod codata_variant_companions;
pub(crate) mod codata_variant_generate;
pub(crate) mod codata_variant_plan;
pub(crate) mod coinductive_surface;
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod ffi_extern_ext;
pub(crate) mod file_context;
pub mod header;
pub(crate) mod hetero_bridge_seed;
pub(crate) mod imports;
pub(crate) mod lake_module_name;
pub mod private_names;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod inductive_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod inductive_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod inductive_ext_elab;
pub(crate) mod infer;
pub(crate) mod instance_alias;
pub(crate) mod instance_priority;
pub(crate) mod instance_store;
mod state_generation;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod instance_priority_ext;
// Unwired roadmap prototype (2026-08-04): compiled only with its unit tests until the live
// pipeline owns it. Mirrors the pattern already used for pattern_match_ext / error_recovery*.
#[cfg(test)]
pub(crate) mod instance_priority_ext2;
pub mod instance_resolution;
pub mod instance_synthesis;
pub(crate) mod instances;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod instances_ext;
pub mod interactive_goals;
pub mod io_bridge;
pub(crate) mod io_monad;
pub(crate) mod island_fence;
pub mod term_info;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod io_monad_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
mod documentation;
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod io_monad_ext2;
/// Lean's refusals outside its kernel: compilation, `#eval`, the safe context.
pub(crate) mod lean_compile_checks;
/// Lean 4.8.0 core constants, for the duplicate-declaration check.
pub(crate) mod lean_core_names;
pub(crate) mod level_mint;
pub(crate) mod level_params;
pub(crate) mod level_role;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod let_rec;
pub(crate) mod let_rec_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod let_rec_ext2;
pub mod macro_cmd;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod macro_cmd_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod macro_hygiene;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod macro_hygiene_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod macro_hygiene_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod macro_hygiene_ext3;
pub(crate) mod macro_integration;
/// `import Mathverse.<Corpus>[.<Constant>]` — Mathverse content as ambient,
/// kernel-checked declarations through the existing gated loader.
pub(crate) mod mathverse_import;
/// Lazy, on-demand resolution of Mathverse names after a CORPUS-level
/// `import Mathverse.<Corpus>` — the request half of the request/load split.
pub(crate) mod mathverse_lazy;
#[cfg(test)]
mod mathverse_lazy_tests;
#[cfg(test)]
mod mathverse_term_resolution_tests;
pub(crate) mod meta;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod meta_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod mutual_decl;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod mutual_decl_ext;
// Unwired roadmap prototype (2026-08-04): compiled only with its unit tests until the live
// pipeline owns it. Mirrors the pattern already used for pattern_match_ext / error_recovery*.
#[cfg(test)]
pub(crate) mod mutual_decl_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod mutual_decl_ext3;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod mutual_inductive;
// Unwired roadmap prototype (2026-08-04): compiled only with its unit tests until the live
// pipeline owns it. Mirrors the pattern already used for pattern_match_ext / error_recovery*.
pub mod module_batch;
// The per-declaration loop `clean check`, `clean lake build` and the LSP share.
pub mod module_driver;
#[cfg(test)]
pub(crate) mod mutual_inductive_ext;
pub(crate) mod mutual_recursion_desugar;
pub(crate) mod name_resolution;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod name_resolution_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod name_resolution_ext2;
pub mod namespace;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod namespace_ext;
pub(crate) mod namespace_open;
pub mod notation;
// Unwired roadmap prototype (2026-08-04): compiled only with its unit tests until the live
// pipeline owns it. Mirrors the pattern already used for pattern_match_ext / error_recovery*.
#[cfg(test)]
pub(crate) mod notation_ext;
pub mod notation_imports;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod notation_priority;
pub(crate) mod notation_priority_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod notation_scope;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod notation_scope_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod notation_scope_ext2;
pub mod options_registry;
pub(crate) mod options_registry_ext;
pub mod oracle_compiler;
#[cfg(test)]
#[cfg(test)]
mod test_env;
// Unwired roadmap prototype. Keep its unit coverage available without making
// placeholder match compilation part of the production elaborator surface.
#[cfg(test)]
pub(crate) mod pattern_match_ext;
mod prelude_providers;
pub(crate) mod preprocess;
pub(crate) mod preprocess_ext;
pub(crate) mod print_axioms;
pub(crate) mod print_cmd;
mod print_equations;
pub(crate) mod proj_recursion;
pub mod register;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod register_ext;
pub(crate) mod registration_warning;
pub(crate) mod section_var_selection;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod section_scope;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod section_scope_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod section_variable_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod section_variable_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod structure_cmd;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod structure_cmd_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod structure_extend;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod structure_extend_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod structure_inherit;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod structure_inherit_ext;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod structure_inherit_ext2;
pub mod syntax_cmd;
pub mod tactic;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tc_outparam;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tc_outparam_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tc_synthesis_ext;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod tc_synthesis_ext2;
pub mod term_elab_registry;
pub(crate) mod u2_histogram;
pub(crate) mod unify;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod unify_ext;
pub(crate) mod value_binder_names;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod variable_cmd;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod variable_cmd_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod where_clause;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
pub(crate) mod universe_occurrence;
#[cfg(test)]
pub(crate) mod where_clause_ext;
pub(crate) mod where_desugar;
pub(crate) mod where_desugar_ext;

// These recovery implementations are unwired roadmap prototypes. Compile them
// only with their unit tests until the live pipeline owns their trust policy.
#[cfg(test)]
pub(crate) mod error_recovery;
#[cfg(test)]
pub(crate) mod error_recovery_ext;
#[cfg(test)]
pub(crate) mod error_recovery_ext2;
pub(crate) mod error_render;
// Value-type half of `error_recovery_ext`, split out for the 500-line rule.
// Same cfg(test) gate as its parent: the recovery prototypes compile only with
// their unit tests until the live pipeline owns their trust policy.
#[cfg(test)]
pub(crate) mod error_recovery_ext_types;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod implicit_args;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod implicit_args_ext;
pub(crate) mod info_tree;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod info_tree_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod lean4_compat;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod lean4_compat_ext;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod lean4_compat_ext2;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod string_interp_ext;
pub(crate) mod string_interpolation;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tactic_interp_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tactic_interp_profile;

#[cfg(test)]
pub(crate) mod test_support;

#[cfg(test)]
#[path = "error_recovery_tests.rs"]
mod error_recovery_tests;

#[cfg(test)]
mod tests_error_render_ratchet;

#[cfg(test)]
#[path = "error_recovery_ext_tests.rs"]
mod error_recovery_ext_tests;

#[cfg(test)]
#[path = "error_recovery_ext2_tests.rs"]
mod error_recovery_ext2_tests;

#[cfg(test)]
#[path = "info_tree_tests.rs"]
mod info_tree_tests;

#[cfg(test)]
#[path = "subobject_projection_tests.rs"]
mod subobject_projection_tests;

#[cfg(test)]
#[path = "structure_proj_binder_info_tests.rs"]
mod structure_proj_binder_info_tests;

#[cfg(test)]
#[path = "info_tree_ext_tests.rs"]
mod info_tree_ext_tests;

#[cfg(test)]
#[path = "include_omit_semantics_tests.rs"]
mod include_omit_semantics_tests;

#[cfg(test)]
#[path = "imported_export_alias_tests.rs"]
mod imported_export_alias_tests;

// Re-export extracted types at crate root for backwards compatibility
/// The Lean world a run's imports resolve in (G72), for callers that set a
/// [`FileContext`]'s with [`FileContext::set_import_context`].
pub use clean_olean::{import_world_for_file, ImportWorld, ImportWorldRefusal};
use derive_handlers::register_user_derive_handler;
pub use error::{ElabElabError, ElabError};
pub use file_context::FileContext;
pub use header::{elaborate_decl_headers_with_context, DeclHeader};
pub use implemented_by::ImplementedByDefect;
pub use imports::{
    effective_import_search_paths, lake_import_search_paths_for_file, nearest_lake_root_for_file,
    olean_available_for_module, olean_available_in_world, process_import_batch_with_search_paths,
    process_imports, process_imports_with_policy, resolve_intra_project_import, ImportPolicy,
};
pub use lake_module_name::{
    entry_module_name, lean_module_name_for_file, path_module_label, path_module_name,
};
pub use preprocess::preprocess_decl_with_context;
#[cfg(test)]
pub(crate) use register::register_elab_result;
pub use register::{kernel_check_failure_count, register_aesop_rule};

/// Run synchronous elaboration on this thread with source compiler and safe-
/// context checks enabled. Direct mathematical elaboration keeps its ordinary
/// default policy outside the closure. Nested calls retain the enabled policy;
/// normal return and unwinding restore the previous scope.
///
/// This enables checks, never grants declaration or proof authority. A
/// declaration may register mathematically while returning source errors in
/// [`ElabResult::source_error_message`]; source consumers must inspect them.
pub fn with_source_compilation_checks<T>(check: impl FnOnce() -> T) -> T {
    let _scope = lean_compile_checks::FrontDoorScope::enter(true);
    check()
}

/// Whether synchronous elaboration on this thread currently applies source
/// compiler policy. This observation grants no authority. Cache consumers must
/// bind this policy to their evidence and replay, or decline cached results.
#[must_use]
pub fn source_compilation_checks_enabled() -> bool {
    lean_compile_checks::front_door_active()
}

impl FileContext {
    /// Whether imports may search external `.olean` paths.
    ///
    /// Trust's Clean-island stand-in import census reads this policy to claim
    /// nothing about a file whose imports a real artifact may have served.
    /// Reading the policy does not change it or authorize an import.
    #[must_use]
    pub fn external_import_search_enabled(&self) -> bool {
        self.external_import_search_enabled_impl()
    }
}

// =============================================================================
// Stack overflow protection for deep recursion
// =============================================================================

/// Minimum stack space to reserve before recursive calls (256 KB).
///
/// CONSTRAINT: must exceed the worst-case stack consumed BETWEEN two
/// consecutive `stack_safe` checkpoints, or the guard itself faults. With
/// the old 32 KB red zone, ONE debug-build elaborator cycle
/// (`elaborate` → `elaborate_surface_inner` → `elab_app_inner` →
/// `elab_universe_inst`'s iterator-adapter chain → `elab_level`) consumed
/// the whole zone, so a checkpoint could pass with ~32 KB remaining and
/// the NEXT checkpoint hit the thread's guard page inside
/// `stacker::__grow` before it could switch segments. Measured 2026-08-26
/// as a stack overflow on default 2 MB libtest threads (any invocation
/// where `.cargo/config.toml`'s `RUST_MIN_STACK` does not reach the test
/// binary): `codata_cmd_tests::test_codata_stream_computes_through_the_encoding`,
/// also `test_codef_stream_e2e` / `test_codata_mk_branching_e2e` under
/// other filter groupings. 256 KB mirrors the kernel's red zone
/// (`clean-kernel/src/expr/mod.rs`), ~8x the measured worst cycle.
/// Regression pin: `codata_cmd_tests::test_codata_stream_encoding_survives_small_thread_stack`.
const MIN_STACK_RED_ZONE: usize = 256 * 1024;

/// Stack size to grow to when running low (1 MB).
///
/// CONSTRAINT: must comfortably exceed `MIN_STACK_RED_ZONE` — each grown
/// segment offers `STACK_GROWTH_SIZE - MIN_STACK_RED_ZONE` usable bytes
/// before the next growth (the kernel ships the same 256 KB / 1 MB pair).
const STACK_GROWTH_SIZE: usize = 1024 * 1024;

/// Stack-safe recursive call wrapper.
///
/// Mirrors the kernel's `stack_safe` pattern (`clean-kernel/src/expr/mod.rs`).
/// Before executing the closure, checks remaining stack space against
/// `MIN_STACK_RED_ZONE` and spawns a new thread with `STACK_GROWTH_SIZE`
/// if running low.
///
/// # REQUIRES
/// - `stacker` crate must be a dependency
///
/// # ENSURES
/// - Closure is called exactly once
/// - Provides stack overflow protection for deep recursion
#[inline(always)]
pub(crate) fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(MIN_STACK_RED_ZONE, STACK_GROWTH_SIZE, f)
}

pub use check_cmd::CheckResult as EnhancedCheckResult;
pub use check_cmd::{check_expression, check_name};
pub use commands::{CheckResult, EvalResult, PrintResult};
pub use eval_cmd::{eval_expression, EvalResult as EnhancedEvalResult};
pub use guard_msgs::{result_messages, CommandMessage, GuardMsgsResult, MessageSeverity};
pub(crate) use infer::mutual_lift::{mutual_lift_idx, MutualLiftState};
/// Test seam: the match join-point outcomes this thread recorded
/// (`infer::elab_match::join_point`).
#[cfg(any(test, debug_assertions))]
#[doc(hidden)]
pub use infer::take_join_outcomes;
pub use infer::{
    ClassRegistration, CommandOutput, DerivedInstance, ElabCtx, ElabResult, HoleContext,
    JoinOutcome,
};
pub use instances::{ClassInfo, InstanceInfo, InstanceTable, DEFAULT_PRIORITY};
pub use macro_integration::{
    expand_surface_macros, surface_to_syntax, syntax_to_surface, MacroCtx, MacroExpansionError,
};
pub use meta::{FreshMVarQ, MetaCtx, SynthInstanceQResult, TransparencyMode};
pub use print_axioms::PrintAxiomsResult;
pub use print_cmd::{print_declaration, DeclKind, PrintResult as EnhancedPrintResult};
pub use reduce_command::ReduceResult;
pub use registration_warning::{
    RegisteredElabResult, RegistrationWarning, RegistrationWarningKind,
};
pub use tactic::{
    apply, assumption, constructor, exact, intro, intros, rfl, Goal, LocalDecl, ProofState,
    RewriteCandidate, TacticError, TacticResult,
};
pub use unify::{MetaId, MetaState, MetaVar, Unifier, UnifyResult};

/// Domain-prefixed alias for collision-free imports.
///
/// Use `ElabLocalDecl` when importing from multiple crates with `LocalDecl` types.
pub use tactic::LocalDecl as ElabLocalDecl;

// Per-declaration timing for `clean check --json`, off unless a caller arms it.
// The recorder is crate-private; its public surface is the four items below,
// defined here at the crate root rather than re-exported from the module.
pub(crate) mod decl_timing;
// Per-declaration refill of the automation work budget (`clean_auto`'s
// `maxHeartbeats`-shaped budget) and the named error it leaves behind.
pub(crate) mod decl_work_budget;

/// What a [`DeclTiming`] record timed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DeclTimingKind {
    /// An `import` command: loading (and converting) its module closure.
    Import,
    /// A declaration the user wrote (`def`, `theorem`, `instance`, …).
    Declaration,
    /// Any other command (`open`, `variable`, `attribute`, `#check`, …).
    Command,
}

/// Wall time the elaborator spent on one declaration, kernel check included.
///
/// Recorded per OUTERMOST non-container declaration -- see `decl_timing.rs`
/// for what that means for `section`/`namespace` members, desugarings and
/// `mutual` blocks.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct DeclTiming {
    /// Namespace-qualified name, `[anonymous]` for an unnamed instance or
    /// example, `mutual(a, b)` for a mutual block.
    pub name: String,
    /// Whether this was an `import`, a declaration, or another command.
    pub kind: DeclTimingKind,
    /// Byte offset of the declaration's span in the source it was parsed from.
    pub byte_start: usize,
    /// Wall time from entering the elaborator to registering the result.
    pub elapsed: std::time::Duration,
    /// Automation work units the declaration spent against its budget
    /// (`clean_auto::automation_work_used`); `0` when the budget is disabled.
    /// Deterministic, unlike `elapsed`: the calibration input for
    /// `clean check --automation-budget`.
    pub automation_work: u64,
}

/// Arm per-declaration timing on THIS thread, discarding anything left from an
/// earlier run. Off unless called; see [`take_decl_timings`].
pub fn begin_decl_timing() {
    decl_timing::begin();
}

/// Disarm per-declaration timing on this thread and return the records made
/// since [`begin_decl_timing`], in elaboration order.
#[must_use]
pub fn take_decl_timings() -> Vec<DeclTiming> {
    decl_timing::take()
}

/// Common imports for elaboration users.
///
/// # Example
///
/// ```rust
/// use clean_elab::prelude::*;
///
/// let env = clean_kernel::Environment::new();
/// let mut ctx = ElabCtx::new(&env);
/// // ... elaborate expressions
/// ```
pub mod prelude {
    pub use crate::meta::{MetaCtx, TransparencyMode};
    pub use crate::tactic::{
        apply, assumption, constructor, exact, intro, intros, rfl, Goal, LocalDecl, ProofState,
        RewriteCandidate, TacticError, TacticResult,
    };
    pub use crate::unify::{MetaId, MetaState, MetaVar, Unifier, UnifyResult};
    pub use crate::{
        elaborate, elaborate_decl, elaborate_decl_and_register,
        elaborate_decl_and_register_with_context, elaborate_decl_and_register_with_warning,
        preprocess_decl_with_context, ElabCtx, ElabError, ElabResult, FileContext,
        RegisteredElabResult, RegistrationWarning, RegistrationWarningKind,
    };
}

fn source_elaboration_advice(
    env: &clean_kernel::Environment,
) -> Result<clean_kernel::Environment, ElabError> {
    if source_prelude::is_island_prelude(env) {
        return Ok(env.clone());
    }
    clean_kernel::tc::with_declaration_budget_suspended(|| env.bootstrap_stub_advice())
        .map_err(|e| register::map_add_decl_error("bootstrap stub advice", e))
}

/// Shared [`module_driver::EnvironmentSetup`] equal to pinned Lean `Init`
/// (Ph3 I.2 / Clean F5).
#[must_use]
pub fn pinned_init_environment_setup() -> module_driver::EnvironmentSetup {
    module_driver::EnvironmentSetup::PINNED_INIT
}

/// Whether `env` carries the island prelude marker (Ph3 I.2 / Clean F5).
#[must_use]
pub fn is_island_environment(env: &clean_kernel::Environment) -> bool {
    source_prelude::is_island_prelude(env)
}

/// Construct an island elaboration environment and citation gate in `decision`
/// over the shared pinned-`Init` constructor, armed with the island prelude's
/// value-less constant fence (Ph3 I.2 / Clean F5).
pub fn island_environment_in_world(
    decision: &clean_olean::SourceWorldDecision,
    header: &clean_parser::FileHeader,
) -> Result<
    (clean_kernel::Environment, clean_olean::ImportedConeGate),
    module_driver::ModuleSetupError,
> {
    module_driver::module_environment_for_header_in_world(
        module_driver::EnvironmentSetup::ISLAND_PINNED_INIT,
        decision,
        header,
    )
}

/// Construct an island elaboration environment and citation gate over the
/// configured compiler-pin snapshot world (`v4.30.0-rc2`) (Ph3 I.2 / Clean F5).
pub fn island_environment_for_header(
    header: &clean_parser::FileHeader,
) -> Result<
    (clean_kernel::Environment, clean_olean::ImportedConeGate),
    module_driver::ModuleSetupError,
> {
    let decision = clean_olean::source_world_for_snapshot().map_err(|reason| {
        module_driver::ModuleSetupError::LeanWorld {
            world: clean_kernel::lean_world::LeanWorld::ORACLE,
            reason: reason.to_string(),
        }
    })?;
    island_environment_in_world(&decision, header)
}

/// Elaborate surface syntax to kernel expression
///
/// # REQUIRES
/// - `env` is a valid Environment with required types (Nat, Bool, etc. if used)
/// - `surface` is a valid surface expression from the parser
///
/// # ENSURES
/// - On success, returns kernel `Expr` with de Bruijn indices
/// - Metavariables are resolved during elaboration
/// - Universe levels are inferred and resolved
///
/// Optional bootstrap vocabulary is elaboration advice only: `env` is not
/// extended. To check the returned IR, opt into its required stub fragments or
/// use the mutable elaboration-and-registration entry point.
pub fn elaborate(
    env: &clean_kernel::Environment,
    surface: &clean_parser::SurfaceExpr,
) -> Result<clean_kernel::Expr, ElabError> {
    let advice = source_elaboration_advice(env)?;
    let mut ctx = ElabCtx::new(&advice);
    let result = (|| {
        let expr = ctx.elaborate(surface)?;
        ctx.finish_required_do_obligations()?;
        Ok(ctx.metas.instantiate_levels(&ctx.metas.instantiate(&expr)))
    })();
    result.map_err(|error: ElabError| error.with_ident_suggestions(&advice))
}

/// Elaborate a surface declaration to a kernel declaration result
///
/// # REQUIRES
/// - Same as `elaborate`
///
/// # ENSURES
/// - On success, returns `ElabResult` variant matching declaration type
/// - Declaration name is extracted and validated
///
/// Like [`elaborate`], this is source advice, not registration. The mutable
/// entry point prepares any requested optional fragments and checks the result.
pub fn elaborate_decl(
    env: &clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> Result<ElabResult, ElabError> {
    let advice = source_elaboration_advice(env)?;
    let mut ctx = ElabCtx::new(&advice);
    ctx.elab_decl(decl)
        .map_err(|error| error.with_ident_suggestions(&advice))
}

/// Elaborate a declaration (without kernel registration) and return both the
/// elaboration result and the hole contexts captured during elaboration.
///
/// Unlike [`elaborate_decl_and_register_with_warning`], this does **not**
/// register the declaration, so it surfaces hole contexts even for declarations
/// that would fail kernel registration — most notably a declaration containing
/// an unfilled `_` hole, whose unsolved metavariable is a free variable the
/// kernel rejects. That is precisely the case an IDE needs: the user is hovering
/// a hole they have not yet filled in.
///
/// The returned `Vec<HoleContext>` is always populated from the elaboration
/// state regardless of whether `result` is `Ok` or `Err`, so callers can show
/// hole goals even when the surrounding term does not fully type-check.
///
/// IDE-surface only: nothing is added to `env`.
pub fn elaborate_decl_capturing_holes(
    env: &clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> (Result<ElabResult, ElabError>, Vec<HoleContext>) {
    let advice = match source_elaboration_advice(env) {
        Ok(advice) => advice,
        Err(error) => return (Err(error), Vec::new()),
    };
    let mut ctx = ElabCtx::new(&advice);
    let result = ctx
        .elab_decl(decl)
        .map_err(|error| error.with_ident_suggestions(&advice));
    let hole_contexts = ctx.collect_hole_contexts();
    (result, hole_contexts)
}

/// Elaborate a surface declaration and register any aesop rules
///
/// This is the primary entry point for elaborating declarations with attributes.
/// It handles the full lifecycle:
/// 1. Processes imports to initialize appropriate Mathlib stubs
/// 2. Elaborates the declaration
/// 3. Registers any `@[aesop ...]` attributes as rules in the environment
/// 4. Returns the elaboration result
///
/// # REQUIRES
/// - `env` is a mutable Environment
/// - `decl` is a valid surface declaration
///
/// # ENSURES
/// - On success, declaration is added to `env`
/// - Aesop rules (if any) are registered in `env`
/// - Import declarations initialize appropriate stubs
/// - Returns `ElabResult` indicating what was done
///
/// # Example
/// ```text
/// let decl = parse_decl("@[aesop safe apply] theorem my_intro : A → B := sorry")?;
/// let result = elaborate_decl_and_register(&mut env, &decl)?;
/// // The aesop rule is now registered in env
/// ```
pub fn elaborate_decl_and_register(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> Result<ElabResult, ElabError> {
    Ok(elaborate_decl_and_register_with_warning(env, decl)?.result)
}

/// Elaborate a declaration with file-level context that persists namespace state.
///
/// Unlike [`elaborate_decl_and_register`], this variant carries namespace state
/// (from `open` and `export` commands) across declarations via [`FileContext`].
/// Use this when processing a sequence of declarations from a single file:
///
/// ```text
/// let mut file_ctx = FileContext::new();
/// for decl in parse_file(code)? {
///     let processed = preprocess_decl_with_context(&decl, &mut file_ctx);
///     elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)?;
/// }
/// ```
///
/// After `open Nat`, subsequent calls will resolve `add` as `Nat.add`.
///
/// # REQUIRES
/// - `env` is a mutable Environment
/// - `decl` is a valid surface declaration (typically pre-processed via
///   [`preprocess_decl_with_context`])
/// - `file_ctx` tracks accumulated variables, universe params, and namespace state
///
/// # ENSURES
/// - On success, declaration is added to `env`
/// - When a `deriving` class fails, the structure or inductive is still
///   added (with every instance its clause did derive) and the call returns
///   `Ok`: an [`ElabResult::Multiple`] whose first leaf is the type and whose
///   later leaves are one [`ElabResult::Failed`] per failed class, each
///   carrying [`ElabError::DerivingHandlerFailed`] — Lean declares the type
///   before it runs the handlers and logs a handler's error
///   (`infer::deriving_log`)
/// - Namespace state from `open`/`export` is persisted in `file_ctx`
pub fn elaborate_decl_and_register_with_context(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: &mut FileContext,
) -> Result<ElabResult, ElabError> {
    Ok(elaborate_decl_and_register_inner(env, decl, Some(file_ctx))?.result)
}

/// Elaborate, register, and return both the result and any trust warning,
/// while threading namespace / option state through a `FileContext`.
pub fn elaborate_decl_and_register_with_context_and_warning(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: &mut FileContext,
) -> Result<RegisteredElabResult, ElabError> {
    elaborate_decl_and_register_inner(env, decl, Some(file_ctx))
}

/// Elaborate a surface declaration, register it, and return any trust warnings.
///
/// This is the report-returning variant of [`elaborate_decl_and_register`].
/// After successful registration, it queries the kernel's stored declaration
/// trust summary provenance and returns a [`RegisteredElabResult`] containing both the
/// elaboration result and an optional [`RegistrationWarning`].
///
/// The warning selection policy preserves Lean 4's `warnIfUsesSorry`
/// priority for explicit vs synthetic `sorry`, while also surfacing
/// `trustedArith` and `trustedAy` debt when no sorry is present.
///
/// # REQUIRES
/// - `env` is a mutable Environment
/// - `decl` is a valid surface declaration
///
/// # ENSURES
/// - On success, declaration is added to `env`. Source-compiler errors are
///   carried by `ElabResult::Diagnosed` without revoking that registration;
///   consumers must inspect `ElabResult::source_error_message` as well.
/// - Warning is computed only after successful registration
/// - If attribute registration fails, no stale warning is returned
pub fn elaborate_decl_and_register_with_warning(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> Result<RegisteredElabResult, ElabError> {
    elaborate_decl_and_register_inner(env, decl, None)
}

/// Internal implementation shared by all `elaborate_decl_and_register*` variants.
///
/// When `file_ctx` is `Some`, namespace state is injected into the `ElabCtx`
/// before elaboration and extracted back afterward so `open`/`export` aliases
/// persist across declarations.
fn elaborate_decl_and_register_inner(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: Option<&mut FileContext>,
) -> Result<RegisteredElabResult, ElabError> {
    elaborate_decl_and_register_inner_with_aux(env, decl, file_ctx, None)
}

/// Build an [`ElabResult::Failed`] leaf for an inner declaration (a member of a
/// `namespace`/`section`/`mutual` block) whose elaboration or kernel check
/// failed.
///
/// The leaf carries a best-effort, namespace-qualified name (so reporting shows
/// e.g. `T.b` rather than the bare short name), a clone of the inner surface
/// declaration (for span-accurate diagnostics), and the original error. It is
/// deliberately NOT registered into the kernel — it stands for a decl that
/// already failed — but it IS a counted leaf so the failure is tallied and
/// reported, never silently dropped.
fn failed_inner_leaf(
    fc: &FileContext,
    inner: &clean_parser::SurfaceDecl,
    error: ElabError,
) -> ElabResult {
    let short = preprocess_ext::decl_name(inner)
        .cloned()
        .unwrap_or_default();
    let ns = fc.namespace_state().current_namespace();
    let qualified = if short.is_anonymous() {
        ns.to_string()
    } else if ns.is_anon() {
        short.to_string()
    } else {
        short
            .qualify_under(&clean_parser::SurfaceName::from_name(ns.clone()))
            .to_string()
    };
    ElabResult::Failed {
        name: qualified,
        decl: Box::new(inner.clone()),
        error: Box::new(error),
    }
}

/// The namespaces entering `target` from `state`'s current namespace
/// activates for the first time: `target` and each of its ancestors below the
/// current namespace that is not already active, outermost first.
fn newly_entered_namespaces(
    state: &namespace::NamespaceState,
    target: &clean_kernel::name::Name,
) -> Vec<clean_kernel::name::Name> {
    entered_namespace_chain(state, target)
        .into_iter()
        .filter(|ns| !state.is_scope_active(ns))
        .collect()
}

/// Every namespace `namespace target` enters from the current one, outermost
/// first: Lean's `addScopes` pushes one scope per component and runs
/// `activateScoped` on each (`Lean/Elab/BuiltinCommand.lean`), a no-op in a
/// state where it is already active.
fn entered_namespace_chain(
    state: &namespace::NamespaceState,
    target: &clean_kernel::name::Name,
) -> Vec<clean_kernel::name::Name> {
    let current = state.current_namespace().clone();
    let mut chain = Vec::new();
    let mut prefix = target.clone();
    while !prefix.is_anon() && prefix != current {
        chain.push(prefix.clone());
        prefix = namespace::parent_name(&prefix);
    }
    chain.reverse();
    chain
}

/// Record `local instance` / `scoped instance` registrations from a
/// just-registered elaboration result into the `FileContext` (B99).
///
/// - `local instance` → recorded at the current local-scope depth; retired
///   (hidden from all later resolution) when that section/namespace block
///   ends. Previously the modifier was silently DROPPED, so a `local
///   instance` leaked past `end` (r82 `instprio_local_section_shadow`:
///   9 provable outside the section where Lean proves 5).
/// - `scoped instance` → recorded with its declaring namespace (the current
///   namespace at registration); visible only while that namespace is
///   current or opened. Previously registered as if global (r82
///   `instprio_scoped_open_in`: 2 provable without `open` where Lean
///   proves 1).
///
/// `Multiple` results (namespace/section blocks) are walked recursively;
/// every other result kind carries no instance scope.
///
/// Both are ALSO recorded in the environment, which holds the instance
/// registration itself and outlives the file: a module elaborated later in the
/// same environment (an importer under `clean check`, any module under `clean
/// project check`) starts with a fresh `FileContext` and used to see another
/// module's `local instance` as global and its `scoped instance` without
/// `open` (`P: namespace N; scoped instance i3 : C := ⟨3⟩; end N`,
/// `M: import P; theorem m : C.v = 3 := rfl` passed; Lean 4.8.0 rejects it).
/// A `scoped instance` goes into the same table the `.olean` loader fills for
/// an imported one ([`clean_olean::ScopedInstanceState`]), with its entry in
/// `scopedEntries` order; a `local instance` is marked local in the
/// environment. Either is in a scope's instance state only through that
/// scope's own entries (`crate::instance_store`).
pub(crate) fn record_instance_scopes(
    fc: &mut FileContext,
    env: &mut clean_kernel::Environment,
    result: &ElabResult,
) {
    use clean_parser::DeclScope;
    match result {
        ElabResult::Instance {
            name, modifiers, ..
        } => match modifiers.scope {
            // `register_elab_result` registered it; its only entry is the
            // local (or scoped) one, so it is marked before the entry is
            // added to the instance state.
            DeclScope::Local => {
                env.mark_local_instance(name.clone());
                fc.record_local_instance(env, name.clone());
            }
            DeclScope::Scoped => {
                let ns = fc.namespace_state().current_namespace().clone();
                fc.record_scoped_instance(name.clone(), ns.clone());
                env.get_ext_state_mut::<clean_olean::ScopedInstanceState>(
                    clean_olean::scoped_instance_idx(),
                )
                .scope_of
                .insert(name.clone(), ns.clone());
                if let Some(priority) = env.instance_priority(name) {
                    fc.instance_store_mut().add_scoped(env, &ns, name, priority);
                }
            }
            DeclScope::Default => {}
        },
        ElabResult::Multiple(results) => {
            for inner in results {
                record_instance_scopes(fc, env, inner);
            }
        }
        _ => {}
    }
}

/// Prepare fixed elaborator-session support before processing a declaration.
///
/// This does not elaborate or register `decl`. Callers attributing environment
/// additions to a source declaration can call this before taking their census;
/// the normal elaborator entry repeats the same idempotent preparation. Imports
/// retain their bridge-seeding suppression so imported definitions and instance
/// priorities are not pre-empted by session support.
pub fn prepare_declaration_environment(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) {
    if source_prelude::is_bare_module(env)
        || matches!(decl, clean_parser::SurfaceDecl::Prelude { .. })
    {
        return;
    }
    env.init_pprod().ok();
    // B101: seed the Lean-core `instHAdd`/`instHMul`/`instHSub` bridge
    // instances (kernel-checked; idempotent; skipped when the constants
    // already exist, e.g. via olean import) so user `Add`/`Mul`/`Sub`
    // instances are reachable through their operators.
    //
    // NOT while elaborating an `import`. This call runs once per declaration,
    // and an `import` IS a declaration handled by the elaborator afterward — so
    // seeding here pre-empted the very import that supplies Lean's genuine
    // `instHAdd`/`instHSub`/`instHMul`. The seed registers them at
    // `BRIDGE_INSTANCE_PRIORITY` (50, deliberately below the prelude's fused
    // monomorphic instances), and both of the import's repair paths are
    // first-writer-wins — the constant is skipped as a name collision and
    // `register_real_instance_entries` skips any name already in the registry —
    // so Lean's decoded priority 1000 was discarded and `a - b` elaborated
    // through Clean's invented `instHSubNat` instead of Lean's
    // `instHSub Nat instSubNat`. `HDiv`/`HMod`, which have no bridge here, kept
    // Lean's stack and were the only Nat operators that matched their own
    // imported lemmas.
    //
    // A rejected raw command can precede those imports too. It must not
    // install substitute bridges
    // before the real import gets a chance to supply its declarations.
    //
    // The seed stays self-healing: it is idempotent and runs again on the NEXT
    // declaration, so a file whose imports do not supply the bridge constants
    // still gets them before any term is elaborated. Files with no `import` are
    // unaffected.
    //
    // The seed runs with the ambient per-declaration budget SUSPENDED. It is
    // environment seeding — a fixed set of three repo-authored, kernel-checked
    // bridge definitions — not the declaration's own proof search, and
    // `clean check` already excludes the rest of environment construction by
    // arming the budget only after `Environment::with_prelude()`. Charging it
    // to whichever declaration happened to run first made the seed's own
    // `add_decl` fail with `DeclarationBudgetExhausted` under a tight
    // `--decl-budget`, which trips the seed's `debug_assert!` — an assertion
    // whose real subject is "did a co-tenant reshape the prelude classes",
    // not "was there fuel left". Measured 2026-08-27 at `--decl-budget 1`.
    if !matches!(
        decl,
        clean_parser::SurfaceDecl::Import { .. } | clean_parser::SurfaceDecl::RawDecl { .. }
    ) {
        clean_kernel::tc::with_declaration_budget_suspended(|| {
            hetero_bridge_seed::seed_hetero_bridges(env);
        });
    }
}

/// The session support [`prepare_declaration_environment`] installs before a
/// non-`import` declaration, installed up front.
///
/// A caller that compares what two elaborations of the same source ADD to
/// their environments (`clean project check` re-elaborating an import next to
/// its importer's other imports) calls this on the base first, so the
/// comparison sees the source's declarations and not whichever run happened
/// to install `PProd` or the bridge instances first. Idempotent.
pub fn prepare_session_environment(env: &mut clean_kernel::Environment) {
    if source_prelude::is_bare_module(env) {
        return;
    }
    env.init_pprod().ok();
    clean_kernel::tc::with_declaration_budget_suspended(|| {
        hetero_bridge_seed::seed_hetero_bridges(env);
    });
}

/// Track AA: like [`elaborate_decl_and_register_inner`] but installs an optional
/// auxiliary-arm source on the `ElabCtx` before elaborating `decl`. Used to fuse
/// a nested-mutual fold's primary def through `T.rec` with the sibling's arms
/// filling the auxiliary minors. `aux_source` is `(container_name, aux_arms,
/// member_signatures)`; `None` leaves the standard path unchanged.
fn elaborate_decl_and_register_inner_with_aux(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: Option<&mut FileContext>,
    aux_source: Option<(
        clean_parser::SurfaceName,
        Vec<clean_parser::SurfaceMatchArm>,
        Vec<(clean_parser::SurfaceName, clean_parser::SurfaceExpr)>,
    )>,
) -> Result<RegisteredElabResult, ElabError> {
    // Records on drop (every early return below included) when
    // `begin_decl_timing` armed this thread; inert otherwise.
    let _leaf_timer = decl_timing::LeafTimer::start(decl, file_ctx.as_deref());
    // Refills the automation work budget at the same OUTERMOST entry, and
    // names the budget in a failure its exhaustion caused (Lean's
    // `maxHeartbeats`, one window per command; see `decl_work_budget.rs`).
    let work_scope = decl_work_budget::LeafWorkScope::enter(decl);
    let result = elaborate_decl_and_register_leaf(env, decl, file_ctx, aux_source);
    // The declaration's error is the REPORTED one: only now is the
    // nearest-theorem "did you mean" scan worth its cost
    // (`ElabError::UnknownIdentDeferred`).
    work_scope.finish(result.map_err(|error| error.with_ident_suggestions(env)))
}

/// The body of [`elaborate_decl_and_register_inner_with_aux`], behind its
/// timing record and automation-budget scope. Never call this directly: the
/// scope is what refills the budget per declaration.
fn elaborate_decl_and_register_leaf(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    mut file_ctx: Option<&mut FileContext>,
    aux_source: Option<(
        clean_parser::SurfaceName,
        Vec<clean_parser::SurfaceMatchArm>,
        Vec<(clean_parser::SurfaceName, clean_parser::SurfaceExpr)>,
    )>,
) -> Result<RegisteredElabResult, ElabError> {
    let mismatched_world = file_ctx
        .as_deref()
        .map(FileContext::lean_world)
        .transpose()
        .map_err(|error| ElabError::SourceWorld(error.to_string()))?
        .filter(|world| {
            world.requires_genuine_init()
                && clean_olean::environment_world(env) != Some(world.tag())
        });
    if let Some(world) = mismatched_world {
        return Err(ElabError::SourceWorld(format!(
            "{world} source requires its own declared genuine Init environment"
        )));
    }
    if let clean_parser::SurfaceDecl::Import { paths, .. } = decl {
        if let Some(context) = file_ctx.as_deref() {
            for path in paths {
                if let Some(reason) = context.import_source_refusal(path.name()) {
                    return Err(ElabError::UnresolvedImport {
                        module: path.name().to_string(),
                        reason: format!("source elaboration refused: {reason}"),
                    });
                }
            }
        }
    }
    prepare_declaration_environment(env, decl);
    if matches!(
        decl,
        clean_parser::SurfaceDecl::Variable {
            visibility: Some(_),
            ..
        }
    ) {
        let world = match file_ctx.as_deref() {
            Some(context) => context
                .lean_world()
                .map_err(|error| ElabError::SourceWorld(error.to_string()))?,
            None => clean_kernel::lean_world::LeanWorld::ORACLE,
        };
        if !world.variable_visibility() {
            return Err(ElabError::SourceWorld(format!(
                "{world} does not admit public/private variable"
            )));
        }
    }
    // A scope that ended without an environment at hand (a `namespace … end`
    // leaves through `exit_local_scope`) only queued its `local simp` lemmas;
    // unregister them before this declaration can see them.
    if let Some(fc) = file_ctx.as_deref_mut() {
        fc.retire_local_attributes(env);
        fc.refresh_compiler_module(env);
        // Every `private` name already in the environment belongs to another
        // module (see `FileContext::foreign_private_decls`).
        fc.note_foreign_private_decls(env, false);
    }

    // Handle declare_aesop_rule_sets directly (before creating immutable borrow)
    if let clean_parser::SurfaceDecl::DeclareAesopRuleSets { names, .. } = decl {
        for name in names {
            let n = name.name().clone();
            env.declare_aesop_rule_set(n);
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Skipped,
            warning: None,
            hole_contexts: Vec::new(),
        });
    }

    // `codata` command: seeds the lazy Codata.* library on first use, then
    // generates + kernel-checks the M-type encoding (type, accessors,
    // corecursor, rfl laws). Transactional; loud v1 envelope.
    if let clean_parser::SurfaceDecl::Codata { .. } = decl {
        return codata_cmd::elab_codata_decl(env, decl);
    }

    // `codef` copattern definition: compiles to the codata's corecursor.
    if let clean_parser::SurfaceDecl::Codef { .. } = decl {
        return codata_cmd::elab_codef_decl(env, decl);
    }

    // Handle imports: initialize appropriate Mathlib stubs
    if let clean_parser::SurfaceDecl::Import { paths, .. } = decl {
        // `import Mathverse.…` addresses the Mathverse Library, not the `.olean`
        // search path. Split it out FIRST so an ordinary import is dispatched
        // byte-for-byte as before; the test is one string compare on the first
        // path segment (`mathverse_import::is_mathverse_path`).
        //
        // This is where a Mathverse constant becomes AMBIENT. `ElabCtx` holds an
        // immutable `&Environment` for its whole lifetime, so nothing inside term
        // elaboration can install a declaration — but this arm runs with
        // `&mut Environment` in hand, well before any `ElabCtx` is constructed.
        // Once the closure is resident, the elaborator's UNCHANGED name
        // resolution finds it, which is what makes `:= eq_or_ne x y` work without
        // a single hook in `elab_ident`.
        // The `any` probe keeps the ordinary case allocation-free: a file that
        // never mentions Mathverse pays one root-segment compare per import
        // path and reaches `process_imports*` with the very same slice it does
        // today.
        let names_mathverse = paths.iter().any(mathverse_import::is_mathverse_path);
        let module_paths: Vec<clean_parser::SurfaceName>;
        let paths: &[clean_parser::SurfaceName] = if names_mathverse {
            let (mv, rest): (Vec<_>, Vec<_>) = paths
                .iter()
                .cloned()
                .partition(mathverse_import::is_mathverse_path);
            mathverse_import::process_mathverse_imports(env, &mv)?;
            if rest.is_empty() {
                return Ok(RegisteredElabResult {
                    result: ElabResult::Skipped,
                    warning: None,
                    hole_contexts: Vec::new(),
                });
            }
            module_paths = rest;
            &module_paths
        } else {
            paths
        };
        let external_enabled = file_ctx
            .as_ref()
            .map(|fc| fc.external_import_search_enabled())
            .unwrap_or(true);
        if !external_enabled {
            // Clean-native authority check: skip Lake/.olean search and
            // initialize only Clean's built-in module preludes — plus the
            // caller's satisfied-from-source record, which this branch used to
            // drop on the floor (it built its own resolution over an EMPTY
            // set) while the `.olean` path honored it. Same resolution class,
            // same ordering (satisfied -> prelude -> refuse) as
            // `finish_unresolved`; see
            // `process_imports_clean_native_with_satisfied`.
            let policy = file_ctx
                .as_ref()
                .map_or_else(ImportPolicy::default, |fc| fc.import_policy());
            match file_ctx.as_ref() {
                Some(fc) => imports::process_imports_clean_native_with_provided(
                    env,
                    paths,
                    policy,
                    fc.imports_satisfied_without_search(),
                    fc.preloaded_artifact_imports(),
                )?,
                None => imports::process_imports_clean_native(env, paths, policy)?,
            }
        } else if let Some(fc) = file_ctx.as_deref_mut() {
            // Use Lake-discovered search paths if available, and thread the
            // file's persistent `import_visited` set, unresolved-import policy
            // and already-elaborated-from-source record through every import.
            // The `visited` memo is what keeps a Mathlib file's large
            // overlapping `.olean` closures read once rather than re-read per
            // top-level import (O(n²) → O(union)).
            imports::process_imports_for_file(env, paths, fc)?;
        } else {
            process_imports(env, paths)?;
        }
        // What the import brought in is another module's.
        if let Some(fc) = file_ctx.as_deref_mut() {
            fc.note_foreign_private_decls(env, true);
            for path in paths {
                fc.record_compiler_import(path.name());
            }
            // The import may just have restored transitive module metadata.
            fc.refresh_compiler_module(env);
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Skipped,
            warning: None,
            hole_contexts: Vec::new(),
        });
    }

    if let clean_parser::SurfaceDecl::SetOption {
        name, value, body, ..
    } = decl
    {
        // Drop-in: tolerate an UNKNOWN option NAME as a no-op (Lean registers
        // many options Clean does not model — genInjectivity, linter.*); the
        // wrapped/subsequent decls must still elaborate. A KNOWN option with a
        // wrongly-typed value stays a loud error. See
        // `validate_command_option_lenient`.
        let name = options_registry::surface_option_key(name)?;
        let _known = options_registry::validate_command_option_lenient(&name, value.as_deref())?;
        if let Some(inner_decl) = body {
            // Per-declaration scoping: `set_option ... in <decl>`
            // Save previous value, set the option, elaborate the body, then restore.
            let prev = env.get_option(&name).cloned();
            env.set_option(name.clone(), value.clone());
            // The file context's options are re-applied to the env before
            // every ordinary declaration, so a file-scope value (or a `-D`
            // override) would otherwise overwrite this one for the very
            // declaration it scopes. Install it there too, outside the
            // section rollback stack, and put the previous entry back after.
            let prev_file = file_ctx
                .as_deref_mut()
                .map(|fc| fc.replace_option_unscoped(&name, Some(value.clone())));
            let result =
                elaborate_decl_and_register_inner(env, inner_decl, file_ctx.as_deref_mut());
            if let (Some(fc), Some(prev_file)) = (file_ctx.as_deref_mut(), prev_file) {
                fc.replace_option_unscoped(&name, prev_file);
            }
            // Restore previous option state
            match prev {
                Some(old_value) => {
                    env.set_option(name.clone(), old_value);
                }
                None => {
                    env.remove_option(&name);
                }
            }
            return result;
        }
        // File-scope: option persists for all subsequent declarations
        env.set_option(name.clone(), value.clone());
        // Also persist in FileContext for section scoping
        if let Some(ref mut fc) = file_ctx {
            fc.set_option(name.clone(), value.clone());
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Skipped,
            warning: None,
            hole_contexts: Vec::new(),
        });
    }

    // `#guard_msgs (spec)? in cmd` (Lean 4.8.0 `elabGuardMsgs`): `cmd` runs
    // through this same elaborate-and-register pipeline, so whatever it
    // declares stays registered (Lean keeps a command's effects whatever its
    // messages) and a kernel refusal at registration is one of the messages
    // compared. A registration warning survives a match: a `#guard_msgs` that
    // expects Lean's `declaration uses 'sorry'` does not launder the sorry
    // out of the trust census.
    if let clean_parser::SurfaceDecl::GuardMsgs { doc, spec, cmd, .. } = decl {
        let (outcome, warning, hole_contexts) =
            match elaborate_decl_and_register_inner(env, cmd, file_ctx) {
                Ok(registered) => (
                    Ok(registered.result),
                    registered.warning,
                    registered.hole_contexts,
                ),
                Err(error) => (Err(error), None, Vec::new()),
            };
        let result = guard_msgs::conclude(doc.as_deref(), spec, outcome, warning.as_ref())?;
        return Ok(RegisteredElabResult {
            result,
            warning,
            hole_contexts,
        });
    }

    if let Some(result) = print_equations::try_elaborate(env, file_ctx.as_deref(), decl) {
        return result;
    }

    // Handle section blocks the same resilient, incremental way as namespace
    // blocks below, but with SECTION scope semantics.
    //
    // SOUNDNESS (#section-drops-all-but-last / namespace-ABORT lineage — see the
    // `elab_section` SOUNDNESS comment in infer/elaborate_decl.rs): the ElabCtx
    // path `elab_section` did `return Err(e)` on the FIRST failing inner decl,
    // discarding every good sibling. A real Mathlib module puts its ENTIRE file
    // body inside ONE unclosed `@[expose] public section` (no matching `end`), so
    // a single inner-decl failure collapsed the whole file to `decl_count == 1`.
    // `InferCtx.env` is `&Environment` (immutable), so `elab_section` physically
    // CANNOT register inners incrementally; therefore the fix lives HERE, where
    // `&mut env` is available, mirroring the namespace arm: each inner decl is
    // registered into `env` BEFORE the next (so later siblings resolve earlier
    // ones), a sibling failure becomes an explicit `ElabResult::Failed` leaf
    // (counted + reported, never silently swallowed) instead of aborting, and
    // every successful inner still flows through `add_decl`'s real kernel check.
    // No kernel/TCB code is touched. Matches Lean, which reports per-declaration
    // and continues.
    if let clean_parser::SurfaceDecl::Section {
        decls,
        noncomputable,
        ..
    } = decl
    {
        let _noncomputable = lean_compile_checks::NoncomputableSectionScope::enter(*noncomputable);
        let mut results = Vec::new();
        let mut hole_contexts = Vec::new();
        // As in the namespace arm: when there is no persistent FileContext, use a
        // throwaway one so section scoping / variable threading still works.
        let mut temp_fc;
        let fc_ref: &mut FileContext = match file_ctx {
            Some(ref mut fc) => fc,
            None => {
                temp_fc = FileContext::scratch();
                &mut temp_fc
            }
        };
        // A `section` scopes `variable` / `universe` / `set_option` (via
        // `enter_section` / `exit_section`) AND `open` aliases — a section-level
        // `open Foo` is in force WITHIN the section but rolled back at `end`
        // (Lean `elabEnd` pops the section scope). It differs from a namespace
        // only in NOT adding a name PREFIX (so no enter_namespace here). Push an
        // alias scope like the namespace arm so section-level `open`s don't leak
        // past `end` (open_export_e2e::test_open_in_section_does_not_leak).
        fc_ref.enter_section();
        fc_ref.namespace_state_mut().push_scope();
        // Scoped-notation activation frame: an `open` / `open scoped` inside
        // the section activates scoped notations WITHIN the section only.
        fc_ref.macro_ctx_mut().push_scoped_activation_frame();
        for inner in decls {
            // Thread section `variable` binders exactly as the top-level
            // section-marker path in `cmd_core` does: a `variable (x : T)` inner
            // mutates `fc_ref` via `add_variables`, and a later `def` / `theorem`
            // gets those binders prepended.
            //
            // A NESTED `section` inner must NOT be preprocessed here:
            // `preprocess_decl_with_context` calls `enter_section` AND the
            // recursive Section arm calls it again, so the inner section's
            // variable / option scope frame would be double-pushed and mismatched
            // on exit (leaking its `variable`s / `set_option`s to later siblings).
            // Nested sections self-manage their scope through this same arm, so
            // pass them through raw — mirroring how the namespace arm never
            // preprocesses its inners.
            //
            // The same holds for a nested NAMESPACE, and until 2026-09-11 this
            // guard did not say so: `preprocess_decl_with_context` pushes a
            // section frame for a `Namespace` too (`preprocess.rs`), the
            // namespace arm below pushed its own and popped only that one, so
            // the stray frame sat on top when THIS section ended and
            // `exit_section` popped the stray instead of the section's own
            // frame — every `variable` of a section containing a `namespace …
            // end` block survived its `end`. Measured: `section S; variable
            // (n : Nat); namespace A; end A; end S; def f : Nat := n` was
            // ACCEPTED, and in `Mathlib/Order/Basic.lean` the `section
            // Preorder`'s `[Preorder α]` (whose `namespace
            // Mathlib.Tactic.GCongr` block sits inside it) leaked into `section
            // PartialOrder`, where every `a ≤ b` then resolved to the stale
            // `Preorder` local while the lemmas it was proved from expected
            // the `PartialOrder` one — some twenty `Type mismatch … fvar#1 vs
            // PartialOrder.0.…` rows.
            let processed = if matches!(
                inner,
                clean_parser::SurfaceDecl::Section { .. }
                    | clean_parser::SurfaceDecl::Namespace { .. }
            ) {
                None
            } else {
                Some(preprocess_decl_with_context(inner, fc_ref))
            };
            let to_elab = processed.as_ref().unwrap_or(inner);
            // COLLECT per-inner outcomes instead of `?`-aborting on the first
            // failure. A sibling failure must NOT drop the good siblings.
            match elaborate_decl_and_register_inner(env, to_elab, Some(fc_ref)) {
                Ok(inner_result) => {
                    hole_contexts.extend(inner_result.hole_contexts);
                    if !matches!(inner_result.result, ElabResult::Skipped) {
                        results.push(inner_result.result);
                    }
                }
                Err(error) => {
                    // Report against the ORIGINAL `inner` (span-accurate), not the
                    // preprocessed clone — matches the namespace arm.
                    results.push(failed_inner_leaf(fc_ref, inner, error));
                }
            }
        }
        // Pop the alias scope (roll back section-level `open`s) and restore
        // section-scoped `set_option`s in BOTH `fc_ref` and the kernel env
        // (`apply_options_to_env` only ever adds — a section-scoped option would
        // otherwise leak past the section).
        fc_ref.macro_ctx_mut().pop_scoped_activation_frame();
        fc_ref.namespace_state_mut().pop_scope();
        fc_ref.exit_section_restoring_env_options(env);
        return Ok(RegisteredElabResult {
            result: ElabResult::Multiple(results),
            warning: None,
            hole_contexts,
        });
    }

    // Handle namespace blocks by processing each inner declaration individually
    // through the full elaborate-and-register pipeline (#3410). This ensures that
    // each declaration is registered in the environment before the next one is
    // elaborated, allowing cross-references between sibling declarations within
    // the same namespace (e.g., `def baz := bar` after `def bar := 0`).
    if let clean_parser::SurfaceDecl::Namespace { name, decls, .. } = decl {
        let mut results = Vec::new();
        let mut hole_contexts = Vec::new();
        // When file_ctx is None, create a temporary FileContext to carry the
        // namespace state through the inner declarations. This ensures
        // qualify_name() works even without a persistent file context.
        let mut temp_fc;
        let fc_ref: &mut FileContext = match file_ctx {
            Some(ref mut fc) => fc,
            None => {
                temp_fc = FileContext::scratch();
                &mut temp_fc
            }
        };
        let resolved = name.qualify_under(&clean_parser::SurfaceName::from_name(
            fc_ref.namespace_state().current_namespace().clone(),
        ));
        let resolved = resolved.into_name();
        // Entering `namespace A.B` activates the scoped entries of `A` and
        // `A.B` (Lean pushes one scope per component and activates each) —
        // the ones not already active are added to the instance state now.
        let entered_scopes = newly_entered_namespaces(fc_ref.namespace_state(), &resolved);
        let entered_chain = entered_namespace_chain(fc_ref.namespace_state(), &resolved);
        // Lean's `addScope` registers each namespace it enters
        // (`Environment.registerNamespace`), so `open` / `resolveNamespace`
        // find it even when nothing is declared directly under it.
        env.register_namespace(&resolved);
        fc_ref
            .namespace_state_mut()
            .enter_resolved_namespace(resolved);
        // The namespace block is an alias-scope boundary (Lean pushes a Scope
        // per `namespace`; `end` pops it and discards its `open` decls). An
        // `open` inside the block must not leak past `end Foo` (gap sweep B13);
        // `export` aliases are inserted scope-immune and survive.
        fc_ref.namespace_state_mut().push_scope();
        // A namespace block is also a `local`-attribute scope boundary (B99):
        // a `local instance` declared inside dies at `end Foo`, exactly as in
        // a section.
        fc_ref.enter_local_scope();
        // Scoped-notation activation frame: an `open` / `open scoped` inside
        // the block dies at `end Foo`. The block's own namespace needs no
        // explicit activation here — each inner declaration's `ElabCtx` syncs
        // the macro context's current namespace from the namespace state, and
        // the current namespace (with its ancestors) is implicitly active.
        fc_ref.macro_ctx_mut().push_scoped_activation_frame();
        // A `namespace` block scopes `variable` / `universe` / `set_option`
        // exactly as a `section` does (Lean pushes one Scope per namespace) —
        // Mathlib/Data/Subtype.lean declares `variable {p q : α → Prop}`
        // directly under `namespace Subtype` and every decl below uses them.
        // Mirror the Section arm: enter a section frame, thread each inner
        // through `preprocess_decl_with_context` so Variable inners accumulate
        // and later inners get the USED closure prepended, and restore on exit.
        fc_ref.enter_section();
        for ns in &entered_scopes {
            fc_ref.namespace_state_mut().activate_scoped(ns.clone());
        }
        fc_ref.activate_scoped_instances(env, &entered_chain);
        fc_ref.activate_scoped_csimp(env, &entered_chain)?;
        for inner in decls {
            // COLLECT per-inner outcomes instead of `?`-aborting on the first
            // failure (the namespace-ABORT bug). A sibling failure must NOT drop
            // the good siblings: each successful inner decl is still
            // individually elaborated and kernel-checked (and registered, so
            // later siblings can reference it), while each failure is recorded
            // as an explicit `ElabResult::Failed` leaf so it is still COUNTED and
            // REPORTED — never silently swallowed.
            //
            // Nested Section/Namespace inners self-manage their scope through
            // their own arms — preprocessing them here would double-push their
            // frame (see the Section arm's identical guard).
            let processed = if matches!(
                inner,
                clean_parser::SurfaceDecl::Section { .. }
                    | clean_parser::SurfaceDecl::Namespace { .. }
            ) {
                None
            } else {
                Some(preprocess_decl_with_context(inner, fc_ref))
            };
            let to_elab = processed.as_ref().unwrap_or(inner);
            match elaborate_decl_and_register_inner(env, to_elab, Some(fc_ref)) {
                Ok(inner_result) => {
                    // Preserve hole contexts from inner declarations so holes
                    // inside a namespace block remain visible to IDE surfaces.
                    hole_contexts.extend(inner_result.hole_contexts);
                    if !matches!(inner_result.result, ElabResult::Skipped) {
                        results.push(inner_result.result);
                    }
                }
                Err(error) => {
                    results.push(failed_inner_leaf(fc_ref, inner, error));
                }
            }
        }
        fc_ref.macro_ctx_mut().pop_scoped_activation_frame();
        fc_ref.exit_local_scope();
        fc_ref.retire_local_attributes(env);
        fc_ref.namespace_state_mut().pop_scope();
        fc_ref.namespace_state_mut().exit_namespace();
        fc_ref.exit_section_restoring_env_options(env);
        return Ok(RegisteredElabResult {
            result: ElabResult::Multiple(results),
            warning: None,
            hole_contexts,
        });
    }

    // Recursion-through-projection desugaring (Track H, task 1): a recursive
    // method that matches on a *projection* of its sole decreasing binder and
    // rebuilds a wrapper around the smaller sub-component for the recursive
    // call. Split into an auxiliary equation-form def recursing structurally on
    // the projected field's inductive (lowered via the already-proven `T.rec`
    // path) plus a thin wrapper, then elaborate and register both in order —
    // exactly like the namespace path registers sibling decls one by one so the
    // wrapper can reference the auxiliary. Returns `None` (leaving the decl
    // untouched) for anything outside the conservative sound envelope.
    if let Some(split) = proj_recursion::desugar_projection_recursion(decl) {
        let mut results = Vec::new();
        let mut hole_contexts = Vec::new();
        for sub in &split {
            let sub_result = elaborate_decl_and_register_inner(env, sub, file_ctx.as_deref_mut())?;
            hole_contexts.extend(sub_result.hole_contexts);
            if !matches!(sub_result.result, ElabResult::Skipped) {
                results.push(sub_result.result);
            }
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Multiple(results),
            warning: None,
            hole_contexts,
        });
    }

    // Mutual structural recursion via product packing (Track H, task 2): a
    // `mutual` block whose members all recurse structurally on a single shared
    // inductive argument is lowered into ONE packed structural-recursive
    // function (returning a tuple of the components' results) plus projection
    // wrappers — with NO `WellFounded.fix`, `sorry`, or faked termination
    // axiom. The packed function reuses the already-proven equation-form `T.rec`
    // lowering verbatim. Register the synthesized decls in order (pack first,
    // then wrappers) so each wrapper can reference the pack. Returns `None`
    // (deferring to the existing `elab_mutual` path) for anything outside the
    // conservative sound envelope.
    if let clean_parser::SurfaceDecl::Mutual { decls: members, .. } = decl {
        // A mutual block of codata declarations is the tag-index codata
        // surface (QPFTypes mutual answer) — handled by the codata command,
        // BEFORE the recursion desugar (which would silently no-op on it).
        if !members.is_empty()
            && members
                .iter()
                .all(|m| matches!(m, clean_parser::SurfaceDecl::Codata { .. }))
        {
            return codata_cmd::elab_mutual_codata(env, members);
        }
        // A mutual block of codef declarations: joint copattern definitions
        // into a mutual codata block.
        if !members.is_empty()
            && members
                .iter()
                .all(|m| matches!(m, clean_parser::SurfaceDecl::Codef { .. }))
        {
            return codata_cmd::elab_mutual_codef(env, members);
        }
        if let Some(split) = mutual_recursion_desugar::desugar_mutual_structural(members) {
            let mut results = Vec::new();
            let mut hole_contexts = Vec::new();
            for sub in &split {
                let sub_result =
                    elaborate_decl_and_register_inner(env, sub, file_ctx.as_deref_mut())?;
                hole_contexts.extend(sub_result.hole_contexts);
                if !matches!(sub_result.result, ElabResult::Skipped) {
                    results.push(sub_result.result);
                }
            }
            return Ok(RegisteredElabResult {
                result: ElabResult::Multiple(results),
                warning: None,
                hole_contexts,
            });
        }

        // Track AA: a nested-mutual fold `{ T.f : T -> R, T.g : C T -> R }` (the
        // members recurse on DIFFERENT types — the parent inductive `T` and its
        // nested container `C T` — so the product-packing path above declines).
        // Fuse the pair into ONE `T.rec` application: `T.f` is elaborated through
        // the genuine nested mutual recursor with `T.g`'s arms filling the
        // auxiliary `T._<C>` minors (a real fold, NOT a degenerate default), then
        // `T.g` is registered against the now-defined `T.f`. NO `WellFounded.fix`,
        // NO `sorry`, NO faked termination axiom — the kernel re-checks the
        // recursor application. Declines (`None`) for anything outside the
        // envelope, deferring to the existing `elab_mutual` path.
        if let Some(fold) = mutual_recursion_desugar::desugar_mutual_nested(members) {
            let mut results = Vec::new();
            let mut hole_contexts = Vec::new();

            // Primary def: fused through `T.rec` with the auxiliary-arm source.
            let aux_source = Some((
                fold.container_name.clone(),
                fold.aux_arms.clone(),
                fold.member_signatures.clone(),
            ));
            let prim_result = elaborate_decl_and_register_inner_with_aux(
                env,
                &fold.primary_def,
                file_ctx.as_deref_mut(),
                aux_source,
            )?;
            hole_contexts.extend(prim_result.hole_contexts);
            if !matches!(prim_result.result, ElabResult::Skipped) {
                results.push(prim_result.result);
            }

            // Secondary def: `T.g` references the now-registered `T.f`; it folds
            // over the surface container `C T` with `T.f` calls on elements,
            // lowered through the ordinary `C.rec` structural path.
            let sec_result = elaborate_decl_and_register_inner(
                env,
                &fold.secondary_def,
                file_ctx.as_deref_mut(),
            )?;
            hole_contexts.extend(sec_result.hole_contexts);
            if !matches!(sec_result.result, ElabResult::Skipped) {
                results.push(sec_result.result);
            }

            return Ok(RegisteredElabResult {
                result: ElabResult::Multiple(results),
                warning: None,
                hole_contexts,
            });
        }
    }

    // `open … in cmd` / `set_option … in cmd` is Lean's `section cmd₁ cmd₂
    // end` (`Lean/Elab/BuiltinCommand.lean` `expandInCmd`): the elaborator
    // scopes the names and options of the inner command itself, and the
    // INSTANCE STATE is scoped here — a pushed state, with the namespaces the
    // `open` activates activated in it, into which the inner command's
    // attributes are applied, popped afterwards. So a `local` entry or an
    // `-instance` inside it ends with it, while a global or scoped entry
    // reaches every state (measured on Lean 4.8.0: `open N in attribute
    // [-instance] ib` leaves `ib` in force after it).
    let in_scope = file_ctx
        .as_deref()
        .and_then(|fc| in_command_activations(env, fc, decl));
    match (in_scope, file_ctx.as_deref_mut()) {
        (Some(activated), Some(fc)) => {
            fc.enter_local_scope();
            fc.activate_scoped_instances(env, &activated);
            let result = fc.activate_scoped_csimp(env, &activated).and_then(|()| {
                elaborate_general_and_register(
                    env,
                    decl,
                    Some(&mut *fc),
                    aux_source,
                    mathverse_lazy::MATHVERSE_LAZY_LOAD_BUDGET,
                )
            });
            fc.exit_local_scope();
            fc.retire_local_attributes(env);
            result
        }
        _ => elaborate_general_and_register(
            env,
            decl,
            file_ctx,
            aux_source,
            mathverse_lazy::MATHVERSE_LAZY_LOAD_BUDGET,
        ),
    }
}

/// The namespaces whose scoped entries an `open … in` chain around `decl`
/// activates (`open N in open P in cmd`, `set_option … in cmd` among them),
/// or `None` when `decl` is not such a command.
fn in_command_activations(
    env: &clean_kernel::Environment,
    fc: &FileContext,
    decl: &clean_parser::SurfaceDecl,
) -> Option<Vec<clean_kernel::name::Name>> {
    let mut ns_state = fc.namespace_state().clone();
    let mut activated = Vec::new();
    let mut current = decl;
    let mut wrapped = false;
    loop {
        match current {
            clean_parser::SurfaceDecl::Open {
                paths,
                scoped,
                body: Some(inner),
                ..
            } => {
                wrapped = true;
                ns_state.push_scope();
                activated.extend(namespace::open_activations(
                    env,
                    paths,
                    *scoped,
                    &mut ns_state,
                ));
                current = inner;
            }
            clean_parser::SurfaceDecl::SetOption {
                body: Some(inner), ..
            } => {
                wrapped = true;
                current = inner;
            }
            _ => break,
        }
    }
    wrapped.then_some(activated)
}

/// Install the one library constant a failed elaboration asked for, then
/// re-elaborate the declaration from scratch.
///
/// Reached only from the `Err` arm of [`elaborate_general_and_register`], and
/// only when the error carries an [`ElabError::MathverseNameAvailable`]
/// request — which the elaborator mints only while a corpus is armed. Every
/// other failure is returned untouched, so a disarmed file cannot enter this
/// function at all.
///
/// # Why re-elaborate the whole declaration
///
/// `ElabCtx` borrows an elaboration-advice environment built from `env` for
/// its whole lifetime, so the constant cannot be installed mid-elaboration.
/// Nothing has been registered at this point (registration runs after a
/// successful elaboration) and the failed attempt has no environment side
/// effects, so the retry starts from a clean slate — it rebuilds the advice
/// environment, which then contains the installed constant.
///
/// # Termination
///
/// `budget` is the belt; the progress rule is the braces. A request is minted
/// only for a NOT-resident name, and `load_gated_constant` fails closed unless
/// the name ends up resident, so no name can be requested twice and each round
/// strictly grows the environment.
///
/// The retry stays inside the declaration's automation-budget window and any
/// `open … in` scope its caller entered: it is the same declaration, elaborated
/// again, not a new command.
fn mathverse_lazy_retry(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: Option<&mut FileContext>,
    aux_source: Option<(
        clean_parser::SurfaceName,
        Vec<clean_parser::SurfaceMatchArm>,
        Vec<(clean_parser::SurfaceName, clean_parser::SurfaceExpr)>,
    )>,
    budget: u8,
    error: ElabError,
) -> Result<RegisteredElabResult, ElabError> {
    let Some(name) = mathverse_lazy::requested_name(&error).map(ToString::to_string) else {
        return Err(error);
    };
    if budget == 0 {
        return Err(ElabError::MathverseImportFailed {
            name,
            detail: format!(
                "this declaration needed more than {} lazily-resolved Mathverse constants; \
                 import the extras explicitly with `import Mathverse.<Corpus>.<Constant>`",
                mathverse_lazy::MATHVERSE_LAZY_LOAD_BUDGET
            ),
        });
    }
    // THE GATE — the same `load_gated_constant` the eager
    // `import Mathverse.<Corpus>.<Constant>` arm calls. A trust refusal is
    // returned as itself, so a below-`Strict` name fails closed with its reason
    // instead of presenting as `Unknown identifier`.
    mathverse_import::lazy_load_armed(env, &name)?;
    elaborate_general_and_register(env, decl, file_ctx, aux_source, budget - 1)
}

/// Elaborate one ordinary declaration and register it with its attributes
/// (the general arm of [`elaborate_decl_and_register_inner_with_aux`]).
///
/// `budget` is the number of lazily-resolved Mathverse constants this
/// declaration may still install ([`mathverse_lazy_retry`]); every caller
/// outside the retry passes [`mathverse_lazy::MATHVERSE_LAZY_LOAD_BUDGET`].
fn elaborate_general_and_register(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    mut file_ctx: Option<&mut FileContext>,
    aux_source: Option<(
        clean_parser::SurfaceName,
        Vec<clean_parser::SurfaceMatchArm>,
        Vec<(clean_parser::SurfaceName, clean_parser::SurfaceExpr)>,
    )>,
    budget: u8,
) -> Result<RegisteredElabResult, ElabError> {
    // Apply file-level option overrides to the environment before elaboration
    // so that options set in earlier declarations (including section-scoped ones)
    // are visible during type checking and elaboration.
    if let Some(ref fc) = file_ctx {
        fc.apply_options_to_env(env);
    }

    // Untrusted elaboration advice retains the native execution/admission
    // vocabulary. Only structural references in its emitted kernel terms may
    // request those explicit stub fragments in the actual registration context.
    let advice = source_elaboration_advice(env)?;
    let mut ctx = ElabCtx::new(&advice);

    // Keep a copy of the auxiliary-arm source for a possible lazy-Mathverse
    // retry: `set_nested_mutual_aux_arms` consumes it, and the retry rebuilds
    // the `ElabCtx` from scratch. `None` — every declaration except a fused
    // nested-mutual fold — clones for free.
    let aux_retry = aux_source.clone();
    // Likewise the pending section-variable pruning request, which
    // `take_pending_section_prune` consumes below: a retry must elaborate under
    // the same request or it would keep every section variable. Copied only
    // while a corpus is armed (the same probe as `ElabCtx::mathverse_armed`) —
    // no other file can retry.
    let lazy_armed = env
        .get_option(mathverse_lazy::MATHVERSE_ARMED_OPTION)
        .is_some_and(Option::is_some);
    let mut section_prune_retry = None;

    // Track AA: install the fused nested-mutual fold's auxiliary-arm source (if
    // any) so the nested-recursor minor builder fills the auxiliary minors with
    // the sibling's real fold body.
    ctx.set_nested_mutual_aux_arms(aux_source);

    // Inject persisted namespace state and namespace prefix from FileContext
    if let Some(ref file_ctx) = file_ctx {
        if file_ctx.import_world().is_some() {
            ctx.set_source_world(
                file_ctx
                    .lean_world()
                    .map_err(|error| ElabError::SourceWorld(error.to_string()))?,
            );
        }
        ctx.set_namespace_state(file_ctx.namespace_state().clone());
        ctx.set_tactic_goal_capture(file_ctx.tactic_goal_capture());
        ctx.set_term_info_capture(file_ctx.term_info_capture());
        // U2 rung-4 explicitness channel: the file's `universe` names, so the
        // elaborator can tell a merged file-scope name from one the
        // declaration itself wrote after its name. `preprocess_decl_with_context`
        // folds the two into ONE vector; this is the only place both halves
        // are still separable. See `ElabCtx::set_decl_universe_params`.
        ctx.set_file_universe_params(file_ctx.current_universe_params().to_vec());
        // Instance scope state (B99): retired `local instance`s, `scoped
        // instance` namespaces, and the `@[default_instance]` table. All
        // empty unless the file actually used those forms.
        let instance_view = file_ctx.instance_view(env);
        ctx.set_instance_scope_state(
            instance_view.hidden(),
            file_ctx.scoped_instance_map().clone(),
            file_ctx.default_instance_entries(),
        );
        ctx.set_instance_view(instance_view);
        ctx.set_foreign_private_decls(file_ctx.foreign_private_decls());
    }
    // This file's `export` aliases so far; one this declaration makes is
    // registered in the environment below.
    let exports_before = file_ctx
        .as_deref()
        .map_or(0, |fc| fc.namespace_state().exports().len());
    // The namespaces whose scoped entries are active before this declaration;
    // an `open` it makes activates more (see below).
    let scopes_active_before = file_ctx
        .as_deref()
        .map(|fc| fc.namespace_state().activated_scopes().to_vec())
        .unwrap_or_default();

    if let Some(ref mut file_ctx) = file_ctx {
        let active_variable_bindings: Vec<(clean_parser::SurfaceName, u64)> = file_ctx
            .active_variable_bindings()
            .map(|(name, id)| (name.to_owned(), id))
            .collect();
        let mut macro_ctx = file_ctx.take_macro_ctx();
        macro_ctx.set_active_variable_bindings(active_variable_bindings);
        ctx.set_macro_ctx(macro_ctx);
        if let Some(tactic_registry) = file_ctx.take_tactic_registry() {
            ctx.set_tactic_registry(tactic_registry);
        }
        // `elab ... : term` registrations, persisted across declarations for the
        // same reason as the tactic registry above: ElabCtx is rebuilt per
        // declaration, so without this a registered term elaborator is dropped
        // before the next declaration can call it.
        ctx.set_user_term_elabs(file_ctx.take_user_term_elabs());
        ctx.imported_term_syntax = file_ctx.imported_term_syntax.clone();
        ctx.imported_runtime = file_ctx.imported_runtime.clone();
        // `preprocess_decl_with_context` could not scan THIS declaration, so
        // it prepended every section variable and asked for the unused ones
        // to be dropped from the elaborated term (`infer::section_prune`).
        if let Some(request) = file_ctx.take_pending_section_prune(decl.span()) {
            if lazy_armed {
                section_prune_retry = Some(request.clone());
            }
            ctx.set_section_prune_request(request);
        }
    }

    let result = ctx.elab_decl(decl);
    let section_prune = ctx.take_section_prune_outcome();

    if let Some(ref mut file_ctx) = file_ctx {
        file_ctx.replace_macro_ctx(ctx.take_macro_ctx());
        file_ctx.replace_tactic_registry(ctx.take_tactic_registry());
        file_ctx.replace_user_term_elabs(ctx.take_user_term_elabs());
    }

    // Lazy Mathverse resolution (`mathverse_lazy`). A failure that carries an
    // `ElabError::MathverseNameAvailable` request means the elaborator hit a
    // name the installed library HAS, the environment does NOT, and a corpus
    // was armed by `import Mathverse.<Corpus>`. Install it through the gate and
    // re-elaborate. Every other failure — and every failure at all in a file
    // that armed no corpus — takes main's path below unchanged.
    let result = match result {
        Err(error) if mathverse_lazy::requested_name(&error).is_some() => {
            // The failed attempt is discarded whole: its partial term info is
            // NOT recorded (the retry records its own, and the capture is
            // append-only, so recording both would duplicate every span).
            drop(ctx);
            if let (Some(fc), Some(request)) = (file_ctx.as_deref_mut(), section_prune_retry) {
                fc.set_pending_section_prune(decl.span(), Some(request));
            }
            return mathverse_lazy_retry(env, decl, file_ctx, aux_retry, budget, error);
        }
        result => result,
    };

    ctx.finish_term_info();
    let result = result?;

    // Snapshot the hole contexts (expected types + locals for user-written `_`
    // holes) before dropping ctx. Read-only: this only inspects metavariable
    // types for IDE display and never affects what is registered in the kernel.
    let hole_contexts = ctx.collect_hole_contexts();

    // Drain every collected attribute out of `ctx` BEFORE it is dropped: the
    // registrations below need `&mut env`, and `ctx` holds an immutable borrow
    // of it. See `decl_attributes::CtxAttributes`.
    let mut collected_attributes = decl_attributes::CtxAttributes::collect(&mut ctx, Some(&result));
    let simple_equation_sources = std::mem::take(&mut ctx.simple_equation_sources);

    // Extract namespace state back to FileContext before dropping ctx.
    let ns_state = ctx.take_namespace_state();
    drop(ctx); // Release immutable borrow of env

    // Persist namespace state to FileContext (kept borrowed: the tail below
    // also records instance scope state into it — B99).
    if let Some(fc) = file_ctx.as_deref_mut() {
        *fc.namespace_state_mut() = ns_state;
        // Lean's `export` adds its aliases to the ENVIRONMENT
        // (`aliasExtension`, `addAlias`): global, persistent and exported,
        // so an importer resolves them too (round-25 `export_root`: with a
        // root `x` and `export N (x)` in B, `x` is ambiguous in B's importer
        // as in B).
        let new_exports: Vec<(clean_kernel::Name, clean_kernel::Name)> = fc
            .namespace_state()
            .exports()
            .iter()
            .skip(exports_before)
            .map(|alias| (alias.short.clone(), alias.target.clone()))
            .collect();
        for (short, target) in new_exports {
            env.register_export_alias(short, target);
        }
        // An `open` / `open scoped` / `open … hiding` activated namespaces:
        // Lean adds their scoped instances to the state NOW, so each is the
        // newest of its tier (`P: namespace N; scoped instance i3 …`,
        // `Q: instance i4 …`, `M: import P; import Q; open N` takes i3).
        let activated = fc.namespace_state().newly_activated(&scopes_active_before);
        fc.activate_scoped_instances(env, &activated);
        fc.activate_scoped_csimp(env, &activated)?;
    }

    // A `deriving` class that failed is an error beside its type, not instead
    // of it (Lean adds the type before running any handler): the type
    // registers without it, and the failure is reported as its own failed
    // leaf of the returned result (`infer::deriving_log`).
    let (result, logged_deriving_failures) = infer::split_logged_deriving_failures(result);

    // First register the declaration itself (so attributes can reference it)
    let registered_names = source_family_authority::register_source_with_matchers(
        env,
        &result,
        std::mem::take(&mut collected_attributes.matchers),
    )?
    .registered_names;
    // ... and which run added it: an `attribute [implemented_by]` or
    // `attribute [extern]` command may name only the run's own declarations
    // (Lean's imported-module check, `crate::declared_here`), with or
    // without a file context.
    declared_here::record_declared_with_equation_sources(
        env,
        declared_here::ElabUnit::of(file_ctx.as_deref()),
        register::leaf_own_names(&result),
        &simple_equation_sources,
    );

    // Record `local` / `scoped` instance scope state into the FileContext
    // (B99). Must run AFTER successful registration (a rejected declaration
    // registers nothing, so it must not affect scope state) and reads the
    // just-persisted namespace state for the declaring namespace of `scoped`
    // instances.
    if let Some(fc) = file_ctx.as_deref_mut() {
        record_instance_scopes(fc, env, &result);
    }

    // Compute the warning after register_elab_result succeeds but before
    // returning, so we only report on actually-registered declarations.
    let warning = register::registration_warning_for_result(env, &result);

    // Register parameter names for named argument support (#1230) — of the
    // telescope as registered, so a pruned section binder takes its name with
    // it and named arguments still line up with the binders.
    let pruned_decl = section_prune
        .as_ref()
        .and_then(|outcome| decl_without_pruned_section_binders(decl, &result, outcome));
    register::register_param_names(env, pruned_decl.as_ref().unwrap_or(decl), &result);

    let documentation_world = match file_ctx.as_deref() {
        Some(context) => context
            .documentation_world()
            .map_err(|error| ElabError::SourceWorld(error.to_string()))?,
        None => clean_kernel::LeanWorld::ORACLE,
    };
    definition_attrs::record_definitions(env, file_ctx.as_deref(), decl, &result)?;
    // Now register attributes that reference the declaration.
    collected_attributes.apply(env, file_ctx.as_deref_mut())?;
    // Native family recursors travel as typed family/lowering records, not
    // payload definition bodies. Their importer reconstructs their signatures
    // and wrappers. Source-body contexts belong to the ordinary declarations
    // actually exported as constants; binding a reconstruction as an identical
    // source body would reject a genuine family artifact.
    let compilation_names: Vec<_> = registered_names
        .into_iter()
        .filter(|name| env.get_recursor(name).is_none())
        .collect();
    clean_kernel::env::csimp::record_compiled(env, compilation_names);

    // Every checker walks the leaves, so a logged failure is counted and
    // reported exactly like a failed member of a `namespace` block.
    let result = if logged_deriving_failures.is_empty() {
        result
    } else {
        let mut results = Vec::with_capacity(logged_deriving_failures.len() + 1);
        results.push(result);
        results.extend(logged_deriving_failures);
        ElabResult::Multiple(results)
    };

    let result = lean_compile_checks::diagnose_registered(
        env,
        file_ctx.as_deref(),
        result,
        module_driver::surface_decl_span(decl),
    );
    let result = documentation::diagnose_registered(env, result, decl, documentation_world);
    Ok(RegisteredElabResult {
        result,
        warning,
        hole_contexts,
    })
}

/// `decl` without the section binders `outcome` dropped from its elaborated
/// telescope — when the pruning ran on the very declaration `result`
/// registers and dropped something; `None` otherwise (the surface binders
/// then already match the registered telescope).
fn decl_without_pruned_section_binders(
    decl: &clean_parser::SurfaceDecl,
    result: &ElabResult,
    outcome: &infer::section_prune::SectionPruneOutcome,
) -> Option<clean_parser::SurfaceDecl> {
    let registered = match result.primary_leaf() {
        Some(
            ElabResult::Definition { name, .. }
            | ElabResult::Theorem { name, .. }
            | ElabResult::Axiom { name, .. },
        ) => name,
        _ => return None,
    };
    if *registered != outcome.decl || outcome.kept.iter().all(|kept| *kept) {
        return None;
    }
    let mut pruned = decl.clone();
    let (clean_parser::SurfaceDecl::Def { binders, .. }
    | clean_parser::SurfaceDecl::Theorem { binders, .. }
    | clean_parser::SurfaceDecl::Axiom { binders, .. }) = &mut pruned
    else {
        return None;
    };
    if binders.len() < outcome.kept.len() {
        return None;
    }
    let mut kept = outcome.kept.iter();
    binders.retain(|_| kept.next().copied().unwrap_or(true));
    Some(pruned)
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "derive_tests.rs"]
mod derive_tests;

#[cfg(test)]
#[path = "beq_recursive_tests.rs"]
mod beq_recursive_tests;

#[cfg(test)]
#[path = "let_tactic_body_visible_tests.rs"]
mod let_tactic_body_visible_tests;

#[cfg(test)]
#[path = "decidable_eq_fielded_tests.rs"]
mod decidable_eq_fielded_tests;

#[cfg(test)]
#[path = "decidable_eq_list_field_tests.rs"]
mod decidable_eq_list_field_tests;

#[cfg(test)]
#[path = "decidable_eq_trackt_tests.rs"]
mod decidable_eq_trackt_tests;

#[cfg(test)]
#[path = "deriving_trackp_tests.rs"]
mod deriving_trackp_tests;

#[cfg(test)]
#[path = "derive_ext_tests.rs"]
mod derive_ext_tests;

#[cfg(test)]
mod macro_hygiene_tests;

#[cfg(test)]
mod tests_state_t_issue_3418;

#[cfg(test)]
mod mutual_recursion_desugar_tests;

#[cfg(test)]
mod mutual_inductive_elab_tests;

#[cfg(test)]
mod codata_cmd_tests;
#[cfg(test)]
mod mutual_codef_call_typing_tests;

#[cfg(test)]
mod codata_declared_results_tests;

#[cfg(test)]
mod codata_variant_tests;

#[cfg(test)]
mod codata_variant_generate_tests;

#[cfg(test)]
mod nested_local_lift_tests;

#[cfg(test)]
mod proj_recursion_tests;

#[cfg(test)]
mod dot_notation_pi_receiver_tests;

#[cfg(test)]
#[path = "track_r_basic_tests.rs"]
mod track_r_basic_tests;

#[cfg(test)]
#[path = "track_t_fixfv2_tests.rs"]
mod track_t_fixfv2_tests;

#[cfg(test)]
#[path = "track_aa_nested_fold_tests.rs"]
mod track_aa_nested_fold_tests;

#[cfg(test)]
mod tests_issue_3435;

#[cfg(test)]
mod tests_issue_3517;

#[cfg(test)]
mod tests_cases_dependent_motive;

#[cfg(test)]
mod tests_result_only_implicit;

#[cfg(test)]
mod paren_field_group_tests;

#[cfg(test)]
mod tests_issue_3527;

#[cfg(test)]
mod tests_issue_3534;

#[cfg(test)]
mod wave0_tests;

#[cfg(test)]
mod tests_close_fvars_seq_focus;

#[cfg(test)]
mod tests_mathbot_task_tactics;

#[cfg(test)]
mod tests_instance_candidate_hygiene;

#[cfg(test)]
mod tests_instance_open_carrier_postpone;

#[cfg(test)]
mod tests_lean_fidelity_shapes;

#[cfg(test)]
mod tests_expected_type_shape;

#[cfg(test)]
mod tests_expected_type_shape_review;
#[cfg(test)]
mod tests_instance_binders;

#[cfg(test)]
mod tests_lean_core_exports;

#[cfg(test)]
mod tests_cases_nested_block;
#[cfg(test)]
mod tests_do_lane_r5_lift;
#[cfg(test)]
mod tests_do_lane_r5_match;
#[cfg(test)]
mod tests_except_universes;
#[cfg(test)]
mod tests_review_r6;

#[cfg(test)]
mod tests_assumption_unify_congr_rfl;
#[cfg(test)]
mod tests_by_block_head_shapes;
#[cfg(test)]
mod tests_congr_n;
#[cfg(test)]
mod tests_decl_modifier_attrs;
#[cfg(test)]
mod tests_deferred_by_block;
#[cfg(test)]
mod tests_dot_ident_head;
#[cfg(test)]
mod tests_double_quoted_name;
#[cfg(test)]
mod tests_explicit_app_partial;
#[cfg(test)]
mod tests_function_dot_receiver_slot;
#[cfg(test)]
mod tests_grind_ite_split;
#[cfg(test)]
mod tests_implicit_lambda_term;

#[cfg(test)]
mod tests_grind_attr_params;
#[cfg(test)]
mod tests_grind_ext_heq;
#[cfg(test)]
mod tests_grind_preprocess;
#[cfg(test)]
mod tests_grind_refutation;
#[cfg(test)]
mod tests_inhabit_parent_instances;
#[cfg(test)]
mod tests_inst_hole;
#[cfg(test)]
mod tests_instance_universe_finalize;
#[cfg(test)]
mod tests_leading_dot_deferred;
#[cfg(test)]
mod tests_pattern_field_head_beta;
#[cfg(test)]
mod tests_pattern_lambda_interleave;
#[cfg(test)]
mod tests_refine_hole_under_lambda;
#[cfg(test)]
mod tests_rw_term_metas;
#[cfg(test)]
mod tests_section_scope_e2e;
#[cfg(test)]
mod tests_simp_dite_collapse;
#[cfg(test)]
mod tests_simp_prop_hyp;
#[cfg(test)]
mod tests_struct_named_defaults;
#[cfg(test)]
mod tests_structure_field_local_instances;
#[cfg(test)]
mod tests_subst_dependent;
#[cfg(test)]
mod tests_support_imported_core;
#[cfg(test)]
mod tests_tactic_surface_fixes;
#[cfg(test)]
mod tests_tactic_term_no_expected;

#[cfg(test)]
mod tests_unify_eta_meta;

#[cfg(test)]
mod tests_cases_imported_cases_on;

#[cfg(test)]
mod namespace_3410_tests;

#[cfg(test)]
mod lean4_corpus_tests;

#[cfg(test)]
#[path = "attr_macro_ext_tests.rs"]
mod attr_macro_ext_tests;

#[cfg(test)]
mod attr_scoping_tests;

#[cfg(test)]
mod attribute_wiring_tests;

#[cfg(test)]
mod calc_generic_relation_tests;

#[cfg(test)]
mod calc_trans_class_tests;

#[cfg(test)]
mod structure_cmd_tests;

#[cfg(test)]
#[path = "structure_cmd_ext_tests.rs"]
mod structure_cmd_ext_tests;

#[cfg(test)]
mod do_notation_tests;

#[cfg(test)]
mod do_notation_desugar_tests;

#[cfg(test)]
mod do_notation_ext_tests;

#[cfg(test)]
#[path = "do_notation_desugar_ext_tests.rs"]
mod do_notation_desugar_ext_tests;

#[cfg(test)]
mod string_interpolation_tests;

#[cfg(test)]
mod lean4_compat_tests;

#[cfg(test)]
#[path = "lean4_compat_ext2_tests.rs"]
mod lean4_compat_ext2_tests;

#[cfg(test)]
mod auto_bound_tests;

#[cfg(test)]
mod auto_bound_ext_tests;

// NOTE: auto_param_ext_tests / lean4_compat_ext_tests / notation_ext_tests /
// where_clause_ext_tests are orphaned files (never declared here). They are also
// STALE — re-enabling them surfaces ~101 compile errors against removed/renamed
// APIs (e.g. `process_where_clause_ext`, `WhereClauseExtError`), so they are
// obsolete dead tests, not restorable coverage. Tracked for deletion/rewrite
// (org rule: tests must PASS, FAIL, or be DELETED) rather than silently orphaned.

// elab_hooks_tests declared in elab_hooks.rs (not here — see #3285)

#[cfg(test)]
#[path = "elab_hooks_ext_tests.rs"]
mod elab_hooks_ext_tests;

#[cfg(test)]
mod diamond_resolution_tests;

#[cfg(test)]
#[path = "diamond_resolution_ext_tests.rs"]
mod diamond_resolution_ext_tests;

#[cfg(test)]
mod macro_hygiene_ext_tests;

#[cfg(test)]
#[path = "macro_hygiene_ext2_tests.rs"]
mod macro_hygiene_ext2_tests;

#[cfg(test)]
#[path = "macro_hygiene_ext3_tests.rs"]
mod macro_hygiene_ext3_tests;

#[cfg(test)]
mod macro_hygiene_impl_tests;

#[cfg(test)]
mod env_snapshot_tests;

#[cfg(test)]
#[path = "env_snapshot_ext_tests.rs"]
mod env_snapshot_ext_tests;

// tc_outparam_tests declared in tc_outparam.rs (not here — see #3285)

#[cfg(test)]
mod tc_synthesis_ext_tests;

#[cfg(test)]
#[path = "tc_synthesis_ext2_tests.rs"]
mod tc_synthesis_ext2_tests;

#[cfg(test)]
mod structure_extend_ext_tests;

#[cfg(test)]
mod structure_inherit_tests;

#[cfg(test)]
mod structure_inherit_ext_tests;

#[cfg(test)]
#[path = "structure_inherit_ext2_tests.rs"]
mod structure_inherit_ext2_tests;

#[cfg(test)]
mod implicit_args_tests;

#[cfg(test)]
#[path = "implicit_args_ext_tests.rs"]
mod implicit_args_ext_tests;

// mutual_inductive_tests declared in mutual_inductive.rs (not here — see #3285)

#[cfg(test)]
#[path = "mutual_inductive_ext_tests.rs"]
mod mutual_inductive_ext_tests;

#[cfg(test)]
mod ffi_extern_tests;

#[cfg(test)]
#[path = "ffi_extern_ext_tests.rs"]
mod ffi_extern_ext_tests;

#[cfg(test)]
mod io_monad_tests;

#[cfg(test)]
#[path = "io_monad_ext_tests.rs"]
mod io_monad_ext_tests;

#[cfg(test)]
#[path = "io_monad_ext2_tests.rs"]
mod io_monad_ext2_tests;

#[cfg(test)]
mod let_rec_tests;

#[cfg(test)]
#[path = "let_rec_ext_tests.rs"]
mod let_rec_ext_tests;

#[cfg(test)]
#[path = "let_rec_ext2_tests.rs"]
mod let_rec_ext2_tests;

#[cfg(test)]
mod notation_priority_tests;

#[cfg(test)]
#[path = "notation_priority_ext_tests.rs"]
mod notation_priority_ext_tests;

// coercion_tests declared in coercion.rs (not here — see #3285)

#[cfg(test)]
#[path = "coercion_ext_tests.rs"]
mod coercion_ext_tests;

// where_desugar_ext_tests declared in where_desugar_ext.rs (not here — see #3285)

#[cfg(test)]
mod mutual_decl_ext_tests;

#[cfg(test)]
#[path = "mutual_decl_ext2_tests.rs"]
mod mutual_decl_ext2_tests;

#[cfg(test)]
#[path = "mutual_decl_ext3_tests.rs"]
mod mutual_decl_ext3_tests;

#[cfg(test)]
#[path = "section_scope_ext_tests.rs"]
mod section_scope_ext_tests;

#[cfg(test)]
mod section_variable_ext_tests;

#[cfg(test)]
mod namespace_ext_tests;

#[cfg(test)]
mod attribute_ext_tests;

#[cfg(test)]
#[path = "attribute_ext2_tests.rs"]
mod attribute_ext2_tests;

#[cfg(test)]
#[path = "attribute_registry_ext_tests.rs"]
mod attribute_registry_ext_tests;

#[cfg(test)]
#[path = "derive_ext2_tests.rs"]
mod derive_ext2_tests;

#[cfg(test)]
#[path = "derive_handlers_ext_tests.rs"]
mod derive_handlers_ext_tests;

#[cfg(test)]
mod derive_ext_handlers_tests;

#[cfg(test)]
#[path = "derive_ext_handlers2_tests.rs"]
mod derive_ext_handlers2_tests;

#[cfg(test)]
#[path = "instances_ext_tests.rs"]
mod instances_ext_tests;

#[cfg(test)]
mod instance_priority_ext_tests;

#[cfg(test)]
#[path = "instance_priority_ext2_tests.rs"]
mod instance_priority_ext2_tests;

#[cfg(test)]
mod tactic_interp_ext_tests;

#[cfg(test)]
mod notation_scope_ext_tests;

#[cfg(test)]
#[path = "options_registry_ext_tests.rs"]
mod options_registry_ext_tests;

#[cfg(test)]
#[path = "notation_scope_ext2_tests.rs"]
mod notation_scope_ext2_tests;

#[cfg(test)]
mod string_interp_ext_tests;

#[cfg(test)]
mod pattern_match_ext_tests;

#[cfg(test)]
mod inductive_ext_tests;

#[cfg(test)]
mod inductive_ext2_tests;

#[cfg(test)]
#[path = "commands_ext_tests.rs"]
mod commands_ext_tests;

#[cfg(test)]
#[path = "eval_cmd_ext_tests.rs"]
mod eval_cmd_ext_tests;

#[cfg(test)]
#[path = "macro_cmd_ext_tests.rs"]
mod macro_cmd_ext_tests;

#[cfg(test)]
#[path = "dep_graph_ext_tests.rs"]
mod dep_graph_ext_tests;

#[cfg(test)]
#[path = "dep_graph_ext2_tests.rs"]
mod dep_graph_ext2_tests;

#[cfg(test)]
#[path = "name_resolution_ext_tests.rs"]
mod name_resolution_ext_tests;

#[cfg(test)]
#[path = "name_resolution_ext2_tests.rs"]
mod name_resolution_ext2_tests;

#[cfg(test)]
#[path = "unify_ext_tests.rs"]
mod unify_ext_tests;

#[cfg(test)]
#[path = "command_elab_ext_tests.rs"]
mod command_elab_ext_tests;

#[cfg(test)]
#[path = "command_elab_registry_ext_tests.rs"]
mod command_elab_registry_ext_tests;

#[cfg(test)]
#[path = "meta_ext_tests.rs"]
mod meta_ext_tests;

#[cfg(test)]
#[path = "section_variable_ext2_tests.rs"]
mod section_variable_ext2_tests;

#[cfg(test)]
#[path = "preprocess_ext_tests.rs"]
mod preprocess_ext_tests;

#[cfg(test)]
#[path = "register_ext_tests.rs"]
mod register_ext_tests;

#[cfg(test)]
mod tests_elab_surface_fixes;
#[cfg(test)]
mod tests_imported_named_args;
#[cfg(test)]
mod tests_imported_tactic_macro;
#[cfg(test)]
#[path = "variable_cmd_ext_tests.rs"]
mod variable_cmd_ext_tests;

#[cfg(test)]
mod tests_section_variable_inclusion;

#[cfg(test)]
mod tests_section_variable_inclusion_ext;

#[cfg(test)]
mod tests_section_variable_inclusion_inst;

#[cfg(test)]
mod tests_section_variable_inclusion_adv;

#[cfg(test)]
mod tests_section_variable_inclusion_adv2;

#[cfg(test)]
mod tests_bullet_app_boundary;

#[cfg(test)]
mod tests_ascription_without_type;

#[cfg(test)]
mod tests_anon_ctor_one_field;

#[cfg(test)]
mod tests_split_at_source;

#[cfg(test)]
mod tests_anon_ctor_subobject_as_written;

#[cfg(test)]
mod tests_local_simp_attribute;

#[cfg(test)]
mod tests_nested_ctor_dependent_motive;

#[cfg(test)]
mod tests_single_equation_lowering;

#[cfg(test)]
mod tests_rcases_target_equation;

#[cfg(test)]
mod tests_tactic_syntax_forms;

#[cfg(test)]
mod tests_instance_eqns_attribute_in;

#[cfg(test)]
mod tests_rcases_typed_pattern;

#[cfg(test)]
mod tests_simp_lemma_levels;

#[cfg(test)]
mod tests_simp_prop_lemmas;

#[cfg(test)]
mod tests_simp_instance_args;

#[cfg(test)]
mod tests_rintro_rfl;

#[cfg(test)]
mod tests_simp_at_false;

#[cfg(test)]
mod tests_simp_lemma_rows;

#[cfg(test)]
mod tests_simp_lemma_adversarial;

#[cfg(test)]
mod tests_simp_lemma_sources;

#[cfg(test)]
mod tests_pkg4_unifier;

#[cfg(test)]
mod tests_pkg4_level_occurs;

#[cfg(test)]
mod tests_pkg4_proof_meta;

#[cfg(test)]
mod tests_pkg4_review;

#[cfg(test)]
mod tests_fin_ofnat_signature_drift;

#[cfg(test)]
mod tests_elab_app_binders;

#[cfg(test)]
#[path = "tests_instance_alias_keying.rs"]
mod tests_instance_alias_keying;

#[cfg(test)]
#[path = "tests_attribute_target_scope.rs"]
mod tests_attribute_target_scope;
#[cfg(test)]
#[path = "tests_implemented_by_scope.rs"]
mod tests_implemented_by_scope;
#[cfg(test)]
#[path = "tests_implemented_by_validation.rs"]
mod tests_implemented_by_validation;
#[cfg(test)]
#[path = "tests_instance_state_scoping.rs"]
mod tests_instance_state_scoping;
#[cfg(test)]
#[path = "tests_private_defs.rs"]
mod tests_private_defs;
#[cfg(test)]
#[path = "tests_private_families.rs"]
mod tests_private_families;
#[cfg(test)]
#[path = "tests_private_names.rs"]
mod tests_private_names;
#[cfg(test)]
#[path = "tests_private_print.rs"]
mod tests_private_print;
#[cfg(test)]
#[path = "tests_reduce_command.rs"]
mod tests_reduce_command;
#[cfg(test)]
#[path = "tests_term_name_resolution.rs"]
mod tests_term_name_resolution;

#[cfg(test)]
#[path = "tests_alias_goal_opening.rs"]
mod tests_alias_goal_opening;

#[cfg(test)]
#[path = "tests_alias_class_locals.rs"]
mod tests_alias_class_locals;

#[cfg(test)]
#[path = "tests_alias_iff_unreduced.rs"]
mod tests_alias_iff_unreduced;

#[cfg(test)]
#[path = "tests_structure_level_params.rs"]
mod tests_structure_level_params;

#[cfg(test)]
#[path = "tests_level_zero_succ_refuted.rs"]
mod tests_level_zero_succ_refuted;

#[cfg(test)]
#[path = "tests_sort_star_rigid.rs"]
mod tests_sort_star_rigid;

#[cfg(test)]
#[path = "tests_meta_assign_folded_spelling.rs"]
mod tests_meta_assign_folded_spelling;

#[cfg(test)]
#[path = "tests_classical_scope_simp.rs"]
mod tests_classical_scope_simp;

#[cfg(test)]
#[path = "tests_local_instance_ambiguity.rs"]
mod tests_local_instance_ambiguity;

#[cfg(test)]
#[path = "tests_imported_max_level_instance.rs"]
mod tests_imported_max_level_instance;

#[cfg(test)]
#[path = "tests_local_instance_ambiguity_adversarial.rs"]
mod tests_local_instance_ambiguity_adversarial;

#[cfg(test)]
#[path = "tests_w3c_review_adversarial.rs"]
mod tests_w3c_review_adversarial;

#[cfg(test)]
#[path = "tests_decl_timing.rs"]
mod tests_decl_timing;

#[cfg(test)]
mod tests_source_placeholder_authority;

#[cfg(test)]
mod tests_compiler_extern_carriers;
