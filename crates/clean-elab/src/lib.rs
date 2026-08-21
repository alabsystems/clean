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
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod auto_param_ext;
pub mod cert;
pub mod check_cmd;
#[cfg(feature = "cli")]
pub mod cli;
pub(crate) mod coercion;
pub(crate) mod decl_attributes;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod coercion_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod coercion_ext2;
pub mod command_elab;
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
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
pub(crate) mod codata_cmd;
pub mod codata_seed;
pub(crate) mod coinductive_surface;
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod ffi_extern_ext;
pub(crate) mod file_context;
pub mod header;
pub(crate) mod hetero_bridge_seed;
pub(crate) mod imports;
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
pub(crate) mod instance_priority;
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
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod io_monad_ext;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod io_monad_ext2;
pub(crate) mod level_params;
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
pub(crate) mod print_cmd;
pub(crate) mod proj_recursion;
pub mod register;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod register_ext;
pub(crate) mod registration_warning;
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
#[path = "error_recovery_ext_tests.rs"]
mod error_recovery_ext_tests;

#[cfg(test)]
#[path = "error_recovery_ext2_tests.rs"]
mod error_recovery_ext2_tests;

#[cfg(test)]
#[path = "info_tree_tests.rs"]
mod info_tree_tests;

#[cfg(test)]
#[path = "info_tree_ext_tests.rs"]
mod info_tree_ext_tests;

use clean_kernel::Name;

// Re-export extracted types at crate root for backwards compatibility
use derive_handlers::register_user_derive_handler;
pub use error::{ElabElabError, ElabError};
pub use file_context::FileContext;
pub use header::{elaborate_decl_headers_with_context, DeclHeader};
pub use imports::{
    lake_import_search_paths_for_file, nearest_lake_root_for_file, olean_available_for_module,
    process_import_batch_with_search_paths, process_imports, resolve_intra_project_import,
};
pub use preprocess::preprocess_decl_with_context;
#[cfg(not(test))]
use register::register_elab_result;
#[cfg(test)]
pub(crate) use register::register_elab_result;
pub use register::{kernel_check_failure_count, register_aesop_rule};

// =============================================================================
// Stack overflow protection for deep recursion
// =============================================================================

/// Minimum stack space to reserve before recursive calls (32 KB).
const MIN_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack size to grow to when running low (1 MB).
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
pub use infer::{
    ClassRegistration, CommandOutput, DerivedInstance, ElabCtx, ElabResult, HoleContext,
};
pub use instances::{ClassInfo, InstanceInfo, InstanceTable, DEFAULT_PRIORITY};
pub use macro_integration::{
    expand_surface_macros, surface_to_syntax, syntax_to_surface, MacroCtx, MacroExpansionError,
};
pub use meta::{FreshMVarQ, MetaCtx, SynthInstanceQResult, TransparencyMode};
pub use print_cmd::{print_declaration, DeclKind, PrintResult as EnhancedPrintResult};
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
pub fn elaborate(
    env: &clean_kernel::Environment,
    surface: &clean_parser::SurfaceExpr,
) -> Result<clean_kernel::Expr, ElabError> {
    let mut ctx = ElabCtx::new(env);
    ctx.elaborate(surface)
}

/// Elaborate a surface declaration to a kernel declaration result
///
/// # REQUIRES
/// - Same as `elaborate`
///
/// # ENSURES
/// - On success, returns `ElabResult` variant matching declaration type
/// - Declaration name is extracted and validated
pub fn elaborate_decl(
    env: &clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> Result<ElabResult, ElabError> {
    let mut ctx = ElabCtx::new(env);
    ctx.elab_decl(decl)
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
    let mut ctx = ElabCtx::new(env);
    let result = ctx.elab_decl(decl);
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
/// - On success, declaration is added to `env`
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
    let short = preprocess_ext::decl_name(inner).unwrap_or("");
    let ns = fc.namespace_state().current_namespace();
    let qualified = if short.is_empty() {
        ns.to_string()
    } else if ns.is_anon() {
        short.to_string()
    } else {
        format!("{ns}.{short}")
    };
    ElabResult::Failed {
        name: qualified,
        decl: Box::new(inner.clone()),
        error: Box::new(error),
    }
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
pub(crate) fn record_instance_scopes(fc: &mut FileContext, result: &ElabResult) {
    use clean_parser::DeclScope;
    match result {
        ElabResult::Instance {
            name, modifiers, ..
        } => match modifiers.scope {
            DeclScope::Local => fc.record_local_instance(name.clone()),
            DeclScope::Scoped => {
                let ns = fc.namespace_state().current_namespace().clone();
                fc.record_scoped_instance(name.clone(), ns);
            }
            DeclScope::Default => {}
        },
        ElabResult::Multiple(results) => {
            for inner in results {
                record_instance_scopes(fc, inner);
            }
        }
        _ => {}
    }
}

/// Track AA: like [`elaborate_decl_and_register_inner`] but installs an optional
/// auxiliary-arm source on the `ElabCtx` before elaborating `decl`. Used to fuse
/// a nested-mutual fold's primary def through `T.rec` with the sibling's arms
/// filling the auxiliary minors. `aux_source` is `(container_short, aux_arms,
/// member_names)`; `None` leaves the standard path byte-for-byte unchanged.
fn elaborate_decl_and_register_inner_with_aux(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    mut file_ctx: Option<&mut FileContext>,
    aux_source: Option<(String, Vec<clean_parser::SurfaceMatchArm>, Vec<String>)>,
) -> Result<RegisteredElabResult, ElabError> {
    env.init_pprod().ok();
    // B101: seed the Lean-core `instHAdd`/`instHMul`/`instHSub` bridge
    // instances (kernel-checked; idempotent; skipped when the constants
    // already exist, e.g. via olean import) so user `Add`/`Mul`/`Sub`
    // instances are reachable through their operators.
    //
    // NOT while elaborating an `import`. This call runs once per declaration,
    // and an `import` IS a declaration handled further down this function — so
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
    // The seed stays self-healing: it is idempotent and runs again on the NEXT
    // declaration, so a file whose imports do not supply the bridge constants
    // still gets them before any term is elaborated. Files with no `import` are
    // unaffected.
    if !matches!(decl, clean_parser::SurfaceDecl::Import { .. }) {
        hetero_bridge_seed::seed_hetero_bridges(env);
    }

    // Handle declare_aesop_rule_sets directly (before creating immutable borrow)
    if let clean_parser::SurfaceDecl::DeclareAesopRuleSets { names, .. } = decl {
        for name in names {
            let n = Name::from_string(name);
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
        let external_enabled = file_ctx
            .as_ref()
            .map(|fc| fc.external_import_search_enabled())
            .unwrap_or(true);
        if !external_enabled {
            // Clean-native authority check: skip Lake/.olean search and
            // initialize only Clean's built-in module preludes.
            imports::process_imports_clean_native(env, paths)?;
        } else if let Some(fc) = file_ctx.as_deref_mut() {
            // Use Lake-discovered search paths if available. Thread the file's
            // persistent `import_visited` set through every import so a Mathlib
            // file's large overlapping `.olean` closures are read once, not
            // re-read per top-level import (O(n²) → O(union)). Clone the search
            // paths (a file has few — just PathBufs) into a local so the
            // immutable `import_search_paths()` borrow does not conflict with
            // the mutable `import_visited_mut()` borrow of the same `fc`.
            let local_paths = fc.import_search_paths().to_vec();
            imports::process_imports_with_search_paths_shared(
                env,
                paths,
                &local_paths,
                fc.import_visited_mut(),
            )?;
        } else {
            process_imports(env, paths)?;
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
        let _known = options_registry::validate_command_option_lenient(name, value.as_deref())?;
        if let Some(inner_decl) = body {
            // Per-declaration scoping: `set_option ... in <decl>`
            // Save previous value, set the option, elaborate the body, then restore.
            let prev = env.get_option(name).cloned();
            env.set_option(name.clone(), value.clone());
            let result = elaborate_decl_and_register_inner(env, inner_decl, file_ctx);
            // Restore previous option state
            match prev {
                Some(old_value) => {
                    env.set_option(name.clone(), old_value);
                }
                None => {
                    env.remove_option(name);
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
    if let clean_parser::SurfaceDecl::Section { decls, .. } = decl {
        let mut results = Vec::new();
        let mut hole_contexts = Vec::new();
        // As in the namespace arm: when there is no persistent FileContext, use a
        // throwaway one so section scoping / variable threading still works.
        let mut temp_fc;
        let fc_ref: &mut FileContext = match file_ctx {
            Some(ref mut fc) => fc,
            None => {
                temp_fc = FileContext::new();
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
            let processed = if matches!(inner, clean_parser::SurfaceDecl::Section { .. }) {
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
                temp_fc = FileContext::new();
                &mut temp_fc
            }
        };
        fc_ref
            .namespace_state_mut()
            .enter_namespace(Name::from_string(name));
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
                fold.container_short.clone(),
                fold.aux_arms.clone(),
                fold.member_names.clone(),
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

    // Apply file-level option overrides to the environment before elaboration
    // so that options set in earlier declarations (including section-scoped ones)
    // are visible during type checking and elaboration.
    if let Some(ref fc) = file_ctx {
        fc.apply_options_to_env(env);
    }

    let mut ctx = ElabCtx::new(env);

    // Track AA: install the fused nested-mutual fold's auxiliary-arm source (if
    // any) so the nested-recursor minor builder fills the auxiliary minors with
    // the sibling's real fold body.
    ctx.set_nested_mutual_aux_arms(aux_source);

    // Inject persisted namespace state and namespace prefix from FileContext
    if let Some(ref file_ctx) = file_ctx {
        ctx.set_namespace_state(file_ctx.namespace_state().clone());
        // Instance scope state (B99): retired `local instance`s, `scoped
        // instance` namespaces, and the `@[default_instance]` table. All
        // empty unless the file actually used those forms.
        ctx.set_instance_scope_state(
            file_ctx.dead_local_instances().clone(),
            file_ctx.scoped_instance_map().clone(),
            file_ctx.default_instance_entries(),
        );
    }

    if let Some(ref mut file_ctx) = file_ctx {
        let active_variable_bindings: Vec<(String, u64)> = file_ctx
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
    }

    let result = ctx.elab_decl(decl);

    if let Some(ref mut file_ctx) = file_ctx {
        file_ctx.replace_macro_ctx(ctx.take_macro_ctx());
        file_ctx.replace_tactic_registry(ctx.take_tactic_registry());
        file_ctx.replace_user_term_elabs(ctx.take_user_term_elabs());
    }

    let result = result?;

    // Snapshot the hole contexts (expected types + locals for user-written `_`
    // holes) before dropping ctx. Read-only: this only inspects metavariable
    // types for IDE display and never affects what is registered in the kernel.
    let hole_contexts = ctx.collect_hole_contexts();

    // Drain every collected attribute out of `ctx` BEFORE it is dropped: the
    // registrations below need `&mut env`, and `ctx` holds an immutable borrow
    // of it. See `decl_attributes::CtxAttributes`.
    let collected_attributes = decl_attributes::CtxAttributes::collect(&mut ctx);

    // Extract namespace state back to FileContext before dropping ctx.
    let ns_state = ctx.take_namespace_state();
    drop(ctx); // Release immutable borrow of env

    // Persist namespace state to FileContext (kept borrowed: the tail below
    // also records instance scope state into it — B99).
    if let Some(fc) = file_ctx.as_deref_mut() {
        *fc.namespace_state_mut() = ns_state;
    }

    // First register the declaration itself (so attributes can reference it)
    register_elab_result(env, &result)?;

    // Record `local` / `scoped` instance scope state into the FileContext
    // (B99). Must run AFTER successful registration (a rejected declaration
    // registers nothing, so it must not affect scope state) and reads the
    // just-persisted namespace state for the declaring namespace of `scoped`
    // instances.
    if let Some(fc) = file_ctx.as_deref_mut() {
        record_instance_scopes(fc, &result);
    }

    // Compute the warning after register_elab_result succeeds but before
    // returning, so we only report on actually-registered declarations.
    let warning = register::registration_warning_for_result(env, &result);

    // Register parameter names for named argument support (#1230)
    register::register_param_names(env, decl);

    // Now register attributes that reference the declaration.
    collected_attributes.apply(env, file_ctx)?;

    Ok(RegisteredElabResult {
        result,
        warning,
        hole_contexts,
    })
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
mod tests_issue_3527;

#[cfg(test)]
mod tests_issue_3534;

#[cfg(test)]
mod wave0_tests;

#[cfg(test)]
mod tests_close_fvars_seq_focus;

#[cfg(test)]
mod tests_instance_candidate_hygiene;

#[cfg(test)]
mod tests_lean_fidelity_shapes;

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
#[path = "variable_cmd_ext_tests.rs"]
mod variable_cmd_ext_tests;
