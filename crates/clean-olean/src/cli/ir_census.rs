// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean ir-census` — decode every module's compiled IR and print the
//! per-module census the pinned-Lean oracle prints, in the same format.
//!
//! The output is the diff surface of `scripts/ir_census_diff.py`:
//!
//! ```text
//! MOD <module> fdecl_olean=… extern_olean=… fdecl_ir=… extern_ir=… extern_attr=… \
//!     implemented_by=… regular_init=… regular_init_ir=… builtin_init=…
//! TOTAL modules=… <the same nine sums>
//! DECL <module> <olean|ir> <name>      (--print-decl / --print-module)
//! <Lean's IR.Decl rendering>
//! ENDDECL
//! ATTR <module> <kind> <decl> <data>   (--print-attrs; also DECLEXT, DECLSORRY)
//! ```
//!
//! Every row comes from a FULL decode of that module's IR: a declaration that
//! does not decode fails the command (exit non-zero, the module named on
//! stderr) instead of being skipped, and no `TOTAL` line is printed then, so a
//! partial census can never diff clean.

use std::path::PathBuf;

use clap::Args;

use super::OleanCliError;
use crate::import::legacy_module_name;
use crate::lean_ir::census::{run_census, CensusRequest};

/// Arguments for `clean olean ir-census`.
///
/// Bare `pub` like its siblings: the `OleanCommands::IrCensus` variant is
/// `pub`, and a `pub(crate)` payload trips `private_interfaces` under
/// `clippy -D warnings`.
#[derive(Debug, Args)]
pub struct IrCensusArgs {
    /// Module(s) to census (`Init.Prelude`, `Mathlib.Tactic.Common`).
    #[arg(value_name = "MODULE", required = true)]
    pub modules: Vec<String>,

    /// Census the transitive import closure of the modules, not only the
    /// modules themselves.
    #[arg(long)]
    pub closure: bool,

    /// `.olean` search paths, in `LEAN_PATH` order. As in Lean's `findOLean`,
    /// the first entry that holds a module's root package (`Init/`,
    /// `Mathlib/`, …) decides: a module missing from that entry is refused,
    /// never looked up in a later one. When empty, the crate's
    /// [`default_search_paths`](crate::default_search_paths) are used.
    #[arg(long = "search-path", value_name = "PATH")]
    pub search_paths: Vec<PathBuf>,

    /// Also print every IR declaration of the census whose `Name.toString`
    /// spelling is NAME, rendered as Lean's `IR.Decl` formatter renders it.
    /// Repeatable.
    #[arg(long = "print-decl", value_name = "NAME")]
    pub print_decls: Vec<String>,

    /// Also print EVERY IR declaration of this module (both levels), as
    /// `--print-decl` does; `*` means every module of the census. Repeatable.
    #[arg(long = "print-module", value_name = "MODULE")]
    pub print_modules: Vec<String>,

    /// Also print every `extern` / `implemented_by` / `init` /
    /// `builtin_init` attribute entry, every `extern` declaration's
    /// `ExternAttrData` and every `DeclInfo.sorryDep?`, one line each
    /// (`ATTR` / `DECLEXT` / `DECLSORRY`, the oracle's `IR_CENSUS_ATTRS=1`).
    #[arg(long = "print-attrs")]
    pub print_attrs: bool,

    /// Also print the construct profile of the decoded IR (`PROFILE
    /// <key>=<count>` on stderr): how often each IR constructor, flag and
    /// type occurs. Not part of the diffed census text.
    #[arg(long)]
    pub profile: bool,

    /// Modules decoded in parallel (at least 1).
    #[arg(long, default_value_t = 4)]
    pub jobs: usize,
}

/// Dispatch `clean olean ir-census`: print the census, or refuse it when any
/// module failed to decode (the `MOD` rows that did decode are still printed;
/// the `TOTAL` row and every `DECL` / `ATTR` line are not).
pub(super) fn dispatch_ir_census(args: IrCensusArgs) -> Result<(), OleanCliError> {
    if args.jobs == 0 {
        return Err(OleanCliError::InvalidJobs);
    }
    let args_profile = args.profile;
    let modules = args
        .modules
        .iter()
        .map(|m| legacy_module_name(m))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| OleanCliError::IrCensus(e.to_string()))?;
    let search_paths = if args.search_paths.is_empty() {
        crate::default_search_paths()
    } else {
        args.search_paths
    };
    let report = run_census(&CensusRequest {
        modules,
        closure: args.closure,
        search_paths,
        print_decls: args.print_decls,
        print_modules: args.print_modules,
        print_attrs: args.print_attrs,
        jobs: args.jobs,
    })
    .map_err(|e| OleanCliError::IrCensus(e.to_string()))?;
    print!("{}", report.stdout);
    for failure in &report.failures {
        eprintln!("ir-census: FAILED {failure}");
    }
    eprintln!("{}", report.summary);
    if args_profile {
        eprint!("{}", report.profile.render());
    }
    if !report.failures.is_empty() {
        return Err(OleanCliError::IrCensusFailed {
            failed: report.failures.len(),
            total: report.modules,
        });
    }
    Ok(())
}
