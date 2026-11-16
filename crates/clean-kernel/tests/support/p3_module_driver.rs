// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! P3's `elab.module_driver.*` sites: the planted pair handed to `clean
//! check`'s per-declaration loop as SOURCE (`clean_elab::module_driver::
//! elaborate_decls`, with the Lean front door on, as `clean check` runs it, on
//! the builtin prelude). Included by `tests/patched_kernel_control.rs` with
//! `#[path]`; see that file's docs.

use std::path::Path;

use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DriverOptions, EnvironmentSetup, ModuleReport, VerdictKind,
};
use clean_kernel::{DeclarationVerification, Environment, Name};

use crate::control::{self, by, Observed};

pub const PLANTED_SOURCE: &str = "theorem p3_planted_src : False := Nat.zero\n";
pub const LET_REC_SOURCE: &str =
    "theorem p3_letrec_src : False :=\n  let rec go : False := Nat.zero\n  go\n";
pub const HONEST_LET_REC_SOURCE: &str =
    "theorem p3_letrec_honest_src : True :=\n  let rec go : True := True.intro\n  go\n";
pub const PLANTED_SOURCE_REFUSAL: &str = "p3_planted_src=ElaborationFailed";
pub const LET_REC_REFUSAL: &str = "p3_letrec_src=ElaborationFailed";
pub const LET_REC_RESIDENT: &str =
    "every verdict Passed; p3_letrec_src and p3_letrec_src.go resident, DeclarationVerification::FullKernelCheck";

/// `clean check`'s per-declaration loop on `source` (the Lean front door on,
/// the builtin prelude): its verdicts and the environment it registered into.
fn drive_module(source: &str) -> (ModuleReport, Environment) {
    let _lock = module_elaboration_lock();
    let path = Path::new("P3Planted.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("check environment");
    let _budget = DeclBudgetScope::enter(0);
    let parsed = parse_module(path, source).1.expect("source parses");
    let mut file_ctx = module_file_context(path);
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut file_ctx,
        DriverOptions {
            lean_front_door: true,
            ..DriverOptions::default()
        },
        &mut (),
    );
    (report, env)
}

/// `name=Kind` for every verdict, in order.
fn verdict_kinds(report: &ModuleReport) -> String {
    report
        .verdicts
        .iter()
        .map(|verdict| format!("{}={:?}", verdict.name, verdict.kind))
        .collect::<Vec<_>>()
        .join(",")
}

/// Every message the verdicts carry, for the row log and the refusal check.
fn verdict_messages(report: &ModuleReport) -> String {
    report
        .verdicts
        .iter()
        .filter_map(|verdict| verdict.detail.as_deref())
        .collect::<Vec<_>>()
        .join(" | ")
}

/// Whether the driver passed every declaration and left each of `names`
/// resident with the full-check stamp.
fn passed_with_resident(report: &ModuleReport, env: &Environment, names: &[&str]) -> bool {
    !report.verdicts.is_empty()
        && report
            .verdicts
            .iter()
            .all(|verdict| verdict.kind == VerdictKind::Passed)
        && names.iter().all(|name| {
            env.declaration_verification(&Name::from_string(name))
                == Some(DeclarationVerification::FullKernelCheck)
        })
}

pub fn probe_module_driver_source() -> Observed {
    const SITE: &str = "elab.module_driver.source";
    let (report, env) = drive_module(PLANTED_SOURCE);
    let messages = verdict_messages(&report);
    println!("P3_DETAIL\t{SITE}\t{}\t{messages}", verdict_kinds(&report));
    if passed_with_resident(&report, &env, &["p3_planted_src"]) {
        return Observed::minted(SITE, "every verdict Passed; p3_planted_src resident");
    }
    let elaborator_mismatch = control::is_planted_mismatch(&messages)
        || (messages.contains("not definitionally equal")
            && messages.contains("False")
            && messages.contains("Nat"));
    assert!(
        elaborator_mismatch,
        "{SITE}: unexpected refusal {}: {messages}",
        verdict_kinds(&report)
    );
    Observed::refused(SITE, by::SAME_KERNEL_OTHER_ENTRY, verdict_kinds(&report))
}

pub fn probe_module_driver_let_rec() -> Observed {
    const SITE: &str = "elab.module_driver.let_rec_source";
    let (honest, honest_env) = drive_module(HONEST_LET_REC_SOURCE);
    assert!(
        passed_with_resident(
            &honest,
            &honest_env,
            &["p3_letrec_honest_src", "p3_letrec_honest_src.go"]
        ),
        "{SITE}: the honest let rec source must pass with its helper resident: {} {}",
        verdict_kinds(&honest),
        verdict_messages(&honest)
    );
    let (report, env) = drive_module(LET_REC_SOURCE);
    let messages = verdict_messages(&report);
    println!("P3_DETAIL\t{SITE}\t{}\t{messages}", verdict_kinds(&report));
    if passed_with_resident(&report, &env, &["p3_letrec_src", "p3_letrec_src.go"]) {
        return Observed::minted(SITE, LET_REC_RESIDENT);
    }
    assert!(
        control::is_planted_mismatch(&messages),
        "{SITE}: unexpected refusal {}: {messages}",
        verdict_kinds(&report)
    );
    assert!(
        env.get_const(&Name::from_string("p3_letrec_src.go"))
            .is_none(),
        "{SITE}: a refused helper must not be resident"
    );
    Observed::refused(SITE, by::CLEAN_KERNEL, verdict_kinds(&report))
}
