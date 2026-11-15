// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G36 / ledger class (106): an unannotated `let` whose value is a
//! leading-dot constructor is postponed until the body pins its type. Every
//! source was run through the pinned Lean 4.8.0 binary (2026-10-08); each
//! declaration asserted refused here is refused there too.

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DeclVerdict, DriverOptions, EnvironmentSetup, ModuleReport,
    VerdictKind,
};
use std::path::Path;

fn check_module(source: &str) -> ModuleReport {
    let _lock = module_elaboration_lock();
    let path = Path::new("LetPostponeFixture.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("check environment");
    let _budget = DeclBudgetScope::enter(0);
    let parsed = parse_module(path, source).1.expect("fixture parses");
    let mut file_ctx = module_file_context(path);
    elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut file_ctx,
        DriverOptions::default(),
        &mut (),
    )
}

fn verdict<'r>(report: &'r ModuleReport, name: &str) -> &'r DeclVerdict {
    report
        .verdicts
        .iter()
        .find(|v| v.name == name)
        .unwrap_or_else(|| panic!("no verdict for `{name}` in {:#?}", report.verdicts))
}

fn assert_passed(report: &ModuleReport, name: &str) {
    let v = verdict(report, name);
    assert_eq!(v.kind, VerdictKind::Passed, "`{name}` must pass: {v:#?}");
}

fn refused_detail(report: &ModuleReport, name: &str) -> String {
    let v = verdict(report, name);
    assert_ne!(
        v.kind,
        VerdictKind::Passed,
        "`{name}` must be refused: {v:#?}"
    );
    v.detail.clone().unwrap_or_default()
}

/// The pending numeral's consistency check happens after its body, outside
/// tactic dispatch. It must reject a value assigned to an opaque local or a
/// different literal, while retaining the literal identity positive.
#[test]
fn postponed_numeral_consistency_refusal_is_not_a_tactic_failure() {
    use clean_kernel::{Environment, Expr, Name};
    use clean_parser::SurfaceName;

    for (pending_numeral, assigned_local, numeral) in [
        (7_u64, false, 7),
        (7, true, 7),
        (7, false, 8),
        (8, false, 7),
    ] {
        let env = Environment::with_prelude();
        let mut ctx = super::ElabCtx::new(&env);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let source_seven = ctx.elab_nat_literal_with_expected(&7_u64.into(), &nat);
        let local = ctx.fresh_fvar();
        ctx.push_local_let_with_fvar(
            SurfaceName::generated_path("n"),
            local,
            nat.clone(),
            crate::tactic::have_value(source_seven),
        );
        let pending = ctx.postpone_open_numeral(&pending_numeral.into(), &nat);
        let assigned = if assigned_local {
            Expr::fvar(local)
        } else {
            // Ground source numerals retain their OfNat dictionary application.
            // A raw kernel Nat literal only prints the same; it is not the
            // structural source expression this consistency check compares.
            ctx.elab_nat_literal_with_expected(&numeral.into(), &nat)
        };
        assert!(ctx.try_unify(&pending, &assigned));
        let result = ctx.drain_postponed_numerals(0);
        if !assigned_local && numeral == pending_numeral {
            result.expect("the actual same numeral passes");
            assert!(ctx.lean_order_ground_refusal.is_none());
        } else {
            let error = result.expect_err("a different assigned value cannot impersonate seven");
            let crate::ElabError::TypeMismatch { expected, actual } = &error else {
                panic!("the late consistency check is not an attributed tactic error: {error:?}");
            };
            assert_eq!(expected, &pending_numeral.to_string());
            assert_eq!(actual, &crate::error_render::term(&assigned));
            assert!(matches!(
                ctx.lean_order_ground_refusal,
                Some(crate::ElabError::TypeMismatch { .. })
            ));
        }
    }
}

const V3: &str = "inductive V where\n  | nullPtr : V\n  | ptr : Nat → V\n  | fat : Nat → V → V\n";

/// The trust-ir shape (triage F): the dot constructors sit in `if` branches
/// of an unannotated `let`, and `some (.fat d m)` pins the type. A true
/// statement about the result checks.
#[test]
fn test_let_postpone_dot_ctor_in_if_branches_passes() {
    let src = format!(
        "{V3}def dec (a d : Nat) : Option V :=\n  \
         let m := if a == 0 then .nullPtr else .ptr a\n  some (.fat d m)\n\
         theorem dec_val : dec 0 5 = some (.fat 5 .nullPtr) := rfl\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "dec");
    assert_passed(&report, "dec_val");
}

/// Negative twin: the branch taken at `a = 0` is `.nullPtr`, so `.ptr 0` is
/// refused (Lean: `type mismatch`).
#[test]
fn test_let_postpone_wrong_branch_value_refused() {
    let src = format!(
        "{V3}def dec (a d : Nat) : Option V :=\n  \
         let m := if a == 0 then .nullPtr else .ptr a\n  some (.fat d m)\n\
         theorem dec_wrong : dec 0 5 = some (.fat 5 (.ptr 0)) := rfl\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "dec");
    refused_detail(&report, "dec_wrong");
}

/// A bare `.nullPtr` value, and a constructor name two inductives share
/// (`V.ptr`, `W.ptr`): only the body's `Option V` decides it, as in Lean.
#[test]
fn test_let_postpone_bare_and_ambiguous_dot_ctor_pass() {
    let src = format!(
        "{V3}inductive W where\n  | ptr : Nat → W\n\
         def decb (a : Nat) : Option V :=\n  let m := .nullPtr\n  some m\n\
         def deca (a : Nat) : Option V :=\n  let m := .ptr a\n  some m\n\
         theorem deca_val : deca 3 = some (.ptr 3) := rfl\n\
         theorem deca_wrong : deca 3 = some (.ptr 4) := rfl\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "decb");
    assert_passed(&report, "deca");
    assert_passed(&report, "deca_val");
    refused_detail(&report, "deca_wrong");
}

/// The body never pins the type: Lean refuses ("invalid dotted identifier
/// notation"), and Clean reports the eager attempt's error.
#[test]
fn test_let_postpone_unpinned_type_refused() {
    let src = format!("{V3}def u (a : Nat) : Nat :=\n  let m := .nullPtr\n  a\n");
    let report = check_module(&src);
    let detail = refused_detail(&report, "u");
    assert!(
        detail.contains("nullPtr"),
        "refused at the dot constructor: {detail}"
    );
}

/// The body pins a type with no such constructor (`Nat`): Lean refuses
/// (`Nat.nullPtr` unknown), and so does Clean.
#[test]
fn test_let_postpone_pinned_to_wrong_type_refused() {
    let src = format!("{V3}def w (a : Nat) : Option Nat :=\n  let m := .nullPtr\n  some m\n");
    let report = check_module(&src);
    let detail = refused_detail(&report, "w");
    assert!(
        detail.contains("nullPtr"),
        "refused at the dot constructor: {detail}"
    );
}
