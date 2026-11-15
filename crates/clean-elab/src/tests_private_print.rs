// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How `#print` and `#check` show a private declaration (G21 brick B4,
//! `designs/2026-10-08-private-name-mangling.md`). Lean 4.8.0's `mkHeader`
//! (`Print.lean:38-40`) prints `private <kind> <user name>`, the delaborator
//! shows user-facing names unless `pp.privateNames` is set, and a private
//! family's constructors keep their kernel names. Every expectation was
//! measured on pinned Lean 4.8.0 (2026-10-09, `PrivPrint4.lean`):
//!
//! ```text
//! private theorem Foo.pt : Foo.pd 1 = 2 :=
//! rfl
//! private def Foo.pd : Nat → Nat :=
//! fun n => n + 1
//! private axiom Foo.pax : True
//! private inductive Foo.Col : Type
//! number of parameters: 0
//! constructors:
//! _private.PrivPrint4.0.Foo.Col.a : Foo.Col
//! ```
//!
//! Clean's value rendering (`rfl` vs Clean's elaborated term) is not Lean's;
//! the header line is pinned on its own.

use crate::test_support::file_verdicts::{run_named_file, run_named_file_messages};
use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, CommandOutput,
    ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};

const MODULE: &str = "PrivPrint4";

const SOURCE: &str = "namespace Foo
private def pd (n : Nat) : Nat := n + 1
private theorem pt : pd 1 = 2 := rfl
private axiom pax : True
private inductive Col | a | b
theorem pub_t : True := True.intro
end Foo
";

/// The text of every top-level `#print` / `#check` of `src`, in order, in a
/// module named [`MODULE`].
fn command_outputs(src: &str) -> Vec<String> {
    let decls = clean_parser::parse_file(src).unwrap_or_else(|e| panic!("must parse: {e:?}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    file_ctx.set_main_module(Name::from_string(MODULE));
    let mut out = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .unwrap_or_else(|e| panic!("every command must elaborate: {e:?}"));
        match result {
            ElabResult::Command(CommandOutput::Print(print)) => out.push(print.output),
            ElabResult::Command(CommandOutput::Check(check)) => out.push(check.to_string()),
            _ => {}
        }
    }
    out
}

fn first_line(text: &str) -> &str {
    text.lines().next().unwrap_or_default()
}

#[test]
fn test_print_private_axiom_matches_lean_exactly() {
    let src = format!(
        "{SOURCE}/-- info: private axiom Foo.pax : True -/\n#guard_msgs in\n#print Foo.pax\n"
    );
    let verdicts = run_named_file(&src, MODULE);
    assert!(verdicts.iter().all(|(_, v)| v.is_ok()), "{verdicts:?}");
}

#[test]
fn test_print_private_header_lines_are_leans() {
    let outputs = command_outputs(&format!(
        "{SOURCE}open Foo\n#print pt\n#print Foo.pd\n#print Foo.Col\n#print Foo.pub_t\n"
    ));
    assert_eq!(outputs.len(), 4, "{outputs:#?}");
    // `#print pt` under `open Foo` still names the full user name.
    assert_eq!(
        first_line(&outputs[0]),
        "private theorem Foo.pt : Foo.pd 1 = 2 :=",
        "{outputs:#?}"
    );
    assert!(
        first_line(&outputs[1]).starts_with("private def Foo.pd : "),
        "{outputs:#?}"
    );
    assert_eq!(
        first_line(&outputs[2]),
        "private inductive Foo.Col : Type",
        "{outputs:#?}"
    );
    assert!(
        outputs[2].contains("_private.PrivPrint4.0.Foo.Col.a"),
        "constructors keep their kernel names: {outputs:#?}"
    );
    // Control: a public declaration has no modifier.
    assert!(
        first_line(&outputs[3]).starts_with("theorem Foo.pub_t : True"),
        "{outputs:#?}"
    );
    // No mangled name leaks into a header or a rendered type.
    for output in &outputs[..2] {
        assert!(!output.contains("_private"), "{outputs:#?}");
    }
}

/// `pp.privateNames true` shows the kernel names in expressions; the
/// `#print` header keeps Lean's `private` modifier and user name either way.
#[test]
fn test_pp_private_names_shows_kernel_names() {
    let outputs = command_outputs(&format!(
        "{SOURCE}#check Foo.pd 1\nset_option pp.privateNames true\n#check Foo.pd 1\n#print Foo.pt\n"
    ));
    assert_eq!(outputs.len(), 3, "{outputs:#?}");
    assert_eq!(outputs[0], "Foo.pd 1 : Nat", "{outputs:#?}");
    assert!(
        outputs[1].starts_with("_private.PrivPrint4.0.Foo.pd 1 : Nat"),
        "{outputs:#?}"
    );
    assert!(
        outputs[2].starts_with("private theorem Foo.pt : _private.PrivPrint4.0.Foo.pd 1 = 2"),
        "{outputs:#?}"
    );
}

/// An unsolved goal shows a private constant by its user-facing name (Lean
/// 4.8.0: `unsolved goals\n⊢ Foo.pd 1 = 3`).
#[test]
fn test_unsolved_goal_shows_the_user_name() {
    let src = format!("{SOURCE}theorem t_goal : Foo.pd 1 = 3 := by\n  skip\n");
    let verdicts = run_named_file(&src, MODULE);
    let (_, verdict) = verdicts
        .iter()
        .find(|(name, _)| name.ends_with("t_goal"))
        .unwrap_or_else(|| panic!("t_goal must have a verdict: {verdicts:?}"));
    let error = verdict.as_ref().expect_err("the goal is left unsolved");
    assert!(error.contains("⊢ Foo.pd 1 = 3"), "{error}");
    assert!(!error.contains("_private"), "{error}");
}

/// Diagnostics print a private constant by its user name, as Lean 4.8.0's
/// messages do under the default `pp.privateNames false` (G21 review probe
/// `Pkg/M1`: Lean prints `pd 1 = 3` in the `decide`, kernel type-mismatch
/// and `rw` messages). The B1–B4 build printed `_private.Pkg.M1.0.pd 1 = 3`
/// in each.
///
/// The verdicts are the MESSAGES (`Display`, what `clean check` prints). The
/// test used to read each error's `Debug` structure, which no user reads and
/// which keeps raw kernel renderings in several variants (the body-type
/// gate's `TypeMismatch`, `RewriteNoMatch`'s fields); in the round-3/4 merge
/// suite it failed on `TypeMismatch { expected: "_private.Pkg.M1.0.pd 1 = 3",
/// … }` while `clean check` printed `pd 1 = 3` (integ/r5 2026-10-16). That
/// gate now stores `error_render::term` renderings as well.
#[test]
fn test_private_names_in_diagnostics_are_user_facing() {
    let verdicts = run_named_file_messages(
        "private def pd (n : Nat) : Nat := n + 1\n\
         private theorem pt : pd 1 = 2 := rfl\n\
         theorem by_decide : pd 1 = 3 := by decide\n\
         theorem by_term : pd 1 = 3 := pt\n\
         theorem by_rw : pd 2 = 3 := by rw [pt]\n",
        "Pkg.M1",
    );
    let errors: Vec<&String> = verdicts
        .iter()
        .filter_map(|(_, v)| v.as_ref().err())
        .collect();
    assert_eq!(errors.len(), 3, "{verdicts:?}");
    for error in &errors {
        assert!(!error.contains("_private"), "{error}");
    }
    // `decide` refuses in pinned Lean's words, user-facing name included
    // (v4.30.0-rc2: "Tactic `decide` proved that the proposition\n  pd 1 = 3\n
    // is false"; v4.8.0 the same lines after "tactic 'decide' proved that").
    assert!(
        errors
            .iter()
            .any(|e| e.contains("proved that the proposition\n  pd 1 = 3\nis false")),
        "{errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("searched for pd 1 in pd 2 = 3")),
        "{errors:?}"
    );
}
