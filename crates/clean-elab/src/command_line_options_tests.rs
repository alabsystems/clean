// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `-D` overrides: Lean's argument rules, and the override reaching the
//! elaborator exactly as a leading `set_option` does (gap G50).

use super::*;
use crate::{elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context};
use clean_parser::parse_file;

/// The G50 repro: `Foo` is undefined, so only auto-binding accepts it.
const UNDEFINED_TYPE: &str = "theorem t (x : Foo) : x = x := rfl\n";

/// Elaborate `code` as one file under `options`; `Ok(())` when every
/// declaration registered, else the first error rendered.
fn elaborate_with(code: &str, options: &[CommandLineOption]) -> Result<(), String> {
    let decls = parse_file(code).expect("fixture parses");
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    apply_command_line_options(&mut env, &mut file_ctx, options);
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register_with_context_and_warning(&mut env, &processed, &mut file_ctx)
            .map_err(|e| e.to_string())?;
    }
    Ok(())
}

fn auto_implicit_off() -> Vec<CommandLineOption> {
    vec![CommandLineOption::parse("autoImplicit=false").expect("autoImplicit is a Bool option")]
}

#[test]
fn test_command_line_option_auto_implicit_false_refuses_undefined_type() {
    let err = elaborate_with(UNDEFINED_TYPE, &auto_implicit_off())
        .expect_err("-DautoImplicit=false must refuse an undefined type, as Lean's build does");
    assert!(
        err.contains("Foo"),
        "the refusal names the identifier: {err}"
    );
}

#[test]
fn test_command_line_option_absent_keeps_lean_default_auto_bind() {
    // Lean's default is autoImplicit true: the same file is ACCEPTED without
    // the override, so the refusal above is the override's doing.
    elaborate_with(UNDEFINED_TYPE, &[]).expect("default autoImplicit auto-binds `Foo`");
}

#[test]
fn test_command_line_option_in_file_set_option_overrides_it() {
    let code = format!("set_option autoImplicit true\n{UNDEFINED_TYPE}");
    elaborate_with(&code, &auto_implicit_off())
        .expect("an in-file set_option overrides the -D initial value");
}

#[test]
fn test_command_line_option_section_restores_the_override() {
    // A section that turns it back on restores the -D value at `end`.
    let code = "section\nset_option autoImplicit true\ntheorem a (x : Foo) : x = x := rfl\nend\n\
                theorem b (x : Bar) : x = x := rfl\n";
    let err = elaborate_with(code, &auto_implicit_off())
        .expect_err("after `end`, the -D value (false) is back in force");
    assert!(
        err.contains("Bar"),
        "the refusal is the post-section theorem: {err}"
    );
}

#[test]
fn test_command_line_option_later_override_wins() {
    let options = parse_command_line_options(&["autoImplicit=false", "autoImplicit=true"])
        .expect("both parse");
    elaborate_with(UNDEFINED_TYPE, &options).expect("the later -D wins, as in Lean");
}

#[test]
fn test_command_line_option_relaxed_auto_implicit_false_refuses_multi_letter() {
    let options = parse_command_line_options(&["relaxedAutoImplicit=false"]).expect("parses");
    elaborate_with(UNDEFINED_TYPE, &options)
        .expect_err("pinned Lean refuses `Foo` under -DrelaxedAutoImplicit=false");
}

#[test]
fn test_command_line_option_parse_rejects_missing_equals() {
    assert_eq!(
        CommandLineOption::parse("autoImplicit"),
        Err(CommandLineOptionError::MissingEquals)
    );
    assert_eq!(
        CommandLineOptionError::MissingEquals.to_string(),
        "invalid -D parameter, argument must contain '='"
    );
}

#[test]
fn test_command_line_option_parse_rejects_unknown_name_with_lean_message() {
    let err = CommandLineOption::parse("bogus=1").expect_err("unknown name");
    assert_eq!(
        err.to_string(),
        "invalid -D parameter, unknown configuration option 'bogus'"
    );
}

#[test]
fn test_command_line_option_parse_rejects_non_bool_value_with_lean_message() {
    for value in ["0", "False", " false", "maybe"] {
        let err = CommandLineOption::parse(&format!("autoImplicit={value}"))
            .expect_err("a Bool option takes exactly true/false");
        assert_eq!(
            err.to_string(),
            "invalid -D parameter, invalid configuration option 'autoImplicit' value, \
             it must be true/false"
        );
    }
}

#[test]
fn test_command_line_option_parse_trims_the_name_only() {
    let option = CommandLineOption::parse(" autoImplicit=false").expect("name is trimmed");
    assert_eq!(option.name(), "autoImplicit");
    assert_eq!(option.to_arg(), "autoImplicit=false");
}

#[test]
fn test_command_line_option_nat_reads_like_atoi() {
    let parse = |v: &str| {
        CommandLineOption::parse(&format!("maxRecDepth={v}"))
            .expect("Nat options accept any text")
            .value()
            .to_string()
    };
    assert_eq!(parse("1024"), "1024");
    assert_eq!(parse("abc"), "0", "Lean reads -DmaxRecDepth=abc as 0");
    assert_eq!(parse("12abc"), "12");
    assert_eq!(parse("-1"), "4294967295");
    assert_eq!(parse("  +7"), "7");
}

#[test]
fn test_command_line_option_lean_atoi_saturates_to_int_range() {
    assert_eq!(lean_atoi("99999999999999999999"), i32::MAX as u32);
    assert_eq!(lean_atoi(""), 0);
}

#[test]
fn test_command_line_option_string_value_is_verbatim() {
    // The one String option pinned Lean 4.8.0 declares.
    let option = CommandLineOption::parse("trace.profiler.output=a=b c").expect("String option");
    assert_eq!(option.value(), "a=b c");
}

#[test]
fn test_command_line_option_pinned_table_has_every_measured_name() {
    assert_eq!(
        pinned_lean_option_count(),
        342,
        "bin/lean -D accepted exactly 342 names on 2026-10-08"
    );
}

/// Names Clean's registry declares but pinned Lean 4.8.0's `-D` refuses
/// (`invalid -D parameter, unknown configuration option`, measured on
/// `bin/lean`). Two of them change what Clean ACCEPTS, so honouring them
/// would let `clean lake build` pass a package `lake build` fails.
const CLEAN_ONLY_NAMES: [&str; 7] = [
    "clean.inductive.deepInduction",
    "clean.inductive.liftNestedLocals",
    "grind.warning",
    "linter.unusedSimpArgs",
    "pp.coercions.types",
    "pp.parens",
    "pp.format",
];

#[test]
fn test_command_line_option_clean_only_names_refused_like_pinned_lean() {
    for name in CLEAN_ONLY_NAMES {
        let value = if name == "pp.format" { "x" } else { "true" };
        let err = CommandLineOption::parse(&format!("{name}={value}"))
            .expect_err("pinned Lean refuses this name, so Clean must");
        assert_eq!(
            err.to_string(),
            format!("invalid -D parameter, unknown configuration option '{name}'")
        );
    }
}

#[test]
fn test_command_line_option_lean_only_inert_names_accepted_not_applied() {
    // Pinned Lean accepts these; they print, lint or profile, so Clean
    // accepts them and says it does not apply them.
    for arg in [
        "linter.missingDocs=true",
        "linter.deprecated=false",
        "profiler=true",
        "profiler.threshold=10",
        "pp.fieldNotation=false",
        "diagnostics=true",
    ] {
        let option = CommandLineOption::parse(arg).expect("pinned Lean accepts it");
        assert!(!option.is_applied(), "{arg} is not one Clean implements");
    }
    // Lean's own default is a no-op whatever the option does.
    for arg in [
        "maxUniverseOffset=32",
        "tactic.hygienic=true",
        "quotPrecheck=true",
    ] {
        let option = CommandLineOption::parse(arg).expect("a default value is a no-op");
        assert!(!option.is_applied());
    }
    assert!(CommandLineOption::parse("autoImplicit=false")
        .expect("Clean implements autoImplicit")
        .is_applied());
}

#[test]
fn test_command_line_option_lean_only_semantic_names_refused_off_default() {
    for arg in [
        "warningAsError=true",
        "quotPrecheck=false",
        "tactic.hygienic=false",
        "maxUniverseOffset=4",
        "bootstrap.inductiveCheckResultingUniverse=false",
        "genSizeOfSpec=false",
    ] {
        let err = CommandLineOption::parse(arg).expect_err("may change acceptance");
        assert!(
            matches!(err, CommandLineOptionError::NotImplemented { .. }),
            "{arg}: {err}"
        );
    }
}

#[test]
fn test_command_line_option_not_applied_option_changes_nothing() {
    let options = parse_command_line_options(&["linter.missingDocs=true"]).expect("parses");
    elaborate_with(UNDEFINED_TYPE, &options).expect("an unapplied lint option changes nothing");
}

/// `set_option autoImplicit true in <decl>` overrides a `-D` (and a
/// file-scope `set_option`) for that one declaration, as in Lean: pinned
/// `lean -DautoImplicit=false` accepts `t3` and refuses `t4` here. It used to
/// be overwritten by the file context's re-applied options.
#[test]
fn test_command_line_option_set_option_in_overrides_for_one_declaration() {
    let scoped = "set_option autoImplicit true in\ntheorem t3 (x : Baz) : x = x := rfl\n";
    elaborate_with(scoped, &auto_implicit_off())
        .expect("`set_option … in` turns autoImplicit back on for t3");
    let after = format!("{scoped}theorem t4 (x : Qux) : x = x := rfl\n");
    let err = elaborate_with(&after, &auto_implicit_off())
        .expect_err("after the scoped declaration the -D value is back");
    assert!(err.contains("Qux"), "the refusal is t4's: {err}");
    let file_scope = format!("set_option autoImplicit false\n{scoped}");
    elaborate_with(&file_scope, &[]).expect("same over a file-scope set_option");
}
