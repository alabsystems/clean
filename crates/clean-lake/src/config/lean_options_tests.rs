// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reading `leanOptions` / `moreLeanArgs` / `moreLinkArgs` out of
//! `lakefile.lean` (gap G50).

use super::*;
use crate::config::LakeConfig;

/// `~/trust-ir/lean/trust_ir-semantics/lakefile.lean`, verbatim in the parts
/// that matter (comments included).
const TRUST_IR_LAKEFILE: &str = r#"import Lake
open Lake DSL

package trust_irSemantics where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib TrustIr where
  srcDir := "."

lean_lib TrustIrEval where
  srcDir := "."

lean_exe trustir_eval where
  root := `TrustIrEval.Main
  -- Apple-linker-only, so it is not passed elsewhere.
  moreLinkArgs := if System.Platform.isOSX then #["-Wl,-no_data_const"] else #[]
"#;

#[test]
fn test_trust_ir_lakefile_parses_every_field_with_no_diagnostic() {
    let config = LakeConfig::parse(TRUST_IR_LAKEFILE).expect("parses");
    assert!(
        config.diagnostics.is_empty(),
        "nothing skipped: {:?}",
        config.diagnostics
    );
    assert_eq!(
        config.package.lean_options,
        vec![LeanOption {
            name: "autoImplicit".into(),
            value: LeanOptionValue::Bool(false),
        }]
    );
    assert_eq!(config.libs.len(), 2);
    assert_eq!(config.exes.len(), 1);
    assert_eq!(config.exes[0].root, "TrustIrEval.Main");
    let expected: Vec<String> = if cfg!(target_os = "macos") {
        vec!["-Wl,-no_data_const".into()]
    } else {
        Vec::new()
    };
    assert_eq!(
        config.exes[0].more_link_args, expected,
        "host-evaluated, comma kept"
    );
}

#[test]
fn test_lean_options_forms_and_value_kinds() {
    let options = parse_lean_options(
        "#[⟨`pp.unicode.fun, true⟩, { name := `maxHeartbeats, value := 400000 }, \
         ⟨`pp.format, \"a,b\"⟩]",
    )
    .expect("all three forms read");
    assert_eq!(
        options
            .iter()
            .map(LeanOption::define_arg)
            .collect::<Vec<_>>(),
        vec![
            "pp.unicode.fun=true",
            "maxHeartbeats=400000",
            // Lake's `asCliFlagValue` quotes a string value.
            "pp.format=\"a,b\"",
        ]
    );
    assert_eq!(parse_lean_options("#[]"), Some(Vec::new()));
}

#[test]
fn test_lean_options_unreadable_forms_are_none() {
    for text in [
        "mathlibLeanOptions",
        "#[⟨`a, false⟩] ++ extra",
        "#[⟨`a, someDef⟩]",
        "#[⟨``a, true⟩]",
        "#[⟨`a, true, 1⟩]",
        "#[(⟨`a, true⟩ : LeanOption)]",
    ] {
        assert_eq!(parse_lean_options(text), None, "{text}");
    }
}

#[test]
fn test_unreadable_lean_options_is_a_diagnostic_and_recorded() {
    let config = LakeConfig::parse("package p where\n  leanOptions := mathlibLeanOptions\n")
        .expect("lenient parse");
    assert_eq!(config.diagnostics.len(), 1);
    assert_eq!(config.diagnostics[0].token, "leanOptions");
    assert_eq!(
        config.package.unreadable_lean_args,
        vec!["leanOptions := mathlibLeanOptions".to_string()]
    );
}

#[test]
fn test_more_lean_args_and_lib_options_read() {
    let config = LakeConfig::parse(
        "package p where\n  moreLeanArgs := #[\"-DautoImplicit=false\", \"--tstack=1000\"]\n\n\
         lean_lib L where\n  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]\n  \
         moreLeanArgs := #[\"-DmaxRecDepth=1000\"]\n",
    )
    .expect("parses");
    assert!(config.diagnostics.is_empty(), "{:?}", config.diagnostics);
    assert_eq!(
        config.package.more_lean_args,
        vec!["-DautoImplicit=false", "--tstack=1000"]
    );
    assert_eq!(config.libs[0].lean_options[0].name, "relaxedAutoImplicit");
    assert_eq!(config.libs[0].more_lean_args, vec!["-DmaxRecDepth=1000"]);
}

#[test]
fn test_platform_conditional_multi_line_and_negated() {
    let config = LakeConfig::parse(
        "package p\n\nlean_exe e where\n  root := `Main\n  moreLinkArgs :=\n    \
         if !System.Platform.isWindows then #[\"-lm\"]\n    else #[]\n",
    )
    .expect("parses");
    assert!(config.diagnostics.is_empty(), "{:?}", config.diagnostics);
    let expected: Vec<String> = if cfg!(windows) {
        Vec::new()
    } else {
        vec!["-lm".into()]
    };
    assert_eq!(config.exes[0].more_link_args, expected);
    assert_eq!(
        eval_platform_conditional("if System.Platform.isBSD then a else b"),
        None
    );
}

#[test]
fn test_join_field_lines_stops_at_balanced_end() {
    let lines = [
        "  leanOptions := #[",
        "    ⟨`a, false⟩ -- note ]",
        "  ]",
        "  srcDir := \".\"",
    ];
    let (text, next) = join_field_lines(&lines, 0);
    assert_eq!(text, "leanOptions := #[ ⟨`a, false⟩ ]");
    assert_eq!(next, 3, "the next field starts its own read");
}

#[test]
fn test_join_field_lines_never_swallows_the_next_top_level_construct() {
    // An unclosed bracket stops at the next column-0 declaration.
    let lines = [
        "  globs := #[.submodules `Foo",
        "",
        "lean_lib Next where",
        "  srcDir := \".\"",
    ];
    let (_, next) = join_field_lines(&lines, 0);
    assert_eq!(next, 2, "`lean_lib Next` is read as its own declaration");
}

fn package_args(lakefile: &str) -> (Vec<String>, Vec<String>) {
    let config = LakeConfig::parse(lakefile).expect("lenient parse");
    let mut args: Vec<String> = config
        .package
        .lean_options
        .iter()
        .map(|o| format!("-D{}", o.define_arg()))
        .collect();
    args.extend(config.package.more_lean_args.iter().cloned());
    (args, config.package.unreadable_lean_args)
}

/// `A ++ B` reads both arrays, on one line or with `++` opening the next
/// (the review's `lay/concat`: the second array used to be dropped with a
/// "skipped unrecognized `++`" warning while the first was applied).
#[test]
fn test_lean_options_concatenation_reads_every_part() {
    for lakefile in [
        "package p where\n  leanOptions := #[⟨`pp.unicode.fun, true⟩]\n    \
         ++ #[⟨`autoImplicit, false⟩]\n",
        "package p where\n  leanOptions := #[⟨`pp.unicode.fun, true⟩] ++\n    \
         #[⟨`autoImplicit, false⟩]\n",
        "package p where\n  leanOptions := #[⟨`pp.unicode.fun, true⟩] ++ \
         (if System.Platform.isWindows then #[] else #[⟨`autoImplicit, false⟩])\n",
    ] {
        let (args, unreadable) = package_args(lakefile);
        let expected = if cfg!(windows) && lakefile.contains("isWindows") {
            vec!["-Dpp.unicode.fun=true"]
        } else {
            vec!["-Dpp.unicode.fun=true", "-DautoImplicit=false"]
        };
        assert_eq!(args, expected, "{lakefile}");
        assert!(unreadable.is_empty(), "{lakefile}");
    }
}

/// A continuation that is not a form this reader evaluates makes the whole
/// field unreadable, never half-read.
#[test]
fn test_lean_options_unknown_continuation_is_unreadable() {
    let (args, unreadable) = package_args(
        "package p where\n  leanOptions := #[⟨`pp.unicode.fun, true⟩]\n    ++ extraOptions\n",
    );
    assert!(args.is_empty(), "{args:?}");
    assert_eq!(unreadable.len(), 1);
}

#[test]
fn test_weak_lean_args_read_at_package_and_library_level() {
    let config = LakeConfig::parse(
        "package p where\n  weakLeanArgs := #[\"-DautoImplicit=false\"]\n\n\
         lean_lib L where\n  weakLeanArgs := #[\"-DmaxRecDepth=9\"]\n",
    )
    .expect("parses");
    assert!(config.diagnostics.is_empty(), "{:?}", config.diagnostics);
    assert_eq!(config.package.weak_lean_args, vec!["-DautoImplicit=false"]);
    assert_eq!(config.libs[0].weak_lean_args, vec!["-DmaxRecDepth=9"]);
}

/// The review's `lay/oneline` and `lay/attrline` layouts: a field on the
/// declaration's own line, and `@[default_target]` before `lean_lib` on the
/// same line. Both used to lose the library or its options in silence.
#[test]
fn test_lean_options_same_line_layouts_are_read() {
    let (args, unreadable) =
        package_args("package p where leanOptions := #[⟨`autoImplicit, false⟩]\n");
    assert_eq!(args, vec!["-DautoImplicit=false"]);
    assert!(unreadable.is_empty());

    let config = LakeConfig::parse(
        "package p\n\n@[default_target] lean_lib W where\n  roots := #[`W]\n  \
         leanOptions := #[⟨`autoImplicit, false⟩]\n",
    )
    .expect("parses");
    assert_eq!(config.libs.len(), 1, "the library is not dropped");
    assert_eq!(config.libs[0].name, "W");
    assert_eq!(config.default_targets, vec!["W"]);
    assert_eq!(config.libs[0].lean_options.len(), 1);
    assert!(config.package.unreadable_lean_args.is_empty());

    let config = LakeConfig::parse(
        "package p\n\nlean_lib W where leanOptions := #[\n  ⟨`autoImplicit, false⟩\n]\n",
    )
    .expect("parses");
    assert_eq!(config.libs[0].lean_options.len(), 1);
}

/// A layout the scraper does not attribute (the review's `lay/braces`, a
/// `def` the package names) is recorded as unreadable on the package, which
/// refuses every module, instead of vanishing.
#[test]
fn test_lean_options_unattributed_layouts_are_unreadable() {
    for lakefile in [
        "package p {\n  leanOptions := #[⟨`autoImplicit, false⟩]\n}\n",
        "package p { leanOptions := #[⟨`autoImplicit, false⟩] }\n",
        "def opts : LeanConfig := { leanOptions := #[⟨`autoImplicit, false⟩] }\npackage p\n",
        // A column-0 `def` right after a block is swallowed as an unknown
        // field of it; it is still not an attributed option field.
        "package p where\n  version := \"1\"\ndef opts := { leanOptions := #[⟨`autoImplicit, false⟩] }\n",
    ] {
        let (_, unreadable) = package_args(lakefile);
        assert!(!unreadable.is_empty(), "must refuse: {lakefile}");
    }
    // Comments and strings never trip it.
    let (_, unreadable) =
        package_args("-- leanOptions := #[]\n/- weakLeanArgs -/\npackage p where\n  version := \"leanOptions\"\n");
    assert!(unreadable.is_empty(), "{unreadable:?}");
}
