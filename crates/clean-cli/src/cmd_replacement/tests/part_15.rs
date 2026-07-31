// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::*;

fn direct_sorry_source(prefix: &str, suffix: &str) -> String {
    let trust_marker = ["so", "rry"].concat();
    format!(r#"{prefix}Expr::const_(Name::from_string("{trust_marker}"), vec![]){suffix}"#)
}

#[test]
fn sorry_bypass_source_scan_rejects_production_occurrences() {
    let source = direct_sorry_source("fn production() { let _ = ", "; }");
    assert_eq!(
        sorry_bypass_lines_in_production(&source).expect("valid Rust lexical structure"),
        vec![1]
    );
}

#[test]
fn sorry_bypass_source_scan_rejects_multiline_and_commented_constructor_calls() {
    let trust_marker = ["so", "rry"].concat();
    let fixtures = [
        format!("mk_const_str /* split */ (\n/* split */\n\"{trust_marker}\"\n)"),
        format!(
            "Expr /* split */ :: /* split */ const_str /* split */ (\n\
             \"{trust_marker}\",\nvec![]\n)"
        ),
        format!(
            "Expr\n::\nconst_str_levels /* split */ (\n/* split */ \"{trust_marker}\",\nvec![]\n)"
        ),
        format!(
            "Expr /* split */ :: const_ /* split */ (\n\
             crate::Name /* split */ :: from_string /* split */ (\n\
             \"{trust_marker}\"\n),\nvec![]\n)"
        ),
    ];
    for fixture in fixtures {
        assert_eq!(
            sorry_bypass_lines_in_production(&fixture).expect("valid Rust lexical structure"),
            vec![1],
            "multiline constructor must remain visible: {fixture}"
        );
    }
}

#[test]
fn sorry_bypass_source_scan_ignores_cfg_test_module_occurrences() {
    let source = direct_sorry_source(
        "#[cfg(test)]\nmod audit_fixture {\nfn detects_marker() { let _ = ",
        "; }\n}\n",
    );
    assert!(sorry_bypass_lines_in_production(&source)
        .expect("valid Rust lexical structure")
        .is_empty());
}

#[test]
fn sorry_bypass_source_scan_masks_multiline_constructor_inside_cfg_test() {
    let trust_marker = ["so", "rry"].concat();
    let source = format!(
        "#[cfg(test)]\nmod audit_fixture {{\n\
         fn detects_marker() {{\n\
         let _ = Expr::const_(\n\
         Name::from_string(\n\"{trust_marker}\"\n),\n\
         vec![]\n);\n\
         }}\n\
         }}\n"
    );
    assert!(sorry_bypass_lines_in_production(&source)
        .expect("valid Rust lexical structure")
        .is_empty());
}

#[test]
fn sorry_bypass_source_scan_ignores_cfg_test_function_occurrences() {
    let source = direct_sorry_source("#[cfg(test)]\nfn audit_fixture() {\nlet _ = ", ";\n}\n");
    assert!(sorry_bypass_lines_in_production(&source)
        .expect("valid Rust lexical structure")
        .is_empty());
}

#[test]
fn sorry_bypass_source_scan_does_not_mask_following_production_code() {
    let test_only = direct_sorry_source(
        "#[cfg(test)] mod audit_fixture { fn probe() { let _ = ",
        "; } } ",
    );
    let production = direct_sorry_source("fn production() { let _ = ", "; }");
    let source = format!("{test_only}{production}");
    assert_eq!(
        sorry_bypass_lines_in_production(&source).expect("valid Rust lexical structure"),
        vec![1]
    );
}

#[test]
fn sorry_bypass_source_scan_keeps_cfg_any_test_or_feature_fail_closed() {
    let source = direct_sorry_source(
        "#[cfg(any(test, feature = \"audit-fixture\"))]\nfn maybe_production() { let _ = ",
        "; }\n",
    );
    assert_eq!(
        sorry_bypass_lines_in_production(&source).expect("valid Rust lexical structure"),
        vec![2]
    );
}

#[test]
fn sorry_bypass_source_scan_does_not_trust_cfg_tokens_inside_a_macro_invocation() {
    let source = direct_sorry_source(
        "passthrough!(#[cfg(test)] fn stripped_by_macro() { let _ = ",
        "; });",
    );
    assert_eq!(
        sorry_bypass_lines_in_production(&source).expect("valid Rust lexical structure"),
        vec![1]
    );
}

#[test]
fn sorry_bypass_source_scan_ignores_fake_cfg_text_in_literals_and_comments() {
    let production = direct_sorry_source("fn production() { let _ = ", "; }");
    let source = format!(
        "const TEXT: &str = r#\"#[cfg(test)] mod fake {{}}\"#;\n\
         // #[cfg(test)] mod fake {{}}\n\
         {production}"
    );
    assert_eq!(
        sorry_bypass_lines_in_production(&source).expect("valid Rust lexical structure"),
        vec![3]
    );
}

#[test]
fn sorry_bypass_source_scan_fails_closed_on_malformed_lexical_structure() {
    let source = direct_sorry_source("fn production() { let _ = ", "; } /*");
    assert!(sorry_bypass_lines_in_production(&source).is_err());
}

#[test]
fn current_repo_sorry_bypass_lint_accepts_test_only_audit_fixtures() {
    validate_sorry_bypass_lint()
        .expect("strict production scan must ignore syntax-gated test-only fixtures");
}
