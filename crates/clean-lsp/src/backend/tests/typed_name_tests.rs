//! Parser-to-editor identity controls. No displayed string is a semantic key.

use super::{
    collect_deprecated_names, detect_deprecated_usage, detect_duplicate_binders,
    detect_sorry_warnings, detect_unused_variables,
};
use crate::backend::analysis::{collect_ident_locations, collect_used_idents};
use clean_kernel::Name;
use std::collections::HashSet;

#[test]
fn quoted_dotted_use_preserves_its_single_component() {
    let expr = clean_parser::parse_expr("«A.B»").unwrap();
    let mut used = HashSet::new();
    collect_used_idents(&expr, &mut used);
    assert_eq!(used, HashSet::from([Name::anon().str("A.B")]));
    let mut ordinary = HashSet::new();
    collect_used_idents(&clean_parser::parse_expr("A.B").unwrap(), &mut ordinary);
    assert_eq!(ordinary, HashSet::from([Name::anon().str("A")]));
}

#[test]
fn quoted_dotted_binder_use_does_not_report_unused() {
    let decl = clean_parser::parse_decl("def f («A.B» : Nat) : Nat := «A.B»").unwrap();
    assert!(detect_unused_variables(&decl).is_empty());
    let unrelated = clean_parser::parse_decl("def f («A.B» : Nat) : Nat := A.B").unwrap();
    assert_eq!(detect_unused_variables(&unrelated).len(), 1);
}

#[test]
fn quoted_sorry_and_admit_do_not_trigger_incomplete_proof_warnings() {
    for name in ["sorry", "admit"] {
        let quoted = clean_parser::parse_decl(&format!("def f : Nat := «{name}»")).unwrap();
        assert!(detect_sorry_warnings(&quoted).is_empty());
        let plain = clean_parser::parse_decl(&format!("def f : Nat := {name}")).unwrap();
        assert_eq!(detect_sorry_warnings(&plain).len(), 1);
    }
}

#[test]
fn deprecated_name_matching_cannot_borrow_a_dotted_twin() {
    let decls = clean_parser::parse_file(
        "attribute [deprecated] «A.B»\ndef quoted : Nat := «A.B»\ndef nested : Nat := A.B\n",
    )
    .unwrap();
    let names = collect_deprecated_names(&decls);
    assert_eq!(names, HashSet::from([Name::anon().str("A.B")]));
    assert_eq!(detect_deprecated_usage(&decls[1], &names).len(), 1);
    assert!(detect_deprecated_usage(&decls[2], &names).is_empty());
}

#[test]
fn identifier_locations_retain_escape_metadata_and_exact_span() {
    let source = "«Type»";
    let expr = clean_parser::parse_expr(source).unwrap();
    let mut locations = Vec::new();
    collect_ident_locations(&expr, &mut locations);
    assert_eq!(locations.len(), 1);
    let name = clean_parser::parse_name(source).unwrap();
    assert!(locations[0].name.same_syntax(&name));
    assert_eq!(&source[locations[0].start..locations[0].end], source);
    assert!(!locations[0].name.is_unescaped_component("Type"));
}

#[test]
fn quoted_and_plain_same_binder_still_count_as_duplicate_identity() {
    let decl = clean_parser::parse_decl("def f (x : Nat) («x» : Nat) : Nat := x").unwrap();
    assert_eq!(detect_duplicate_binders(&decl).len(), 1);
}

#[test]
fn relative_constructor_selector_does_not_count_as_local_use() {
    let mut used = HashSet::new();
    collect_used_idents(&clean_parser::parse_expr(".ctor").unwrap(), &mut used);
    assert!(used.is_empty());
    collect_used_idents(&clean_parser::parse_expr("«.ctor»").unwrap(), &mut used);
    assert_eq!(used, HashSet::from([Name::anon().str(".ctor")]));
}
