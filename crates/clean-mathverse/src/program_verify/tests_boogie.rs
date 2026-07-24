// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Boogie VC parser.

use super::*;

const SIMPLE_BOOGIE: &str = "\
procedure Increment(x: int) returns (result: int)
  requires x >= 0;
  ensures result > 0;
{
  assert x + 1 > 0; // source: counter.bpl:42
}";

#[test]
fn test_parse_boogie_vcs_simple() {
    let vcs = parse_boogie_vcs(SIMPLE_BOOGIE).expect("should parse");
    assert_eq!(vcs.len(), 3);
    assert_eq!(vcs[0].name, "Increment::requires::0");
    assert_eq!(vcs[1].name, "Increment::ensures::1");
    assert_eq!(vcs[2].name, "Increment::assert::2");
    assert!(vcs.iter().all(|vc| vc.status == VcStatus::Unknown));
}

#[test]
fn test_parse_boogie_vcs_source_location() {
    let vcs = parse_boogie_vcs(SIMPLE_BOOGIE).expect("should parse");
    assert_eq!(vcs[2].source_line, Some(42));
}

#[test]
fn test_parse_boogie_vcs_empty_errors() {
    let result = parse_boogie_vcs("");
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), BoogieParseError::EmptyInput));
}

#[test]
fn test_parse_boogie_vcs_no_procedures_errors() {
    let result = parse_boogie_vcs("// just a comment\nvar x: int;");
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        BoogieParseError::NoProcedures
    ));
}

#[test]
fn test_parse_boogie_vcs_multiple_procedures() {
    let input = "\
procedure A()
  requires true;
{
}
procedure B()
  ensures false;
{
}";
    let vcs = parse_boogie_vcs(input).expect("should parse");
    assert_eq!(vcs.len(), 2);
    assert_eq!(vcs[0].name, "A::requires::0");
    assert_eq!(vcs[1].name, "B::ensures::0");
}

#[test]
fn test_parse_boogie_vcs_with_source_file_comment() {
    let input = "\
// source_file: search.bpl
procedure Search(arr: [int]int, len: int)
  requires len > 0;
{
}";
    let vcs = parse_boogie_vcs(input).expect("should parse");
    assert_eq!(vcs[0].source_file.as_deref(), Some("search.bpl"));
}

#[test]
fn test_parse_boogie_expr_true() {
    let f = parse_boogie_expr("true");
    assert_eq!(f, VcFormula::bool_lit(true));
}

#[test]
fn test_parse_boogie_expr_false() {
    let f = parse_boogie_expr("false");
    assert_eq!(f, VcFormula::bool_lit(false));
}

#[test]
fn test_parse_boogie_expr_integer() {
    let f = parse_boogie_expr("42");
    assert_eq!(f, VcFormula::int_lit(42));
}

#[test]
fn test_parse_boogie_expr_variable() {
    let f = parse_boogie_expr("my_var");
    assert_eq!(f, VcFormula::var("my_var"));
}

#[test]
fn test_parse_boogie_expr_comparison() {
    let f = parse_boogie_expr("x >= 0");
    assert_eq!(f.kind, VcFormulaKind::Le);
    assert_eq!(f.args.len(), 2);
    // x >= 0 becomes 0 <= x
    assert_eq!(f.args[0], VcFormula::int_lit(0));
    assert_eq!(f.args[1], VcFormula::var("x"));
}

#[test]
fn test_parse_boogie_expr_implication() {
    let f = parse_boogie_expr("x >= 0 ==> result > 0");
    assert_eq!(f.kind, VcFormulaKind::Implies);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_boogie_expr_conjunction() {
    let f = parse_boogie_expr("a && b");
    assert_eq!(f.kind, VcFormulaKind::And);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_boogie_expr_negation() {
    let f = parse_boogie_expr("!done");
    assert_eq!(f.kind, VcFormulaKind::Not);
    assert_eq!(f.args.len(), 1);
}

#[test]
fn test_parse_boogie_expr_equality() {
    let f = parse_boogie_expr("x == y");
    assert_eq!(f.kind, VcFormulaKind::Eq);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_boogie_expr_func_app() {
    let f = parse_boogie_expr("f(x, y)");
    assert_eq!(f.kind, VcFormulaKind::FuncApp("f".to_string()));
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_extract_procedure_name() {
    assert_eq!(
        extract_procedure_name("procedure Foo(x: int)"),
        Some("Foo".to_string())
    );
    assert_eq!(
        extract_procedure_name("procedure Bar returns (r: bool)"),
        Some("Bar".to_string())
    );
    assert_eq!(extract_procedure_name("procedure"), None);
}

#[test]
fn test_extract_source_line() {
    assert_eq!(
        extract_source_line("assert x > 0; // source: file.bpl:42"),
        Some(42)
    );
    assert_eq!(extract_source_line("assert x > 0;"), None);
    assert_eq!(extract_source_line("assert x > 0; // source: 99"), Some(99));
}

#[test]
fn test_boogie_type_parse_int() {
    assert_eq!(BoogieType::parse("int").unwrap(), BoogieType::Int);
}

#[test]
fn test_boogie_type_parse_bool() {
    assert_eq!(BoogieType::parse("bool").unwrap(), BoogieType::Bool);
}

#[test]
fn test_boogie_type_parse_bv() {
    assert_eq!(BoogieType::parse("bv32").unwrap(), BoogieType::Bv(32));
    assert_eq!(BoogieType::parse("bv8").unwrap(), BoogieType::Bv(8));
}

#[test]
fn test_boogie_type_parse_map() {
    let result = BoogieType::parse("[int]int").unwrap();
    assert_eq!(
        result,
        BoogieType::Map(Box::new(BoogieType::Int), Box::new(BoogieType::Int))
    );
}

#[test]
fn test_boogie_type_parse_named() {
    assert_eq!(
        BoogieType::parse("MyType").unwrap(),
        BoogieType::Named("MyType".to_string())
    );
}

#[test]
fn test_strip_trailing_semicolon() {
    assert_eq!(strip_trailing_semicolon("x >= 0;"), "x >= 0");
    assert_eq!(strip_trailing_semicolon("x >= 0"), "x >= 0");
    assert_eq!(strip_trailing_semicolon("  x ;  "), "x");
}

#[test]
fn test_split_args() {
    let args = split_args("x, y, z");
    assert_eq!(args, vec!["x", "y", "z"]);
}

#[test]
fn test_split_args_nested() {
    let args = split_args("f(a, b), c");
    assert_eq!(args, vec!["f(a, b)", "c"]);
}

#[test]
fn test_split_args_empty() {
    let args = split_args("");
    assert!(args.is_empty());
}
