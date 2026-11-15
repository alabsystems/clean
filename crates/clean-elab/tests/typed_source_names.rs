//! Source identifiers must reach the header index and kernel with exact Names.
//! These tests use the public, all-or-nothing module frontend, not an AST alias.

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_elab::FileContext;
use clean_kernel::{Environment, Name};

const DATA: &str = "inductive Data where\n  | make : Data\n";

fn check(source: &str) -> (Environment, clean_elab::module_batch::ModuleOutcome) {
    let declarations = clean_parser::parse_file(source).expect("actual source parse");
    let mut env = Environment::new();
    let mut file = FileContext::new();
    let outcome = elaborate_module(
        &mut env,
        &mut file,
        &[SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }],
        BatchOptions::islands(),
    );
    (env, outcome)
}

fn accepted(source: &str) -> Environment {
    let (env, outcome) = check(source);
    assert!(
        outcome.is_clean() && outcome.committed,
        "{}",
        outcome.render_rejections()
    );
    env
}

fn requires_constant(env: &Environment, name: Name) {
    assert!(
        env.get_const(&name).is_some(),
        "missing exact identity: {name:?}"
    );
}

#[test]
fn ordinary_source_identity_control() {
    let env = accepted(&format!("{DATA}def identity (x : Data) : Data := x\n"));
    requires_constant(&env, Name::anon().str("identity"));
}

#[test]
fn quoted_dotted_and_hierarchical_declarations_coexist() {
    let env = accepted(&format!("{DATA}namespace A\ndef B (x : Data) : Data := x\nend A\ndef «A.B» (x : Data) : Data := x\n"));
    requires_constant(&env, Name::anon().str("A").str("B"));
    requires_constant(&env, Name::anon().str("A.B"));
}

#[test]
fn quoted_numeral_declaration_is_string_not_numeric_name() {
    let env = accepted(&format!("{DATA}def «7» (x : Data) : Data := x\n"));
    requires_constant(&env, Name::anon().str("7"));
    assert!(env.get_const(&Name::anon().num(7)).is_none());
}

#[test]
fn quoted_unicode_declaration_retains_exact_component() {
    let env = accepted(&format!("{DATA}def «λ星» (x : Data) : Data := x\n"));
    requires_constant(&env, Name::anon().str("λ星"));
}

#[test]
fn quoted_dotted_body_reference_cannot_borrow_hierarchical_twin() {
    let env = accepted(&format!("{DATA}namespace A\ndef B (x : Data) : Data := x\nend A\ndef «A.B» (x : Data) : Data := Data.make\ndef nested (x : Data) : Data := A.B x\ndef quoted (x : Data) : Data := «A.B» x\n"));
    let nested = env
        .get_const(&Name::anon().str("nested"))
        .unwrap()
        .value
        .as_ref()
        .unwrap()
        .collect_constants();
    let quoted = env
        .get_const(&Name::anon().str("quoted"))
        .unwrap()
        .value
        .as_ref()
        .unwrap()
        .collect_constants();
    assert!(nested.contains(&Name::anon().str("A").str("B")));
    assert!(!nested.contains(&Name::anon().str("A.B")));
    assert!(quoted.contains(&Name::anon().str("A.B")));
    assert!(!quoted.contains(&Name::anon().str("A").str("B")));
}

#[test]
fn escaped_contextual_keyword_remains_an_identifier() {
    let env = accepted(&format!("{DATA}def «outParam» (x : Data) : Data := x\ndef usesKeyword (x : Data) : Data := «outParam» x\n"));
    let value = env
        .get_const(&Name::anon().str("usesKeyword"))
        .unwrap()
        .value
        .as_ref()
        .unwrap();
    assert!(value
        .collect_constants()
        .contains(&Name::anon().str("outParam")));
}

#[test]
fn escaped_sort_keyword_remains_a_constant_reference() {
    let env = accepted(&format!(
        "{DATA}def «Type» (x : Data) : Data := x\ndef usesType (x : Data) : Data := «Type» x\n"
    ));
    let value = env
        .get_const(&Name::anon().str("usesType"))
        .unwrap()
        .value
        .as_ref()
        .unwrap();
    assert!(value
        .collect_constants()
        .contains(&Name::anon().str("Type")));
}

#[test]
fn quoted_namespace_prefix_is_not_split_during_entry_or_exit() {
    let env = accepted(&format!("{DATA}namespace «A.B»\ndef leaf (x : Data) : Data := x\nend «A.B»\ndef outside (x : Data) : Data := x\n"));
    requires_constant(&env, Name::anon().str("A.B").str("leaf"));
    requires_constant(&env, Name::anon().str("outside"));
    assert!(env
        .get_const(&Name::anon().str("A").str("B").str("leaf"))
        .is_none());
}

#[test]
fn exact_duplicate_identity_still_refuses_atomically() {
    let (env, outcome) = check(&format!(
        "{DATA}def same (x : Data) : Data := x\ndef «same» (x : Data) : Data := x\n"
    ));
    assert!(!outcome.is_clean() && !outcome.committed);
    assert!(env.get_const(&Name::anon().str("same")).is_none());
}

#[test]
fn quoted_universe_parameter_retains_one_string_component() {
    let env = accepted("def identity.{«u.v»} (A : Sort «u.v») (x : A) : A := x\n");
    let decl = env.get_const(&Name::anon().str("identity")).unwrap();
    assert_eq!(decl.level_params, vec![Name::anon().str("u.v")]);
}

#[test]
fn explicit_quoted_dotted_reference_retains_its_target() {
    let env = accepted(&format!(
        "{DATA}def «A.B» (x : Data) : Data := x\ndef explicitUse (x : Data) : Data := @«A.B» x\n"
    ));
    let value = env
        .get_const(&Name::anon().str("explicitUse"))
        .unwrap()
        .value
        .as_ref()
        .unwrap();
    assert!(value.collect_constants().contains(&Name::anon().str("A.B")));
}

#[test]
fn malformed_qualified_identifier_remains_a_parse_error() {
    assert!(clean_parser::parse_decl("def A. : Type := Type").is_err());
}
