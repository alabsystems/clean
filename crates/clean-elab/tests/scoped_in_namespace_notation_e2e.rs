//! Mathlib's `scoped[NS] <notation>` (`Mathlib/Tactic/ScopedNS.lean`) through
//! the elaborator. The macro is `with_weak_namespace _root_.NS scoped <cmd>`,
//! so a root `scoped[Foo]` notation is registered under `Foo`: inert at root,
//! active after `open Foo`, and expanding to what its template names.
//! Breadth class (69) in docs/FRONTEND_CLASS_LEDGER.md.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Elaborate every declaration of `source`, continuing past a failed one,
/// and return the environment it leaves.
fn elaborate_file(source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source parses");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let _ = elaborate_decl_and_register(&mut env, &processed);
    }
    env
}

const NOTATION: &str = "scoped[Foo] infixl:65 \" +++ \" => Nat.add\n";

#[test]
fn test_root_scoped_in_namespace_notation_elaborates_after_open() {
    let source = format!("{NOTATION}open Foo\ntheorem sns_t : 2 +++ 3 = 5 := rfl\n");
    let env = elaborate_file(&source);
    assert!(
        env.get_const(&Name::from_string("sns_t")).is_some(),
        "after `open Foo` the `scoped[Foo]` notation must expand to `Nat.add` and \
         the theorem must kernel-register\n--- source ---\n{source}"
    );
}

#[test]
fn test_root_scoped_in_namespace_notation_is_inert_before_open() {
    let source = format!("{NOTATION}theorem sns_t : 2 +++ 3 = 5 := rfl\n");
    let env = elaborate_file(&source);
    assert!(
        env.get_const(&Name::from_string("sns_t")).is_none(),
        "a `scoped[Foo]` notation must be inert at root until `open Foo`"
    );
}

#[test]
fn test_root_scoped_in_namespace_notation_is_active_inside_its_namespace() {
    let source = format!("{NOTATION}namespace Foo\ntheorem sns_t : 2 +++ 3 = 5 := rfl\nend Foo\n");
    let env = elaborate_file(&source);
    assert!(
        env.get_const(&Name::from_string("Foo.sns_t")).is_some(),
        "inside `namespace Foo` the `scoped[Foo]` notation must be active"
    );
}

const NOTATION_IN_BAR: &str =
    "namespace Bar\nscoped[Foo] infixl:65 \" +++ \" => Nat.add\nend Bar\n";

#[test]
fn test_scoped_in_namespace_notation_declared_elsewhere_belongs_to_the_named_namespace() {
    let source = format!("{NOTATION_IN_BAR}open Foo\ntheorem sns_t : 2 +++ 3 = 5 := rfl\n");
    let env = elaborate_file(&source);
    assert!(
        env.get_const(&Name::from_string("sns_t")).is_some(),
        "`scoped[Foo]` inside `namespace Bar` is scoped to `_root_.Foo`: `open Foo` \
         must activate it\n--- source ---\n{source}"
    );
}

#[test]
fn test_scoped_in_namespace_notation_declared_elsewhere_is_not_the_enclosing_namespaces() {
    let source = format!("{NOTATION_IN_BAR}open Bar\ntheorem sns_t : 2 +++ 3 = 5 := rfl\n");
    let env = elaborate_file(&source);
    assert!(
        env.get_const(&Name::from_string("sns_t")).is_none(),
        "the notation belongs to `Foo`, not the enclosing `Bar`: `open Bar` must not \
         activate it"
    );
}
