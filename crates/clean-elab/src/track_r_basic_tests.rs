// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Track R regression tests: driving the real TrustIr `Basic.lean` through
//! `clean check`.
//!
//! These cover the elaborator gaps that blocked the genuine surface program
//! `lean/trust_ir-semantics/TrustIr/Basic.lean`:
//!
//!   * Recursive function over a user-recursive inductive defined *inside a
//!     namespace*, whose self-call is written as method dot-notation on the
//!     decreasing variable (`elemTy.bitWidth`) — the exact shape of
//!     `TrustIr.Ty.bitWidth`.
//!   * The same with arms out of declaration order and a trailing wildcard
//!     `_ => none` (recursor minor premises must be reordered + expanded).
//!   * `_root_.Bool` root-namespace escape in a return type.
//!   * Namespace-qualified constant dot-notation under an expected type
//!     (`apply Foo.lemma`), which must not auto-bind the namespace head.
//!
//! Every synthesized recursive definition is held to the wave soundness bar:
//! `infer_type` succeeds on its kernel value AND its axiom closure is empty
//! (no `sorry`, no faked termination axiom) — the recursion is genuinely
//! lowered through the already-proven structural `.rec` path.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file;

/// Elaborate + register every decl in `code` into a fresh prelude env,
/// asserting each elaborates without error (mirrors the `clean check` path).
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!("decl {i} fell through to RawDecl (parser error recovery): content={content:?}, span={span:?}");
        }
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

/// Assert a constant is registered, its value kernel-checks (`infer_type`
/// succeeds and is def-eq to the declared type), and its axiom closure is empty.
fn assert_sound_const(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let info = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name} should be registered"));

    let value = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should be a definition with a value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("infer_type({name}.value) failed: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{name}: inferred value type not def-eq to declared type"
    );

    let deps = env
        .axiom_deps(&n)
        .unwrap_or_else(|| panic!("{name} is registered, axiom_deps should return Some"));
    let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "{name} must have an EMPTY axiom closure (sound structural recursion), got {dep_names:?}"
    );
}

/// `TrustIr.Ty.bitWidth` shape: namespaced recursive method over a recursive
/// inductive, self-call via dot notation on the decreasing variable, equation
/// form. Was: `UnknownIdentWithSuggestions name="Foo.Ty.bitWidth"`.
#[test]
fn test_namespaced_recursive_method_dot_notation_self_call() {
    let env = elab_all(
        r#"
namespace Foo
inductive Ty where
  | I32 : Ty
  | Vector : Nat -> Ty -> Ty
  deriving Repr
def Ty.bitWidth : Ty -> Option Nat
  | .I32 => some 32
  | .Vector lanes elemTy =>
    match elemTy.bitWidth with
    | some elemWidth => some (lanes * elemWidth)
    | none => none
end Foo
"#,
    );
    assert_sound_const(&env, "Foo.Ty.bitWidth");
}

/// Arms out of declaration order with a trailing wildcard catch-all: the
/// recursor minor premises must be emitted in constructor declaration order and
/// the wildcard expanded over every otherwise-unhandled constructor, with IH
/// binders on the recursive constructor. Was: a kernel type-mismatch from a
/// mis-placed minor premise.
#[test]
fn test_recursive_method_reordered_arms_and_wildcard() {
    let env = elab_all(
        r#"
namespace Foo
inductive Ty where
  | I8 : Ty
  | I32 : Ty
  | Bool : Ty
  | Ptr : Ty
  | Vector : Nat -> Ty -> Ty
  | Ref : Ty -> Ty
  | Unit : Ty
  deriving Repr
def Ty.bitWidth : Ty -> Option Nat
  | .Bool => some 1
  | .I8   => some 8
  | .I32  => some 32
  | .Vector lanes elemTy =>
    match elemTy.bitWidth with
    | some elemWidth => some (lanes * elemWidth)
    | none => none
  | .Ptr  => some 64
  | .Ref _ => some 64
  | _ => none
end Foo
"#,
    );
    assert_sound_const(&env, "Foo.Ty.bitWidth");
}

/// A non-recursive constructor appearing *after* the recursive one must not
/// shift subsequent minor premises. Was: `expected motive Unit, got Ty`.
#[test]
fn test_recursive_method_nonrecursive_ctor_after_recursive() {
    let env = elab_all(
        r#"
namespace Foo
inductive Ty where
  | I32 : Ty
  | Vector : Nat -> Ty -> Ty
  | Unit : Ty
  deriving Repr
def Ty.bitWidth : Ty -> Option Nat
  | .I32  => some 32
  | .Vector lanes elemTy =>
    match elemTy.bitWidth with
    | some elemWidth => some (lanes * elemWidth)
    | none => none
  | .Unit => none
end Foo
"#,
    );
    assert_sound_const(&env, "Foo.Ty.bitWidth");
}

/// Nested `match` in an arm body must not swallow the enclosing match's
/// subsequent arms (column-sensitive `matchAlts`). The inner `match
/// elemTy.bitWidth with` previously consumed the outer `| .Unit` arm.
#[test]
fn test_nested_match_in_arm_does_not_eat_outer_arms() {
    // The recursive (nested-match) arm sits in the *middle*: a non-recursive
    // arm precedes it (so the motive is resolved before the recursion) and
    // another follows it (so a regression in arm association is observable —
    // before the fix the inner `match elemTy.bitWidth with` swallowed the
    // trailing `| .Unit` arm, leaving the outer match with one arm).
    let env = elab_all(
        r#"
namespace Foo
inductive Ty where
  | I32 : Ty
  | Vector : Nat -> Ty -> Ty
  | Unit : Ty
  deriving Repr
def Ty.bitWidth (t : Ty) : Option Nat :=
  match t with
  | .I32 => some 32
  | .Vector lanes elemTy =>
    match elemTy.bitWidth with
    | some w => some (lanes * w)
    | none => none
  | .Unit => none
end Foo
"#,
    );
    assert_sound_const(&env, "Foo.Ty.bitWidth");
}

/// `_root_.Bool` root-namespace escape in a return-type position resolves to
/// the global `Bool`. Was: `UnknownIdentWithSuggestions name="_root_.Bool"`.
#[test]
fn test_root_namespace_escape_in_return_type() {
    let env = elab_all(
        r#"
namespace Foo
inductive Ty where
  | I8 : Ty
  | I32 : Ty
  deriving Repr
def Ty.isSigned : Ty -> _root_.Bool
  | .I8 | .I32 => true
end Foo
"#,
    );
    let n = Name::from_string("Foo.Ty.isSigned");
    assert!(
        env.get_const(&n).is_some(),
        "Foo.Ty.isSigned should be registered"
    );
}

/// Namespace-qualified constant under an expected type: `apply Foo.mylem` must
/// resolve to the constant `Foo.mylem`, not auto-bind `Foo` as an auto-implicit
/// and mis-resolve `mylem` against the goal's head type (`Eq.mylem`).
#[test]
fn test_qualified_const_dot_notation_not_autoimplicit() {
    let env = elab_all(
        r#"
namespace Foo
theorem mylem (n m : Nat) (h : n = m) : n = m := h
theorem use_it (a b : Nat) (h : a = b) : a = b := by
  apply Foo.mylem
  exact h
end Foo
"#,
    );
    assert!(
        env.get_const(&Name::from_string("Foo.use_it")).is_some(),
        "Foo.use_it should be registered"
    );
}
