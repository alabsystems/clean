// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for recursion-through-projection desugaring (Track H, task 1).
//!
//! These cover the end-to-end elaboration of a recursive method that matches
//! on a projection of its decreasing binder, plus the RIGOROUS soundness
//! obligations the wave bar demands for any new kernel term:
//!
//! * `infer_type` succeeds on the kernel value of both synthesized constants
//!   (`F` wrapper and `F.go` auxiliary) — the term is well-typed.
//! * `axiom_deps` is EMPTY for both — no `sorry`, no faked termination axiom,
//!   no trust-boundary escape hatch crept in via the desugaring. Soundness is
//!   inherited wholesale from the already-proven structural `.rec` lowering
//!   that the auxiliary equation-form def reuses.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file;

/// Elaborate every decl in `code` into a fresh prelude environment, asserting
/// each one elaborates and registers without error.
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

/// Assert a constant is registered, its value infers a type (well-typed), and
/// its axiom closure is empty (no `sorry`/faked-termination dependency).
fn assert_sound_const(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let info = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name} should be registered"));

    // (1) infer_type soundness: the kernel value must type-check.
    let value = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should be a definition with a value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("infer_type({name}.value) failed: {e:?}"));
    // Sanity: the inferred type is def-eq to the declared type.
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{name}: inferred value type not def-eq to declared type"
    );

    // (2) axiom_deps must be empty: no sorry / faked termination axiom.
    let deps = env
        .axiom_deps(&n)
        .unwrap_or_else(|| panic!("{name} is registered, axiom_deps should return Some"));
    let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "{name} must have an EMPTY axiom closure (sound structural recursion), got {dep_names:?}"
    );
}

const PROJ_REC_SRC: &str = r#"
inductive Lst where
  | nil : Lst
  | cons : Nat -> Lst -> Lst

structure Box where
  data : Lst

def Box.len (b : Box) : Nat :=
  match b.data with
  | Lst.nil => 0
  | Lst.cons _ t => Nat.succ (Box.len { data := t })
"#;

#[test]
fn test_proj_recursion_elaborates_and_registers_both() {
    let env = elab_all(PROJ_REC_SRC);
    assert!(
        env.get_const(&Name::from_string("Box.len")).is_some(),
        "wrapper Box.len should be registered"
    );
    assert!(
        env.get_const(&Name::from_string("Box.len.go")).is_some(),
        "auxiliary Box.len.go should be registered"
    );
}

#[test]
fn test_proj_recursion_soundness_wrapper_and_aux() {
    let env = elab_all(PROJ_REC_SRC);
    // Both the wrapper and the structurally-recursive auxiliary must be
    // well-typed and depend on NO axioms.
    assert_sound_const(&env, "Box.len.go");
    assert_sound_const(&env, "Box.len");
}

#[test]
fn test_proj_recursion_computes_via_kernel_rfl() {
    // The `rfl` proofs force the kernel to reduce the lowered `Lst.rec`
    // applications to numerals; if the lowering were unsound or non-computing
    // these would fail to elaborate.
    let code = r#"
inductive Lst where
  | nil : Lst
  | cons : Nat -> Lst -> Lst

structure Box where
  data : Lst

def Box.len (b : Box) : Nat :=
  match b.data with
  | Lst.nil => 0
  | Lst.cons _ t => Nat.succ (Box.len { data := t })

theorem bl_nil : Box.len { data := Lst.nil } = 0 := rfl
theorem bl_one : Box.len { data := Lst.cons 7 Lst.nil } = 1 := rfl
theorem bl_two : Box.len { data := Lst.cons 7 (Lst.cons 9 Lst.nil) } = 2 := rfl
"#;
    let env = elab_all(code);
    for thm in ["bl_nil", "bl_one", "bl_two"] {
        assert!(
            env.get_const(&Name::from_string(thm)).is_some(),
            "{thm} (rfl) should kernel-check and register"
        );
        // The rfl proof itself must carry no axiom dependency.
        let deps = env
            .axiom_deps(&Name::from_string(thm))
            .expect("registered theorem should report axiom_deps");
        assert!(
            deps.is_empty(),
            "{thm} rfl proof must have empty axiom closure, got {:?}",
            deps.iter().map(|d| d.to_string()).collect::<Vec<_>>()
        );
    }
}

/// A non-recursive projection match must be LEFT UNTOUCHED by the pre-pass
/// (no spurious `.go` auxiliary). The existing non-recursive `casesOn` path
/// handles it.
#[test]
fn test_non_recursive_projection_match_not_split() {
    let code = r#"
inductive Lst where
  | nil : Lst
  | cons : Nat -> Lst -> Lst

structure Box where
  data : Lst

def Box.headOr (b : Box) : Nat :=
  match b.data with
  | Lst.nil => 0
  | Lst.cons h _ => h
"#;
    let env = elab_all(code);
    assert!(
        env.get_const(&Name::from_string("Box.headOr")).is_some(),
        "Box.headOr should be registered"
    );
    assert!(
        env.get_const(&Name::from_string("Box.headOr.go")).is_none(),
        "non-recursive projection match must NOT synthesize a .go auxiliary"
    );
}
