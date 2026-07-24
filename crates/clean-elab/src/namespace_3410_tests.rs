// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #3410 — Basic.lean UnknownFVar in namespace and
//! `Int.land` dot-notation failure.
//!
//! These tests mirror the pattern used in tMIR's `Basic.lean` (312 lines)
//! that failed to elaborate end-to-end:
//!
//! 1. A namespace block containing a large inductive plus structures and
//!    functions that reference it (produced the `UnknownFVar(FVarId(48))`
//!    TypeMismatch failure).
//! 2. A `namespace Int` block defining `Int.land` and a theorem using dot
//!    notation `Int.land` — the dot-notation resolver reported
//!    `UnknownIdent("land (dot notation on type-valued expression)")` on
//!    expressions like `Int.land a b`.
//!
//! The fixes live in:
//! - `src/lib.rs`: preprocess inner declarations of a `Namespace` block so
//!   inductives / structures / functions defined earlier in the block are
//!   visible to later declarations, and so `variable`/`universe` commands
//!   inside a namespace are propagated via the FileContext.
//! - `src/infer/elab_proj.rs`: fall back to inductive / constructor /
//!   recursor lookups in the Sort-typed dot-notation path, and enforce
//!   private visibility on the qualified-name fallback.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elab_file(env: &mut Environment, code: &str) -> Vec<Result<ElabResult, crate::ElabError>> {
    let decls = parse_file(code).expect("parse_file should succeed");
    let mut file_ctx = FileContext::new();
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(env, &processed, &mut file_ctx)
        })
        .collect()
}

/// Core #3410 repro: a namespace block that contains an inductive declared
/// early and a function defined later in the same block that references the
/// inductive. Before the fix, the later function could not see the earlier
/// inductive (the flattened namespace elab path did not preprocess inner
/// decls through the FileContext), and elaboration failed with an FVar
/// lookup error.
#[test]
fn test_3410_namespace_inductive_then_function_referencing_it() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace TMir
  inductive Ty : Type
  | int : Ty
  | bool : Ty

  def isInt : Ty -> Bool
  | Ty.int => true
  | Ty.bool => false
end TMir
";
    let results = elab_file(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "namespace-inner decl {i} failed to elaborate: {:?}",
            r.as_ref().err()
        );
    }
    assert!(
        env.get_inductive(&Name::from_string("TMir.Ty")).is_some(),
        "expected TMir.Ty inductive to be registered"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.isInt")).is_some(),
        "expected TMir.isInt def to be registered"
    );
}

/// A namespace containing a `variable` command followed by a definition
/// that references that variable. Before the fix this triggered the
/// reported `UnknownFVar(FVarId(N))` error because the flattened namespace
/// elab path did not call the preprocessor, so `variable`-introduced
/// binders were never prepended to subsequent declarations.
#[test]
fn test_3410_namespace_variable_then_def_using_variable() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace TMir
  variable (α : Type)
  def id_in_ns (x : α) : α := x
end TMir
";
    let results = elab_file(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "namespace variable/def decl {i} failed: {:?}",
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("TMir.id_in_ns")).is_some(),
        "expected TMir.id_in_ns in environment"
    );
}

/// `namespace Int` block defining `Int.land` and a theorem that uses
/// `Int.land a b` — this was the second half of #3410. The dot-notation
/// resolver must find the `land` constant registered inside the `Int`
/// namespace when we write `Int.land a b` at file scope after the block.
///
/// Uses `MyInt` rather than `Int` since `Environment::with_prelude()`
/// already registers `Int`. The shape of the test is identical to
/// Basic.lean, where `Int` was a bare `axiom` type (tMIR does not import
/// Mathlib's Int instances).
#[test]
fn test_3410_int_land_dot_notation_across_namespace_boundary() {
    let mut env = Environment::new();
    let prelude = "\
axiom MyInt : Type
axiom MyInt.zero : MyInt

namespace MyInt
  def land (a : MyInt) (_b : MyInt) : MyInt := a
end MyInt

def usesLand (a b : MyInt) : MyInt := MyInt.land a b
";
    let results = elab_file(&mut env, prelude);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "MyInt.land decl {i} failed: {:?}",
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("MyInt.land")).is_some(),
        "expected MyInt.land to be registered"
    );
    assert!(
        env.get_const(&Name::from_string("usesLand")).is_some(),
        "expected usesLand (which calls MyInt.land) to elaborate"
    );
}

/// Combined scenario mirroring the full Basic.lean TMir namespace shape:
/// a 10-constructor inductive Ty, a structure whose field is Ty, and a
/// function that projects the structure field and pattern-matches on it.
/// This exercises the exact interaction that originally produced
/// `TypeMismatch { expected: "valid type", actual: "UnknownFVar(FVarId(48))" }`.
#[test]
fn test_3410_namespace_large_inductive_structure_and_use() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace TMir
  inductive Ty : Type
  | int : Ty
  | nat : Ty
  | bool : Ty
  | char : Ty
  | unit : Ty
  | str : Ty
  | float : Ty
  | ptr : Ty -> Ty
  | arr : Ty -> Ty
  | tuple : Ty -> Ty -> Ty

  structure Binding where
    ty : Ty

  def bindingTy (b : Binding) : Ty := b.ty
end TMir
";
    let results = elab_file(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "TMir namespace decl {i} failed: {:?}",
            r.as_ref().err()
        );
    }
    assert!(
        env.get_inductive(&Name::from_string("TMir.Ty")).is_some(),
        "expected TMir.Ty inductive"
    );
    assert!(
        env.get_inductive(&Name::from_string("TMir.Binding"))
            .is_some(),
        "expected TMir.Binding structure"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.bindingTy"))
            .is_some(),
        "expected TMir.bindingTy def"
    );
}

/// Combined scenario: a namespace with multiple structures and a function
/// that references fields of an earlier structure declared in the same
/// namespace. This is the shape of the `TMir` namespace in Basic.lean.
#[test]
fn test_3410_namespace_structure_then_function_projecting_fields() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace TMir
  structure Loc where
    idx : Nat

  def locIdx (l : Loc) : Nat := l.idx
end TMir
";
    let results = elab_file(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "namespace structure/projection decl {i} failed: {:?}",
            r.as_ref().err()
        );
    }
    assert!(
        env.get_inductive(&Name::from_string("TMir.Loc")).is_some(),
        "expected TMir.Loc structure in environment"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.locIdx")).is_some(),
        "expected TMir.locIdx def in environment"
    );
}

/// Track Z: a def named `Set.denote` inside `namespace TMir`, then referenced in
/// a sibling theorem. The prelude already ships `Set : Type u → Type u` (a
/// Pi-typed *type* constant), so `Set.denote` resolves its receiver `Set` to the
/// prelude axiom and the dot-projection `Set.denote` previously failed with
/// "cannot extract type name from Pi …" — even though `TMir.Set.denote` is a
/// genuine in-namespace def. The dot resolver now walks the active namespace
/// chain for `T.field` constants, so the reference resolves to `TMir.Set.denote`.
/// Mirrors trust-ir `Semantics/Aggregate.lean` `Set.denote_repr_independent`.
#[test]
fn test_z_namespaced_set_denote_dot_on_pi_type() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace TMir
  def Set.denote (elems : List Nat) : List Nat := elems

  theorem Set.denote_idem (elems : List Nat) :
      Set.denote elems = Set.denote elems := rfl
end TMir
";
    let results = elab_file(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "namespaced Set.denote decl {i} failed to elaborate: {:?}",
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("TMir.Set.denote"))
            .is_some(),
        "expected TMir.Set.denote def in environment"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.Set.denote_idem"))
            .is_some(),
        "expected TMir.Set.denote_idem theorem in environment"
    );
}
