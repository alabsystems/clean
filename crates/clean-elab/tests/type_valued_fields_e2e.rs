// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end probes for `Type`-valued structure and class fields.
//!
//! A field `Prov : Type` followed by another field on the next line read the
//! next field's NAME as the universe level of `Type` (`Type n`), and the rest
//! of the field block fell to a parser-recovery raw declaration — `clean
//! check` reported "parser recovery produced raw declaration: Colon  Nat" for
//! a structure Lean 4.30 accepts. Lean's `Type` / `Sort` level carries
//! `checkColGt` (`Lean/Parser/Term.lean:135-139`) and the field block saves
//! the first field's column (`structFields := manyIndent …`), so the next
//! field is never a level; `where` instances and `{ … }` instances
//! (`sepByIndent`) likewise.
//!
//! The later tests cover the same guard in `where` auxiliary declarations
//! and inside binder groups.
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass here matches the observable `clean check` verdict, and every
//! `rfl` pin is re-checked by the kernel.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{ExprKind, Name};
use clean_parser::parse_file;

/// Drive the real file pipeline. Returns the environment (post-registration)
/// plus the elaboration results, or the first error's message.
fn elaborate_file(source: &str) -> Result<(Environment, Vec<ElabResult>), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok((env, results))
}

fn expect_pass(source: &str) -> Environment {
    elaborate_file(source)
        .unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"))
        .0
}

/// Number of explicit fields the constructor `ctor` takes: the length of its
/// Pi telescope after `params` parameters.
fn ctor_field_count(env: &Environment, ctor: &str, params: usize) -> usize {
    let info = env
        .get_const(&Name::from_string(ctor))
        .unwrap_or_else(|| panic!("{ctor} is registered"));
    let mut ty = info.type_.clone();
    let mut arity = 0;
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        arity += 1;
        ty = (**body).clone();
    }
    arity - params
}

const D1: &str = "structure D1 where\n  Prov : Type\n  n : Nat\n\n";

/// The reported structure: `Prov : Type` then `n : Nat` is two fields, both
/// projectable, and a field-dependent signature over them checks.
#[test]
fn type_field_then_nat_field_declares_both_fields() {
    let src = format!(
        "{D1}def useD1 (d : D1) (p : d.Prov) : d.Prov := p\n\
         def d1 : D1 := ⟨Nat, 7⟩\n\
         theorem d1_n : d1.n = 7 := rfl\n\
         theorem d1_use : useD1 d1 (3 : Nat) = 3 := rfl\n"
    );
    let env = expect_pass(&src);
    assert_eq!(ctor_field_count(&env, "D1.mk", 0), 2);
}

/// The reported class: `Prov : Type` then a function field over it.
#[test]
fn class_type_field_then_function_field_declares_both_fields() {
    let src = "class MemC (M : Type) where\n  Prov : Type\n  alloc : M → Option (M × Prov)\n\n\
               instance : MemC Nat where\n  Prov := Nat\n  alloc := fun m => some (m + 1, m)\n";
    let env = expect_pass(src);
    assert_eq!(ctor_field_count(&env, "MemC.mk", 1), 2);
}

/// Several `Type` fields in a row, then fields over them — the memory-model
/// dictionary shape — declare, construct with a `where` instance whose
/// first values are `Type`-free, and project.
#[test]
fn several_type_fields_then_function_fields() {
    let src = "structure MemDict where\n  Prov : Type\n  FrameExtra : Type\n  St : Type\n  \
               newCall : FrameExtra\n  allocate : St → Nat → Option (St × Prov)\n\n\
               def basic : MemDict where\n  Prov := Nat\n  FrameExtra := Unit\n  St := Nat\n  \
               newCall := ()\n  allocate := fun s n => some (s + n, s)\n\n\
               theorem basic_alloc : basic.allocate 2 3 = some (5, 2) := rfl\n";
    let env = expect_pass(src);
    assert_eq!(ctor_field_count(&env, "MemDict.mk", 0), 5);
}

/// A `where` instance whose field VALUE is `Type`, followed by another field.
#[test]
fn where_instance_type_value_then_next_field() {
    let src = "structure Bx where\n  T : Type 1\n  n : Nat\n\n\
               def bx : Bx where\n  T := Type\n  n := 3\n\n\
               theorem bx_n : bx.n = 3 := rfl\n";
    expect_pass(src);
}

/// A `{ … }` instance whose field value is `Type`, the next field aligned
/// under the first.
#[test]
fn brace_instance_type_value_then_next_field() {
    let src = "structure Bx where\n  T : Type 1\n  n : Nat\n\n\
               def bx : Bx := { T := Type\n                n := 4 }\n\n\
               theorem bx_n : bx.n = 4 := rfl\n";
    expect_pass(src);
}

/// Same-line levels keep their meaning: `A : Type u` is `Sort (u+1)`.
#[test]
fn same_line_universe_levels_still_apply() {
    let src = "universe u\n\nstructure Lv where\n  A : Type u\n  n : Nat\n\n\
               def lv : Lv := ⟨Nat, 1⟩\n\
               theorem lv_n : lv.n = 1 := rfl\n";
    expect_pass(src);
}

/// A `where` auxiliary declaration whose body is `Type`, then another one.
/// Lean's `whereDecls` (`sepByIndent`) saves the first declaration's column,
/// so `k` is the next declaration, not the level of `Type`. Lean 4.30.0-rc2
/// accepts the file.
#[test]
fn where_decl_type_value_then_next_decl() {
    let src = "def g : Nat := k\nwhere\n  T := Type\n  k := 3\n\n\
               theorem g_eq : g = 3 := rfl\n";
    expect_pass(src);
}

/// Explicit and implicit binder groups parse their contents with no saved
/// position (`withoutPosition`), so a level continuation inside one, at or
/// left of the enclosing block's column, is still the level. Lean
/// 4.30.0-rc2 accepts both files.
#[test]
fn binder_group_level_continuations() {
    let env = expect_pass(
        "universe u\nstructure S where\n    f : ∀ {α : Sort\n  u}, α → α\n    n : Nat\n\
         def s : S := ⟨fun x => x, 4⟩\ntheorem s_n : s.n = 4 := rfl\n",
    );
    assert_eq!(ctor_field_count(&env, "S.mk", 0), 2);
    expect_pass(
        "universe u\nclass C where\n    g : ∀ (α : Sort u), α → α\ninstance : C where\n    \
         g := fun (α : Sort\n  u) (x : α) => x\ntheorem c_g : (C.g Nat 3 : Nat) = 3 := rfl\n",
    );
}
