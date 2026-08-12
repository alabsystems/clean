// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: numeric tuple projection on `Prod` — `p.2`, chained `p.2.1`,
//! and doubly-nested `s.2.2` — must lex, elaborate, kernel-check, AND reduce to
//! the correct field.
//!
//! ## The two historical defects this pins
//!
//! 1. **Elaborator off-by-one on the SECOND `Prod` field.** `p.1` projected
//!    correctly but `p.2` reported `Projection index 2 out of bounds for Prod
//!    (fields: 2)`. Lean's numeric projection is 1-based at the surface and
//!    0-based in the kernel `Expr.proj`; the bound is `idx <= num_fields`
//!    (`Lean/Elab/App.lean`: `idx - 1 < numFields`). For `Prod` (num_fields = 2)
//!    both `.1` and `.2` are in range and must yield `fst` / `snd`.
//!
//! 2. **Lexer mis-lexing chained numeric projection as a float.** `p.2.1` is
//!    `(p.2).1`, but the lexer read the `2.1` as the float literal `2.1`,
//!    producing a hard parse error. A digit that is itself a projection index
//!    (immediately after a `.`) must not absorb a following `.<digit>` as a
//!    fractional part.
//!
//! Every case is checked two ways: (a) the `def` elaborates and kernel-checks
//! (the kernel rejects an out-of-bounds `Expr.proj`, so reaching registration
//! proves the emitted index is valid), and (b) applied to a concrete value it
//! reduces to the *correct* field — distinct `Nat`s pin every slot so an
//! off-by-one reads the wrong number rather than being masked.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, Name, TypeChecker};
use clean_parser::parse_file;

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_lit(n: u32) -> Expr {
    let mut e = const_("Nat.zero");
    for _ in 0..n {
        e = Expr::app(const_("Nat.succ"), e);
    }
    e
}

/// Fresh environment with `Nat` and `Prod` (+ `Prod.mk`/`fst`/`snd`) registered,
/// exactly as the prelude ships them.
fn prod_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_prod().expect("init_prod");
    env
}

/// Definitional equality against a kernel `Nat` literal (results normalize to a
/// succ/zero tower, so a head-name comparison would not suffice).
fn def_eq(env: &Environment, expr: &Expr, reference: &Expr) -> bool {
    TypeChecker::new(env).is_def_eq(expr, reference)
}

fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

fn try_elaborate_decls_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse: {e}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| format!("{e}"))?;
    }
    Ok(())
}

// =============================================================================
// Defect 1 — `.2` off-by-one on Prod. `.1` is the control (was already green).
// =============================================================================

#[test]
fn test_prod_second_field_projection_elaborates() {
    let mut env = prod_env();
    // The literal historical repro: `p.2` reported "index 2 out of bounds".
    try_elaborate_decls_into(&mut env, "def b (p : Nat × Nat) : Nat := p.2")
        .expect("`p.2` on Nat × Nat must elaborate + kernel-check (Prod's second field)");
}

#[test]
fn test_prod_first_field_projection_elaborates() {
    let mut env = prod_env();
    try_elaborate_decls_into(&mut env, "def a (p : Nat × Nat) : Nat := p.1")
        .expect("`p.1` on Nat × Nat must elaborate (control — the first field)");
}

#[test]
fn test_prod_numeric_projections_reduce_to_correct_field() {
    let mut env = prod_env();
    elaborate_decls_into(
        &mut env,
        "def pv : Nat × Nat := Prod.mk 7 3\n\
         def getFst : Nat := pv.1\n\
         def getSnd : Nat := pv.2",
    );

    // Distinct values (7, 3) so an off-by-one reads the wrong number.
    assert!(
        def_eq(&env, &const_("getFst"), &nat_lit(7)),
        "pv.1 must reduce to the first field 7, got {:?}",
        TypeChecker::new(&env).whnf(&const_("getFst")).kind()
    );
    assert!(
        def_eq(&env, &const_("getSnd"), &nat_lit(3)),
        "pv.2 must reduce to the second field 3, got {:?}",
        TypeChecker::new(&env).whnf(&const_("getSnd")).kind()
    );
    assert!(
        !def_eq(&env, &const_("getSnd"), &nat_lit(7)),
        "pv.2 must NOT read the first field (off-by-one guard)"
    );
}

// =============================================================================
// Defect 1 (lexer) — chained numeric projection `p.2.1` = `(p.2).1`, not the
// float `2.1`.
// =============================================================================

#[test]
fn test_chained_numeric_projection_lexes_and_elaborates() {
    let mut env = prod_env();
    // `Nat × Nat × Nat` is `Prod Nat (Prod Nat Nat)`; `p.2.1` reads the first
    // field of the inner pair. This lexed as the float `2.1` before the fix.
    try_elaborate_decls_into(&mut env, "def f (p : Nat × Nat × Nat) : Nat := p.2.1").expect(
        "chained `p.2.1` must lex as (p.2).1 (not the float 2.1) and elaborate + kernel-check",
    );
}

#[test]
fn test_chained_numeric_projection_reduces_to_correct_field() {
    let mut env = prod_env();
    elaborate_decls_into(
        &mut env,
        "def tv : Nat × Nat × Nat := Prod.mk 7 (Prod.mk 3 5)\n\
         def mid : Nat := tv.2.1",
    );
    // tv = (7, (3, 5)); tv.2 = (3, 5); tv.2.1 = 3.
    assert!(
        def_eq(&env, &const_("mid"), &nat_lit(3)),
        "tv.2.1 must reduce to 3 (first field of the inner pair), got {:?}",
        TypeChecker::new(&env).whnf(&const_("mid")).kind()
    );
    assert!(
        !def_eq(&env, &const_("mid"), &nat_lit(7)) && !def_eq(&env, &const_("mid"), &nat_lit(5)),
        "tv.2.1 must be neither the outer field (7) nor the inner second field (5)"
    );
}

// =============================================================================
// Doubly-nested `s.2.2` on `(Nat × Nat) × (Nat × Nat)` — the map's explicit
// case. Two chained SECOND-field projections stress the off-by-one twice.
// =============================================================================

#[test]
fn test_double_second_projection_reduces_to_correct_field() {
    let mut env = prod_env();
    elaborate_decls_into(
        &mut env,
        "def qv : (Nat × Nat) × (Nat × Nat) := Prod.mk (Prod.mk 1 2) (Prod.mk 3 4)\n\
         def d : Nat := qv.2.2",
    );
    // qv = ((1,2),(3,4)); qv.2 = (3,4); qv.2.2 = 4.
    assert!(
        def_eq(&env, &const_("d"), &nat_lit(4)),
        "qv.2.2 must reduce to 4 (second field of the second pair), got {:?}",
        TypeChecker::new(&env).whnf(&const_("d")).kind()
    );
}

#[test]
fn test_mixed_chain_second_then_first_reduces() {
    let mut env = prod_env();
    elaborate_decls_into(
        &mut env,
        "def rv : (Nat × Nat) × (Nat × Nat) := Prod.mk (Prod.mk 1 2) (Prod.mk 3 4)\n\
         def e : Nat := rv.2.1",
    );
    // rv.2 = (3,4); rv.2.1 = 3.
    assert!(
        def_eq(&env, &const_("e"), &nat_lit(3)),
        "rv.2.1 must reduce to 3, got {:?}",
        TypeChecker::new(&env).whnf(&const_("e")).kind()
    );
}
