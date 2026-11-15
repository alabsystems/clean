// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! A bare pattern identifier that merely spells a NON-nullary constructor of
//! the expected type is a binder, not a zero-argument constructor pattern.
//!
//! Regression (clean 0ed84bff1): `classify_match_pattern_name` applied the
//! expected-family shorthand (`name` -> `Expected.name`) to any constructor, so
//! `| H.h mk _ => mk` against a field of type `R` with a two-field `R.mk`
//! became `R.mk` with zero arguments and failed with
//! `ConstructorPatternArityMismatch { expected: 2, actual: 0 }`. In Lean 4 an
//! unresolved bare identifier in a pattern is a binder. The shorthand then
//! applied only to constructors with no explicit fields, so the nullary
//! `| red =>` spelling resolved to `Color.red`.
//!
//! 2026-09-25: the nullary shorthand is refused too. Lean 4 binds `red` there
//! as well (so Lean 4.8.0 rejects `| red => 0 | green => 1` as a redundant
//! alternative), and reading it as `Color.red` proved false theorems about
//! definitions Lean accepts (`| some c => 0 | _ => 1`). The unambiguous
//! spellings — `.red`, `Color.red`, `open Color` — keep the constructor.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => results.iter().for_each(|r| collect_failures(r, out)),
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

fn assert_accepts(source: &str, what: &str) {
    if let Err(e) = elaborate_module(source) {
        panic!("{what} must elaborate + kernel-check, but failed:\n{e}");
    }
}

#[test]
fn bare_name_of_two_field_ctor_binds_the_field() {
    // `rfl` pins the binder semantics: `mk` is the R field, returned as-is.
    assert_accepts(
        r#"
inductive R where
  | mk : Nat → Nat → R

inductive H where
  | h : R → Nat → H

def f : H → R
  | H.h mk _ => mk

theorem f_returns_field : f (H.h (R.mk 1 2) 7) = R.mk 1 2 := rfl
"#,
        "bare `mk` binder over a two-field `R.mk`",
    );
}

#[test]
fn bare_name_of_two_field_ctor_binds_in_term_match() {
    // The trust-soundness shape: the binder shares its name with the field
    // type's constructor (`DeclarationRef.declaration`).
    assert_accepts(
        r#"
inductive DeclarationRef where
  | declaration : Nat → Bool → DeclarationRef

inductive ProjectionHead where
  | exact : DeclarationRef → Nat → Nat → ProjectionHead

def headRef (p : ProjectionHead) : DeclarationRef :=
  match p with
  | ProjectionHead.exact declaration _ _ => declaration

theorem headRef_exact :
    headRef (ProjectionHead.exact (DeclarationRef.declaration 3 true) 4 5)
      = DeclarationRef.declaration 3 true := rfl
"#,
        "bare `declaration` binder in a term-level match",
    );
}

#[test]
fn bare_nullary_ctor_shorthand_is_refused_and_unambiguous_spellings_resolve() {
    // `red` does not resolve by ordinary name resolution: Lean binds it, the
    // shorthand would test it. Refused rather than guessed.
    let error = elaborate_module(
        r#"
inductive Color where
  | red : Color
  | green : Color

def pick : Color → Nat
  | red => 0
  | green => 1
"#,
    )
    .expect_err("bare `red` resolved only through `Color` must be refused");
    assert!(
        error.contains("is a pattern variable in Lean 4") && error.contains("Color.red"),
        "refused for the wrong reason: {error}"
    );
    // If any spelling below were a binder, its first arm would be a
    // catch-all and `pick… Color.green` would reduce to 0, failing `rfl`.
    assert_accepts(
        r#"
inductive Color where
  | red : Color
  | green : Color

def pickDot : Color → Nat
  | .red => 0
  | .green => 1

def pickQual : Color → Nat
  | Color.red => 0
  | Color.green => 1

open Color in
def pickOpen : Color → Nat
  | red => 0
  | green => 1

theorem pickDot_green : pickDot Color.green = 1 := rfl
theorem pickQual_green : pickQual Color.green = 1 := rfl
theorem pickOpen_green : pickOpen Color.green = 1 := rfl
theorem pickOpen_red : pickOpen Color.red = 0 := rfl
"#,
        "dotted, qualified and opened constructor spellings",
    );
}

#[test]
fn bare_nullary_ctor_shorthand_rejects_a_wrong_reduction() {
    // Red control for the test above: the shorthand must not be a catch-all.
    let result = elaborate_module(
        r#"
inductive Color where
  | red : Color
  | green : Color

open Color in
def pick : Color → Nat
  | red => 0
  | green => 1

theorem pick_green_wrong : pick Color.green = 0 := rfl
"#,
    );
    assert!(
        matches!(&result, Err(error) if !error.contains("is a pattern variable in Lean 4")),
        "`pick Color.green = 0` must not kernel-check: {result:?}"
    );
}
