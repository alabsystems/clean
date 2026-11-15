// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Fin.ofNat` signature drift: Lean's `tests/elab/788.lean` and its controls.
//!
//! Pinned Lean (`leanprover--lean4---v4.30.0-rc2`) declares
//! `Fin.ofNat (n : Nat) [NeZero n] (a : Nat) : Fin n`. Clean's builtin prelude
//! (`clean-kernel` `env/data.rs`) keeps the Lean v4.8 signature
//! `Fin.ofNat {n : Nat} (a : Nat) : Fin (Nat.succ n)`, which the `UInt<w>.ofNat`
//! re-verification and the compiler's `Fin.ofNat` decode depend on, and it has
//! no `NeZero` at all. So `Fin.ofNat _ 0` (788.lean line 4) gives Clean's
//! constant two explicit arguments where it has one.
//!
//! Clean accepted 788.lean until 8c866b7fe removed the elaborator's rule that,
//! when an application had more arguments than explicit binders, the surplus
//! filled LEADING IMPLICIT binders. Lean has no such rule (`elabAppArgs` never
//! lets the argument count change what an implicit binder means), and the rule
//! accepted the wrong program too: under it `Fin.ofNat 8 0 : Fin 9` read as
//! `@Fin.ofNat 8 0 : Fin (Nat.succ 8)`, while pinned Lean reads `Fin.ofNat 8 0`
//! at `Fin 8` and rejects it. The refusal below is therefore correct for the
//! signature Clean has; 788.lean agrees again only when the builtin prelude
//! carries Lean's own `Fin.ofNat` (with `NeZero`), not by reviving the rule.
//!
//! Each arm was run through pinned Lean (exit status in the comment) and through
//! a release `clean check --json --lean-world v4.30.0-rc2`, which refuses each
//! `Fin.ofNat` arm with the same `TooManyArguments` this file pins.
//!
//! Not pinned here, because it is a false acceptance rather than behaviour to
//! keep: Clean accepts the v4.8 spelling `example : Fin 9 := Fin.ofNat 0`,
//! which pinned Lean rejects (`failed to synthesize NeZero 0`).

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// Parse `code`, then preprocess, elaborate and register each declaration
/// over the builtin prelude, as `clean check` does for a file without imports.
fn elab_prelude(code: &str) -> Vec<Result<ElabResult, ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("test source parses");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

/// The one declaration of `code` must be refused with `TooManyArguments`
/// against Clean's v4.8 `Fin (Nat.succ _)` result type.
fn assert_fin_ofnat_arity_refusal(code: &str, label: &str) {
    let results = elab_prelude(code);
    assert_eq!(results.len(), 1, "{label}: expected one declaration result");
    let err = results
        .into_iter()
        .next()
        .and_then(Result::err)
        .unwrap_or_else(|| panic!("{label}: must be refused while Clean's Fin.ofNat is v4.8's"));
    match err {
        ElabError::TooManyArguments {
            func_type,
            remaining_args,
        } => {
            assert_eq!(remaining_args, 1, "{label}: one surplus argument");
            assert!(
                func_type.starts_with("Fin (Nat.succ "),
                "{label}: refused at Clean's v4.8 result type, got {func_type}"
            );
        }
        other => panic!("{label}: expected TooManyArguments, got {other:?}"),
    }
}

/// 788.lean line 4. Pinned Lean ACCEPTS (exit 0); Clean refuses until its
/// prelude carries Lean's `Fin.ofNat`. Fails loudly the day that changes.
#[test]
fn test_fin_ofnat_788_hole_size_refused_under_v48_signature() {
    assert_fin_ofnat_arity_refusal(
        "example : (0 : Fin 9) = (Fin.ofNat _ 0) := by\n  simp only [OfNat.ofNat]\n",
        "788.lean line 4",
    );
}

/// 788.lean's first example (`(0 : Nat) = Nat.zero`) does not involve
/// `Fin.ofNat` and must keep elaborating. Pinned Lean accepts.
#[test]
fn test_fin_ofnat_788_nat_example_still_elaborates() {
    let results = elab_prelude("example : (0 : Nat) = Nat.zero := by\n  simp only [OfNat.ofNat]\n");
    assert_eq!(results.len(), 1);
    if let Some(Err(e)) = results.first() {
        panic!("788.lean line 1 must elaborate: {e:?}");
    }
}

/// NEGATIVE CONTROL: pinned Lean REJECTS (exit 1: `Fin.ofNat 8 0 : Fin 8`).
/// The removed surplus-fills-implicit rule accepted it as
/// `@Fin.ofNat 8 0 : Fin 9`.
#[test]
fn test_fin_ofnat_explicit_size_off_by_one_refused() {
    assert_fin_ofnat_arity_refusal(
        "example : Fin 9 := Fin.ofNat 8 0\n",
        "Fin.ofNat 8 0 : Fin 9",
    );
}

/// NEGATIVE CONTROL inside the 788 shape: pinned Lean REJECTS (exit 1).
#[test]
fn test_fin_ofnat_788_shape_off_by_one_refused() {
    assert_fin_ofnat_arity_refusal(
        "example : (0 : Fin 9) = (Fin.ofNat 8 0) := by\n  simp only [OfNat.ofNat]\n",
        "788 shape with Fin.ofNat 8 0",
    );
}
