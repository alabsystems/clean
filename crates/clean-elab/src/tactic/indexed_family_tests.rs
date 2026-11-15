// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `cases` / `induction` on **indexed** inductive families (RC-S).
//!
//! # What was broken
//!
//! An eliminator for a family with `k > 0` indices takes those indices as real
//! arguments — `T.casesOn params motive INDICES major minors…`,
//! `T.rec params motive minors… INDICES major` — and its motive abstracts over
//! them. `cases_core` and `assemble_induction_proof` built a one-binder motive
//! and passed **no** indices at all, so the major premise slid into the first
//! index slot and every later argument moved one position left. The assembled
//! term's inferred type came out as an unapplied `Pi`, with a still-open minor
//! premise metavariable printed through its FVar encoding —
//! `MetaState::to_fvar(MetaId(1))` = `FVarId(9223372036854775809)` = `2^63+1` —
//! sitting in the major premise's place. That number is the routine meta-FVar
//! tag (`META_FVAR_TAG | 1`), **not** a fabricated free variable: chasing it as
//! an fvar-allocation bug leads nowhere, and it is unrelated to the identical
//! bit pattern that surfaced in the `rw`/`simp` imported-lemma arbiter.
//!
//! # Why these fixtures, and not `Nat` / `List` / `Option`
//!
//! `Nat`, `List`, `Option`, `Or`, `Sum`, `And`, `Prod`, every `structure` — all
//! have **zero** indices, so they pass with or without the fix and prove
//! nothing here.
//!
//! The first four tests are a matched **control pair**: `IdxT` and `ParT` have
//! the same two constructors, the same field arities (a nullary one and one
//! binding `(n : Nat)` plus a recursive field), the same `with` block and the
//! same trivial target. They differ in exactly one thing — whether the varying
//! `Nat` is an **index** or a **parameter**. Pre-fix the two `ParT` tests pass
//! and the two `IdxT` tests fail; that is what proves the index is the cause
//! rather than the prelude, the `with`-block dispatcher, `close_fvars`, or the
//! per-branch field-FVar numbering fixed in #3528.
//!
//! The later tests go further than "the spine type-checks": `Rel2.base`
//! inhabits only `Rel2 0 0` and `Vec.nil` only `Vec a 0`, so those branches
//! close **iff** the motive abstracted the index and the branch goal came back
//! specialized. `vec_copy` closes its recursive branch with the induction
//! hypothesis, which is well-typed only if the IH was formed at the recursive
//! FIELD's index (`Vec a m`) rather than at the major premise's (`Vec a n`).

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Parse, preprocess and elaborate every declaration in `code` against a
/// prelude environment, returning the environment and the per-declaration
/// results.
fn elab(code: &str) -> (Environment, Vec<Result<ElabResult, crate::ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    let results = decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect();
    (env, results)
}

/// Every declaration elaborated and kernel-checked, `name` is registered, and
/// its transitive axiom closure contains no `sorry` / `sorryAx`.
fn assert_green(code: &str, name: &str, context: &str) {
    let (env, results) = elab(code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "{context}: declaration {i} failed: {:?}",
            r.as_ref()
                .expect_err("failed declaration must have an error")
        );
    }
    let n = Name::from_string(name);
    assert!(
        env.get_const(&n).is_some(),
        "{context}: '{name}' should be registered after a kernel-checked proof"
    );
    let deps: Vec<String> = env
        .axiom_deps(&n)
        .expect("registered constant has an axiom closure")
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        !deps.iter().any(|d| d == "sorry" || d == "sorryAx"),
        "{context}: '{name}' must not depend on sorry/sorryAx; closure = {deps:?}"
    );
}

/// A one-**index** family: the trailing `Nat` is constrained differently by each
/// constructor. This is the shape of `Nat.le`, `List.Sublist`, `Vector`,
/// `Relation.TransGen`.
const IDX_T: &str = r"
inductive IdxT : Nat → Type where
  | a : IdxT 0
  | b : (n : Nat) → IdxT n → IdxT (n + 1)
";

/// CONTROL for [`IDX_T`]: the same two constructors and the same field arities,
/// with the trailing `Nat` declared as a **parameter** instead — so the family
/// has zero indices and takes the historical one-binder-motive path.
const PAR_T: &str = r"
inductive ParT (k : Nat) : Type where
  | a : ParT k
  | b : (n : Nat) → ParT k → ParT k
";

// ---------------------------------------------------------------------------
// The matched control pair
// ---------------------------------------------------------------------------

/// RED before the fix: `IdxT.casesOn` was applied as
/// `motive major minor_a minor_b`, putting the major premise in the index slot.
/// Reported as
/// `TypeMismatch { expected: True, actual: Pi(…, FVar(FVarId(9223372036854775809))) }`.
#[test]
fn test_cases_indexed_family_kernel_checks() {
    let code = format!(
        "{IDX_T}
theorem idx_cases (m : Nat) (h : IdxT m) : True := by
  cases h with
  | a => trivial
  | b n hn => trivial
"
    );
    assert_green(&code, "idx_cases", "cases on a one-index family");
}

/// CONTROL: identical shape with a parameter in place of the index. Green on
/// both binaries — this is what isolates the failure above to index handling.
#[test]
fn test_cases_parameterized_control_is_green_either_way() {
    let code = format!(
        "{PAR_T}
theorem par_cases (k : Nat) (h : ParT k) : True := by
  cases h with
  | a => trivial
  | b n hn => trivial
"
    );
    assert_green(&code, "par_cases", "cases on the parameterized control");
}

/// Same defect on the recursor path: `T.rec` takes the indices AFTER the minor
/// premises, a separate insertion point in a separate function
/// (`assemble_induction_proof`), so the `cases` test above proves nothing here.
#[test]
fn test_induction_indexed_family_kernel_checks() {
    let code = format!(
        "{IDX_T}
theorem idx_induction (m : Nat) (h : IdxT m) : True := by
  induction h with
  | a => trivial
  | b n hn ih => trivial
"
    );
    assert_green(&code, "idx_induction", "induction on a one-index family");
}

/// CONTROL for the recursor path. `ParT` binds a field in its second
/// constructor, so this also re-covers the per-branch FVar numbering of #3528
/// and stays green either way.
#[test]
fn test_induction_parameterized_control_is_green_either_way() {
    let code = format!(
        "{PAR_T}
theorem par_induction (k : Nat) (h : ParT k) : True := by
  induction h with
  | a => trivial
  | b n hn ih => trivial
"
    );
    assert_green(
        &code,
        "par_induction",
        "induction on the parameterized control",
    );
}

// ---------------------------------------------------------------------------
// Index SPECIALIZATION, not merely a well-formed spine
// ---------------------------------------------------------------------------

/// Two indices, no parameters — exercises the whole index telescope (motive
/// binder chain and eliminator argument run), and pins specialization:
/// `Rel2.base : Rel2 0 0` closes the `base` branch only if that branch's goal
/// came back as `Rel2 0 0` rather than the original `Rel2 x y`.
#[test]
fn test_cases_two_index_family_specializes_each_branch() {
    let code = r"
inductive Rel2 : Nat → Nat → Prop where
  | base : Rel2 0 0
  | step : (a : Nat) → (b : Nat) → Rel2 a b → Rel2 (a + 1) (b + 1)

theorem rel2_id (x y : Nat) (h : Rel2 x y) : Rel2 x y := by
  cases h with
  | base => exact Rel2.base
  | step a b h2 => exact Rel2.step a b h2
";
    assert_green(code, "rel2_id", "cases on a two-index family");
}

/// An index over `Type` rather than `Prop`: the motive's return universe and
/// the eliminator's extra level parameter are on a different path from the
/// `Prop` tests. `Vec.nil : Vec a 0` again only closes a specialized branch.
#[test]
fn test_cases_indexed_type_family_specializes_each_branch() {
    let code = r"
inductive Vec (a : Type) : Nat → Type where
  | nil : Vec a 0
  | cons : (n : Nat) → a → Vec a n → Vec a (n + 1)

def vec_id (a : Type) (n : Nat) (v : Vec a n) : Vec a n := by
  cases v with
  | nil => exact Vec.nil
  | cons m x t => exact Vec.cons m x t
";
    assert_green(code, "vec_id", "cases on an indexed Type family");
}

/// The induction hypothesis of an indexed family must be the motive applied at
/// the RECURSIVE FIELD's own index — `Vec a m`, not the major premise's
/// `Vec a n`. `exact Vec.cons m x ih` type-checks only under the former.
#[test]
fn test_induction_indexed_type_family_ih_carries_the_fields_index() {
    let code = r"
inductive Vec (a : Type) : Nat → Type where
  | nil : Vec a 0
  | cons : (n : Nat) → a → Vec a n → Vec a (n + 1)

def vec_copy (a : Type) (n : Nat) (v : Vec a n) : Vec a n := by
  induction v with
  | nil => exact Vec.nil
  | cons m x t ih => exact Vec.cons m x ih
";
    assert_green(code, "vec_copy", "induction on an indexed Type family");
}
