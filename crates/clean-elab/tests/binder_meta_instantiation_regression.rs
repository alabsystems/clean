// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression lock: **binder-closing sites instantiate assigned metavars/levels
//! before abstracting the binder fvar.**
//!
//! ## The soundness gap this guards (source-elab loose-fvar bug)
//!
//! `InferCtx`'s binder-closing sites in `infer/elab_core.rs` (`elab_lambda`,
//! `elab_pi`, the `dite` branch lambdas, and the `let`/`let rec` bodies) call
//! `X.abstract_fvar(fvar)` to close a binder. `abstract_fvar` walks the raw
//! `Expr` and rewrites occurrences of `fvar` to a bound variable — but a
//! metavariable node `Meta(?m)` is opaque to that walk: it never looks inside
//! `?m`'s *assignment*. So when a metavar in the domain or body was ASSIGNED
//! during elaboration to a term that mentions `fvar` (e.g. an inserted implicit
//! argument unified to the binder, or an unannotated dependent Pi domain unified
//! to `… fvar …`), abstracting *first* leaves the `Meta(?m)` node untouched.
//! When the term is later instantiated (the kernel `add_decl` path does), the
//! assignment surfaces `fvar` as a **loose free variable** inside the now-closed
//! binder — which the kernel rejects with "Declaration … contains free
//! variables", or, for a leaked Pi domain, "expected Sort, inferred Pi(…,
//! FVar(0), …)".
//!
//! The fix instantiates assigned metavars/levels in the domain and body BEFORE
//! `abstract_fvar`, so the fvar is materialized syntactically and abstraction
//! bounds it correctly. Each case below reproduces one binder site; before the
//! fix the declaration left a loose fvar and `add_decl` rejected it, after the
//! fix it elaborates and kernel-checks.
//!
//! These drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`).

use clean_kernel::env::Environment;

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real file pipeline. Ok iff every declaration elaborates AND
/// kernel-checks (the loose-fvar leak manifests as an `add_decl` rejection).
fn try_elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// `elab_lambda` site: the body is an implicit-headed value whose inserted
/// implicit argument unifies to the lambda's binder fvar. `fun m => f` with
/// `f : ∀ {n : Nat}, n = n` elaborates the body to `@f ?n` with `?n := m`; if
/// `?n` is not instantiated before abstracting `m`, the closed lambda hides a
/// loose `m` inside the metavar assignment.
#[test]
fn test_elab_lambda_implicit_arg_metavar_does_not_leak_fvar() {
    try_elaborate(
        "def lam_meta_leak (f : forall {n : Nat}, n = n) : forall (m : Nat), m = m := fun m => f",
    )
    .expect("lambda body with an implicit-arg metavar bound to the binder must close cleanly");
}

/// `elab_pi` site: an unannotated dependent Pi binder (`BAll.imp_right`-shape
/// `forall (m : Nat) h, …`) whose domain metavar unifies to a term mentioning an
/// outer binder. Here `h`'s inferred domain is `m = m` (mentions `m`); if the
/// domain metavar is not instantiated before abstracting `m`, the outer Pi
/// domain leaks a loose `m`.
#[test]
fn test_elab_pi_unannotated_dependent_domain_does_not_leak_fvar() {
    try_elaborate(
        "theorem pi_meta_leak (Q : forall (n : Nat), n = n -> Prop) \
         (pf : forall (m : Nat) (h : m = m), Q m h) : forall (m : Nat) h, Q m h := pf",
    )
    .expect("unannotated dependent Pi domain bound to an outer binder must close cleanly");
}

/// `dite` branch site: a branch body inserts an implicit argument that unifies
/// to the branch's hypothesis fvar (`Decidable.forall_or_left` / `ite_eq_or_eq`
/// shape). In `if h : c then use (pf h) else 0`, elaborating `use (pf h)` inserts
/// `use`'s implicit `{x : c}` and unifies `?x := h` (from `pf h : P h`); the
/// then-branch body then mentions `h` both explicitly and inside the `?x`
/// assignment. If `?x` is not instantiated before abstracting the branch
/// hypothesis, the closed `(fun h => …)` hides a loose `h`.
#[test]
fn test_dite_branch_implicit_arg_metavar_does_not_leak_fvar() {
    try_elaborate(
        "def dite_meta_leak (c : Prop) [Decidable c] (P : c -> Prop) \
         (use : forall {x : c}, P x -> Nat) (pf : forall (x : c), P x) : Nat := \
         if h : c then use (pf h) else 0",
    )
    .expect(
        "dite branch body with an implicit-arg metavar bound to the hypothesis must close cleanly",
    );
}

/// Control: the same shapes with no metavar-to-fvar assignment still elaborate
/// (guards against the instantiate call perturbing the common no-leak path).
#[test]
fn test_plain_binders_still_elaborate() {
    try_elaborate("def plain_lambda : forall (m : Nat), Nat := fun m => m")
        .expect("plain lambda must still elaborate");
    try_elaborate("theorem plain_pi (m : Nat) : m = m := rfl")
        .expect("plain reflexivity must still elaborate");
}
