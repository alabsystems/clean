// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An UNTYPED binder's own type is solved from the first place the binder is
//! USED as a type — and is a HARD ERROR when nothing uses it (task #65).
//!
//! # What was broken
//!
//! `def idA {alpha} (x : alpha) : alpha := x` parses correctly (the dotless
//! `{alpha}` became an implicit binder in `f13fa1ffb`) and then died:
//!
//! ```text
//! $ clean check repro.lean
//!   0 passed, 1 failed
//!   ✗ idA: elaboration error at line 1: def idA: elaboration left unresolved
//!     variables (unsolved metavariables ?[0])
//! ```
//!
//! `?[0]` is `alpha`'s own type. The binder was elaborated as a fresh
//! metavariable `?α : Sort ?u` and then abandoned: nothing in Clean ever read
//! `(x : alpha)` as a CONSTRAINT on `?α`.
//!
//! # Lean's rule, measured — solve-from-use, not a `Sort u` default
//!
//! Pinned `lean` v4.30.0-rc2, `set_option pp.parens true`:
//!
//! ```text
//! def m {a} (x : a) : a := x            => def m.{u_1} : {a : (Sort u_1)} → (a → a)
//! def n {a} (x : a) (l : List a) : Nat  => def n.{u_1} : {a : (Type u_1)} → …
//! def k {a} (x : Nat) : Nat := x        => error: Failed to infer type of binder a
//! ```
//!
//! The `def k` row is why this is not a default. Defaulting an unconstrained
//! `{a}` to `Sort ?u` would silently ACCEPT a declaration Lean rejects, and a
//! check that cannot say no is the failure mode this repo has been bitten by
//! repeatedly. So the refusal is pinned here with the same weight as the fix:
//! `test_unconstrained_untyped_binder_is_refused` is the negative control, and
//! without it every test below is satisfied by a blanket default.
//!
//! # Why the assertions are structural
//!
//! Each positive case asserts on the REGISTERED `ConstantInfo` — the leading
//! Pi's domain is an `ExprKind::Sort`, and for the `List` row that sort's level
//! is a `Succ` (i.e. `Type _`, not `Prop`/`Sort 0`). Nothing here matches a
//! pretty-printed string: a printer can render a metavariable and a solved sort
//! identically, so a printer match could not tell the fix from the bug.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, ExprKind, Level, Name};
use clean_parser::parse_file;

/// Elaborate every declaration of `src` against the kernel prelude through the
/// same `preprocess` → `elaborate_with_context` pair `clean check` uses, and
/// return `(env, per-declaration verdict)` in source order.
fn elab_source(label: &str, src: &str) -> (Environment, Vec<(String, Result<(), String>)>) {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("{label} must parse: {e}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        ElabResult::Skipped => {}
                        other => panic!("{label}: unexpected leaf {other:?}"),
                    }
                }
            }
            Err(error) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| format!("<decl {}>", verdicts.len()), ToString::to_string);
                verdicts.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    (env, verdicts)
}

/// Elaborate one declaration and require it to REGISTER, returning the env.
fn must_register(label: &str, src: &str) -> Environment {
    let (env, verdicts) = elab_source(label, src);
    assert_eq!(
        verdicts.len(),
        1,
        "{label}: expected exactly one declaration"
    );
    verdicts[0]
        .1
        .as_ref()
        .unwrap_or_else(|e| panic!("{label}: must elaborate, got: {e}"));
    env
}

/// Elaborate one declaration and require it to be REFUSED, returning the error.
fn must_fail(label: &str, src: &str) -> String {
    let (_, verdicts) = elab_source(label, src);
    assert_eq!(
        verdicts.len(),
        1,
        "{label}: expected exactly one declaration"
    );
    match &verdicts[0].1 {
        Err(e) => e.clone(),
        Ok(()) => panic!("{label}: must be REFUSED — it registered instead"),
    }
}

/// The leading Pi domain of a registered constant, structurally.
fn leading_domain(env: &Environment, name: &str) -> clean_kernel::Expr {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"));
    match info.type_.kind() {
        ExprKind::Pi(_, domain, _) => domain.as_ref().clone(),
        other => panic!("{name}: expected a Pi type, got {other:?}"),
    }
}

fn level_param_count(env: &Environment, name: &str) -> usize {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"))
        .level_params
        .len()
}

/// The reproducer. `{alpha}` is solved from `(x : alpha)`, the very next
/// binder — not from the body.
#[test]
fn test_untyped_binder_solved_from_next_binder() {
    let env = must_register("idA", "def idA {alpha} (x : alpha) : alpha := x\n");
    let domain = leading_domain(&env, "idA");
    assert!(
        matches!(domain.kind(), ExprKind::Sort(_)),
        "idA: `{{alpha}}`'s domain must be solved to a Sort, got {:?}",
        domain.kind()
    );
    assert_eq!(
        level_param_count(&env, "idA"),
        1,
        "idA: Lean registers `def idA.{{u_1}} : {{a : Sort u_1}} → a → a` — one \
         universe parameter, not two. A second one means the metavariable's own \
         declared level `Sort ?u` was left free instead of being forced to \
         `?v + 1` by the assignment."
    );
}

/// `List a` forces `Sort ?v` to narrow to `Type _`. Lean prints
/// `{a : Type u_1}`, i.e. `Sort (u_1 + 1)`, so the level must be a `Succ`.
#[test]
fn test_untyped_binder_narrowed_to_type_by_list_use() {
    let env = must_register("n1", "def n1 {a} (x : a) (l : List a) : Nat := 0\n");
    let domain = leading_domain(&env, "n1");
    match domain.kind() {
        ExprKind::Sort(level) => assert!(
            matches!(level, Level::Succ(_)),
            "n1: `List a` forces `Type _`; expected Sort(Succ(..)), got Sort({level:?})"
        ),
        other => panic!("n1: expected a solved Sort domain, got {other:?}"),
    }
}

/// THE NEGATIVE CONTROL. Nothing uses `{a}` as a type, so there is nothing to
/// solve it from and Lean errors ("Failed to infer type of binder a"). A
/// `Sort u` DEFAULT would accept this; the solve-from-use rule must not.
#[test]
fn test_unconstrained_untyped_binder_is_refused() {
    let err = must_fail("k1", "def k1 {a} (x : Nat) : Nat := x\n");
    assert!(
        err.contains("unresolved") || err.contains("nsolved"),
        "k1: the refusal must still name the unsolved binder type; got: {err}"
    );
}

/// The same refusal for an unconstrained binder that shares its group with one
/// that IS solved (`{a b}`, with only `a` used) — so the refusal is per-binder,
/// not "the declaration has no untyped binder anywhere".
#[test]
fn test_partially_constrained_untyped_binders_still_refused() {
    let err = must_fail("k2", "def k2 {a b} (x : a) : a := x\n");
    assert!(
        err.contains("unresolved") || err.contains("nsolved"),
        "k2: `b` is used nowhere and must still be refused; got: {err}"
    );
}

/// Use as a Pi DOMAIN (`∀ x : alpha, …`), not as a binder annotation. This is
/// the shape `Mathlib/Data/Subtype.lean`'s `restrict_apply` hits through
/// `(f : ∀ x, β x)`, and it is a different elaboration site (`elab_pi`).
#[test]
fn test_untyped_binder_solved_from_pi_domain_use() {
    let env = must_register(
        "a3",
        "def a3 {alpha} (f : forall x : alpha, Nat) : Nat := 0\n",
    );
    let domain = leading_domain(&env, "a3");
    assert!(
        matches!(domain.kind(), ExprKind::Sort(_)),
        "a3: a Pi domain use must solve `{{alpha}}`, got {:?}",
        domain.kind()
    );
}

/// Use as a LAMBDA domain (`fun (x : alpha) => …`), the third site.
///
/// The shape is chosen so the lambda is the ONLY use: no declared return type,
/// and the one other binder is `Nat`. A spelling like
/// `def lam {alpha} (y : alpha) := (fun (x : alpha) => x) y` would be solved by
/// the `(y : alpha)` binder before the lambda is ever reached, and would then
/// pass with the lambda site deleted — i.e. it would not exercise it.
#[test]
fn test_untyped_binder_solved_from_lambda_domain_use() {
    let env = must_register(
        "lam11",
        "def lam11 {alpha} (k : Nat) := (fun (x : alpha) => k)\n",
    );
    let domain = leading_domain(&env, "lam11");
    assert!(
        matches!(domain.kind(), ExprKind::Sort(_)),
        "lam11: a lambda domain use must solve `{{alpha}}`, got {:?}",
        domain.kind()
    );
}

/// The TACTIC half, and the second wall behind this brick. `by rfl` opens a
/// `ProofState`, and the locals crossing that bridge were instantiated for
/// LEVELS only — so a local whose type is an expression metavariable the
/// ElabCtx had already SOLVED arrived spelled as the raw metavariable, and the
/// assembled proof died its kernel re-check with
/// `TypeMismatch { expected: Sort(?u_1), inferred: FVar(9223372036854775808) }`
/// (that number is `2^63`, a metavariable in its fvar encoding).
///
/// `test_untyped_binder_term_spelling_is_the_bridge_control` is the control
/// that localizes it: the identical theorem with a TERM body never crosses the
/// bridge and passed throughout.
#[test]
fn test_untyped_binder_survives_the_tactic_bridge() {
    let env = must_register(
        "id_tac",
        "theorem id_tac {alpha} (x : alpha) : x = x := by rfl\n",
    );
    let domain = leading_domain(&env, "id_tac");
    assert!(
        matches!(domain.kind(), ExprKind::Sort(_)),
        "id_tac: `{{alpha}}`'s domain must be solved to a Sort, got {:?}",
        domain.kind()
    );
}

/// The control for the test above: same theorem, TERM body, no tactic bridge.
#[test]
fn test_untyped_binder_term_spelling_is_the_bridge_control() {
    let env = must_register(
        "id_term",
        "theorem id_term {alpha} (x : alpha) : x = x := rfl\n",
    );
    let domain = leading_domain(&env, "id_term");
    assert!(
        matches!(domain.kind(), ExprKind::Sort(_)),
        "id_term: `{{alpha}}`'s domain must be solved to a Sort, got {:?}",
        domain.kind()
    );
}

/// The three ANNOTATED controls that already passed before this brick. They are
/// the non-vacuousness evidence: the fix must not have been "accept everything".
#[test]
fn test_annotated_binder_controls_still_register() {
    for (label, src) in [
        ("idB", "def idB {alpha : Type} (x : alpha) : alpha := x\n"),
        (
            "idC",
            "def idC.{u} {alpha : Sort u} (x : alpha) : alpha := x\n",
        ),
        ("idD", "def idD {alpha : Sort _} (x : alpha) : alpha := x\n"),
    ] {
        let env = must_register(label, src);
        let domain = leading_domain(&env, label);
        assert!(
            matches!(domain.kind(), ExprKind::Sort(_)),
            "{label}: annotated control must keep its Sort domain, got {:?}",
            domain.kind()
        );
    }
}
