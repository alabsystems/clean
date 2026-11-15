// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end pins for **imported `export` aliases in the TACTIC name path**.
//!
//! ## The gap
//!
//! `Lean.aliasExtension` rows decoded from an `.olean` land in the kernel
//! environment's own alias table (`Environment::register_export_alias`,
//! written by `clean-olean`'s `register_real_alias_entries`). Before this
//! file's fix the ONLY consumer of `Environment::get_export_alias` in the
//! whole elaborator was the TERM path (`infer/elab_core.rs`): the tactic-side
//! resolver `name_resolution::resolve_identifier` consulted the in-file
//! `NamespaceState` table and never the environment's, so a lemma named
//! through an imported alias resolved to nothing and was dropped WITHOUT a
//! diagnostic — `simp [compl]` behaved exactly like a bare `simp`.
//!
//! Measured at Mathlib (`Mathlib/Order/Basic.lean`, `compl_lt`/`compl_le`/
//! `compl_gt`/`compl_ge`): `simp [compl]` and `simp` left the SAME residual
//! goal, while `simp [Compl.compl]` — the fully qualified spelling — did
//! unfold. `compl` reaches the file through `export Compl (compl)` in
//! `Mathlib/Order/Notation.lean`. The asymmetry that makes it invisible is
//! that the statement elaborates fine: the term path resolves the alias.
//!
//! ## What the fixture stands in for
//!
//! Registering the alias directly on the environment is exactly the state an
//! import leaves behind (`clean-olean` calls the same method), and keeps this
//! file prelude-only and sub-second instead of paying for `import Init`.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Drive the real file pipeline (`clean check`'s own path).
fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// The declarations an imported module would have supplied.
const IMPORTED_SOURCE: &str = concat!(
    "namespace Ns\n",
    "axiom Gg : Nat -> Nat\n",
    "axiom Hh : Nat -> Nat\n",
    "axiom Kk : Nat -> Nat\n",
    "axiom ghEq : forall (n : Nat), Ns.Gg n = Ns.Hh n\n",
    "axiom gkEq : forall (n : Nat), Ns.Gg n = Ns.Kk n\n",
    "end Ns\n",
    "axiom shadowEq : forall (n : Nat), Ns.Gg n = Ns.Hh n\n",
);

/// A prelude environment carrying `IMPORTED_SOURCE` plus the alias rows an
/// `.olean`'s `Lean.aliasExtension` would have decoded.
///
/// `ghEq` is the plain alias (`export Ns (ghEq)`). `shadowEq` deliberately
/// COLLIDES with a real root-level constant and points somewhere else, so the
/// precedence control below can tell which one won.
fn imported_env() -> Environment {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, IMPORTED_SOURCE)
        .expect("fixture declarations must elaborate on a prelude environment");
    env.register_export_alias(Name::from_string("ghEq"), Name::from_string("Ns.ghEq"));
    env.register_export_alias(Name::from_string("shadowEq"), Name::from_string("Ns.gkEq"));
    env
}

fn expect_registers(source: &str) {
    let mut env = imported_env();
    if let Err(e) = try_elaborate_into(&mut env, source) {
        panic!("must elaborate and kernel-register, got: {e}\n--- source ---\n{source}");
    }
}

fn expect_fails(source: &str) -> String {
    let mut env = imported_env();
    match try_elaborate_into(&mut env, source) {
        Ok(()) => panic!("must NOT elaborate\n--- source ---\n{source}"),
        Err(e) => e,
    }
}

/// THE GAP: `simp [<imported alias>]` must reach the aliased lemma.
///
/// Before the fix this failed with `simp made no progress` — the name was
/// dropped silently and the tactic was a bare `simp`.
#[test]
fn test_simp_imported_export_alias_lemma_rewrites() {
    expect_registers("theorem t_alias (n : Nat) : Ns.Gg n = Ns.Hh n := by simp [ghEq]\n");
}

/// The same alias through `rw`: the fix sits in the SHARED tactic resolver
/// (`resolve_global_name` -> `resolve_identifier`), so `rw` is repaired with
/// `simp`, not separately.
#[test]
fn test_rw_imported_export_alias_lemma_rewrites() {
    expect_registers("theorem t_rw (n : Nat) : Ns.Gg n = Ns.Hh n := by rw [ghEq]\n");
}

/// CONTROL: the fully qualified spelling passed before the fix and must keep
/// passing. Its passing while the alias spelling failed is what made the gap
/// a silent one.
#[test]
fn test_simp_qualified_name_still_rewrites() {
    expect_registers("theorem t_qualified (n : Nat) : Ns.Gg n = Ns.Hh n := by simp [Ns.ghEq]\n");
}

/// PRECEDENCE CONTROL: a real root-level constant OUTRANKS an imported alias
/// of the same short name.
///
/// `shadowEq` exists as a root constant proving `Gg n = Hh n` AND as an alias
/// pointing at `Ns.gkEq : Gg n = Kk n`. The goal is closable only by the
/// former: if the alias were consulted first, simp would rewrite the goal to
/// `Ns.Kk n = Ns.Hh n` and fail. The alias consult therefore has to run after
/// the root-constant lookup, which is where this fix puts it.
///
/// DIVERGENCE, stated rather than implied, on two counts. Against the pinned
/// `lean` v4.30.0-rc2 this exact collision is an `Ambiguous term` ERROR,
/// because Lean folds constants and aliases into ONE candidate set per
/// resolution stage; Clean's tactic resolver has no ambiguity channel, so it
/// keeps the constant it already resolved. And the TERM path
/// (`infer/elab_core.rs`, step 2c) consults the imported table one step
/// EARLIER, ahead of the root-level constant, so on a genuine collision the
/// two paths would disagree. Both are deliberately the NARROW side at THIS
/// stage: at the root, keeping the constant changes nothing that resolved
/// before the fix, whereas letting the alias win would silently retarget an
/// existing name.
///
/// That is a statement about the ROOT stage only, and it must not be read as
/// one about the resolver. The namespace-prefix walk consults the imported
/// table before the root lookup is reached, so an alias found there DOES
/// outrank a root constant of the same short name — which is Lean's rule, and
/// is pinned with its control in `tests/simp_proj_eta_adversarial_e2e.rs`.
#[test]
fn test_root_constant_outranks_imported_alias_of_same_name() {
    expect_registers("theorem t_shadow (n : Nat) : Ns.Gg n = Ns.Hh n := by simp [shadowEq]\n");
}

/// An alias whose TARGET does not exist resolves to nothing, exactly as
/// before: the alias table is consulted only to find a constant that is
/// really there, so a stale row can never make a name resolve.
#[test]
fn test_imported_alias_with_missing_target_is_not_resolved() {
    let mut env = imported_env();
    env.register_export_alias(
        Name::from_string("danglEq"),
        Name::from_string("Ns.noSuchEq"),
    );
    let err = match try_elaborate_into(
        &mut env,
        "theorem t_dangling (n : Nat) : Ns.Gg n = Ns.Hh n := by simp [danglEq]\n",
    ) {
        Ok(()) => panic!("a dangling alias must not close the goal"),
        Err(e) => e,
    };
    assert!(
        !err.contains("panic"),
        "a dangling alias must fail cleanly, got: {err}"
    );
}

/// SOUNDNESS GATE: the alias makes a lemma REACHABLE; it does not make a
/// false goal provable. `Ns.Gg n = Ns.Kk n` is not derivable from `ghEq`
/// alone, so this must still fail.
#[test]
fn test_simp_imported_alias_does_not_close_an_underivable_goal() {
    let _ = expect_fails("theorem t_false (n : Nat) : Ns.Gg n = Ns.Kk n := by simp [ghEq]\n");
}
