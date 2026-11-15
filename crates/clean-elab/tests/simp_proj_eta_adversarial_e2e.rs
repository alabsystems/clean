// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ADVERSARIAL pins for the three W3F changes — the near-miss shapes the
//! package's own fixtures do not reach.
//!
//! Every arm here was ground-truthed against the pinned
//! `leanprover--lean4---v4.30.0-rc2` binary before it was written; the probe
//! and Lean's verdict are quoted on each test.
//!
//! What is covered that the package's files do not cover:
//!
//! * **Field SELECTION.** `proj_reduce::reduce_proj` reads
//!   `args[num_params + idx]`. A one-field class cannot tell a wrong offset
//!   from a right one, and the package's fixtures are all one-field. A
//!   two-field class whose fields have the SAME type makes a wrong offset a
//!   silent WRONG VALUE, which is the failure mode `CLAUDE.md`'s corpus rule
//!   names explicitly.
//! * **The SECOND `reduce_proj` call**, on the node rebuilt after the
//!   congruence descent. Only a NESTED projection reaches it: the outer node's
//!   structure argument is itself a `Proj`, so the constant-head pre-check
//!   refuses it on the way in and it can only reduce after the inner one has.
//! * **The transparency ceiling at a non-instance.** `whnf_instances` unfolds
//!   `@[reducible]` definitions and REGISTERED INSTANCES; a class-typed plain
//!   `def` must stay folded, and Lean agrees (it warns that such a `def` must
//!   be marked `@[reducible]`/`@[implicit_reducible]`, then leaves the goal).
//! * **Eta at more than one binder**, and an eta-reduced pattern binding a
//!   LAMBDA rather than a function symbol.
//! * **Alias precedence ACROSS resolution stages** — an imported alias reached
//!   at a namespace prefix outranks a root constant of the same short name,
//!   which the root-level rule's "an alias can only add a resolution" reading
//!   does not cover. Ground-truthed: Lean resolves to the alias target.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

fn try_elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
}

fn expect_registers(source: &str) {
    if let Err(e) = try_elaborate(source) {
        panic!("must elaborate and kernel-register, got: {e}\n--- source ---\n{source}");
    }
}

fn expect_fails(source: &str, why: &str) {
    if try_elaborate(source).is_ok() {
        panic!("{why}\n--- source ---\n{source}");
    }
}

// ---------------------------------------------------------------------------
// Projection reduction
// ---------------------------------------------------------------------------

/// Two fields of the SAME type, so selecting the wrong one is well typed and
/// silent. `Rr` and `Qq` are distinct opaque axioms, so only the declared
/// field's value can close each goal by `rfl`.
const TWO_FIELDS: &str = concat!(
    "axiom Rr : Prop -> Prop\n",
    "axiom Qq : Prop -> Prop\n",
    "axiom Pp : Nat -> Prop\n",
    "class Two (A : Type) where\n",
    "  fstf : (A -> Prop) -> (A -> Prop)\n",
    "  sndf : (A -> Prop) -> (A -> Prop)\n",
    "instance instTwoNat : Two Nat where\n",
    "  fstf := fun f => fun a => Rr (f a)\n",
    "  sndf := fun f => fun a => Qq (f a)\n",
);

/// Field 0 of a class with ONE parameter: `args[num_params + 0]`.
///
/// Pinned Lean (`projfield.lean`, exit 0): `simp [Two.fstf]` closes
/// `Two.fstf Pp n = Rr (Pp n)`.
#[test]
fn test_simp_projection_selects_field_zero_of_a_two_field_class() {
    expect_registers(&format!(
        "{TWO_FIELDS}theorem t_f (n : Nat) : Two.fstf Pp n = Rr (Pp n) := by simp [Two.fstf]\n"
    ));
}

/// Field 1: `args[num_params + 1]`. An offset that ignored `num_params` would
/// hand back the class's TYPE argument here, and one that ignored `idx` would
/// hand back `fstf` — both silently.
///
/// Pinned Lean (`projfield.lean`, exit 0).
#[test]
fn test_simp_projection_selects_field_one_of_a_two_field_class() {
    expect_registers(&format!(
        "{TWO_FIELDS}theorem t_s (n : Nat) : Two.sndf Pp n = Qq (Pp n) := by simp [Two.sndf]\n"
    ));
}

/// THE WRONG-VALUE DETECTOR: `fstf` must not produce `sndf`'s value. Without
/// this arm the two tests above pass under an off-by-one that swaps them.
///
/// Pinned Lean (`projfield_bad.lean`, exit 1, `unsolved goals`).
#[test]
fn test_simp_projection_does_not_return_a_neighbouring_field() {
    expect_fails(
        &format!(
            "{TWO_FIELDS}theorem t_bad (n : Nat) : Two.fstf Pp n = Qq (Pp n) := by simp [Two.fstf]\n"
        ),
        "field 0 must not reduce to field 1's value",
    );
}

/// EXPLICIT MODE. `@Two.sndf Nat instTwoNat Pp n` spells the instance
/// argument itself; the unfold substitutes the same `Proj` body, so the
/// reduction must fire identically.
///
/// Pinned Lean (`projmore.lean`, exit 0).
#[test]
fn test_simp_projection_reduces_under_explicit_application() {
    expect_registers(&format!(
        "{TWO_FIELDS}theorem t_at (n : Nat) : @Two.sndf Nat instTwoNat Pp n = Qq (Pp n) := by simp [Two.sndf]\n"
    ));
}

/// NESTED — the arm that reaches the SECOND `reduce_proj` call.
///
/// `Box.run (HasBox.box)` unfolds to `Proj(Box, 0, Proj(HasBox, 0, inst))`.
/// The outer node's structure argument is a `Proj`, not a constant
/// application, so the constant-head pre-check refuses it on the way IN; it
/// can only reduce on the node REBUILT after the congruence descent has
/// reduced the inner one. Delete the post-descent call and this is the arm
/// that goes red.
///
/// Pinned Lean (`projmore.lean`, exit 0 — Lean reports `Box.run` as an unused
/// simp argument because `simpProj` reduces the rebuilt `.proj` node without
/// needing the accessor unfolded).
#[test]
fn test_simp_reduces_a_nested_projection_after_the_congruence_descent() {
    expect_registers(concat!(
        "axiom Qq : Prop -> Prop\n",
        "axiom Pp : Nat -> Prop\n",
        "axiom qEq : forall (p : Prop), Qq p = p\n",
        "structure Box where\n",
        "  run : (Nat -> Prop) -> (Nat -> Prop)\n",
        "class HasBox (A : Type) where\n",
        "  box : Box\n",
        "instance instHasBoxNat : HasBox Nat where\n",
        "  box := Box.mk (fun f => fun a => Qq (f a))\n",
        "theorem t_nested (n : Nat) :\n",
        "  Box.run (@HasBox.box Nat instHasBoxNat) Pp n = Pp n := by\n",
        " simp [HasBox.box, Box.run, qEq]\n",
    ));
}

/// CEILING at a NON-INSTANCE. `whnf_instances` reduces at reducible+instances
/// transparency, so a class-typed plain `def` — neither `@[reducible]` nor a
/// registered instance — must leave the projection stuck.
///
/// Pinned Lean (`projdef.lean`, exit 1): the same file warns
/// "Definition `dCop` of class type must be marked with `@[reducible]` or
/// `@[implicit_reducible]`" and then reports `unsolved goals ⊢ Cop.cop Pp n ↔ Pp n`.
/// The goal is chosen so `rfl` cannot rescue it: closing it needs `qEq` to
/// fire on a `Qq` that only exists once the projection reduces.
#[test]
fn test_simp_leaves_a_projection_on_a_plain_definition_unreduced() {
    expect_fails(
        concat!(
            "axiom Qq : Prop -> Prop\n",
            "axiom Pp : Nat -> Prop\n",
            "axiom qEq : forall (p : Prop), Qq p = p\n",
            "class Cop (A : Type) where\n",
            "  cop : (A -> Prop) -> (A -> Prop)\n",
            "def dCop : Cop Nat := Cop.mk (fun f => fun a => Qq (f a))\n",
            "theorem t_def (n : Nat) : @Cop.cop Nat dCop Pp n = Pp n := by simp [Cop.cop, qEq]\n",
        ),
        "a projection on a class-typed plain `def` must stay folded at \
         reducible+instances transparency, as it does in Lean",
    );
}

// ---------------------------------------------------------------------------
// Pattern eta-normalization
// ---------------------------------------------------------------------------

/// A lemma whose eta-expanded subterm carries TWO binders, matched against a
/// goal LOCAL — the same row shape as `dite_ne_right_iff`, one binder deeper.
///
/// Pinned Lean (`eta2.lean`, exit 0): `simp [lemEta2]` closes both the
/// goal-local and the global-constant arm.
///
/// MEASURED NON-VACUOUS: with the matcher calling `eta_reduce` ONCE — the
/// shape this branch shipped — this arm fails with
/// `simp: no progress made on ⊢ Eq Nat (Hh #F0) (Gg (#F0 0 0))`, because one
/// call contracts only the inner binder (`fun a b => ?x a b` → `fun a => ?x a`)
/// and the matcher, unlike the traversal, never gets a second pass. Closed by
/// `eta_reduce_fixpoint`.
#[test]
fn test_simp_eta_matches_a_two_binder_goal_local_function() {
    expect_registers(concat!(
        "axiom Hh : (Nat -> Nat -> Nat) -> Nat\n",
        "axiom Gg : Nat -> Nat\n",
        "axiom lemEta2 : forall (x : Nat -> Nat -> Nat), Hh (fun a => fun b => x a b) = Gg (x 0 0)\n",
        "theorem t_local2 (A : Nat -> Nat -> Nat) : Hh A = Gg (A 0 0) := by simp [lemEta2]\n",
    ));
}

/// CONTROL for the arm above: the same lemma against a global CONSTANT. An
/// empty matching context can still type a global, so this arm passes with or
/// without any eta work — it is here to show the two-binder LEMMA itself is
/// well formed and offered.
///
/// Pinned Lean (`eta2.lean`, exit 0).
#[test]
fn test_simp_eta_two_binder_pattern_matches_a_global_constant() {
    expect_registers(concat!(
        "axiom Hh : (Nat -> Nat -> Nat) -> Nat\n",
        "axiom Gg : Nat -> Nat\n",
        "axiom Aq2 : Nat -> Nat -> Nat\n",
        "axiom lemEta2 : forall (x : Nat -> Nat -> Nat), Hh (fun a => fun b => x a b) = Gg (x 0 0)\n",
        "theorem t_const2 : Hh Aq2 = Gg (Aq2 0 0) := by simp [lemEta2]\n",
    ));
}

/// NEAR MISS: after `fun h => ?x h` contracts to `?x`, the pattern variable
/// can bind a LAMBDA that is not an eta-expansion of anything — here the
/// constant function `fun _ => c`. Lean matches it too (its `isDefEqEta`
/// eta-expands the other side), and the instantiated conclusion carries the
/// beta-redex `(fun _ => c) h`, which simp must then reduce.
///
/// Pinned Lean (`etaconst2.lean`, exit 0) under `simp only [diteEqRight]`, so
/// no default simp lemma can be doing the work.
#[test]
fn test_simp_eta_reduced_pattern_binds_a_constant_function() {
    expect_registers(concat!(
        "axiom Pp : Prop\n",
        "axiom instPp : Decidable Pp\n",
        "axiom Ww : Nat -> Prop\n",
        "axiom diteEqRight : forall (x : Pp -> Nat) (y : Nat),\n",
        "  (@dite Nat Pp instPp (fun h => x h) (fun _ => y) = y) ↔ (forall (h : Pp), Ww (x h))\n",
        "theorem t_constfun (c : Nat) (b : Nat) :\n",
        "  (@dite Nat Pp instPp (fun _ => c) (fun _ => b) = b) ↔ (forall (hh : Pp), Ww c) := by\n",
        " simp only [diteEqRight]\n",
    ));
}

/// The goal-LOCAL partner of the arm above, under `simp only` and with a
/// right-hand side no default lemma can produce — the package's own eta
/// fixture uses plain `simp`, so this separates "the pattern matched" from
/// "the default set closed it".
///
/// Pinned Lean (`etaconst2.lean`, exit 0).
#[test]
fn test_simp_only_eta_matches_a_goal_local_under_a_distinguishing_rhs() {
    expect_registers(concat!(
        "axiom Pp : Prop\n",
        "axiom instPp : Decidable Pp\n",
        "axiom Ww : Nat -> Prop\n",
        "axiom diteEqRight : forall (x : Pp -> Nat) (y : Nat),\n",
        "  (@dite Nat Pp instPp (fun h => x h) (fun _ => y) = y) ↔ (forall (h : Pp), Ww (x h))\n",
        "theorem t_local (A : Pp -> Nat) (b : Nat) :\n",
        "  (@dite Nat Pp instPp A (fun _ => b) = b) ↔ (forall (h : Pp), Ww (A h)) := by\n",
        " simp only [diteEqRight]\n",
    ));
}

// ---------------------------------------------------------------------------
// Imported-alias precedence ACROSS stages
// ---------------------------------------------------------------------------

/// The goal both namespace arms elaborate, so the two differ ONLY in whether
/// the prefix alias is registered.
const NAMESPACE_GOAL: &str = concat!(
    "namespace Inner\n",
    "theorem t_stage (n : Nat) : Deep.Gg2 n = Deep.Hh2 n := by simp [stageEq]\n",
    "end Inner\n",
);

const ALIAS_IMPORTED: &str = concat!(
    "namespace Deep\n",
    "axiom Gg2 : Nat -> Nat\n",
    "axiom Hh2 : Nat -> Nat\n",
    "axiom Kk2 : Nat -> Nat\n",
    "axiom gh2 : forall (n : Nat), Deep.Gg2 n = Deep.Hh2 n\n",
    "axiom gk2 : forall (n : Nat), Deep.Gg2 n = Deep.Kk2 n\n",
    "end Deep\n",
    "axiom stageEq : forall (n : Nat), Deep.Gg2 n = Deep.Kk2 n\n",
);

/// An imported alias reached at a NAMESPACE PREFIX outranks a root constant of
/// the same short name — Lean's rule, and NOT what "an alias can only make a
/// name that resolved to nothing resolve" would predict. That reading holds
/// only WITHIN one resolution stage; across stages the inner namespace wins,
/// and this fix consults the imported table at every prefix step.
///
/// Ground-truthed (`aliasns.lean`): with `theorem Foo.bar : 1 = 1`, a root
/// `theorem bar : 2 = 2`, and `export Foo (bar)` inside `namespace N`, the
/// pinned binary answers `#check @bar` with `bar : 1 = 1` — the alias target,
/// not the root constant.
///
/// Here the root `stageEq` proves `Gg2 n = Kk2 n` and the `Inner.stageEq`
/// alias points at `Deep.gh2 : Gg2 n = Hh2 n`. Only the alias closes the goal.
///
/// THE VERDICT IS READ OFF THE REGISTERED CONSTANT, NOT OFF THE `Result`, and
/// that is not a style choice: `elaborate_decl_and_register`'s `Namespace` arm
/// (`lib.rs`) deliberately COLLECTS per-inner outcomes into
/// `ElabResult::Failed` leaves instead of `?`-aborting, so a namespace block
/// containing a failing declaration still returns `Ok`. A test that reads only
/// the `Result` — the idiom every root-level fixture in this directory uses —
/// is VACUOUS the moment its source is wrapped in `namespace … end`. Measured:
/// the control below passed as written against an `is_err()` assertion.
#[test]
fn test_imported_alias_at_a_namespace_prefix_outranks_a_root_constant() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, ALIAS_IMPORTED).expect("fixture must elaborate");
    env.register_export_alias(
        Name::from_string("Inner.stageEq"),
        Name::from_string("Deep.gh2"),
    );
    try_elaborate_into(&mut env, NAMESPACE_GOAL).expect("the namespace block itself must run");
    assert!(
        env.get_const(&Name::from_string("Inner.t_stage")).is_some(),
        "the namespace-prefix alias must win over the root constant, so the \
         theorem must be proved and registered"
    );
}

/// The same fixture WITHOUT the prefix alias: the root constant is then the
/// only `stageEq` there is, it rewrites the goal to `Kk2 n = Hh2 n`, and the
/// theorem must NOT be registered. Without this control the arm above could be
/// passing because the root lemma happened to close the goal.
#[test]
fn test_root_constant_alone_does_not_close_the_namespace_prefix_goal() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, ALIAS_IMPORTED).expect("fixture must elaborate");
    try_elaborate_into(&mut env, NAMESPACE_GOAL).expect("the namespace block itself must run");
    assert!(
        env.get_const(&Name::from_string("Inner.t_stage")).is_none(),
        "the root `stageEq` proves Gg2 = Kk2 and must not close Gg2 = Hh2"
    );
}

/// HARNESS GATE for the two arms above, and a finding in its own right: a
/// declaration that fails INSIDE a `namespace` block leaves
/// `elaborate_decl_and_register` returning `Ok`. Pin it, so that if the
/// namespace arm ever starts propagating the error the two tests above are
/// re-read rather than silently weakened — and so the next author of a
/// namespace-scoped fixture does not write the `is_err()` assertion that was
/// written here first.
#[test]
fn test_a_failing_declaration_inside_a_namespace_still_returns_ok() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, ALIAS_IMPORTED).expect("fixture must elaborate");
    let unprovable = concat!(
        "namespace Inner\n",
        "theorem t_unprovable (n : Nat) : Deep.Gg2 n = Deep.Kk2 n := by simp\n",
        "end Inner\n",
    );
    assert!(
        try_elaborate_into(&mut env, unprovable).is_ok(),
        "the namespace arm collects inner failures instead of aborting"
    );
    assert!(
        env.get_const(&Name::from_string("Inner.t_unprovable"))
            .is_none(),
        "the failing inner declaration must not be registered"
    );
}
