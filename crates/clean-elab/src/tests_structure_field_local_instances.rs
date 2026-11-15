// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for the structure/class FIELD-elaboration scope carrying
//! no local instances at all.
//!
//! Queue-C brick 1 (`docs/plans/BRICK_QUEUE_2026-08-31-C.md` §7.1), the census
//! row `DenselyOrdered` at `Mathlib/Order/Basic.lean:964`:
//!
//! ```text
//! Mathlib.Tactic.LE.LE.LT.DenselyOrdered: elaboration error at line 964:
//!   failed to synthesize instance `LT fvar#0`
//! ```
//!
//! ## The mechanism
//!
//! `ElabCtx::elab_structure` pushes the declaration's parameters and each field
//! onto the local stack with `push_local`, and never called
//! `push_local_instance` for any of them. So while a field's TYPE is being
//! elaborated, instance search sees the global table and nothing else — the
//! declaration's own `[LT α]` is a local that synthesis cannot reach.
//!
//! ## Ground truth, taken from the pinned toolchain and NOT from `def`
//!
//! Measured against `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`
//! with `set_option pp.parens true`. Lean's rule is `Lean.Meta.withNewFVar`:
//! it consults `isClass? fvarType` and, when that answers, calls
//! `withNewLocalInstance`. So **every local declaration whose type is a class is
//! a local instance, whatever its binder info** — which is strictly wider than
//! the `BinderInfo::InstImplicit` test `elab_def_body` applies, and wider than
//! the brick's own one-line statement of the rule. Lean accepts all three of
//! the shapes below; Clean rejected all three.
//!
//! ## Why the arms are shaped this way
//!
//! The queue isolated this with a four-arm control, and the controls are the
//! evidence — a fix that makes everything synthesize would satisfy the flipping
//! arms and prove nothing. So this file pins BOTH directions:
//!
//! | arm | must be | reverting the fix |
//! |---|---|---|
//! | `def` with `[LT α]` used in its body | GREEN | stays GREEN |
//! | `class` with no instance binder | GREEN | stays GREEN |
//! | `class` with an UNUSED `[LT α]` binder | GREEN | stays GREEN |
//! | nothing of that class in scope at all | RED | stays RED |
//! | `class`/`structure` field USING its own `[LT α]` | GREEN | goes RED |
//! | later field using an earlier class-typed FIELD | GREEN | goes RED |
//! | field using the `extends` parent subobject | GREEN | goes RED |
//!
//! The last two also pin the **convenient approximation**: restricting the
//! registration to `BinderInfo::InstImplicit` (what `def` does, and the literal
//! reading of the brick) passes every own-binder arm and still fails these two,
//! because a field — including the `toParent` subobject field an `extends`
//! clause synthesizes — carries `BinderInfo::Default`. `extends` is the
//! dominant Mathlib class shape, so that approximation must not go green here.
//!
//! ## The divergence this module used to record is CLOSED (2026-09-10)
//!
//! `def f (α : Type u) (i : MyLT α) ...` — a class-typed binder that is
//! EXPLICIT rather than instance-implicit — is accepted by Lean, and used to
//! be refused by Clean because `elab_def_body` keyed its
//! `push_local_instance` on `BinderInfo::InstImplicit`. Every push site now
//! goes through `binder_is_local_instance` (`infer/instance.rs`), which is
//! blind to binder info exactly as `Lean.Meta.withNewFVar` is, so the `def`
//! path accepts the explicit spelling too. The former failure pin was
//! inverted into `test_def_path_accepts_an_explicit_class_typed_binder_like_lean`
//! the day the widening landed; the four surface spellings are pinned end to
//! end by `tests/fixtures/source_frontier/p28_class_typed_local_is_an_instance.lean`.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

/// Elaborate every declaration in `src`, returning the first error (as its
/// `Debug` rendering) or `None` when all of them registered.
fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// A self-contained one-method class, so no arm depends on what the prelude
/// happens to register. `MyLT` plays `LT`'s role and `MyLT.mylt` plays `<`'s;
/// the queue's own control already showed the notation is irrelevant (writing
/// `LT.lt a b` instead of `a < b` failed identically).
const MY_LT: &str = "class MyLT (a : Type u) where\n  mylt : a -> a -> Prop\n";

fn base_env() -> Environment {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, MY_LT) {
        panic!("the fixture class `MyLT` must elaborate, got: {e}");
    }
    env
}

/// Assert `src` elaborates and kernel-checks in a fresh fixture environment.
fn assert_elaborates(src: &str, label: &str) {
    let mut env = base_env();
    if let Some(e) = elab(&mut env, src) {
        panic!("{label} must elaborate and kernel-check, got: {e}");
    }
}

/// Assert `src` FAILS, and specifically as an instance-synthesis failure naming
/// the class — not as a parse error or some unrelated collapse.
fn assert_fails_to_synthesize(src: &str, label: &str) {
    let mut env = base_env();
    let Some(e) = elab(&mut env, src) else {
        panic!("{label} must NOT elaborate — no instance of `MyLT` is in scope");
    };
    assert!(
        e.contains("MyLT"),
        "{label}: must fail because `MyLT` cannot be synthesized, got: {e}"
    );
}

// ---------------------------------------------------------------------------
// CONTROLS — green before the fix and green after it. If any of these ever goes
// red, the arms below stop discriminating and prove nothing.
// ---------------------------------------------------------------------------

/// Arm A. The `def` path already registered its `[…]` binder as a local
/// instance; this is the behaviour the structure path was measured against.
#[test]
fn test_def_with_instance_binder_is_unchanged() {
    assert_elaborates(
        "def myLt (a : Type u) [MyLT a] (x y : a) : Prop := MyLT.mylt x y\n",
        "arm A (def with [MyLT a])",
    );
}

/// Arm C. A class with no instance binder at all never needed synthesis.
#[test]
fn test_class_without_instance_binder_is_unchanged() {
    assert_elaborates(
        "class CNoInst (a : Type u) : Prop where\n  triv : forall x : a, True\n",
        "arm C (class, no instance binder)",
    );
}

/// Arm D. The binder is PRESENT but unused in every field — this is what proved
/// the defect was the USE and not the binder.
#[test]
fn test_class_with_unused_instance_binder_is_unchanged() {
    assert_elaborates(
        "class CUnused (a : Type u) [MyLT a] : Prop where\n  triv : forall x : a, True\n",
        "arm D (class, [MyLT a] present but unused)",
    );
}

/// The fail-closed control. Nothing of class `MyLT` is in scope, so the field
/// MUST still be refused. Without this arm, "register everything as an
/// instance" or "stop checking" would pass every other test in the file.
#[test]
fn test_field_with_no_instance_in_scope_still_fails_closed() {
    assert_fails_to_synthesize(
        "structure NoInst (a : Type u) : Prop where\n  \
         prop : forall x y : a, MyLT.mylt x y -> True\n",
        "fail-closed control (no MyLT binder anywhere)",
    );
}

// ---------------------------------------------------------------------------
// THE FIX — red before it, green after it.
// ---------------------------------------------------------------------------

/// Arm E, and the census row itself: `class C (α) [LT α]` whose field uses `<`.
/// This is `DenselyOrdered` reduced to its mechanism.
#[test]
fn test_class_field_may_use_the_declarations_own_instance_binder() {
    assert_elaborates(
        "class CUsed (a : Type u) [MyLT a] : Prop where\n  \
         dense : forall x y : a, MyLT.mylt x y -> True\n",
        "arm E (class field uses its own [MyLT a])",
    );
}

/// Arm B. Same shape on a plain `structure`, whose projections keep the
/// instance-implicit binder rather than flattening it — so the two kinds go
/// through different projection code and both need covering.
#[test]
fn test_structure_field_may_use_the_declarations_own_instance_binder() {
    assert_elaborates(
        "structure SDense (a : Type u) [MyLT a] : Prop where\n  \
         dense : forall x y : a, MyLT.mylt x y -> True\n",
        "arm B (structure field uses its own [MyLT a])",
    );
}

/// MUTATION GUARD 1. The instance arrives as an EXPLICIT earlier field, whose
/// binder info is `Default`. Keying the registration on
/// `BinderInfo::InstImplicit` — the convenient approximation — leaves this red.
#[test]
fn test_later_field_may_use_an_earlier_class_typed_field() {
    assert_elaborates(
        "structure EarlierField (a : Type u) where\n  \
         inner : MyLT a\n  \
         prop  : forall x y : a, MyLT.mylt x y -> True\n",
        "earlier class-typed field is a local instance",
    );
}

/// MUTATION GUARD 2, and the shape that actually dominates Mathlib: the
/// instance arrives through an `extends` parent subobject, two levels up. The
/// synthesized `toMyPO` field is `BinderInfo::Default`, so this is the second
/// arm the `InstImplicit`-only approximation cannot pass.
#[test]
fn test_field_may_use_an_instance_from_the_extends_parent() {
    assert_elaborates(
        // NB: the field is `refl`, not `rfl` — the latter is reserved and the
        // fixture dies in parser recovery before the elaborator is reached.
        "class MyPO (a : Type u) extends MyLT a where\n  \
         refl : forall x : a, True\n\
         class MyOrd (a : Type u) extends MyPO a where\n  \
         more : forall x y : a, MyLT.mylt x y -> True\n",
        "extends-parent subobject is a local instance",
    );
}

// ---------------------------------------------------------------------------
// The divergence this file recorded is CLOSED (6f3f83dec, 2026-09-10).
// ---------------------------------------------------------------------------

/// Lean accepts `def f (a : Type u) (i : MyLT a) …` — `Lean.Meta.withNewFVar`
/// is blind to binder info — and so does Clean now: `binder_is_local_instance`
/// (`infer/instance.rs`) makes ANY local whose type is a class a local
/// instance at every push site, the `def` path included. This test used to be
/// pinned as a FAILURE with the instruction to invert it the day the `def`
/// path was widened; that day was 2026-09-10, and the four spellings are
/// pinned end to end by `tests/fixtures/source_frontier/p28_class_typed_local_is_an_instance.lean`.
#[test]
fn test_def_path_accepts_an_explicit_class_typed_binder_like_lean() {
    let mut env = base_env();
    let err = elab(
        &mut env,
        "def explicitInst (a : Type u) (i : MyLT a) (x y : a) : Prop := MyLT.mylt x y\n",
    );
    assert!(
        err.is_none(),
        "an explicit class-typed binder is a local instance on the `def` path, as in Lean: {err:?}"
    );
}
