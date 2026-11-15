// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PKG4, root cause 2's second face: a PROOF metavariable in an argument of a
//! DEFINED head was never assigned, although unification reported success.
//!
//! `Mathlib/Logic/Basic.lean`'s `Classical.choose_eq` / `choose_eq'` are
//! `@Exists.choose_spec _ (· = a) _`: the trailing `_ : ∃ x, x = a` is fixed
//! only by unifying `Exists.choose ?h =?= Exists.choose ⟨a, rfl⟩`. Lean
//! compares two applications of one constant argument by argument BEFORE it
//! unfolds either (`isDefEqApp`, `Lean/Meta/ExprDefEq.lean:2120-2131`; inside
//! lazy delta, `tryHeuristic`, `:1423-1480`) and assigns `?h := ⟨a, rfl⟩`.
//!
//! Clean reduced both arguments to WHNF first. `Exists.choose` is a
//! definition over `Classical.choice`, so both sides unfolded down to
//! `(choice N₁).val =?= (choice N₂).val` with `N₁`, `N₂` PROOFS of one `Nonempty
//! _`; their comparison ended in the kernel's `is_def_eq`, which answers `true`
//! by proof irrelevance — the metavariable `?h` inside `N₁` is an opaque free
//! variable to the kernel. Unification succeeded, `?h` stayed unassigned, and
//! the declaration died at registration: `Declaration contains free variables
//! (fvar ids [2^63+N])`. The same statement over an AXIOM head passed all
//! along, because WHNF of an axiom application changes nothing and the
//! arguments were compared as written.
//!
//! Every fixture here was ground-truthed on the pinned toolchain
//! (`~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`): no errors.

use crate::tests_pkg4_unifier::{assert_elaborates, elab_after};

/// `Exists.choose`'s shape without `import Init`: a DEFINITION that unfolds to
/// a projection of a choice over a `Nonempty` PROOF built from the argument.
const CHOOSE_BASE: &str = "\
universe u
axiom myCh {α : Sort u} : Nonempty α → α
noncomputable def myIndef {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  myCh (@Exists.elim α p (Nonempty {x // p x}) h (fun x px => Nonempty.intro (Subtype.mk x px)))
noncomputable def myChoose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α := (myIndef p h).val
theorem myChoose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (myChoose h) :=
  (myIndef p h).property
variable {α : Sort u}
";

/// CONTROLS that passed before the fix: the proof argument written out, and
/// the proof argument a LOCAL (`?h =?= h` is a bare-metavariable assignment on
/// every path).
#[test]
fn test_proof_meta_in_defined_head_controls_elaborate() {
    assert_elaborates(
        CHOOSE_BASE,
        "theorem v3 (a : α) : @myChoose _ (· = a) ⟨a, rfl⟩ = a := \
         @myChoose_spec _ (· = a) ⟨a, rfl⟩\n\
         theorem v5 (a : α) (h : ∃ x, x = a) : @myChoose α (fun x => x = a) h = a := \
         @myChoose_spec α (fun x => x = a) _\n",
        "the written-out and local-hypothesis controls",
    );
}

/// `Classical.choose_eq`'s face: the trailing `_` is a proof metavariable
/// fixed only by the expected type, through the defined head `myChoose`.
#[test]
fn test_proof_meta_in_defined_head_is_assigned_from_expected_type() {
    for (name, decl) in [
        (
            "v1 (`·` predicate, `_` type)",
            "theorem v1 (a : α) : @myChoose _ (· = a) ⟨a, rfl⟩ = a := \
             @myChoose_spec _ (· = a) _\n",
        ),
        (
            "v2 (`fun` predicate, `_` type)",
            "theorem v2 (a : α) : @myChoose _ (fun x => x = a) ⟨a, rfl⟩ = a := \
             @myChoose_spec _ (fun x => x = a) _\n",
        ),
        (
            "v4 (everything explicit but the proof)",
            "theorem v4 (a : α) : @myChoose α (fun x => x = a) ⟨a, rfl⟩ = a := \
             @myChoose_spec α (fun x => x = a) _\n",
        ),
    ] {
        if let Some(e) = elab_after(CHOOSE_BASE, decl) {
            panic!("{name} must elaborate and kernel-check (pinned Lean accepts it), got: {e}");
        }
    }
}

/// Init's ACTUAL layering, which the base above flattens: `Exists.choose` is a
/// `@[reducible]` wrapper over `Classical.choose`, and `Exists.choose_spec` is
/// stated with the dotted `P.choose`. A reducible head is the one a WHNF-first
/// comparison unfolds most eagerly, so it is pinned separately.
const CHOOSE_REDUCIBLE_WRAPPER: &str = "\
@[reducible] noncomputable def Exists.choose2 {α : Sort u} {p : α → Prop} (P : ∃ a, p a) : α :=
  myChoose P
theorem Exists.choose2_spec {α : Sort u} {p : α → Prop} (P : ∃ a, p a) : p P.choose2 :=
  myChoose_spec P
";

/// The same three faces through the reducible wrapper. Measured on main's
/// frozen binary (`clean-5e2e6dc0e check`, prelude-only): v1, v2 and v4 die
/// `Declaration contains free variables (fvar ids [2^63+N])`; the written-out
/// and local-hypothesis controls pass. With `import Init` and the real
/// `Exists.choose` (a release build of this branch, 78 s) all of
/// `Classical.choose_eq`'s spellings pass — that run is too heavy for the
/// suite, so this arm is its prelude-only stand-in.
#[test]
fn test_proof_meta_under_reducible_wrapper_is_assigned_from_expected_type() {
    // The wrapper goes BEFORE the base's trailing `variable` line, as in the
    // measured replica: it binds its own `α`.
    const SECTION_VAR: &str = "variable {α : Sort u}\n";
    let defs = CHOOSE_BASE
        .strip_suffix(SECTION_VAR)
        .expect("CHOOSE_BASE ends with its `variable` line");
    let base = format!("{defs}{CHOOSE_REDUCIBLE_WRAPPER}{SECTION_VAR}");
    for (name, decl) in [
        (
            "v1 (`·` predicate, `_` type)",
            "theorem v1 (a : α) : @Exists.choose2 _ (· = a) ⟨a, rfl⟩ = a := \
             @Exists.choose2_spec _ (· = a) _\n",
        ),
        (
            "v2 (`fun` predicate, `_` type)",
            "theorem v2 (a : α) : @Exists.choose2 _ (fun x => x = a) ⟨a, rfl⟩ = a := \
             @Exists.choose2_spec _ (fun x => x = a) _\n",
        ),
        (
            "v4 (everything explicit but the proof)",
            "theorem v4 (a : α) : @Exists.choose2 α (fun x => x = a) ⟨a, rfl⟩ = a := \
             @Exists.choose2_spec α (fun x => x = a) _\n",
        ),
        (
            "v3/v5 (controls: proof written out, proof a local)",
            "theorem v3 (a : α) : @Exists.choose2 _ (· = a) ⟨a, rfl⟩ = a := \
             @Exists.choose2_spec _ (· = a) ⟨a, rfl⟩\n\
             theorem v5 (a : α) (h : ∃ x, x = a) : \
             @Exists.choose2 α (fun x => x = a) h = a := \
             @Exists.choose2_spec α (fun x => x = a) _\n",
        ),
    ] {
        if let Some(e) = elab_after(&base, decl) {
            panic!("{name} must elaborate and kernel-check (pinned Lean accepts it), got: {e}");
        }
    }
}
